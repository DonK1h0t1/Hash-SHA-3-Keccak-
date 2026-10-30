import hashlib
import hmac
import os
import sys
import tkinter as tk
from tkinter import messagebox, scrolledtext, ttk

#  параметры и константы 
MASK64 = 0xFFFFFFFFFFFFFFFF
STATE_BYTES = 200          # состояние = 1600 бит = 200 байт = 25 слов по 64 бита
NUM_ROUNDS = 24            # n_r = 12 + 2l, для Keccak-f[1600] l = 6
MIN_ROUNDS, MAX_ROUNDS = 1, 24
SALT_BYTES = 16            # длина случайной соли по умолчанию (128 бит)
SUFFIX_SHA3 = 0x06         # стандарт NIST FIPS 202 (SHA-3)
SUFFIX_KECCAK = 0x01       # оригинальный Keccak
SUFFIX_CSHAKE = 0x04       # cSHAKE (два бита 00 + padding)

# ёмкость c = 200 - r (в байтах), всегда c = 2 * длина хеша
VARIANTS = {
    "SHA3-224": (28, 144, SUFFIX_SHA3),
    "SHA3-256": (32, 136, SUFFIX_SHA3),
    "SHA3-384": (48, 104, SUFFIX_SHA3),
    "SHA3-512": (64, 72, SUFFIX_SHA3),
    "Keccak-256": (32, 136, SUFFIX_KECCAK),
    "Keccak-512": (64, 72, SUFFIX_KECCAK),
}
DEFAULT_VARIANT = "SHA3-256"

# KMAC: rate зависит от уровня безопасности
KMAC_RATES = {
    "KMAC128": 168,   # c = 256 → r = 1344 бит = 168 байт
    "KMAC256": 136,   # c = 512 → r = 1088 бит = 136 байт
}

def rotl64(value: int, n: int) -> int:
    n %= 64
    if n == 0:
        return value
    return ((value << n) | (value >> (64 - n))) & MASK64

def _lfsr_bit(t: int) -> int:
    t %= 255
    if t == 0:
        return 1
    reg = 1
    for _ in range(t):
        reg <<= 1
        if reg & 0x100:
            reg ^= 0x171
    return reg & 1

def make_round_constants() -> list:
    constants = []
    for ir in range(NUM_ROUNDS):
        rc = 0
        for j in range(7):
            if _lfsr_bit(j + 7 * ir):
                rc |= 1 << ((1 << j) - 1)
        constants.append(rc)
    return constants

def make_rho_offsets() -> list:
    offsets = [[0] * 5 for _ in range(5)]
    x, y = 1, 0
    for t in range(24):
        offsets[x][y] = ((t + 1) * (t + 2) // 2) % 64
        x, y = y, (2 * x + 3 * y) % 5
    return offsets

def make_chi_sbox() -> list:
    table = []
    for value in range(32):
        a = [(value >> i) & 1 for i in range(5)]
        out = 0
        for i in range(5):
            bit = a[i] ^ ((1 - a[(i + 1) % 5]) & a[(i + 2) % 5])
            out |= bit << i
        table.append(out)
    return table

ROUND_CONSTANTS = make_round_constants()
RHO_OFFSETS = make_rho_offsets()
CHI_SBOX = make_chi_sbox()

# перестановка Keccak-f[1600] 
def fingerprint(state: list) -> int:
    fp = 0
    for lane in state:
        fp ^= lane
    return fp

def chi_sbox_layer(b: list) -> list:
    out = [0] * 25
    for y in range(5):
        row = b[5 * y:5 * y + 5]
        for z in range(64):
            index = (((row[0] >> z) & 1)
                     | (((row[1] >> z) & 1) << 1)
                     | (((row[2] >> z) & 1) << 2)
                     | (((row[3] >> z) & 1) << 3)
                     | (((row[4] >> z) & 1) << 4))
            value = CHI_SBOX[index]
            for x in range(5):
                out[x + 5 * y] |= ((value >> x) & 1) << z
    return out

def chi_lane_layer(b: list) -> list:
    out = [0] * 25
    for y in range(5):
        for x in range(5):
            out[x + 5 * y] = b[x + 5 * y] ^ ((~b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y] & MASK64)
    return out

def keccak_f(state: list, rounds: int = NUM_ROUNDS, use_sbox: bool = True, log=None) -> list:
    a = list(state)
    for ir in range(NUM_ROUNDS - rounds, NUM_ROUNDS):
        # θ
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ rotl64(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        fp_theta = fingerprint(a)
        # ρ + π
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl64(a[x + 5 * y], RHO_OFFSETS[x][y])
        fp_rhopi = fingerprint(b)
        # χ
        a = chi_sbox_layer(b) if use_sbox else chi_lane_layer(b)
        fp_chi = fingerprint(a)
        # ι
        a[0] ^= ROUND_CONSTANTS[ir]
        if log is not None:
            log.append(f"Раунд {ir + 1:>2}  RC={ROUND_CONSTANTS[ir]:016X}  "
                       f"θ={fp_theta:016X}  ρπ={fp_rhopi:016X}  χ={fp_chi:016X}  ι={fingerprint(a):016X}")
    return a

# padding pad10*1 
def keccak_pad(message: bytes, rate: int, suffix: int) -> bytes:
    pad_len = rate - (len(message) % rate)
    if pad_len == 1:
        return message + bytes([suffix | 0x80])
    return message + bytes([suffix]) + b"\x00" * (pad_len - 2) + b"\x80"

# губка 
def keccak_sponge(message: bytes, rate: int, out_len: int, suffix: int,
                  rounds: int = NUM_ROUNDS, use_sbox: bool = True, log=None) -> bytes:
    padded = keccak_pad(message, rate, suffix)
    state = [0] * 25
    for offset in range(0, len(padded), rate):
        block = padded[offset:offset + rate]
        for i in range(rate // 8):
            state[i] ^= int.from_bytes(block[8 * i:8 * i + 8], "little")
        state = keccak_f(state, rounds, use_sbox, log if offset == 0 else None)
    output = b""
    while True:
        output += b"".join(state[i].to_bytes(8, "little") for i in range(rate // 8))
        if len(output) >= out_len:
            return output[:out_len]
        state = keccak_f(state, rounds, use_sbox)

def keccak_hash(data: bytes, variant: str = DEFAULT_VARIANT, rounds: int = NUM_ROUNDS,
                use_sbox: bool = True, log=None) -> bytes:
    out_len, rate, suffix = VARIANTS[variant]
    return keccak_sponge(data, rate, out_len, suffix, rounds, use_sbox, log)

# кодирование SP 800-185 
def left_encode(x: int) -> bytes:
    """left_encode(x) = n || x (big-endian), n — число байт x"""
    if x == 0:
        return b"\x01\x00"
    n = (x.bit_length() + 7) // 8
    return bytes([n]) + x.to_bytes(n, "big")

def right_encode(x: int) -> bytes:
    """right_encode(x) = x (big-endian) || n"""
    if x == 0:
        return b"\x00\x01"
    n = (x.bit_length() + 7) // 8
    return x.to_bytes(n, "big") + bytes([n])

def encode_string(s: bytes) -> bytes:
    """encode_string(S) = left_encode(len(S)*8) || S"""
    return left_encode(len(s) * 8) + s

def bytepad(X: bytes, w: int) -> bytes:
    """bytepad(X, w) = left_encode(w) || X || zeros  (длина кратна w)"""
    z = left_encode(w) + X
    pad_len = (w - len(z) % w) % w
    return z + b"\x00" * pad_len

#  cSHAKE и KMAC (NIST SP 800-185) 
def cshake(X: bytes, L: int, N: bytes, S: bytes, rate: int,
           rounds: int = NUM_ROUNDS, use_sbox: bool = True) -> bytes:
    """
    cSHAKE128 / cSHAKE256.
    L — длина выхода в битах.
    N — function name. 
    S — customization string.
    rate: 168 для 128-бит, 136 для 256-бит.
    """
    if N == b"" and S == b"":
        # вырождается в SHAKE → суффикс 0x1F
        return keccak_sponge(X, rate, (L + 7) // 8, 0x1F, rounds, use_sbox)
    # bytepad(encode_string(N) || encode_string(S), rate) || X || 00
    prefix = bytepad(encode_string(N) + encode_string(S), rate)
    # суффикс 0x04 = два бита 00 + начало padding
    return keccak_sponge(prefix + X, rate, (L + 7) // 8, SUFFIX_CSHAKE, rounds, use_sbox)

def kmac(key: bytes, message: bytes, out_len: int, customization: bytes = b"",
         security: int = 128, rounds: int = NUM_ROUNDS, use_sbox: bool = True) -> bytes:
    """
    KMAC128 / KMAC256.
    out_len — длина выхода в байтах.
    security: 128 → KMAC128 (rate=168), 256 → KMAC256 (rate=136).
    """
    if security == 128:
        rate = 168
    elif security == 256:
        rate = 136
    else:
        raise ValueError("security должен быть 128 или 256")
    # newX = bytepad(encode_string(K), rate) || X || right_encode(L)
    new_x = bytepad(encode_string(key), rate) + message + right_encode(out_len * 8)
    return cshake(new_x, out_len * 8, b"KMAC", customization, rate, rounds, use_sbox)

#  соль, HMAC, общий compute 
def random_salt_hex() -> str:
    return os.urandom(SALT_BYTES).hex().upper()

def salted_input(message: bytes, salt: bytes) -> bytes:
    return salt + message

def hmac_keccak(key: bytes, message: bytes, variant: str = DEFAULT_VARIANT,
                rounds: int = NUM_ROUNDS, use_sbox: bool = True) -> bytes:
    _, rate, _ = VARIANTS[variant]
    if len(key) > rate:
        key = keccak_hash(key, variant, rounds, use_sbox)
    key = key.ljust(rate, b"\x00")
    inner = keccak_hash(bytes(k ^ 0x36 for k in key) + message, variant, rounds, use_sbox)
    return keccak_hash(bytes(k ^ 0x5C for k in key) + inner, variant, rounds, use_sbox)

def compute_digest(message: bytes, variant: str, rounds: int, use_sbox: bool,
                   salt: bytes = b"", key: bytes = b"",
                   mac_mode: str = "none", customization: bytes = b"") -> bytes:
    """
    mac_mode: "none" | "hmac" | "kmac128" | "kmac256"
    """
    data = salted_input(message, salt)
    if mac_mode == "hmac":
        if not key:
            raise ValueError("Для HMAC нужен ключ")
        return hmac_keccak(key, data, variant, rounds, use_sbox)
    if mac_mode in ("kmac128", "kmac256"):
        if not key:
            raise ValueError("Для KMAC нужен ключ")
        security = 128 if mac_mode == "kmac128" else 256
        # длина выхода берём из выбранного варианта SHA-3 (или фиксируем 32/64)
        out_len = VARIANTS.get(variant, (32, 0, 0))[0]
        return kmac(key, data, out_len, customization, security, rounds, use_sbox)
    # обычный хеш
    return keccak_hash(data, variant, rounds, use_sbox)

def bit_difference(a: bytes, b: bytes) -> int:
    return sum(bin(x ^ y).count("1") for x, y in zip(a, b))

# самопроверка
def self_test() -> list:
    lines, ok_all = [], True

    def check(name, got, expected):
        nonlocal ok_all
        ok = got == expected
        ok_all &= ok
        lines.append(f"[{'OK' if ok else 'ОШИБКА'}] {name}")
        if not ok:
            lines.append(f"      got:      {got.hex() if isinstance(got, bytes) else got}")
            lines.append(f"      expected: {expected.hex() if isinstance(expected, bytes) else expected}")

    # базовые константы
    check("RC[0] = 0x0000000000000001", ROUND_CONSTANTS[0], 0x1)
    check("RC[23] = 0x8000000080008008", ROUND_CONSTANTS[23], 0x8000000080008008)
    check("S-box χ == χ над словами",
          chi_sbox_layer(list(range(1, 26))),
          chi_lane_layer(list(range(1, 26))))

    # SHA-3 vs hashlib
    sha3 = {"SHA3-224": hashlib.sha3_224, "SHA3-256": hashlib.sha3_256,
            "SHA3-384": hashlib.sha3_384, "SHA3-512": hashlib.sha3_512}
    for name, func in sha3.items():
        for size in (0, 1, 3, 71, 72, 135, 136, 137, 300):
            msg = bytes((i * 7 + 3) % 256 for i in range(size))
            check(f"{name}, длина сообщения {size}",
                  keccak_hash(msg, name), func(msg).digest())

    # Keccak 
    check("Keccak-256('')",
          keccak_hash(b"", "Keccak-256").hex(),
          "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
    check("Keccak-256('abc')",
          keccak_hash(b"abc", "Keccak-256").hex(),
          "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")

    # HMAC
    check("HMAC-SHA3-256",
          hmac_keccak(b"secret key", b"hello", "SHA3-256"),
          hmac.new(b"secret key", b"hello", hashlib.sha3_256).digest())
    check("HMAC-SHA3-512, длинный ключ",
          hmac_keccak(b"k" * 200, b"hello", "SHA3-512"),
          hmac.new(b"k" * 200, b"hello", hashlib.sha3_512).digest())

    # официальные тестовые векторы NIST SP 800-185 
    key32 = bytes.fromhex("404142434445464748494A4B4C4D4E4F"
                          "505152535455565758595A5B5C5D5E5F")
    msg4 = bytes.fromhex("00010203")
    msg_long = bytes.fromhex(
        "000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F"
        "202122232425262728292A2B2C2D2E2F303132333435363738393A3B3C3D3E3F"
        "404142434445464748494A4B4C4D4E4F505152535455565758595A5B5C5D5E5F"
        "606162636465666768696A6B6C6D6E6F707172737475767778797A7B7C7D7E7F"
        "808182838485868788898A8B8C8D8E8F909192939495969798999A9B9C9D9E9F"
        "A0A1A2A3A4A5A6A7A8A9AAABACADAEAFB0B1B2B3B4B5B6B7B8B9BABBBCBDBEBF"
        "C0C1C2C3C4C5C6C7")
    custom = b"My Tagged Application"

    # Sample #1: KMAC128, key=32B, data=4B, S="", L=256
    check("KMAC128 Sample #1 (NIST)",
          kmac(key32, msg4, 32, b"", 128).hex().upper(),
          "E5780B0D3EA6F7D3A429C5706AA43A00FADBD7D49628839E3187243F456EE14E")

    # Sample #2: KMAC128, key=32B, data=4B, S="My Tagged Application", L=256
    check("KMAC128 Sample #2 (NIST)",
          kmac(key32, msg4, 32, custom, 128).hex().upper(),
          "3B1FBA963CD8B0B59E8C1A6D71888B7143651AF8BA0A7070C0979E2811324AA5")

    # Sample #3: KMAC128, key=32B, data=long, S="My Tagged Application", L=256
    check("KMAC128 Sample #3 (NIST)",
          kmac(key32, msg_long, 32, custom, 128).hex().upper(),
          "1F5B4E6CCA02209E0DCB5CA635B89A15E271ECC760071DFD805FAA38F9729230")

    # Sample #4: KMAC256, key=32B, data=4B, S="My Tagged Application", L=512
    check("KMAC256 Sample #4 (NIST)",
          kmac(key32, msg4, 64, custom, 256).hex().upper(),
          "20C570C31346F703C9AC36C61C03CB64C3970D0CFC787E9B79599D273A68D2F7"
          "F69D4CC3DE9D104A351689F27CF6F5951F0103F33F4F24871024D9C27773A8DD")

    # Sample #5: KMAC256, key=32B, data=long, S="", L=512
    check("KMAC256 Sample #5 (NIST)",
          kmac(key32, msg_long, 64, b"", 256).hex().upper(),
          "75358CF39E41494E949707927CEE0AF20A3FF553904C86B08F21CC414BCFD691"
          "589D27CF5E15369CBBFF8B9A4C2EB17800855D0235FF635DA82533EC6B759B69")

    lines.append("")
    lines.append("ИТОГ: все проверки пройдены" if ok_all else "ИТОГ: есть ошибки!")
    return lines


# графический интерфейс 
class App:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.last_hash = ""
        root.title("Хеш-функция Keccak")
        root.geometry("760x880")

        tk.Label(root, text="Входной текст:").pack(pady=(10, 2))
        self.text_input = scrolledtext.ScrolledText(root, width=85, height=5)
        self.text_input.insert("1.0", "Пример текста для хеширования")
        self.text_input.pack(padx=10)

        # соль
        tk.Label(root, text=f"Соль (HEX, пусто = без соли; по умолчанию {SALT_BYTES * 2} символов):").pack(pady=(8, 2))
        frame_salt = tk.Frame(root)
        frame_salt.pack()
        self.entry_salt = tk.Entry(frame_salt, width=50, font=("Consolas", 10))
        self.entry_salt.insert(0, random_salt_hex())
        self.entry_salt.pack(side=tk.LEFT, padx=(0, 5))
        tk.Button(frame_salt, text="Сгенерировать", command=self.generate_salt).pack(side=tk.LEFT, padx=2)
        tk.Button(frame_salt, text="Без соли", command=lambda: self.entry_salt.delete(0, tk.END)).pack(side=tk.LEFT, padx=2)

        # ключ
        tk.Label(root, text="Ключ (текст; пусто = обычный хеш):").pack(pady=(8, 2))
        self.entry_key = tk.Entry(root, width=65, font=("Consolas", 10))
        self.entry_key.pack()

        # customization для KMAC
        tk.Label(root, text="Customization (для KMAC, обычно пусто):").pack(pady=(6, 2))
        self.entry_custom = tk.Entry(root, width=65, font=("Consolas", 10))
        self.entry_custom.pack()

        # вариант, раунды, S-box, MAC-режим
        frame_opts = tk.Frame(root)
        frame_opts.pack(pady=(10, 0))
        tk.Label(frame_opts, text="Алгоритм:").pack(side=tk.LEFT)
        self.variant_var = tk.StringVar(value=DEFAULT_VARIANT)
        ttk.Combobox(frame_opts, textvariable=self.variant_var, values=list(VARIANTS),
                     width=14, state="readonly").pack(side=tk.LEFT, padx=(5, 10))

        tk.Label(frame_opts, text="MAC:").pack(side=tk.LEFT)
        self.mac_var = tk.StringVar(value="none")
        ttk.Combobox(frame_opts, textvariable=self.mac_var,
                     values=["none", "hmac", "kmac128", "kmac256"],
                     width=10, state="readonly").pack(side=tk.LEFT, padx=(5, 10))

        tk.Label(frame_opts, text="Раундов:").pack(side=tk.LEFT)
        self.spin_rounds = tk.Spinbox(frame_opts, from_=MIN_ROUNDS, to=MAX_ROUNDS, width=4)
        self.spin_rounds.delete(0, tk.END)
        self.spin_rounds.insert(0, str(NUM_ROUNDS))
        self.spin_rounds.pack(side=tk.LEFT, padx=(5, 10))

        self.sbox_var = tk.BooleanVar(value=True)
        tk.Checkbutton(frame_opts, text="χ через S-box", variable=self.sbox_var).pack(side=tk.LEFT)

        # основные кнопки
        frame_main = tk.Frame(root)
        frame_main.pack(pady=12)
        tk.Button(frame_main, text="Хешировать", width=16, bg="#4CAF50", fg="white",
                  command=self.do_hash).pack(side=tk.LEFT, padx=5)
        tk.Button(frame_main, text="Лавинный эффект", width=16, bg="#2196F3", fg="white",
                  command=self.show_avalanche).pack(side=tk.LEFT, padx=5)

        # служебные
        frame_tools = tk.Frame(root)
        frame_tools.pack()
        for caption, command in (("Параметры r / c", self.show_params),
                                 ("Padding", self.show_padding),
                                 ("Константы RC и ρ", self.show_constants),
                                 ("S-box χ", self.show_sbox)):
            tk.Button(frame_tools, text=caption, command=command).pack(side=tk.LEFT, padx=3)

        frame_tools2 = tk.Frame(root)
        frame_tools2.pack(pady=(4, 0))
        tk.Button(frame_tools2, text="Процесс по раундам (1-й блок)", command=self.show_trace).pack(side=tk.LEFT, padx=3)
        tk.Button(frame_tools2, text="Самопроверка (hashlib + NIST KMAC)", command=self.show_self_test).pack(side=tk.LEFT, padx=3)

        # эталон
        tk.Label(root, text="Эталонный хеш для проверки (HEX):").pack(pady=(10, 2))
        frame_ref = tk.Frame(root)
        frame_ref.pack()
        self.entry_ref = tk.Entry(frame_ref, width=65, font=("Consolas", 10))
        self.entry_ref.pack(side=tk.LEFT, padx=(0, 5))
        tk.Button(frame_ref, text="Сверить", command=self.verify).pack(side=tk.LEFT)

        tk.Label(root, text="Результат:").pack(pady=(10, 2))
        self.text_result = scrolledtext.ScrolledText(root, width=85, height=9, font=("Consolas", 10))
        self.text_result.pack(padx=10)

        frame_res = tk.Frame(root)
        frame_res.pack(pady=10)
        tk.Button(frame_res, text="Копировать хеш", command=self.copy_hash).pack(side=tk.LEFT, padx=5)
        tk.Button(frame_res, text="Хеш → в поле эталона", command=self.hash_to_reference).pack(side=tk.LEFT, padx=5)

    # чтение полей 
    def get_rounds(self) -> int:
        try:
            rounds = int(self.spin_rounds.get())
        except ValueError:
            rounds = NUM_ROUNDS
        return max(MIN_ROUNDS, min(rounds, MAX_ROUNDS))

    def get_salt(self):
        text = "".join(self.entry_salt.get().split())
        try:
            return bytes.fromhex(text) if text else b""
        except ValueError:
            messagebox.showerror("Ошибка", "Соль должна быть в HEX (0-9, A-F), чётное число символов!")
            return None

    def get_message(self) -> bytes:
        return self.text_input.get("1.0", tk.END).rstrip("\n").encode("utf-8")

    def get_key(self) -> bytes:
        return self.entry_key.get().encode("utf-8")

    def get_custom(self) -> bytes:
        return self.entry_custom.get().encode("utf-8")

    # действия 
    def set_result(self, text: str):
        self.text_result.delete("1.0", tk.END)
        self.text_result.insert("1.0", text)

    def show_window(self, title: str, content: str, width: int = 90, height: int = 30):
        win = tk.Toplevel(self.root)
        win.title(title)
        box = scrolledtext.ScrolledText(win, width=width, height=height, font=("Consolas", 10))
        box.pack(padx=10, pady=10, fill=tk.BOTH, expand=True)
        box.insert("1.0", content)

    def do_hash(self):
        salt = self.get_salt()
        if salt is None:
            return
        variant = self.variant_var.get()
        rounds = self.get_rounds()
        key = self.get_key()
        mac_mode = self.mac_var.get()
        custom = self.get_custom()
        try:
            digest = compute_digest(self.get_message(), variant, rounds, self.sbox_var.get(),
                                    salt, key, mac_mode, custom)
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось вычислить: {e}")
            return
        self.last_hash = digest.hex().upper()
        mode_name = {"none": "обычный хеш", "hmac": "HMAC",
                     "kmac128": "KMAC128", "kmac256": "KMAC256"}[mac_mode]
        lines = [f"Алгоритм: {variant}   раундов: {rounds}",
                 f"Режим: {mode_name}",
                 f"Соль: {salt.hex().upper() if salt else '(нет)'}",
                 f"Customization: {custom.decode('utf-8', errors='replace') if custom else '(пусто)'}",
                 f"Длина выхода: {len(digest) * 8} бит", "",
                 "Хеш / MAC (HEX):", self.last_hash]
        if rounds != NUM_ROUNDS:
            lines += ["", "ВНИМАНИЕ: число раундов ≠ 24 — учебный режим,",
                      "результат НЕ совпадает со стандартом."]
        self.set_result("\n".join(lines))

    def verify(self):
        if not self.last_hash:
            messagebox.showinfo("Проверка", "Сначала нажмите «Хешировать».")
            return
        ref = "".join(self.entry_ref.get().split()).upper()
        same = hmac.compare_digest(ref.encode(), self.last_hash.encode())
        messagebox.showinfo("Проверка",
                            "Хеши совпадают — данные не изменены." if same
                            else "Хеши не совпадают — данные, соль, ключ или алгоритм другие.")

    def show_avalanche(self):
        salt = self.get_salt()
        if salt is None:
            return
        data = salted_input(self.get_message(), salt)
        if not data:
            messagebox.showerror("Ошибка", "Нужно непустое сообщение или соль.")
            return
        variant, rounds, key = self.variant_var.get(), self.get_rounds(), self.get_key()
        mac_mode = self.mac_var.get()
        custom = self.get_custom()
        changed = bytes([data[0] ^ 1]) + data[1:]
        try:
            h1 = compute_digest(data, variant, rounds, self.sbox_var.get(), b"", key, mac_mode, custom)
            h2 = compute_digest(changed, variant, rounds, self.sbox_var.get(), b"", key, mac_mode, custom)
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))
            return
        # пересчитываем без соли, т.к. data уже содержит соль
        # (для простоты лавинного эффекта)
        diff, total = bit_difference(h1, h2), len(h1) * 8
        self.show_window("Лавинный эффект", "\n".join([
            "Меняем ровно 1 бит во входных данных и сравниваем выходы.", "",
            f"Было:   {h1.hex().upper()}", f"Стало:  {h2.hex().upper()}", "",
            f"Различается бит: {diff} из {total}  ({diff * 100 / total:.1f} %)",
            "У хорошей хеш/MAC-функции это около 50 %.",
            "При 1–2 раундах процент заметно отличается от 50 %."]), 80, 14)

    def show_params(self):
        out_len, rate, suffix = VARIANTS[self.variant_var.get()]
        mac = self.mac_var.get()
        extra = ""
        if mac == "kmac128":
            extra = "\nKMAC128: rate = 168 байт, capacity = 256 бит"
        elif mac == "kmac256":
            extra = "\nKMAC256: rate = 136 байт, capacity = 512 бит"
        self.show_window("Параметры губки", "\n".join([
            f"Алгоритм: {self.variant_var.get()}", "",
            f"Размер состояния b = r + c = 1600 бит (5×5 слов по 64 бита)",
            f"Скорость r = {rate * 8} бит ({rate} байт)",
            f"Ёмкость  c = {(STATE_BYTES - rate) * 8} бит ({STATE_BYTES - rate} байт)",
            f"Длина хеша d = {out_len * 8} бит",
            f"Суффикс padding: 0x{suffix:02X}",
            f"Раундов в стандарте: {NUM_ROUNDS}",
            extra,
            "",
            f"Стойкость к коллизиям ≈ 2^{out_len * 4}, к прообразу ≈ 2^{out_len * 8}"]), 80, 16)

    def show_padding(self):
        salt = self.get_salt()
        if salt is None:
            return
        _, rate, suffix = VARIANTS[self.variant_var.get()]
        data = salted_input(self.get_message(), salt)
        padded = keccak_pad(data, rate, suffix)
        lines = [f"Вход (соль + сообщение), байт: {len(data)}", f"Скорость r = {rate} байт",
                 f"После padding: {len(padded)} байт = {len(padded) // rate} блок(ов)",
                 f"Добавлено байт: {len(padded) - len(data)}", ""]
        for i in range(0, len(padded), rate):
            lines.append(f"Блок {i // rate + 1}: {padded[i:i + rate].hex().upper()}")
        lines += ["", f"Хвост: суффикс 0x{suffix:02X}, нули, последний байт 0x80."]
        self.show_window("Padding pad10*1", "\n".join(lines), 100, 16)

    def show_constants(self):
        lines = ["Раундовые константы RC[i] (шаг ι):"]
        lines += [f"RC[{i:>2}] = {rc:016X}" for i, rc in enumerate(ROUND_CONSTANTS)]
        lines += ["", "Сдвиги ρ r[x][y] (строки — y, столбцы — x):"]
        for y in range(5):
            lines.append("   ".join(f"{RHO_OFFSETS[x][y]:>2}" for x in range(5)))
        self.show_window("Константы Keccak", "\n".join(lines), 50, 38)

    def show_sbox(self):
        lines = ["S-box шага χ (5 бит → 5 бит):", ""]
        for v, out in enumerate(CHI_SBOX):
            lines.append(f"{v:>2}  {v:05b}  →  {out:>2}  {out:05b}")
        lines += ["", "Формула: b[x] = a[x] XOR ((NOT a[x+1]) AND a[x+2])"]
        self.show_window("S-box χ", "\n".join(lines), 62, 38)

    def show_trace(self):
        salt = self.get_salt()
        if salt is None:
            return
        variant, rounds = self.variant_var.get(), self.get_rounds()
        _, rate, suffix = VARIANTS[variant]
        data = salted_input(self.get_message(), salt)
        log = [f"{variant}: первый блок после padding поглощается нулевым состоянием.",
               "Для каждого шага показан «отпечаток» состояния (XOR всех 25 слов).", ""]
        keccak_sponge(data, rate, VARIANTS[variant][0], suffix, rounds, self.sbox_var.get(), log)
        self.show_window("Процесс по раундам (первый блок)", "\n".join(log), 120, 30)

    def show_self_test(self):
        self.show_window("Самопроверка", "\n".join(self_test()), 80, 40)

    def generate_salt(self):
        self.entry_salt.delete(0, tk.END)
        self.entry_salt.insert(0, random_salt_hex())

    def copy_hash(self):
        if self.last_hash:
            self.root.clipboard_clear()
            self.root.clipboard_append(self.last_hash)

    def hash_to_reference(self):
        self.entry_ref.delete(0, tk.END)
        self.entry_ref.insert(0, self.last_hash)


if __name__ == "__main__":
    if "--test" in sys.argv:
        print("\n".join(self_test()))
    else:
        window = tk.Tk()
        App(window)
        window.mainloop()