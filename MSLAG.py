import hashlib
import os
from dataclasses import dataclass


# ------------------------------------------------------------
# Эллиптическая кривая secp256k1
# ------------------------------------------------------------
@dataclass
class Point:
    x: int
    y: int
    is_inf: bool = False

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Point):
            return False
        if self.is_inf and other.is_inf:
            return True
        if self.is_inf or other.is_inf:
            return False
        return self.x == other.x and self.y == other.y


# Параметры кривой
P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A = 0
B = 7

# Базовая точка
GX = 55066263022277343669578718895168534326250603453777594175500187360389116729240
GY = 32670510020758816978083085130507043184471273380659243275938904335757337482424
G = Point(GX, GY)
INF = Point(0, 0, is_inf=True)


def egcd(a: int, b: int) -> tuple[int, int, int]:
    """Расширенный алгоритм Евклида"""
    if a == 0:
        return b, 0, 1
    g, y, x = egcd(b % a, a)
    return g, x - (b // a) * y, y


def modinv(a: int, mod: int = P) -> int:
    """Обратный элемент по модулю"""
    a = a % mod
    if a == 0:
        raise ValueError("modular inverse does not exist")
    g, x, _ = egcd(a, mod)
    if g != 1:
        raise ValueError("modular inverse does not exist")
    return x % mod


def point_add(p1: Point, p2: Point) -> Point:
    """Сложение двух точек на эллиптической кривой"""
    if p1.is_inf:
        return p2
    if p2.is_inf:
        return p1

    if p1.x == p2.x and (p1.y + p2.y) % P == 0:
        return INF

    if p1.x == p2.x and p1.y == p2.y:
        if p1.y == 0:
            return INF
        m = (3 * p1.x * p1.x + A) * modinv(2 * p1.y) % P
    else:
        dx = (p2.x - p1.x) % P
        dy = (p2.y - p1.y) % P
        m = dy * modinv(dx) % P

    rx = (m * m - p1.x - p2.x) % P
    ry = (m * (p1.x - rx) - p1.y) % P
    return Point(rx, ry)


def scalar_mult(k: int, point: Point) -> Point:
    """Умножение точки на скаляр (алгоритм double-and-add)"""
    if k == 0 or point.is_inf:
        return INF

    result = INF
    addend = point

    while k:
        if k & 1:
            result = point_add(result, addend)
        addend = point_add(addend, addend)
        k >>= 1

    return result


def hash_to_scalar(*args: int | Point | str) -> int:
    """Хеширование произвольного количества аргументов в скаляр"""
    h = hashlib.sha256()
    for arg in args:
        if isinstance(arg, Point):
            if arg.is_inf:
                h.update(b"inf")
            else:
                h.update(arg.x.to_bytes(32, "big"))
                h.update(arg.y.to_bytes(32, "big"))
        elif isinstance(arg, int):
            h.update(arg.to_bytes(32, "big"))
        elif isinstance(arg, str):
            h.update(arg.encode())
        else:
            h.update(str(arg).encode())
    return int.from_bytes(h.digest(), "big") % N


def hash_to_point(point: Point) -> Point:
    """Отображение точки в другую точку кривой"""
    if point.is_inf:
        return G

    data = point.x.to_bytes(32, "big") + point.y.to_bytes(32, "big")

    for i in range(256):
        h = hashlib.sha256(data + i.to_bytes(1, "big")).digest()
        x_candidate = int.from_bytes(h, "big") % P

        y_sq = (pow(x_candidate, 3, P) + B) % P
        legendre = pow(y_sq, (P - 1) // 2, P)

        if legendre == 1:
            y_candidate = pow(y_sq, (P + 1) // 4, P)
            return Point(x_candidate, y_candidate)

    raise RuntimeError("Cannot map point to curve after 256 attempts")


# ------------------------------------------------------------
# MLSAG протокол
# ------------------------------------------------------------
class MLSAG:
    @staticmethod
    def generate_keys() -> tuple[int, Point]:
        """Генерация пары ключей (секретный, публичный)"""
        sk = int.from_bytes(os.urandom(32), "big") % N
        if sk == 0:
            sk = 1
        pk = scalar_mult(sk, G)
        return sk, pk

    @staticmethod
    def sign(
        message: str,
        public_keys: list[list[Point]],
        real_signer_index: int,
        secret_keys: list[int],
    ) -> dict:
        """
        Генерация MLSAG подписи

        Параметры:
            message: подписываемое сообщение
            public_keys: матрица n x m публичных ключей
            real_signer_index: индекс реального подписанта (0..n-1)
            secret_keys: вектор секретных ключей длины m

        Возвращает:
            словарь с компонентами подписи
        """
        n = len(public_keys)
        m = len(public_keys[0])
        pi = real_signer_index

        if len(secret_keys) != m:
            raise ValueError(f"Expected {m} secret keys, got {len(secret_keys)}")

        # Вычисление образов I_j = x_j * H(P_j^pi)
        images = []
        for j in range(m):
            h_point = hash_to_point(public_keys[pi][j])
            images.append(scalar_mult(secret_keys[j], h_point))

        # Генерация случайных alpha_j
        alpha = [int.from_bytes(os.urandom(32), "big") % N for _ in range(m)]

        # Вычисление L и R для реального подписанта
        L_pi = [scalar_mult(alpha[j], G) for j in range(m)]
        R_pi = []
        for j in range(m):
            h_point = hash_to_point(public_keys[pi][j])
            R_pi.append(scalar_mult(alpha[j], h_point))

        # Начальное значение c_{pi+1}
        hash_input = [message]
        for j in range(m):
            hash_input.append(L_pi[j])
            hash_input.append(R_pi[j])
        c_next = hash_to_scalar(*hash_input)

        c_values = [0] * n
        s_matrix = [[0] * m for _ in range(n)]

        # Обход кольца от pi+1 до pi-1
        i = (pi + 1) % n
        while i != pi:
            for j in range(m):
                s_matrix[i][j] = int.from_bytes(os.urandom(32), "big") % N

            L_i = []
            R_i = []
            for j in range(m):
                term1 = scalar_mult(s_matrix[i][j], G)
                term2 = scalar_mult(c_next, public_keys[i][j])
                L_ij = point_add(term1, term2)

                h_point = hash_to_point(public_keys[i][j])
                term1 = scalar_mult(s_matrix[i][j], h_point)
                term2 = scalar_mult(c_next, images[j])
                R_ij = point_add(term1, term2)

                L_i.append(L_ij)
                R_i.append(R_ij)

            c_values[i] = c_next

            hash_input = [message]
            for j in range(m):
                hash_input.append(L_i[j])
                hash_input.append(R_i[j])
            c_next = hash_to_scalar(*hash_input)

            i = (i + 1) % n

        c_values[pi] = c_next

        # Решение уравнений для s_{pi,j}
        for j in range(m):
            s_matrix[pi][j] = (alpha[j] - (c_values[pi] * secret_keys[j]) % N) % N

        return {
            "images": images,
            "c1": c_values[0],
            "s_matrix": s_matrix,
            "n": n,
            "m": m,
        }

    @staticmethod
    def verify(message: str, public_keys: list[list[Point]], signature: dict) -> bool:
        """
        Проверка MLSAG подписи

        Параметры:
            message: подписанное сообщение
            public_keys: матрица n x m публичных ключей
            signature: словарь с компонентами подписи

        Возвращает:
            True если подпись корректна, иначе False
        """
        images = signature["images"]
        c1 = signature["c1"]
        s_matrix = signature["s_matrix"]
        n = signature["n"]
        m = signature["m"]

        if len(public_keys) != n:
            return False
        for i in range(n):
            if len(public_keys[i]) != m:
                return False

        c_next = c1
        i = 0

        while True:
            L_i = []
            R_i = []

            for j in range(m):
                term1 = scalar_mult(s_matrix[i][j], G)
                term2 = scalar_mult(c_next, public_keys[i][j])
                L_ij = point_add(term1, term2)

                h_point = hash_to_point(public_keys[i][j])
                term1 = scalar_mult(s_matrix[i][j], h_point)
                term2 = scalar_mult(c_next, images[j])
                R_ij = point_add(term1, term2)

                L_i.append(L_ij)
                R_i.append(R_ij)

            hash_input = [message]
            for j in range(m):
                hash_input.append(L_i[j])
                hash_input.append(R_i[j])
            c_next_new = hash_to_scalar(*hash_input)

            i = (i + 1) % n
            if i == 0:
                return c_next_new == c1

            c_next = c_next_new


# ------------------------------------------------------------
# Демонстрация работы
# ------------------------------------------------------------
def main() -> None:
    print("Генерация ключей для 3 участников, каждый имеет 2 ключа")
    n, m = 3, 2

    all_secret_keys = []
    all_public_keys = []

    for i in range(n):
        user_sk = []
        user_pk = []
        for j in range(m):
            sk, pk = MLSAG.generate_keys()
            user_sk.append(sk)
            user_pk.append(pk)
        all_secret_keys.append(user_sk)
        all_public_keys.append(user_pk)
        print(
            f"  Участник {i}: публичные ключи = {[(pk.x % 100, pk.y % 100) for pk in user_pk]}..."
        )

    real_index = 1
    real_secret_keys = all_secret_keys[real_index]
    message = "Пример сообщения для подписи MLSAG"

    print("\nПодписание сообщения...")
    signature = MLSAG.sign(message, all_public_keys, real_index, real_secret_keys)
    print("Подпись создана")

    print("Проверка подписи...")
    valid = MLSAG.verify(message, all_public_keys, signature)
    print(f"Подпись верна: {valid}")

    print("\nГенерация второй подписи с теми же ключами...")
    signature2 = MLSAG.sign(message, all_public_keys, real_index, real_secret_keys)

    print(f"Образы в первой подписи: {[img.x for img in signature['images']]}")
    print(f"Образы во второй подписи: {[img.x for img in signature2['images']]}")

    if all(i1.x == i2.x for i1, i2 in zip(signature["images"], signature2["images"])):
        print("Образы совпадают - подписи связаны (linkable)")
    else:
        print("Образы различаются")


if __name__ == "__main__":
    main()
