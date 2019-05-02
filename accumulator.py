from os import urandom
from math import log2, ceil, floor
from Crypto.Util import number
from hashlib import sha256
from typing import Tuple, Union, Iterable
from collections import namedtuple
from dataclasses import dataclass
import operator

# https://eprint.iacr.org/2018/1188.pdf

RSA_2048 = 25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357

HASH_SIZE_BYTES = 32
HASH_SIZE_BITS = HASH_SIZE_BYTES * 8
HASH = sha256

ADDITIVE_IDENTITY = 0
MULTIPLICATIVE_IDENTITY = 1


def egcd(a: int, b: int) -> Tuple[int, int, int]:
    u, u1 = 1, 0
    v, v1 = 0, 1
    g, g1 = a, b
    while g1:
        q = g // g1
        u, u1 = u1, u - q * u1
        v, v1 = v1, v - q * v1
        g, g1 = g1, g - q * g1
    return g, u, v


def modinv(a: int, m: int) -> int:
    g, x, y = egcd(a, m)
    if g != 1:
        raise Exception('modular inverse does not exist')
    return x % m


def number_bits_bytes_ceil(num: int, max_bits: int = None) -> Tuple[int, int]:
    n_bits = ceil(log2(num))
    if max_bits is not None and n_bits > max_bits:
        n_bits = max_bits
    n_bytes = (n_bits + (8 - (n_bits % 8))) // 8
    return n_bits, n_bytes


def number_bits_bytes_floor(num: int, max_bits: int = None) -> Tuple[int, int]:
    n_bits = floor(log2(num))
    if max_bits is not None and n_bits > max_bits:
        n_bits = max_bits
    n_bytes = (n_bits - (n_bits % 8)) // 8
    return n_bits, n_bytes


def random_prime(n_bits: int, easy_sqrt: bool = False) -> int:
    while True:
        n = number.getPrime(n_bits, urandom)
        if not easy_sqrt:
            return n
        # Congruency to 3 mod 4, means `sqrt(n) <- n^{{p+1}/4}`
        if n % 4 == 3:
            return n


def random_rsa_modulus(n_bits: int, easy_sqrt: bool = False) -> int:
    p = random_prime(n_bits, easy_sqrt)
    q = random_prime(n_bits, easy_sqrt)
    return p * q


def Bezout(x: int, y: int) -> Tuple[int, int]:
    _, a, b = egcd(x, y)
    return a, b


def ShamirTrick(w1: int, w2: int, x: int, y: int) -> int:
    w1_x = pow(w1, x)
    w2_y = pow(w2, y)
    if w1_x == w2_y:
        raise RuntimeError("Equivalent")
    a, b = Bezout(x, y)
    return w1_x * w2_y


def xor_bytes(a: bytes, b: bytes) -> bytes:
    assert len(a) == len(b)
    return bytes(x ^ y for x, y in zip(a, b))


class HashSet(object):
    """
    Maintains a set of items, which can be succinctly represented as a single 32 byte value
    This is used to reduce the overhead of hashing all of the items each time you need that representation
    While still making it easy/fast to update the set without having to re-hash all of the items again
    e.g. turns an `O(n)` operation to re-hash the set into an `O(1)` operation.
    """
    def __init__(self, items=None):
        self._guid = b'\0' * HASH_SIZE_BYTES
        if items:
            for item in items:
                self.add(item)

    @property
    def guid(self) -> bytes:
        return self._guid

    @classmethod
    def as_bytes(cls, item) -> bytes:
        if isinstance(item, bytes):
            return item
        elif isinstance(item, (int, GroupElement)):
            if isinstance(item, GroupElement):
                n_bits = ceil(log2(item.modulus))
                value = item.value
            else:
                n_bits = ceil(log2(item))
                value = item
            n_bits += 8 - (n_bits % 8)
            n_bytes = n_bits // 8
            return int.to_bytes(value, n_bytes, 'little')
        raise TypeError(item)

    @classmethod
    def hash_item(cls, item) -> bytes:
        item_bytes = cls.as_bytes(item)
        result = HASH(item_bytes).digest()
        return result

    def add(self, item) -> bytes:
        hashed_item = self.hash_item(item)
        self._guid = xor_bytes(self._guid, hashed_item)
        return hashed_item

    def remove(self, item) -> bytes:
        hashed_item = self.hash_item(item)
        self._guid = xor_bytes(self._guid, hashed_item)
        return hashed_item


class PrimeSet(object):
    """
    A set of prime numbers (derived from items), where the product of the primes
    is used as its representation.
    """

    def __init__(self, items=None, n_bytes: int = HASH_SIZE_BYTES):
        self._n_bytes = n_bytes
        self._product = MULTIPLICATIVE_IDENTITY
        if items:
            for item in items:
                self.add(items)

    def __contains__(self, item):
        return (self._product % item) == 0

    def as_prime(self, item) -> int:
        """
        Consistently convert 'raw elements' into prime numbers
        suitable for inclusion in an RSA accumulator.
        """
        return hash2prime(item, output_bytes=self._n_bytes)

    @property
    def product(self) -> int:
        return self._product

    def add_prime(self, prime_item) -> int:
        assert prime_item not in self  # ignored when optimised
        assert number.isPrime(prime_item)  # ignored when optimised
        self._product *= prime_item        
        return prime_item

    def add(self, item) -> int:
        return self.add_prime(self.as_prime(item))

    def remove_prime(self, prime_item) -> int:
        assert prime_item in self  # ignored when optimised
        assert number.isPrime(prime_item)  # ignored when optimised
        self._product = self._product // prime_item
        return prime_item

    def remove(self, item) -> int:
        return self.remove_prime(self.as_prime(item))


class PrimeHashSet(object):
    def __init__(self, items=None, n_bytes=HASH_SIZE_BYTES):
        self._ps = PrimeSet(items, n_bytes=n_bytes)
        self._hs = HashSet(items)
        self._items = set()

    def __contains__(self, item):
        return item in self._items

    def as_prime(self, *args) -> int:
        return self._ps.as_prime(*args)

    def __iter__(self):
        return iter(self._items)

    @property
    def guid(self) -> bytes:
        return self._hs.guid

    @property
    def product(self) -> int:
        return self._ps.product

    def add(self, item) -> int:        
        prime_item = self._ps.add(item)
        self._hs.add(item)
        self._items.add(item)
        return prime_item

    def remove(self, item) -> int:
        prime_item = self._ps.remove(item)
        self._hs.remove(item)
        self._items.remove(prime_item)
        return prime_item


class GroupElement(object):
    def __init__(self, value: int, modulus: int):
        self.value = value
        self.modulus = modulus

    @classmethod
    def as_int(cls, other: Union[int, '__class__']):
        if isinstance(other, cls):
            return other.value
        assert isinstance(other, int)
        return other

    def hash_to_group(self, *args) -> '__class__':
        new_value = hash2intmod(self.modulus, *args)
        return __class__(new_value, self.modulus)

    @classmethod
    def generator(cls, modulus) -> '__class__':
        return cls(2, modulus)

    def as_bytes(self, endian='little') -> bytes:
        n_bits, n_bytes = number_bits_bytes_ceil(self.modulus)
        return int.to_bytes(self.value, n_bytes, endian)

    def __repr__(self):
        group_name = "RSA-2048" if self.modulus == RSA_2048 else str(self.modulus)
        return "%s<%d mod %s>" % (type(self).__name__, self.value, group_name)

    def __div__(self, other: Union[int, '__class__']) -> '__class__':
        value = self.as_int(other)
        base = modinv(self.value, self.modulus)
        result = pow(base, value, self.modulus)
        return __class__(result, modulus)

    def __pow__(self, other: Union[int, '__class__'], modulus: int = None) -> '__class__':
        if modulus is not None:
            if modulus != self.modulus:
                raise RuntimeError("Cannot exponentiate using different modulus")
        exponent = self.as_int(other)

        # Allow for negative exponentiation, exponent our inverse by its absolute value
        # e.g. (x ** -10) == (1/x) ** 10
        if exponent < 0:
            base = modinv(self.value, self.modulus)
            exponent = -exponent
        else:
            base = self.value

        result = pow(base, exponent, self.modulus)
        return __class__(result, self.modulus)

    def __int__(self):
        return self.value

    def __mul__(self, other: Union[int, '__class__']):
        value = self.as_int(other)
        return __class__((self.value * value) % self.modulus, self.modulus)

    def __add__(self, other: Union[int, '__class__']):
        value = self.as_int(other)
        return __class__((self.value + value) % self.modulus, self.modulus)

    def __hash__(self):
        return hash((type(self), self.value, self.modulus))

    def __eq__(self, other):
        if isinstance(other, int):
            return self.value == other
        elif isinstance(other, type(self)):
            return self.value == other.value and self.modulus == other.modulus
        raise TypeError("Cannot compare %r with %r" % (self, other))


def as_bytes(*all_items):
    """
    Convert all items into a concatenated sequence of bytes
    """
    result = []
    for item in all_items:
        # Convert item into hashable bytes
        if isinstance(item, GroupElement):
            item = item.as_bytes()
        elif isinstance(item, int):
            _, n_bytes = number_bits_bytes_ceil(item)
            item = int.to_bytes(item, n_bytes, 'little')
        elif not isinstance(item, bytes):
            raise TypeError(item)
        result.append(item)
    return b''.join(result)


def hash2bytes(*items: Union[GroupElement, int, bytes], n_bytes: int = HASH_SIZE_BYTES):
    """
    Convert input items to bytes, concatenate them together, then hash
    Return exactly `n_bytes` worth of hash, truncating the hash and
    extending it by iteratively hashing if more bytes are needed.
    """
    item = as_bytes(*items)
    result = hashed_item = HASH(item).digest()
    while len(result) < n_bytes:
        hashed_item = HASH(hashed_item).digest()
        result += hashed_item
    return result[:n_bytes]


def hash2int(*args, **kwargs):
    return int.from_bytes(hash2bytes(*args, **kwargs), 'little')


def hash2intmod(modulus : int, *args):
    _, n_bytes = number_bits_bytes_ceil(modulus)
    return hash2int(*args, n_bytes=n_bytes) % modulus


def hash2prime(*items: Union[GroupElement, int, bytes], output_bytes: int = HASH_SIZE_BYTES):
    item = as_bytes(*items)

    while True:        
        item = HASH(item).digest()
        i = int.from_bytes(item[:output_bytes], 'little')
        if number.isPrime(i):
            return i


class NI_PoE(object):
    """
    Non-Interactive Proofs of Exponentiation (NI-PoE). See BBF'18 (pages 8 and 42) for details.
    """

    @classmethod
    def prove(cls, base: GroupElement, exp: int, result: GroupElement) -> GroupElement:
        l = hash2prime(base, exp, result)
        q, _ = divmod(exp, l)
        return base ** q

    @classmethod
    def verify(cls, base: GroupElement, exp: int, result: GroupElement, proof: GroupElement) -> bool:
        l = hash2prime(base, exp, result)
        r = exp % l
        w = (proof ** l) * (base ** r)
        return w == result


@dataclass
class NI_PoKE2:
    """
    Non-Interactive Proofs of Knowledge of Exponent (NI-PoKE2).

    See BBF'18:

     - pg 10 (§3.2, "Extending PoKE for general bases")
     - pg 42 (appendix D)
    """

    z: GroupElement
    Q: GroupElement
    r: int

    def __iter__(self) -> Tuple[GroupElement, GroupElement, int]:
        return iter((self.z, self.Q, self.r))

    @classmethod
    def prove(cls, u: GroupElement, x: int, w: GroupElement):
        # u = base
        # x = exponent
        # w = result
        # XXX: cambrian implementation differs with `g`
        #      paper specifies hash to group, cambrian/accumulator uses generator (2)
        g = u.hash_to_group(u, w)
        z = g ** x
        l = hash2prime(u, w, z)
        alpha = hash2int(u, w, z, l)  #  XXX: paper doesn't specify how big \alpha is
        q, r = divmod(x, l)
        Q = (u * (g ** alpha)) ** q   # (ug^a)^q
        return __class__(z, Q, r)

    @classmethod
    def verify(cls, u: GroupElement, w: GroupElement, proof: '__class__'):
        # u = base
        # w = result
        z, Q, r = proof
        g = u.hash_to_group(u, w)
        l = hash2prime(u, w, z)
        alpha = hash2int(u, w, z, l)
        rhs = w * (z ** alpha)
        beta = (u * (g ** alpha)) ** r  #  ug^a
        lhs = (Q ** l) * beta           #  Q^l(ug^a)^r
        return lhs == rhs


@dataclass
class NonMembershipProof:
    item: int
    a: int
    B: GroupElement

    def __iter__(self):
        return iter((self.item, self.a, self.B))


@dataclass
class MembershipProof:
    item: int
    witness: GroupElement

    def __iter__(self):
        return iter((self.item, self.witness))


class Accumulator(object):
    def __init__(self, modulus: int):
        self.p_bits, self.p_bytes = number_bits_bytes_floor(modulus, HASH_SIZE_BITS)
        self.value = self.generator = GroupElement.generator(modulus)
        self._items = PrimeHashSet(n_bytes=self.p_bytes)

    def as_prime(self, *args):
        return self._items.as_prime(*args)

    @property
    def guid(self) -> bytes:
        return self._items.guid

    @property
    def product(self) -> int:
        return self._items.product

    def __iter__(self):
        return iter(self._items)

    def __contains__(self, item):
        return item in self._items

    def add_prime(self, prime_item: int) -> int:
        # We assume primality of item is guaranteed
        old_value = self.value
        self.value = self.value ** prime_item
        return old_value
 
    def add(self, item) -> int:
        if isinstance(item, type(self)):
            item = item.value        
        return self.add_prime(self._items.add(item))

    def DelWMem(self, proof: MembershipProof) -> int:
        """
        BBF'18 pg 16 § 4.2 figure 2

        Remove an item, by providing its witness

         - The witness is the previous value of the accumulator
         - Thus, we verify the witness for the item (proof of inclusion)
         - Then the new value for the accumulator becomes the witness
        """
        item, witness = proof
        if not self.VerMem(item, witness):
            raise KeyError("invalid witness")
        if len(self.items) == 1:
            if witness != int(self.generator):
                raise RuntimeError("With 1 item in set, witness must be generator!")
        prime_item = self._items.remove(item)
        self.value = witness
        return prime_item

    def VerMem(self, item, witness: GroupElement) -> bool:
        prime_item = self._items.as_prime(item)
        result = witness ** prime_item
        return result == self.value

    def BatchAdd(self, items: Iterable[int]):
        """
        BBF'18 pg 16 § 4.2 figure 2

        Perform a batch-update of the accumulator

         - Returns old value, and proof of the exponentation
        """
        x_star = reduce(operator.mul, items)
        old_value = self.value
        self.value = self.value ** x_star
        return old_value, NI_PoE.prove(old_value, x_star, self.value)

    def BatchDel(self, items: Iterable[MembershipProof]):
        """
        BBF'18 pg 16 § 4.2 figure 2

        Given witnesses for many items, delete them all from the accumulator

         - For each of the items, we verify their inclusion.
        """
        items = iter(items)

        proof = next(items)        
        item, witness = proof
        if not self.VerMem(item, witness):
            raise RuntimeError("Invalid witness %r" % (proof,))

        new_value = old_value = self.value
        # new_value = A_{t+1}

        for proof in items:
            x_i, witness = proof
            if not self.VerMem(x_i, witness):
                raise RuntimeError("Invalid witness %r" % (proof,))
            new_value = ShamirTrick(new_value, witness, x_star, x_i)
            x_star *= x_i

        return new_value, NI_PoE.prove(old_value, x_star, new_value)

    def MemWitCreate(self, our_item) -> GroupElement:
        """
        Provide a witness for an item which exists within the accumulator
        This is, essentially, the accumulator but without our item
        """
        assert our_item in self
        witness = self.generator
        for item in self:
            if our_item == item:
                continue
            prime_item = self._items.as_prime(item)
            witness = witness ** prime_item
        return witness

    def NonMemWitCreateFast_cambrial(self, our_item):
        """
        Translated from cambrian/accumulator::`prove_nonmembership`
        """
        # proof = self.NonMemWitCreate(our_item)
        x = self.as_prime(our_item)
        gcd, a, b = egcd(self.product, x)
        # assert gcd != 1
        g = self.generator
        d = g ** a
        v = self.value ** b
        g_inv = g / v
        poke2_proof = NI_PoKE2.prove(self.value, b, v)
        poe_proof = NI_PoE.prove(d, x, g_inv)
        return (d, v, g_inv, poke2_proof, poe_proof)

    def NonMemWitCreateFast_paper(self, s_star, x_star):
        """
        BBF'18 pg 16 `NonMemWitCreate*`
        """
        a, b = Bezout(s_star, x_star)
        V = self.value ** a
        B = self.generator ** b
        pi_V = NI_PoKE2.prove(self.value, a, V)             # V = A^a
        pi_g = NI_PoE.prove(x_star, B, self.generator / V)  # B^x = g * (V^-1)
        # Is this an equivalent proof satisfiable for `VerNonMem`
        return (V, B, pi_V, pi_g)

    def NonMemWitCreate(self, our_item) -> NonMembershipProof:
        x = self.as_prime(our_item)
        g, a, b = egcd(self.product, x)
        """
        # XXX: we allow non-membership proofs to be created
        #      this shows than even invalid non-membership proofs fail to validate
        if g != 1:
            raise RuntimeError("Inputs not co-prime")
        """
        B = self.generator ** b
        return NonMembershipProof(our_item, a, B)

    def VerNonMem(self, proof: NonMembershipProof):
        our_item, a, B = proof
        x = self.as_prime(our_item)
        c = self.value ** a               # A^a
        d = B ** x                        # B^x
        return (c * d) == self.generator  # (A^a)(B^x) == g


# --------------------


if __name__ == "__main__":
    import sys
    """    
    P = 7919
    Q = 7907
    N = P * Q
    Phi = (P-1)*(Q-1)

    A = Accumulator(N)
    our_item = 10
    A.add(our_item)
    found = 0
    for i, x in enumerate(range(2,N-1)):
        wit = A.NonMemWitCreate(x)
        result = A.VerNonMem(wit, x)        
        if result:
            found += 1
        elif x != our_item:
            print('.', log2(Phi), 1/log2(Phi), found/i, A.as_prime(x), A.as_prime(our_item), wit)
    sys.exit(1)
    """

    # PoE test
    exp = 20
    base = GroupElement(2, RSA_2048)
    result = GroupElement(1048576, RSA_2048)
    proof = NI_PoE.prove(base, exp, result)
    assert True == NI_PoE.verify(base, exp, result, proof)

    # PoKE2 test
    proof = NI_PoKE2.prove(base, exp, result)
    assert True == NI_PoKE2.verify(base, result, proof)

    left_acc = Accumulator(RSA_2048)
    left_acc.add(1)
    left_acc.add(2)
    left_wit = left_acc.add(left_acc)
    left_a = left_acc.MemWitCreate(1)
    left_b = left_acc.MemWitCreate(2)

    # Interestingly, the witness for the accumulator is it's self...
    assert left_acc.VerMem(left_wit, left_wit)
    assert left_acc.VerMem(1, left_a)
    assert left_acc.VerMem(2, left_b)

    left_exc = left_acc.NonMemWitCreate(3)
    assert True == left_acc.VerNonMem(left_exc)

    left_exc = left_acc.NonMemWitCreate(1)
    assert False == left_acc.VerNonMem(left_exc)


    # --------------------


    right_acc = Accumulator(RSA_2048)
    right_acc.add(3)
    right_acc.add(4)
    right_wit = right_acc.add(right_acc)
    right_a = right_acc.MemWitCreate(3)
    right_b = right_acc.MemWitCreate(4)

    assert right_acc.VerMem(right_wit, right_wit)
    assert right_acc.VerMem(3, right_a)
    assert right_acc.VerMem(4, right_b)


    # --------------------


    root_acc = Accumulator(RSA_2048)
    root_acc.add(left_acc)
    root_acc.add(right_acc)

    # TODO: prove 'left' exists in 'root'
    # TODO: prove 'right' exists in 'root'

