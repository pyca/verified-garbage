import VerifiedGarbage.TCB.Mem

/-!
# SM3 (GB/T 32905-2016)

**Trusted** (as every file in `Spec/`). The SM3 cryptographic hash function,
transcribed from the English description of GB/T 32905-2016 in
draft-sca-cfrg-sm3-02, *The SM3 Cryptographic Hash Function* (January
2018): https://www.ietf.org/archive/id/draft-sca-cfrg-sm3-02.txt. This is an
expired Internet-Draft, not an RFC; section numbers below refer to it.
Messages are sequences of bytes (the standard allows any number of bits);
every 32-bit word is big-endian (§5.3.3: "All 32-bit words used here are
stored in big-endian format").

SM3 has SHA-256's Merkle–Damgård structure, block size, padding and digest
size; it differs in its initialization vector, its message expansion (68
words `W` and 64 words `W'`), its compression function and its feed-forward,
an exclusive or rather than an addition.

The primitives implemented in assembly are the compression function over a
run of whole blocks (`compressBlocks`), and the streaming (incremental)
interface: initialize, absorb message bytes, pad and output the hash value,
on a streaming state that `Repr` relates to the message absorbed so far.
Their contracts are in `Spec/Sm3/Contract.lean`.
-/

namespace VG.Spec.Sm3

/-- A 32-bit word (§2). -/
abbrev Word := BitVec 32

/-- The eight words `A … H` of a hash value `V_i`, or of the registers of the
compression function (§3.2, §5.3.3). -/
abbrev HashValue := Vector Word 8

/-- A 512-bit message block `B_i`, as sixteen 32-bit words `W_0 … W_15`
(§5.3.2). -/
abbrev Block := Fin 16 → Word

/-! ## Primitives and functions (§4) -/

/-- §4.1: the initialization vector `IV`. -/
def iv : HashValue :=
  #v[0x7380166f, 0x4914b2b9, 0x172442d7, 0xda8a0600, 0xa96f30bc, 0x163138aa, 0xe38dee4d, 0xb0fb0e4e]

/-- §4.2: the constant `T_j`. -/
def T (j : Nat) : Word := if j < 16 then 0x79cc4519 else 0x7a879d8a

/-- §4.3: `FF_j(X, Y, Z)` is `X xor Y xor Z` for `0 ≤ j ≤ 15`, and
`(X and Y) or (X and Z) or (Y and Z)` for `16 ≤ j ≤ 63`. -/
def ff (j : Nat) (x y z : Word) : Word :=
  if j < 16 then x ^^^ y ^^^ z else (x &&& y) ||| (x &&& z) ||| (y &&& z)

/-- §4.3: `GG_j(X, Y, Z)` is `X xor Y xor Z` for `0 ≤ j ≤ 15`, and
`(X and Y) or (not(X) and Z)` for `16 ≤ j ≤ 63`. -/
def gg (j : Nat) (x y z : Word) : Word :=
  if j < 16 then x ^^^ y ^^^ z else (x &&& y) ||| (~~~x &&& z)

/-- §4.4: `P_0(X) = X xor (X <<< 9) xor (X <<< 17)`. -/
def p0 (x : Word) : Word := x ^^^ x.rotateLeft 9 ^^^ x.rotateLeft 17

/-- §4.4: `P_1(X) = X xor (X <<< 15) xor (X <<< 23)`. -/
def p1 (x : Word) : Word := x ^^^ x.rotateLeft 15 ^^^ x.rotateLeft 23

/-! ## Padding (§5.2) -/

/-- The big-endian bytes of a word. -/
def wordBytes (x : Word) : List Byte :=
  [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8]

/-- §5.2: append the bit `1`, then the least number `k` of `0` bits that
makes the length `≡ 448 (mod 512)`, then `L = num2str(l, 64)`, the message
length `l` in bits as a 64-bit big-endian integer. For a message of bytes,
the `1` bit and the first seven `0` bits are the byte `0x80`. (SM3 is only
defined for `l < 2⁶⁴`, §5.1.) -/
def pad (m : List Byte) : List Byte :=
  let l : BitVec 64 := BitVec.ofNat 64 (8 * m.length)
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++
    ((List.range 8).reverse.map fun i => l.extractLsb' (8 * i) 8)

/-- §5.3.2: `B_i = W_0 || … || W_15`, the block whose `j`-th word is made of
bytes `4j … 4j+3` of `byte` (big-endian). -/
def parseBlock (byte : Nat → Byte) : Block := fun j =>
  (byte (4 * j) ++ byte (4 * j + 1) ++ byte (4 * j + 2) ++ byte (4 * j + 3) : Word)

/-! ## Message expansion (§5.3.2) -/

/-- `W_j = B_i`'s `j`-th word for `0 ≤ j ≤ 15`, and
`W_j = P_1(W_{j-16} xor W_{j-9} xor (W_{j-3} <<< 15)) xor (W_{j-13} <<< 7) xor W_{j-6}`
for `16 ≤ j ≤ 67`.

`expand B j` is the list `[W_{j-1}, W_{j-2}, …, W_0]` (most recent first, so
`W_{j-i}` is at index `i - 1`); building it one word at a time keeps
evaluation linear rather than exponential. -/
def expand (B : Block) : Nat → List Word
  | 0 => []
  | j + 1 =>
    let w := expand B j
    (if h : j < 16 then B ⟨j, h⟩
     else p1 (w[15]! ^^^ w[8]! ^^^ w[2]!.rotateLeft 15) ^^^ w[12]!.rotateLeft 7 ^^^ w[5]!) :: w

/-- `W_j` -/
def W (B : Block) (j : Nat) : Word := (expand B (j + 1)).headD 0

/-- `W'_j = W_j xor W_{j+4}` for `0 ≤ j ≤ 63`. -/
def W' (B : Block) (j : Nat) : Word := W B j ^^^ W B (j + 4)

/-! ## Compression function (§5.3.3) -/

/-- Iteration `j` of the compression function, on the registers
`v = (A, B, C, D, E, F, G, H)`:

    SS1 <- ((A <<< 12) + E + (T_j <<< (j mod 32))) <<< 7
    SS2 <- SS1 xor (A <<< 12)
    TT1 <- FF_j(A, B, C) + D + SS2 + W'_j
    TT2 <- GG_j(E, F, G) + H + SS1 + W_j
    D <- C;  C <- B <<< 9;   B <- A;  A <- TT1
    H <- G;  G <- F <<< 19;  F <- E;  E <- P_0(TT2)

(`+` is addition modulo 2³², §3.1.) -/
def round (B : Block) (v : HashValue) (j : Nat) : HashValue :=
  let a := v[0]; let b := v[1]; let c := v[2]; let d := v[3]
  let e := v[4]; let f := v[5]; let g := v[6]; let h := v[7]
  let ss1 := (a.rotateLeft 12 + e + (T j).rotateLeft (j % 32)).rotateLeft 7
  let ss2 := ss1 ^^^ a.rotateLeft 12
  let tt1 := ff j a b c + d + ss2 + W' B j
  let tt2 := gg j e f g + h + ss1 + W B j
  #v[tt1, a, b.rotateLeft 9, c, p0 tt2, e, f.rotateLeft 19, g]

/-- The registers after iterations `0 … n-1`, starting from `V`. -/
def rounds (V : HashValue) (B : Block) (n : Nat) : HashValue :=
  (List.range n).foldl (round B) V

/-- `V_{i+1} = CF(V_i, B_i) = (A || B || … || H) xor V_i`, after the 64
iterations. -/
def compress (V : HashValue) (B : Block) : HashValue :=
  Vector.zipWith (· ^^^ ·) (rounds V B 64) V

/-! ## Iterative hashing (§5.3.1, §5.3.4) -/

/-- `V` updated with the first `n` 64-byte blocks `B_0 … B_{n-1}` of the bytes
`p`. -/
def compressList (V : HashValue) (p : List Byte) (n : Nat) : HashValue :=
  (List.range n).foldl (fun V i => compress V (parseBlock fun k => p.getD (64 * i + k) 0)) V

/-- The SM3 hash value `y = V_n` of a message (§5.3.4), as 32 big-endian
bytes. -/
def hash (m : List Byte) : List Byte :=
  let p := pad m
  (compressList iv p (p.length / 64)).toList.flatMap wordBytes

/-! ## The compression function on memory

These read the arguments of the assembly primitive from memory: a hash value
is stored as eight native (little-endian) `u32`s, and message blocks are
consecutive runs of 64 bytes. -/

/-- The hash value stored as `[u32; 8]` at `p`. -/
def stateAt (m : Mem) (p : Addr) : HashValue :=
  Vector.ofFn fun j => m.readW (p + BitVec.ofNat 64 (4 * j)) 32

/-- The 64-byte block at `p`. -/
def blockAt (m : Mem) (p : Addr) : Block := parseBlock fun k => m (p + BitVec.ofNat 64 k)

/-- `V` updated with the `n` consecutive blocks at `p`. -/
def compressBlocks (V : HashValue) (m : Mem) (p : Addr) (n : Nat) : HashValue :=
  (List.range n).foldl (fun V i => compress V (blockAt m (p + BitVec.ofNat 64 (64 * i)))) V

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-! ## Streaming

The streaming primitives hash a message given in pieces. Their state is 96
bytes: the hash value after the message's whole blocks (stored as by
`stateAt`), followed by a 64-byte buffer holding the bytes of the message
after its last whole block. The length of the message is not part of the
state: the caller keeps it (in bytes, modulo 2⁶⁴) and passes it to every
call. (Lengths are public, so it may live anywhere; and `pad` only uses the
length modulo 2⁶⁴ bits, which that count determines.) -/

/-- The streaming state at `p` (96 bytes) represents the message `m`: its
hash value is `iv` updated with the `⌊|m| / 64⌋` whole blocks of `m`, and its
buffer starts with the remaining `|m| mod 64` bytes of `m`. The rest of the
buffer is unspecified. -/
def Repr (mem : Mem) (p : Addr) (m : List Byte) : Prop :=
  stateAt mem p = compressList iv m (m.length / 64) ∧
  bytesAt mem (p + 32) (m.length % 64) = m.drop (64 * (m.length / 64))

end VG.Spec.Sm3
