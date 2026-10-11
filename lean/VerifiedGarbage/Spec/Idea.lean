module

public import VerifiedGarbage.TCB.Mem

/-!
# IDEA and ECB

**Trusted.** IDEA (the International Data Encryption Algorithm) is
transcribed from X. Lai, *On the Design and Security of Block Ciphers*,
ETH Series in Information Processing, vol. 1, Hartung-Gorre, 1992, §3.3
(as published in Lai and Massey, "A Proposal for a New Block Encryption
Standard", EUROCRYPT '90, with the modified, "IPES" key schedule of
EUROCRYPT '91): eight rounds and an output transformation on four 16-bit
words, from 52 16-bit subkeys.

The operations are ⊕ (bitwise XOR of words), ⊞ (addition modulo 2¹⁶) and
⊙ (multiplication modulo 2¹⁶ + 1, a prime, of the nonzero residues, where
the word 0 stands for 2¹⁶ and the product 2¹⁶ is the word 0).

* Encryption subkeys: the 128-bit key, as eight words, most significant
  first, gives the first eight subkeys; the key is then rotated left by 25
  bits, giving the next eight, and so on to 52.
* A round, with subkeys `Z₁ … Z₆`, maps `(X₁, X₂, X₃, X₄)` to
  `(X₁ ⊙ Z₁ ⊕ t₁, X₃ ⊞ Z₃ ⊕ t₁, X₂ ⊞ Z₂ ⊕ t₂, X₄ ⊙ Z₄ ⊕ t₂)`, where
  `t₀ = ((X₁ ⊙ Z₁) ⊕ (X₃ ⊞ Z₃)) ⊙ Z₅`,
  `t₁ = (((X₂ ⊞ Z₂) ⊕ (X₄ ⊙ Z₄)) ⊞ t₀) ⊙ Z₆` and `t₂ = t₀ ⊞ t₁`
  (the middle words are exchanged).
* The output transformation, with `Z₄₉ … Z₅₂`, maps the last round's
  output `(X₁, X₂, X₃, X₄)` to `(X₁ ⊙ Z₄₉, X₃ ⊞ Z₅₀, X₂ ⊞ Z₅₁, X₄ ⊙ Z₅₂)`:
  it undoes the last round's exchange.
* Decryption is the same computation with the decryption subkeys: for
  `r = 1 … 9`, the first and fourth of round `r`'s (or the output
  transformation's) are the ⊙-inverses of the first and fourth of
  encryption round `10 - r`; the second and third are the ⊞-negations of
  the third and second (of the second and third, for `r = 1` and `r = 9`);
  and the fifth and sixth (`r ≤ 8`) are the fifth and sixth of encryption
  round `9 - r`.

The ⊙-inverse of `x` is `x ^ (2¹⁶ - 1)` modulo 2¹⁶ + 1: the nonzero
residues form a group of order 2¹⁶ (Fermat), and 0, standing for
2¹⁶ ≡ -1, is its own inverse.

Blocks and keys are big-endian words in memory, as in the published test
vectors (NESSIE's among them); the subkey schedules are 52 little-endian
16-bit words. ECB applies the cipher independently to each block (SP
800-38A §6.1). All key bytes, subkeys and data are secret in the contracts;
nothing here permits secret-dependent branches or memory access in an
implementation of ⊙ or of the inverse.
-/

@[expose] public section

namespace VG.Spec.Idea

abbrev Word := BitVec 16
abbrev Block := Vector Byte 8
abbrev State := Vector Word 4
/-- 52 subkeys, `Z₁ … Z₅₂` at indices 0–51. -/
abbrev Schedule := Vector Word 52

/-- The residue modulo 2¹⁶ + 1 that a word stands for: 0 stands for 2¹⁶. -/
def residue (a : Word) : Nat := if a = 0 then 2 ^ 16 else a.toNat

/-- ⊙: multiplication modulo 2¹⁶ + 1; a product of 2¹⁶ is the word 0. -/
def mul (a b : Word) : Word :=
  BitVec.ofNat 16 (residue a * residue b % (2 ^ 16 + 1))

/-- `a ^ e` modulo `m`, by square-and-multiply, with reduction at every step
(as `Spec.Dsa.powMod`). -/
def powMod (a e m : Nat) : Nat :=
  if e = 0 then 1 % m else
    let t := powMod a (e / 2) m
    let u := t * t % m
    if e % 2 = 0 then u else u * a % m
termination_by e
decreasing_by omega

/-- The ⊙-inverse, `a ^ (2¹⁶ - 1)` modulo 2¹⁶ + 1. -/
def inv (a : Word) : Word :=
  BitVec.ofNat 16 (powMod (residue a) (2 ^ 16 - 1) (2 ^ 16 + 1))

/-- The key as a 128-bit number, its first byte most significant. -/
def keyValue (key : Vector Byte 16) : BitVec 128 :=
  key.toList.foldl (fun out byte => (out <<< 8) ||| byte.zeroExtend 128) 0

/-- The encryption subkeys: subkey `8j + i` (from 0) is word `i` (most
significant first) of the key rotated left by `25 j` bits. -/
def expandKey (key : Vector Byte 16) : Schedule :=
  Vector.ofFn fun n =>
    let k := (keyValue key).rotateLeft (25 * (n.val / 8))
    (k >>> (16 * (7 - n.val % 8))).setWidth 16

/-- One round, with the subkeys `z₁ … z₆`. -/
def round (z₁ z₂ z₃ z₄ z₅ z₆ : Word) (x : State) : State :=
  let a := mul (x.getD 0 0) z₁
  let b := x.getD 1 0 + z₂
  let c := x.getD 2 0 + z₃
  let d := mul (x.getD 3 0) z₄
  let t₀ := mul (a ^^^ c) z₅
  let t₁ := mul ((b ^^^ d) + t₀) z₆
  let t₂ := t₀ + t₁
  #v[a ^^^ t₁, c ^^^ t₁, b ^^^ t₂, d ^^^ t₂]

/-- The output transformation, with `z₁ … z₄` (`Z₄₉ … Z₅₂`). -/
def output (z₁ z₂ z₃ z₄ : Word) (x : State) : State :=
  #v[mul (x.getD 0 0) z₁, x.getD 2 0 + z₂, x.getD 1 0 + z₃, mul (x.getD 3 0) z₄]

/-- Eight rounds and the output transformation under the subkeys `z`:
encryption under `expandKey`, decryption under `invertKey` of it. -/
def crypt (z : Schedule) (x : State) : State :=
  let k (i : Nat) := z.getD i 0
  let x := (List.range 8).foldl (fun x r =>
    round (k (6 * r)) (k (6 * r + 1)) (k (6 * r + 2)) (k (6 * r + 3))
      (k (6 * r + 4)) (k (6 * r + 5)) x) x
  output (k 48) (k 49) (k 50) (k 51) x

/-- The decryption subkeys of the encryption subkeys `z`: decryption round
`r` (from 0; `r = 8` is the output transformation) inverts encryption
round `8 - r`. -/
def invertKey (z : Schedule) : Schedule :=
  let k (i : Nat) := z.getD i 0
  Vector.ofFn fun n =>
    let r := n.val / 6
    let e := 6 * (8 - r)
    let ends := r = 0 ∨ r = 8
    match n.val % 6 with
    | 0 => inv (k e)
    | 1 => -k (if ends then e + 1 else e + 2)
    | 2 => -k (if ends then e + 2 else e + 1)
    | 3 => inv (k (e + 3))
    | 4 => k (6 * (7 - r) + 4)
    | _ => k (6 * (7 - r) + 5)

/-- External blocks are four big-endian words. -/
def decodeBlock (b : Block) : State :=
  Vector.ofFn fun i => (b.getD (2 * i.val) 0 ++ b.getD (2 * i.val + 1) 0 : BitVec 16)

def encodeBlock (x : State) : Block :=
  Vector.ofFn fun i => ((x.getD (i.val / 2) 0) >>> (8 * (1 - i.val % 2))).setWidth 8

def cryptBlock (z : Schedule) (b : Block) : Block :=
  encodeBlock (crypt z (decodeBlock b))

def encryptBlock (key : Vector Byte 16) (b : Block) : Block :=
  cryptBlock (expandKey key) b

def decryptBlock (key : Vector Byte 16) (b : Block) : Block :=
  cryptBlock (invertKey (expandKey key)) b

/-- SP 800-38A §6.1 under the subkeys `z`, including empty input: ECB
encryption under `expandKey`, decryption under `invertKey` of it. -/
def ecb (z : Schedule) (input : List Block) : List Block :=
  input.map (cryptBlock z)

/-! ## Memory layouts for contracts -/

def blockAt (m : Mem) (p : Addr) : Block :=
  Vector.ofFn fun i => m (p + BitVec.ofNat 64 i.val)

def keyAt (m : Mem) (p : Addr) : Vector Byte 16 :=
  Vector.ofFn fun i => m (p + BitVec.ofNat 64 i.val)

/-- 104 bytes: 52 little-endian 16-bit subkeys. -/
def scheduleAt (m : Mem) (p : Addr) : Schedule :=
  Vector.ofFn fun i =>
    m (p + BitVec.ofNat 64 (2 * i.val + 1)) ++ m (p + BitVec.ofNat 64 (2 * i.val))

def blocksAt (m : Mem) (p : Addr) (n : Nat) : List Block :=
  (List.range n).map fun i => blockAt m (p + BitVec.ofNat 64 (8 * i))

end VG.Spec.Idea
