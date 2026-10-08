import VerifiedGarbage.TCB.Mem

/-!
# Camellia (RFC 3713)

**Trusted** (as every file in `Spec/`). The block cipher Camellia,
transcribed from RFC 3713, *A Description of the Camellia Encryption
Algorithm* (April 2004, https://www.rfc-editor.org/rfc/rfc3713.txt);
section numbers below refer to it. Keys of 128, 192 and 256 bits are
covered; blocks are 128 bits. ECB applies the cipher independently to each
block (SP 800-38A §6.1).

The RFC's 64- and 128-bit variables are `BitVec`s, and its operators the
`BitVec` ones: `>>`/`<<` are `>>>`/`<<<`, `<<<` (rotation) is `rotateLeft`,
`^`, `&`, `|` and `~` are `^^^`, `&&&`, `|||` and `~~~`, and `& MASKn` of a
wider value is `setWidth n`. Keys, plaintexts and ciphertexts are strings
of bytes, read as big-endian numbers (§2.1: "the leftmost bit is the most
significant"; Appendix A gives them as bytes in that order).

SBOX1 is copied from the table of §2.4.1; `VerifiedGarbageTest/Camellia.lean`
checks it, and the whole cipher, against the RFC's text and its known
answers, and against NTT's published vectors.

The schedule's layout in memory (`scheduleWords`) is this specification's
own choice, shared by every implementation: the 64-bit subkeys in the order
encryption uses them, each as its 8 bytes, most significant first.
-/

namespace VG.Spec.Camellia

/-! ## The S-boxes (§2.4.1) -/

/-- §2.4.1, SBOX1, in printed order: row `0x10 * r`, column `c` is
`SBOX1[16 r + c]` (in decimal, as printed). -/
def sbox1Table : Vector Byte 256 :=
  let rows : Vector (Vector Byte 16) 16 := #v[
    #v[112, 130, 44, 236, 179, 39, 192, 229, 228, 133, 87, 53, 234, 12, 174, 65],
    #v[35, 239, 107, 147, 69, 25, 165, 33, 237, 14, 79, 78, 29, 101, 146, 189],
    #v[134, 184, 175, 143, 124, 235, 31, 206, 62, 48, 220, 95, 94, 197, 11, 26],
    #v[166, 225, 57, 202, 213, 71, 93, 61, 217, 1, 90, 214, 81, 86, 108, 77],
    #v[139, 13, 154, 102, 251, 204, 176, 45, 116, 18, 43, 32, 240, 177, 132, 153],
    #v[223, 76, 203, 194, 52, 126, 118, 5, 109, 183, 169, 49, 209, 23, 4, 215],
    #v[20, 88, 58, 97, 222, 27, 17, 28, 50, 15, 156, 22, 83, 24, 242, 34],
    #v[254, 68, 207, 178, 195, 181, 122, 145, 36, 8, 232, 168, 96, 252, 105, 80],
    #v[170, 208, 160, 125, 161, 137, 98, 151, 84, 91, 30, 149, 224, 255, 100, 210],
    #v[16, 196, 0, 72, 163, 247, 117, 219, 138, 3, 230, 218, 9, 63, 221, 148],
    #v[135, 92, 131, 2, 205, 74, 144, 51, 115, 103, 246, 243, 157, 127, 191, 226],
    #v[82, 155, 216, 38, 200, 55, 198, 59, 129, 150, 111, 75, 19, 190, 99, 46],
    #v[233, 121, 167, 140, 159, 110, 188, 142, 41, 245, 249, 182, 47, 253, 180, 89],
    #v[120, 152, 6, 106, 231, 70, 113, 186, 212, 37, 171, 66, 136, 162, 141, 250],
    #v[114, 7, 185, 85, 248, 238, 172, 10, 54, 73, 42, 104, 60, 56, 241, 164],
    #v[64, 40, 211, 123, 187, 201, 67, 193, 21, 227, 173, 244, 119, 199, 128, 158]]
  rows.flatten

/-- `SBOX1[x]`. -/
def sbox1 (x : Byte) : Byte := sbox1Table.getD x.toNat 0

/-- `SBOX2[x] = SBOX1[x] <<< 1`. -/
def sbox2 (x : Byte) : Byte := (sbox1 x).rotateLeft 1

/-- `SBOX3[x] = SBOX1[x] <<< 7`. -/
def sbox3 (x : Byte) : Byte := (sbox1 x).rotateLeft 7

/-- `SBOX4[x] = SBOX1[x <<< 1]`. -/
def sbox4 (x : Byte) : Byte := sbox1 (x.rotateLeft 1)

/-! ## The F-, FL- and FLINV-functions (§2.4) -/

/-- §2.4.1, `F(F_IN, KE)`: `t1 … t8` are the bytes of `x = F_IN ^ KE`,
`t1` the most significant, and `F_OUT` the bytes `y1 … y8`, `y1` the most
significant. -/
def f (fIn ke : BitVec 64) : BitVec 64 :=
  let x := fIn ^^^ ke
  let t (i : Nat) : Byte := (x >>> (64 - 8 * i)).setWidth 8
  let t1 := sbox1 (t 1)
  let t2 := sbox2 (t 2)
  let t3 := sbox3 (t 3)
  let t4 := sbox4 (t 4)
  let t5 := sbox2 (t 5)
  let t6 := sbox3 (t 6)
  let t7 := sbox4 (t 7)
  let t8 := sbox1 (t 8)
  let y1 := t1 ^^^ t3 ^^^ t4 ^^^ t6 ^^^ t7 ^^^ t8
  let y2 := t1 ^^^ t2 ^^^ t4 ^^^ t5 ^^^ t7 ^^^ t8
  let y3 := t1 ^^^ t2 ^^^ t3 ^^^ t5 ^^^ t6 ^^^ t8
  let y4 := t2 ^^^ t3 ^^^ t4 ^^^ t5 ^^^ t6 ^^^ t7
  let y5 := t1 ^^^ t2 ^^^ t6 ^^^ t7 ^^^ t8
  let y6 := t2 ^^^ t3 ^^^ t5 ^^^ t7 ^^^ t8
  let y7 := t3 ^^^ t4 ^^^ t5 ^^^ t6 ^^^ t8
  let y8 := t1 ^^^ t4 ^^^ t5 ^^^ t6 ^^^ t7
  y1 ++ y2 ++ y3 ++ y4 ++ y5 ++ y6 ++ y7 ++ y8

/-- §2.4.2, `FL(FL_IN, KE)`. -/
def fl (flIn ke : BitVec 64) : BitVec 64 :=
  let x1 : BitVec 32 := (flIn >>> 32).setWidth 32
  let x2 : BitVec 32 := flIn.setWidth 32
  let k1 : BitVec 32 := (ke >>> 32).setWidth 32
  let k2 : BitVec 32 := ke.setWidth 32
  let x2 := x2 ^^^ (x1 &&& k1).rotateLeft 1
  let x1 := x1 ^^^ (x2 ||| k2)
  x1 ++ x2

/-- §2.4.2, `FLINV(FLINV_IN, KE)`, the inverse of `FL`. -/
def flinv (flinvIn ke : BitVec 64) : BitVec 64 :=
  let y1 : BitVec 32 := (flinvIn >>> 32).setWidth 32
  let y2 : BitVec 32 := flinvIn.setWidth 32
  let k1 : BitVec 32 := (ke >>> 32).setWidth 32
  let k2 : BitVec 32 := ke.setWidth 32
  let y1 := y1 ^^^ (y2 ||| k2)
  let y2 := y2 ^^^ (y1 &&& k1).rotateLeft 1
  y1 ++ y2

/-! ## The key schedule (§2.2) -/

/-- §2.2, `Sigma1 … Sigma6`. -/
def sigma1 : BitVec 64 := 0xA09E667F3BCC908B
def sigma2 : BitVec 64 := 0xB67AE8584CAA73B2
def sigma3 : BitVec 64 := 0xC6EF372FE94F82BE
def sigma4 : BitVec 64 := 0x54FF53A5F1D36F1C
def sigma5 : BitVec 64 := 0x10E527FADE682D1D
def sigma6 : BitVec 64 := 0xB05688C2B3E6C1FD

/-- The bytes `bs` as an `n`-bit big-endian number. -/
def ofBytes (n : Nat) (bs : List Byte) : BitVec n :=
  BitVec.ofNat n (bs.foldl (fun acc b => 256 * acc + b.toNat) 0)

/-- §2.2, `KL` and `KR` of the key `K` (the bytes `key`, of 16, 24 or 32):
```
128-bit key K:  KL = K;  KR = 0;
192-bit key K:  KL = K >> 64;  KR = ((K & MASK64) << 64) | (~(K & MASK64));
256-bit key K:  KL = K >> 128; KR = K & MASK128;
``` -/
def klkr (key : List Byte) : BitVec 128 × BitVec 128 :=
  if key.length = 16 then
    let k : BitVec 128 := ofBytes 128 key
    (k, 0)
  else if key.length = 24 then
    let k : BitVec 192 := ofBytes 192 key
    ((k >>> 64).setWidth 128,
      ((k.setWidth 64).setWidth 128 <<< 64) ||| (~~~(k.setWidth 64)).setWidth 128)
  else
    let k : BitVec 256 := ofBytes 256 key
    ((k >>> 128).setWidth 128, k.setWidth 128)

/-- §2.2, `KA` and `KB` from `KL` and `KR`:
```
D1 = (KL ^ KR) >> 64;  D2 = (KL ^ KR) & MASK64;
D2 = D2 ^ F(D1, Sigma1);  D1 = D1 ^ F(D2, Sigma2);
D1 = D1 ^ (KL >> 64);  D2 = D2 ^ (KL & MASK64);
D2 = D2 ^ F(D1, Sigma3);  D1 = D1 ^ F(D2, Sigma4);
KA = (D1 << 64) | D2;
D1 = (KA ^ KR) >> 64;  D2 = (KA ^ KR) & MASK64;
D2 = D2 ^ F(D1, Sigma5);  D1 = D1 ^ F(D2, Sigma6);
KB = (D1 << 64) | D2;
``` -/
def kakb (kl kr : BitVec 128) : BitVec 128 × BitVec 128 :=
  let d1 : BitVec 64 := ((kl ^^^ kr) >>> 64).setWidth 64
  let d2 : BitVec 64 := (kl ^^^ kr).setWidth 64
  let d2 := d2 ^^^ f d1 sigma1
  let d1 := d1 ^^^ f d2 sigma2
  let d1 := d1 ^^^ (kl >>> 64).setWidth 64
  let d2 := d2 ^^^ kl.setWidth 64
  let d2 := d2 ^^^ f d1 sigma3
  let d1 := d1 ^^^ f d2 sigma4
  let ka : BitVec 128 := d1 ++ d2
  let d1 : BitVec 64 := ((ka ^^^ kr) >>> 64).setWidth 64
  let d2 : BitVec 64 := (ka ^^^ kr).setWidth 64
  let d2 := d2 ^^^ f d1 sigma5
  let d1 := d1 ^^^ f d2 sigma6
  let kb : BitVec 128 := d1 ++ d2
  (ka, kb)

/-- The subkeys: `kw1 … kw4`, `k1 … k18` (or `k24`) and `ke1 … ke4` (or
`ke6`), in order. -/
structure Subkeys where
  kw : List (BitVec 64)
  k : List (BitVec 64)
  ke : List (BitVec 64)
  deriving DecidableEq, Repr

/-- `(X <<< r) >> 64`. -/
def hi (x : BitVec 128) (r : Nat) : BitVec 64 := ((x.rotateLeft r) >>> 64).setWidth 64

/-- `(X <<< r) & MASK64`. -/
def lo (x : BitVec 128) (r : Nat) : BitVec 64 := (x.rotateLeft r).setWidth 64

/-- §2.2, the subkeys of a key of 16 bytes (the first list) or of 24 or 32
bytes (the second), in the order the RFC lists them. -/
def expandKey (key : List Byte) : Subkeys :=
  let (kl, kr) := klkr key
  let (ka, kb) := kakb kl kr
  if key.length = 16 then
    { kw := [hi kl 0, lo kl 0, hi ka 111, lo ka 111]
      k := [hi ka 0, lo ka 0, hi kl 15, lo kl 15, hi ka 15, lo ka 15,
        hi kl 45, lo kl 45, hi ka 45, lo kl 60, hi ka 60, lo ka 60,
        hi kl 94, lo kl 94, hi ka 94, lo ka 94, hi kl 111, lo kl 111]
      ke := [hi ka 30, lo ka 30, hi kl 77, lo kl 77] }
  else
    { kw := [hi kl 0, lo kl 0, hi kb 111, lo kb 111]
      k := [hi kb 0, lo kb 0, hi kr 15, lo kr 15, hi ka 15, lo ka 15,
        hi kb 30, lo kb 30, hi kl 45, lo kl 45, hi ka 45, lo ka 45,
        hi kr 60, lo kr 60, hi kb 60, lo kb 60, hi kl 77, lo kl 77,
        hi kr 94, lo kr 94, hi ka 94, lo ka 94, hi kl 111, lo kl 111]
      ke := [hi kr 30, lo kr 30, hi kl 60, lo kl 60, hi ka 77, lo ka 77] }

/-- The number of rounds: 18 for a key of 16 bytes, 24 for one of 24 or 32
(§2.3.1, §2.3.2). -/
def rounds (keyLen : Nat) : Nat := if keyLen = 16 then 18 else 24

/-! ## Encryption and decryption (§2.3) -/

/-- §2.3.1 and §2.3.2: the Feistel network of `sk.k.length` rounds (18 or
24), with `FL` and `FLINV` inserted every 6 rounds:
```
D1 = M >> 64;  D2 = M & MASK64;
D1 = D1 ^ kw1;  D2 = D2 ^ kw2;                // Prewhitening
D2 = D2 ^ F(D1, k1);  D1 = D1 ^ F(D2, k2);    // Rounds 1 and 2
…                                             // and so on, each pair of rounds
D1 = FL(D1, ke1);  D2 = FLINV(D2, ke2);       // before rounds 7, 13 (and 19)
…                                             // with ke3, ke4 (and ke5, ke6)
D2 = D2 ^ kw3;  D1 = D1 ^ kw4;                // Postwhitening
C = (D2 << 64) | D1;
```
Round pair `i` (from 0) is rounds `2i + 1` and `2i + 2`, with subkeys
`k(2i + 1)` and `k(2i + 2)`; it is preceded by `FL` and `FLINV` with
`ke(2j - 1)` and `ke(2j)` when it starts round `6j + 1`, `j ≥ 1`. -/
def encryptWith (sk : Subkeys) (m : BitVec 128) : BitVec 128 :=
  let d1 : BitVec 64 := (m >>> 64).setWidth 64 ^^^ sk.kw.getD 0 0
  let d2 : BitVec 64 := m.setWidth 64 ^^^ sk.kw.getD 1 0
  let (d1, d2) := (List.range (sk.k.length / 2)).foldl (fun (d1, d2) i =>
    let (d1, d2) :=
      if i % 3 = 0 ∧ i ≠ 0 then
        let j := i / 3
        (fl d1 (sk.ke.getD (2 * j - 2) 0), flinv d2 (sk.ke.getD (2 * j - 1) 0))
      else (d1, d2)
    let d2 := d2 ^^^ f d1 (sk.k.getD (2 * i) 0)
    let d1 := d1 ^^^ f d2 (sk.k.getD (2 * i + 1) 0)
    (d1, d2)) (d1, d2)
  let d2 := d2 ^^^ sk.kw.getD 2 0
  let d1 := d1 ^^^ sk.kw.getD 3 0
  d2 ++ d1

/-- §2.3.3: decryption is encryption with the order of the subkeys reversed:
`kw1 ↔ kw3`, `kw2 ↔ kw4`, `k1 ↔ k18` (or `k24`), `k2 ↔ k17` (`k23`), …,
`ke1 ↔ ke4` (`ke6`), `ke2 ↔ ke3` (`ke5`), …. -/
def reverseSubkeys (sk : Subkeys) : Subkeys :=
  { kw := [sk.kw.getD 2 0, sk.kw.getD 3 0, sk.kw.getD 0 0, sk.kw.getD 1 0]
    k := sk.k.reverse
    ke := sk.ke.reverse }

def decryptWith (sk : Subkeys) (c : BitVec 128) : BitVec 128 :=
  encryptWith (reverseSubkeys sk) c

/-! ## Blocks and ECB -/

abbrev Block := Vector Byte 16

/-- A block as a 128-bit number, its first byte the most significant. -/
def decodeBlock (b : Block) : BitVec 128 := ofBytes 128 b.toList

/-- The bytes of a 128-bit number, the most significant first. -/
def encodeBlock (x : BitVec 128) : Block :=
  Vector.ofFn fun i => (x >>> (8 * (15 - i.val))).setWidth 8

def encryptBlock (sk : Subkeys) (b : Block) : Block := encodeBlock (encryptWith sk (decodeBlock b))

def decryptBlock (sk : Subkeys) (b : Block) : Block := encodeBlock (decryptWith sk (decodeBlock b))

inductive Direction | encrypt | decrypt
  deriving DecidableEq, Repr

/-- SP 800-38A §6.1, including empty input. -/
def ecb (sk : Subkeys) (direction : Direction) (input : List Block) : List Block :=
  input.map (match direction with | .encrypt => encryptBlock sk | .decrypt => decryptBlock sk)

/-! ## The schedule in memory

The subkeys are stored in the order encryption uses them, as 64-bit words:
`kw1, kw2`, then for each group of six rounds `j` (from 0) its subkeys
`k(6j + 1) … k(6j + 6)` and, but after the last group, `ke(2j + 1)` and
`ke(2j + 2)`; then `kw3, kw4`. Word `2 + 8j + i` is `k(6j + i + 1)` for
`i < 6`, and `8 + 8j`, `9 + 8j` are `ke(2j + 1)`, `ke(2j + 2)` (or `kw3`,
`kw4` after the last group): `8 g + 2` words for `g = rounds / 6` groups,
26 for 18 rounds and 34 for 24. -/

/-- The number of subkeys for `rounds` rounds (18 or 24): 26 or 34. -/
def scheduleLength (rounds : Nat) : Nat := 8 * (rounds / 6) + 2

/-- The subkeys as stored, in the order encryption uses them. -/
def scheduleWords (sk : Subkeys) : List (BitVec 64) :=
  let groups := sk.k.length / 6
  [sk.kw.getD 0 0, sk.kw.getD 1 0] ++
    (List.range groups).flatMap (fun j =>
      (sk.k.drop (6 * j)).take 6 ++
        if j + 1 < groups then [sk.ke.getD (2 * j) 0, sk.ke.getD (2 * j + 1) 0] else []) ++
    [sk.kw.getD 2 0, sk.kw.getD 3 0]

/-- The subkeys of `rounds` rounds (18 or 24) from the words as stored. -/
def subkeysOfWords (rounds : Nat) (ws : List (BitVec 64)) : Subkeys :=
  let groups := rounds / 6
  { kw := [ws.getD 0 0, ws.getD 1 0, ws.getD (8 * groups) 0, ws.getD (8 * groups + 1) 0]
    k := (List.range groups).flatMap fun j => (List.range 6).map fun i => ws.getD (2 + 8 * j + i) 0
    ke := (List.range (groups - 1)).flatMap fun j => [ws.getD (8 + 8 * j) 0, ws.getD (9 + 8 * j) 0] }

/-- A word as its 8 bytes, the most significant first. -/
def wordBytes (w : BitVec 64) : List Byte := (List.range 8).map fun i => (w >>> (56 - 8 * i)).setWidth 8

/-- The schedule's bytes, as `vg_camellia_expand_key` writes them. -/
def scheduleBytes (sk : Subkeys) : List Byte := (scheduleWords sk).flatMap wordBytes

/-! ## On memory -/

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- The 64-bit word at `p`, its first byte the most significant. -/
def wordAt (m : Mem) (p : Addr) : BitVec 64 := ofBytes 64 (bytesAt m p 8)

/-- The subkeys of `rounds` rounds (18 or 24) in the schedule at `p`. -/
def subkeysAt (m : Mem) (p : Addr) (rounds : Nat) : Subkeys :=
  subkeysOfWords rounds
    ((List.range (scheduleLength rounds)).map fun i => wordAt m (p + BitVec.ofNat 64 (8 * i)))

def blockAt (m : Mem) (p : Addr) : Block :=
  Vector.ofFn fun i => m (p + BitVec.ofNat 64 i.val)

def blocksAt (m : Mem) (p : Addr) (n : Nat) : List Block :=
  (List.range n).map fun i => blockAt m (p + BitVec.ofNat 64 (16 * i))

end VG.Spec.Camellia
