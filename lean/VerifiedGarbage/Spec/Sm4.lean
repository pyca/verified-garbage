import VerifiedGarbage.TCB.Mem

/-!
# SM4 and ECB

**Trusted.** SM4 (GB/T 32907-2016), transcribed from the English description
in draft-ribose-cfrg-sm4-10 (April 2018):
https://www.ietf.org/archive/id/draft-ribose-cfrg-sm4-10.txt.
This is an expired Internet-Draft, not an RFC. Sections 6.1–6.2 define F,
tau, L, L' and the S-box; §§7.1–7.2 define the 32 rounds, final word
reversal and decryption; §7.3 defines the key schedule, FK and CK.
ECB applies the cipher independently to complete blocks (§8.3 and
SP 800-38A §6.1), without padding.

Keys and blocks are 128 bits. Input words and output words are big-endian;
round keys are stored as 32 little-endian 32-bit words for the contracts.
All key bytes, round keys and data are secret. The specification's S-box
lookup does not permit secret-dependent memory accesses in implementations.
-/

namespace VG.Spec.Sm4

abbrev Block := Vector Byte 16
abbrev Word := BitVec 32
/-- `rk_0` through `rk_31`, in encryption order. -/
abbrev Schedule := Vector Word 32
abbrev State := Word × Word × Word × Word

/-- §6.2.3, Figure 1, in row-major order. -/
def sbox : Vector Byte 256 :=
  let rows : Vector (Vector Byte 16) 16 := #v[
    #v[0xD6, 0x90, 0xE9, 0xFE, 0xCC, 0xE1, 0x3D, 0xB7, 0x16, 0xB6, 0x14, 0xC2, 0x28, 0xFB, 0x2C, 0x05],
    #v[0x2B, 0x67, 0x9A, 0x76, 0x2A, 0xBE, 0x04, 0xC3, 0xAA, 0x44, 0x13, 0x26, 0x49, 0x86, 0x06, 0x99],
    #v[0x9C, 0x42, 0x50, 0xF4, 0x91, 0xEF, 0x98, 0x7A, 0x33, 0x54, 0x0B, 0x43, 0xED, 0xCF, 0xAC, 0x62],
    #v[0xE4, 0xB3, 0x1C, 0xA9, 0xC9, 0x08, 0xE8, 0x95, 0x80, 0xDF, 0x94, 0xFA, 0x75, 0x8F, 0x3F, 0xA6],
    #v[0x47, 0x07, 0xA7, 0xFC, 0xF3, 0x73, 0x17, 0xBA, 0x83, 0x59, 0x3C, 0x19, 0xE6, 0x85, 0x4F, 0xA8],
    #v[0x68, 0x6B, 0x81, 0xB2, 0x71, 0x64, 0xDA, 0x8B, 0xF8, 0xEB, 0x0F, 0x4B, 0x70, 0x56, 0x9D, 0x35],
    #v[0x1E, 0x24, 0x0E, 0x5E, 0x63, 0x58, 0xD1, 0xA2, 0x25, 0x22, 0x7C, 0x3B, 0x01, 0x21, 0x78, 0x87],
    #v[0xD4, 0x00, 0x46, 0x57, 0x9F, 0xD3, 0x27, 0x52, 0x4C, 0x36, 0x02, 0xE7, 0xA0, 0xC4, 0xC8, 0x9E],
    #v[0xEA, 0xBF, 0x8A, 0xD2, 0x40, 0xC7, 0x38, 0xB5, 0xA3, 0xF7, 0xF2, 0xCE, 0xF9, 0x61, 0x15, 0xA1],
    #v[0xE0, 0xAE, 0x5D, 0xA4, 0x9B, 0x34, 0x1A, 0x55, 0xAD, 0x93, 0x32, 0x30, 0xF5, 0x8C, 0xB1, 0xE3],
    #v[0x1D, 0xF6, 0xE2, 0x2E, 0x82, 0x66, 0xCA, 0x60, 0xC0, 0x29, 0x23, 0xAB, 0x0D, 0x53, 0x4E, 0x6F],
    #v[0xD5, 0xDB, 0x37, 0x45, 0xDE, 0xFD, 0x8E, 0x2F, 0x03, 0xFF, 0x6A, 0x72, 0x6D, 0x6C, 0x5B, 0x51],
    #v[0x8D, 0x1B, 0xAF, 0x92, 0xBB, 0xDD, 0xBC, 0x7F, 0x11, 0xD9, 0x5C, 0x41, 0x1F, 0x10, 0x5A, 0xD8],
    #v[0x0A, 0xC1, 0x31, 0x88, 0xA5, 0xCD, 0x7B, 0xBD, 0x2D, 0x74, 0xD0, 0x12, 0xB8, 0xE5, 0xB4, 0xB0],
    #v[0x89, 0x69, 0x97, 0x4A, 0x0C, 0x96, 0x77, 0x7E, 0x65, 0xB9, 0xF1, 0x09, 0xC5, 0x6E, 0xC6, 0x84],
    #v[0x18, 0xF0, 0x7D, 0xEC, 0x3A, 0xDC, 0x4D, 0x20, 0x79, 0xEE, 0x5F, 0x3E, 0xD7, 0xCB, 0x39, 0x48]]
  rows.flatten

/-- §6.2.1: apply S to each of the four bytes. -/
def tau (a : Word) : Word :=
  let sub (j : Nat) := sbox.getD ((a >>> (8 * j)).setWidth 8).toNat 0
  sub 3 ++ sub 2 ++ sub 1 ++ sub 0

/-- §6.2.2: encryption's linear transformation L. -/
def linear (b : Word) : Word :=
  b ^^^ b.rotateLeft 2 ^^^ b.rotateLeft 10 ^^^ b.rotateLeft 18 ^^^ b.rotateLeft 24

/-- §6.2.2: key expansion's linear transformation L'. -/
def keyLinear (b : Word) : Word :=
  b ^^^ b.rotateLeft 13 ^^^ b.rotateLeft 23

def t (a : Word) : Word := linear (tau a)
def keyT (a : Word) : Word := keyLinear (tau a)

/-- §7.3.1, the family key FK. -/
def fk : Vector Word 4 := #v[0xA3B1BAC6, 0x56AA3350, 0x677D9197, 0xB27022DC]

/-- §7.3.2: CK's j-th byte is `(4*i+j)*7 mod 256`, most significant first. -/
def ck (i : Nat) : Word :=
  let byte (j : Nat) := BitVec.ofNat 8 ((4 * i + j) * 7)
  byte 0 ++ byte 1 ++ byte 2 ++ byte 3

/-- Four consecutive bytes as a big-endian word. -/
def wordAt (b : Block) (i : Nat) : Word :=
  b.getD i 0 ++ b.getD (i + 1) 0 ++ b.getD (i + 2) 0 ++ b.getD (i + 3) 0

def initial (b : Block) : State :=
  (wordAt b 0, wordAt b 4, wordAt b 8, wordAt b 12)

/-- §6.1: `(X_i, X_{i+1}, X_{i+2}, X_{i+3})` becomes
`(X_{i+1}, X_{i+2}, X_{i+3}, X_i xor T(X_{i+1} xor X_{i+2} xor X_{i+3} xor rk_i))`. -/
def round (rk : Word) (s : State) : State :=
  let (a, b, c, d) := s
  (b, c, d, a ^^^ t (b ^^^ c ^^^ d ^^^ rk))

/-- §7.3: the same recurrence with T', starting from MK xor FK. -/
def expandKey (key : Block) : Schedule := Id.run do
  let mut state : State :=
    (wordAt key 0 ^^^ fk[0], wordAt key 4 ^^^ fk[1],
     wordAt key 8 ^^^ fk[2], wordAt key 12 ^^^ fk[3])
  let mut keys : Schedule := Vector.replicate 32 0
  for i in List.range 32 do
    let (a, b, c, d) := state
    let rk := a ^^^ keyT (b ^^^ c ^^^ d ^^^ ck i)
    keys := keys.set! i rk
    state := (b, c, d, rk)
  return keys

/-- §7.1: 32 rounds followed by R, reversing the four output words. -/
def crypt (key : Nat → Word) (b : Block) : Block :=
  let (a, b, c, d) := (List.range 32).foldl (fun s i => round (key i) s) (initial b)
  let out : Vector Word 4 := #v[d, c, b, a]
  Vector.ofFn fun i => (out.getD (i.val / 4) 0 >>> (8 * (3 - i.val % 4))).setWidth 8

def encryptBlock (k : Schedule) (b : Block) : Block := crypt (fun i => k.getD i 0) b

/-- §7.2: identical encryption procedure with round keys in reverse order. -/
def decryptBlock (k : Schedule) (b : Block) : Block := crypt (fun i => k.getD (31 - i) 0) b

inductive Direction | encrypt | decrypt
  deriving DecidableEq, Repr

/-- ECB on complete blocks, including empty input. -/
def ecb (k : Schedule) (direction : Direction) (input : List Block) : List Block :=
  input.map (match direction with | .encrypt => encryptBlock k | .decrypt => decryptBlock k)

/-! ## Memory layouts for contracts -/

def blockAt (m : Mem) (p : Addr) : Block :=
  Vector.ofFn fun i => m (p + BitVec.ofNat 64 i.val)

/-- 128 bytes: 32 little-endian 32-bit round keys in encryption order. -/
def scheduleAt (m : Mem) (p : Addr) : Schedule :=
  Vector.ofFn fun i =>
    (List.range 4).foldl (fun out j =>
      out ||| ((m (p + BitVec.ofNat 64 (4 * i.val + j))).zeroExtend 32 <<< (8 * j))) 0

def blocksAt (m : Mem) (p : Addr) (n : Nat) : List Block :=
  (List.range n).map fun i => blockAt m (p + BitVec.ofNat 64 (16 * i))

end VG.Spec.Sm4
