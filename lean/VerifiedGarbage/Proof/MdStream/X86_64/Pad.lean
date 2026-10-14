module

public import VerifiedGarbage.TCB.X86_64.Sse

/-!
# Streaming Merkle–Damgård hash functions on x86-64: the vectors of the padding

The values `finalize`'s padding (`Impl.MdStream.X86_64.head`) builds in SSE
registers, byte by byte: the bytes `0, 1, …, 15` (`idxVal`), a byte in every
byte (`bcastVal`), and the first 16 bytes of the padding (`head_byte`): the
bytes before position `t` kept, the marker at `t`, zeros after it.
-/

@[expose] public section

namespace VG.Proof.MdStream.X86_64

open VG VG.X86_64

/-- The 16 bytes of `v`. -/
def vbytes (v : BitVec 128) : List Byte := (List.range 16).map (byte v)

theorem vbytes_length (v : BitVec 128) : (vbytes v).length = 16 := by simp [vbytes]

theorem vbytes_getElem (v : BitVec 128) {i : Nat} (hi : i < (vbytes v).length) :
    (vbytes v)[i] = byte v i := by simp [vbytes]

theorem byte_ofBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : byte (ofBytes f) i = f i := by
  simp only [byte, ofBytes]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Nat.reduceMul, Nat.reduceSub, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_eq_self]

theorem byte_and (a b : BitVec 128) (i : Nat) : byte (a &&& b) i = byte a i &&& byte b i :=
  BitVec.extractLsb'_and

theorem byte_or (a b : BitVec 128) (i : Nat) : byte (a ||| b) i = byte a i ||| byte b i :=
  BitVec.extractLsb'_or

/-- `b` (less than 256) in every byte, as `bcast` leaves it: `movq` of
`b · 0x0101010101010101`, then `punpcklqdq` of the register with itself. -/
def bcastVal (b : Nat) : BitVec 128 :=
  XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ BitVec.ofNat 64 (b * 0x0101010101010101))
    ((0 : BitVec 64) ++ BitVec.ofNat 64 (b * 0x0101010101010101))

theorem byte_bcastVal_all : ∀ b < 256, ∀ i < 16, byte (bcastVal b) i = BitVec.ofNat 8 b := by
  decide +kernel

theorem byte_bcastVal {b : Nat} (hb : b < 256) {i : Nat} (hi : i < 16) :
    byte (bcastVal b) i = BitVec.ofNat 8 b :=
  byte_bcastVal_all b hb i hi

/-- The bytes `0, 1, …, 15`, as `idxV` leaves them. -/
def idxVal : BitVec 128 :=
  XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ 0x0706050403020100#64) ((0 : BitVec 64) ++ 0x0f0e0d0c0b0a0908#64)

theorem byte_idxVal_all : ∀ i < 16, byte idxVal i = BitVec.ofNat 8 i := by decide +kernel

theorem byte_idxVal {i : Nat} (hi : i < 16) : byte idxVal i = BitVec.ofNat 8 i := byte_idxVal_all i hi

theorem slt_small : ∀ t < 16, ∀ i < 16, (BitVec.ofNat 8 i).slt (BitVec.ofNat 8 t) = decide (i < t) := by
  decide +kernel

theorem eq_small : ∀ t < 16, ∀ i < 16, (BitVec.ofNat 8 t = BitVec.ofNat 8 i) = (t = i) := by
  decide +kernel

/-- Byte `i` of the first 16 bytes of the padding, from the 16 bytes `x` of the
buffer, its position `t` within them and the marker `mk`. -/
theorem head_byte (x : BitVec 128) {t : Nat} (ht : t < 16) {mk : Nat} (hmk : mk < 256) {i : Nat}
    (hi : i < 16) :
    byte (XBinOp.eval .por (XBinOp.eval .pand x (XBinOp.eval .pcmpgtb (bcastVal t) idxVal))
      (XBinOp.eval .pand (XBinOp.eval .pcmpeqb (bcastVal t) idxVal) (bcastVal mk))) i =
      if i < t then byte x i else if i = t then BitVec.ofNat 8 mk else 0 := by
  simp only [XBinOp.eval, byte_or, byte_and, byte_ofBytes _ hi, byte_bcastVal (by omega : t < 256) hi,
    byte_bcastVal hmk hi, byte_idxVal hi, slt_small t ht i hi, eq_small t ht i hi]
  have e : ∀ y : BitVec 8, 255#8 &&& y = y := by decide
  have e' : ∀ y : BitVec 8, y &&& 255#8 = y := by decide
  by_cases h₁ : i < t
  · have h₃ : t ≠ i := by omega
    simp [h₁, h₃, e']
  · by_cases h₂ : i = t
    · subst h₂; simp [e]
    · have h₃ : t ≠ i := fun h => h₂ h.symm
      simp [h₁, h₂, h₃]

end VG.Proof.MdStream.X86_64
