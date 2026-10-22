module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.Inverse

/-! # Width, saved length and static operands throughout the round -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

namespace Stage

theorem read_header {σ s : State} {base : Addr} {bytes w d : Nat}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes) (hd : d + 4 ≤ 256) :
    readSrc s (.mem (VG.Impl.Mont.X86.sc d)) = some (s.mem.readW (off base d) 32) :=
  readSrc_sc h.context.ws (Nat.le_trans hd (Nat.le_trans (Nat.le_add_right _ _) hf))

theorem width {σ s : State} {base : Addr} {bytes w : Nat}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes)
    (initial : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w := by
  have h52 : 52 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  rw [h.read_workspace32 hf h52 (header_static w (by decide)), initial]

theorem read_stack32 {σ s : State} {base : Addr} {bytes w d : Nat}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes)
    (hd : d + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes)
    (cursor : d + 4 ≤ tableCursor ∨ tableCursor + 4 ≤ d) :
    s.mem.readW (off (byteAddr (σ.gpr .esp)) d) 32 = σ.mem.readW (off (byteAddr (σ.gpr .esp)) d) 32 := by
  simpa only [Mem.readW] using congrArg (BitVec.setWidth 32) (h.read_stack hf hd cursor)

theorem length {σ s : State} {base : Addr} {bytes w : Nat} {len : BitVec 32}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes)
    (initial : σ.mem.readW (off (byteAddr (σ.gpr .esp)) savedLength) 32 = len) :
    readSrc s (.mem (sp savedLength)) = some len := by
  rw [h.context.read_sp (by decide), h.stack, h.read_stack32 hf (by decide) (.inl (by decide)), initial]

theorem array_constant {σ s : State} {base : Addr} {bytes w j : Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hf : arrAt w 28 ≤ bytes)
    (hj : j = 0 ∨ j = 9 ∨ j = 10 ∨ j = 27) : numAt s.mem base w j = numAt σ.mem base w j := by
  have bound := array_fits_bytes (j := j) hf (by rcases hj with rfl | rfl | rfl | rfl <;> decide)
  unfold numAt
  rw [h.read_workspace hf (by omega : arrAt w j + 8 * w ≤ bytes)
    ((array_static hw hj).prefix (by omega : 8 * w ≤ 8 * (w + 2)))]

theorem modulus_constant {σ s : State} {base : Addr} {bytes w : Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hf : arrAt w 28 ≤ bytes) :
    val32 s.mem base 256 (2 * w) = val32 σ.mem base 256 (2 * w) := by
  have e := h.array_constant hw hf (.inl rfl)
  rw [candidate_words, candidate_words] at e
  simpa only [arrAt, Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] using e

theorem inverse_constant {σ s : State} {base : Addr} {bytes w : Nat}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes) : w32 s.mem base 56 = w32 σ.mem base 56 := by
  have h60 : 60 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  exact congrArg BitVec.toNat (h.read_workspace32 hf h60 (header_static w (by decide)))

end Stage
end VG.Proof.MillerRabin.X86
