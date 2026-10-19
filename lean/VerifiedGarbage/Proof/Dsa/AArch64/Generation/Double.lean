module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Framework.Omega

/-! Doubling the subgroup order and the saved generator exponent in native code. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

theorem doubleArray_ok {s : State} {B : Addr} {Z w dst : Nat}
    (h : Ws s B Z w) (hd : dst < 16)
    (hfit : 2 * wv s.mem B (slot w dst) w < 2 ^ (64 * w)) :
    WP isa (Impl.Dsa.AArch64.Generation.doubleArray dst) s fun t =>
      wv t.mem B (slot w dst) w = 2 * wv s.mem B (slot w dst) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have sd := h.sl hd
  unfold Impl.Dsa.AArch64.Generation.doubleArray
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, hm₁, _⟩, k₁⟩ => ?_))
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x7, .x14, .x3]
    (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = false ∧ t.mem = s₁.mem)
    (by brun [h12]) rfl rfl rfl) fun s₂ ⟨⟨h14, hc, hm₂⟩, k₂⟩ => ?_)
  refine WP.mono (base_ok dst .x16 (((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0)
    ((k₂.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h16, hm₃, hc₃⟩, k₃⟩ => ?_
  have k := (k₁.trans k₂).trans k₃
  refine WP.mono (shl_ok (h.scr.congr k.wr) h16
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.w1; omega)
    (by have := h.w2; omega) (by omega)) fun t ⟨hv, _, ho, kt⟩ => ?_
  rw [hc₃, hc, hm₃, hm₂, hm₁] at hv
  rw [hm₃, hm₂, hm₁] at ho
  refine ⟨?_, ho, (k.trans kt).mono (by decide)⟩
  cases he : t.c <;> rw [he] at hv <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega

end VG.Proof.Dsa.AArch64.Generation
