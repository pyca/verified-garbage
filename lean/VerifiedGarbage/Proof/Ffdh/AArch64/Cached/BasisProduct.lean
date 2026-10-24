module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis
import VerifiedGarbage.Proof.Framework.Omega

/-! Adding one precomputed tooth to an already constructed subset entry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem basis_product (M : Mont) {p : Parameters} {s : State} {E F : Nat} (h : Basis p E s)
 (selected : wv s.mem p.B (slot p.w 1) p.w=Spec.Rsa.powMod p.G F p.P*2^(64*p.w)%p.P) :
 WP isa (M.mm 6 5 1) s fun t =>
 Power p (E+F) t ∧ Basis p E t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound1 : wv s.mem p.B (slot p.w 1) p.w<p.P := by
  rw [selected];exact Nat.mod_lt _ (by have := p.modulusPositive;omega)
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 5<8) (by decide : 1<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound1) ?_
 rintro t ⟨good,_,_,bound,product,frame,rest⟩
 have mod := h.toModState.after_arrays good frame (by decide) (by decide) (by decide)
 have value := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded p.coprime bound h.value selected product
 exact ⟨⟨mod,bound,value⟩,h.after_arrays good frame (by decide) (by decide) (by decide) (by decide),frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
