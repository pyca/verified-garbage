module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-! Convert the validated generator into the first canonical Montgomery tooth. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generator_basis (M : Mont) {p : Parameters} {s : State} (h : ModState p s)
 (generator : wv s.mem p.B (slot p.w 1) p.w=p.G) (reduced : p.G<p.P) :
 WP isa (M.mm 5 1 4) s fun t =>
 Basis p 1 t ∧ Arrays p.B p.w [2,3,5] s.mem t.mem ∧ Keep mmRegs s t := by
 have r2Bound : wv s.mem p.B (slot p.w 4) p.w<p.P := by
  rw [h.r2];exact Nat.mod_lt _ (by have := p.modulusPositive;omega)
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width
  (by decide : 5<8) (by decide : 1<8) (by decide : 4<8) (by decide) (by decide)
  (by decide) (by decide) (by decide) h.modulus h.inverse r2Bound) ?_
 rintro t ⟨good,_,_,bound,product,frame,rest⟩
 have mod := h.after_arrays good frame (by decide) (by decide) (by decide)
 have r2Eq : 2^(128*p.w)=2^(64*p.w)*2^(64*p.w) := by rw [←Nat.pow_add];congr 1;omega
 have target : wv t.mem p.B (slot p.w 5) p.w*2^(64*p.w)%p.P=
  (p.G*2^(64*p.w))*2^(64*p.w)%p.P := by
  rw [generator,h.r2,r2Eq,Nat.mul_mod_mod,←Nat.mul_assoc] at product
  exact product
 have cancel := VG.Proof.Bignum.mont_cancel p.coprime target
 rw [Nat.mod_eq_of_lt bound] at cancel
 refine ⟨⟨mod,bound,?_⟩,frame,rest⟩
 simpa only [VG.Proof.Bignum.powMod_eq,Nat.pow_one,Nat.mod_eq_of_lt reduced] using cancel

end VG.Proof.Ffdh.AArch64.Cached
