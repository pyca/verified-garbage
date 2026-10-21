module
public import VerifiedGarbage.Proof.Rsa.X86.RvBody
public import VerifiedGarbage.Proof.Rsa.X86.RvPair

import VerifiedGarbage.Proof.Rsa.X86.RvModulusTiming
import VerifiedGarbage.Proof.Rsa.X86.RvFailureTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeSized
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The wrapper exposes only the public modulus and declared attempt count -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Recover

/-- Recovery needs only the public modulus bytes and declared attempt count. -/
def BodyPair (g : CallGeometry) (s t : State) : Prop :=
  Pair g s t ∧ (∀ r ∈ narrowW g, Region.Disjoint ⟨g.sp.setWidth 64, 52⟩ r) ∧
    inputBytes g s.mem 0 = inputBytes g t.mem 0 ∧
    (calculated g s.mem).2 = (calculated g t.mem).2

theorem body_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (BodyPair g) VG.Impl.Rsa.X86.RecoverRt.body (fun _ _ => True) := by
  let r := fun s t => BodyPair g s t ∧
    s.zf = some (Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length) ∧
    t.zf = some (Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length)
  have branch : RelCT isa r (.ite .e VG.Impl.Rsa.X86.RecoverRt.sized VG.Impl.Rsa.X86.Recover.failure) (fun _ _ => True) := by
    have flags : ∀ s t, r s t → isa.eval .e s = isa.eval .e t := by
      intro s t h
      change s.zf = t.zf
      rw [h.2.1, h.2.2]
      unfold inputValue
      rw [h.1.2.2.1]
    apply VG.RelCT.ite (M := isa) (c := .e) (P := r) flags
    · apply (sizedNarrow_relCT g len).mono
      · intro s t ⟨h, cond⟩
        have vs := Option.some.inj (h.2.1.symm.trans cond)
        have vt := Option.some.inj (h.2.2.symm.trans ((flags s t h).symm.trans cond))
        exact ⟨h.1.1.left, h.1.1.right, h.1.2.1, congrArg Spec.Rsa.os2ip h.1.2.2.1, vs, vt, h.1.2.2.2⟩
      · intro s t h; exact h
    · exact (failure_relCT g).mono (fun _ _ h => h.1.1.1) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨pair, apart, modulus, attempts⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (modulus_relCT g _ _ _ _ _ _ pair e1 f1).1
      obtain ⟨zs, ms, ks⟩ := wp_result (modulus_ok pair.left len) e1
      obtain ⟨zt, mt, kt⟩ := wp_result (modulus_ok pair.right len) f1
      have next : BodyPair g u v := by
        refine ⟨pair.keepMem ks kt (by decide) (by decide) ms mt, ?_⟩
        rw [ms, mt]
        exact ⟨apart, modulus, attempts⟩
      have vs : u.zf = some (Spec.Rsa.modulusValid (inputValue g u.mem 0) (inputBytes g u.mem 0).length) := by
        rw [ms]
        simp only [inputValue, inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer]
        exact zs
      have vt : v.zf = some (Spec.Rsa.modulusValid (inputValue g v.mem 0) (inputBytes g v.mem 0).length) := by
        rw [mt]
        simp only [inputValue, inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer]
        exact zt
      have eq2 := (branch _ _ _ _ _ _ ⟨next, vs, vt⟩ e2 f2).1
      exact ⟨by rw [eq1, eq2], trivial⟩

end VG.Proof.Rsa.X86.Recover
