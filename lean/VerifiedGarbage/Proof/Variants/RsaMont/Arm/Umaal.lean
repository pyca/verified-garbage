module

public import VerifiedGarbage.Proof.Variants.RsaMont.Arm.Base
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal

/-! # The callable Montgomery product and square with UMAAL rows -/

@[expose] public section
namespace VG.Proof.Variants.RsaMont.Arm.Umaal
open VG VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : MontBackend where
  mul := umaalRows MontCall.code
  verified := montCallUmaal_verified
  correct := by
    intro s base len w o a b h ho ha hb
    obtain ⟨tr, t, run, post⟩ := Base.variant.correct s h ho ha hb
    exact ⟨tr, t, Exec.subst row_sim run, post⟩
  rawCT := by
    intro base len w o a b ho ha hb s t tr1 tr2 u v h e1 e2
    obtain ⟨st, su, es, _⟩ := Base.variant.correct s h.1 ho ha hb
    obtain ⟨tt, tv, et, _⟩ := Base.variant.correct t h.2.1 ho ha hb
    have es' : Exec VG.Arm.isa (umaalRows MontCall.code) s st su := Exec.subst row_sim es
    have et' : Exec VG.Arm.isa (umaalRows MontCall.code) t tt tv := Exec.subst row_sim et
    obtain ⟨rfl, rfl⟩ := Exec.det es' e1
    obtain ⟨rfl, rfl⟩ := Exec.det et' e2
    exact Base.variant.rawCT ho ha hb _ _ _ _ _ _ h es et
  stackOk := Nat.le_trans (armStack_umaalRows _) Base.variant.stackOk
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Variants.RsaMont.Arm.Umaal
