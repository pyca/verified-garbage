module

public import VerifiedGarbage.Proof.Bignum.Arm.Entry
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The complete callable Montgomery function is constant time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt Operand)

theorem montFn_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => FnInput base len w o a b s ∧ FnInput base len w o a b t ∧ s.sp = t.sp)
      MontFn.mul (fun _ _ => True) := by
  unfold MontFn.mul
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed (rs := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]) (by decide) hs.stackFit
  have pt' := push_pushed (rs := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]) (by decide) ht.stackFit
  have es : montPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : montPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := loadStack_ct .r12 36 _ _ _ _ _ _ (by simp only [montPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, _, _⟩ := mont_entry_ok s0 hs hb.1
      obtain ⟨_, t1, run2, ready2, _, _⟩ := mont_entry_ok t0 ht hb.1
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have hw : 2 ≤ w := hs.width ▸ hs.layout.1
      have fit : arrAt w 8 ≤ 8 * len := hs.width ▸ hs.layout.2.2.1
      have tmpFits : arrAt w 3 + 32 ≤ 8 * len := by
        have := array_end_le (w := w) (j := 3) (k := 8) (by decide)
        omega
      have body := relCT_keep_sp
        ((montFnBody_ct ho ha hb tmpFits).mono
          (P' := fun (s t : State) => FnBodyReady base len w o a b s ∧ FnBodyReady base len w o a b t ∧ s.sp = t.sp)
          (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
      obtain ⟨tailTrace, _⟩ := body.seq montRestore_ct _ _ _ _ _ _ ⟨ready1, ready2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
