module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
import VerifiedGarbage.Proof.Bignum.Arm.MontCallCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Constant-time AAPCS framing of a verified Montgomery dispatcher. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt Operand)

theorem montCallWithFn_ct (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => CallInput base len w o a b s ∧ CallInput base len w o a b t ∧ s.sp = t.sp)
      (MontCallWith.code arithmetic) (fun _ _ => True) := by
  unfold MontCallWith.code
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed (rs := MontCall.savedRegs) (by decide) hs.stackFit
  have pt' := push_pushed (rs := MontCall.savedRegs) (by decide) ht.stackFit
  have es : callPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : callPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := loadStack_ct .r12 40 _ _ _ _ _ _ (by simp only [callPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, mem1, rest1⟩ := call_entry_ok s0 hs hb.1
      obtain ⟨_, t1, run2, ready2, mem2, rest2⟩ := call_entry_ok t0 ht hb.1
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have hw : 2 ≤ w := hs.width ▸ hs.layout.1
      have fit : arrAt w 8 ≤ 8 * len := hs.width ▸ hs.layout.2.2.1
      have tmpFits : arrAt w 3 + 32 ≤ 8 * len := by
        have := array_end_le (w := w) (j := 3) (k := 8) (by decide)
        omega
      have body := relCT_keep_sp (law.ct (base := base) ho ha hb tmpFits) (fun _ _ h => h.2.2)
      obtain ⟨tailTrace, _⟩ := body.seq montCallRestore_ct _ _ _ _ _ _
        ⟨callBodyReady_of_entry s0 hs _ ready1 mem1 rest1,
          callBodyReady_of_entry t0 ht _ ready2 mem2 rest2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
