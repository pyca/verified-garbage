module
public import VerifiedGarbage.Proof.Bignum.Arm.PdInput
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn

import VerifiedGarbage.Proof.Bignum.Arm.PdEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.PdBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.PdEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # The callable checked public RSA operation leaks only public arguments, modulus, and exponent -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pdFn_ct {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdFnInput base dst np ep xp len k eLen N R eb xb1 s ∧
      PdFnInput base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PdFn.code (fun _ _ => True) := by
  unfold PdFn.code
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.stackFit
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.stackFit
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := pdEntry_ct _ _ _ _ _ _ (by simp only [pcPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, _, _, _⟩ := pd_entry_ready s0 hs
      obtain ⟨_, t1, run2, ready2, _, _, _⟩ := pd_entry_ready t0 ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have body := relCT_keep_sp
        (pdBody_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
          (len := len) (k := k) (eLen := eLen) (N := N) (R := R) (eb := eb) (xb1 := xb1) (xb2 := xb2))
        (fun _ _ h => h.2.2)
      have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
        stackLoads_ct pcCalleeSaved
      obtain ⟨tailTrace, _⟩ := body.seq restore _ _ _ _ _ _ ⟨ready1, ready2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
