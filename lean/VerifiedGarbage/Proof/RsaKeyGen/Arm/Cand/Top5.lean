module
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Loads
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top2

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top4
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top3
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin5
import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.MillerRabin.Arm.Run

/-! # A candidate on ARMv7: constant time (`cand_ct`)

Two calls with the same public parameters `mkP` leak the same: the entry's
addresses are on the stack, the body's are the stage's (`candBody_vp`), and
the restore's on the stack.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {s : State}

/-- The body's run from its start, in its two parts. -/
theorem body_parts [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) (h : CIn s) :
    ∃ tr1 tr2 t w, Exec isa (.block entry) (sx s) tr1 t ∧
      Exec isa (seqs [.block lenCheck, .ite .eq finNone (main v.name v.code)]) t tr2 w ∧
      In (mkP s) t ∧ Bk (mkP s) t t ∧ Bk (mkP s) t w := by
  obtain ⟨tr1, t, e1, pre, -, -, -, -⟩ := entry_ok h
  obtain ⟨tr2, w, e2, rf⟩ := (candBody_vp v).wp t t ⟨pre, ⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩⟩
  exact ⟨tr1, tr2, t, w, e1, e2, pre, ⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩, rf.2.1⟩

/-- Two calls with the same public parameters. -/
theorem cand_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) :
    RelCT isa (fun s t => CIn s ∧ CIn t ∧ s.sp = t.sp ∧ mkP s = mkP t) (code v.name v.code) (fun _ _ => True) := by
  unfold code
  apply RelCT.frame (fun _ _ h => h.2.2.1)
  intro s t tr1 tr2 u w hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp, hP⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide)
    (s := s0) (by have := hs.spLo; simp only [List.length_cons, List.length_nil]; omega)
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide)
    (s := t0) (by have := ht.spLo; simp only [List.length_cons, List.length_nil]; omega)
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq body1 rest1 =>
    cases e2 with
    | seq body2 rest2 =>
      obtain ⟨trW1, w1, t1, run1, -, -, -, -, -⟩ := body_wide v hs
      obtain ⟨trW2, w2, t2, run2, -, -, -, -, -⟩ := body_wide v ht
      obtain ⟨rfl, rfl⟩ := Exec.det body1 run1
      obtain ⟨rfl, rfl⟩ := Exec.det body2 run2
      obtain ⟨a1, b1, x1, y1, ea1, eb1, pre1, bx1, by1⟩ := body_parts v hs
      obtain ⟨a2, b2, x2, y2, ea2, eb2, pre2, bx2, by2⟩ := body_parts v ht
      have cov1 := hs.xCovers pre1
      have cov2 := ht.xCovers pre2
      have run1' := Exec.widen (rd := s0.rd) (wr := (pcPushed s0).wr) (Exec.seq ea1 eb1)
        (Covers.append (Covers.refl _) cov1) cov1
      have run2' := Exec.widen (rd := t0.rd) (wr := (pcPushed t0).wr) (Exec.seq ea2 eb2)
        (Covers.append (Covers.refl _) cov2) cov2
      simp only [State.withRegions_withRegions] at run1' run2'
      obtain ⟨rfl, hw1⟩ := Exec.det run1 run1'
      obtain ⟨rfl, hw2⟩ := Exec.det run2 run2'
      have trE := (VG.Proof.Rsa.Arm.setupChecked_ct [.str .r0 .r12 foOut] (by decide) (by decide)) _ _ _ _ _ _
        (show (sx s0).sp = (sx t0).sp by show s0.sp - _ = t0.sp - _; rw [sp]) ea1 ea2
      rw [← hP] at pre2 bx2 by2
      have trB := ((candBody_vp v (P := mkP s0)).ct _ _ _ _ _ _
        ⟨_, _, ⟨pre1, bx1⟩, ⟨pre2, bx2⟩⟩ eb1 eb2).1
      have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
        (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
        (by rw [hw1, hw2]; show y1.sp = y2.sp; rw [by1.sp, pre1.sp, by2.sp, pre2.sp]) rest1 rest2).1
      exact ⟨by rw [trE.1, trB, trR], trivial⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand
