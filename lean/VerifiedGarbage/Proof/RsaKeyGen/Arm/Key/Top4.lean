module
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top1

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top3
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # An RSA key on ARMv7: constant time (`key_ct`)

Two calls with the same public parameters `mkP` leak the same: the body's
addresses are the stage's (`body_vp`), and the restore's on the stack.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Impl.RsaKeyGen.Arm.Key (code body)

/-- Two calls with the same public parameters. -/
theorem key_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] : RelCT isa (fun s t => CIn s ∧ CIn t ∧ s.sp = t.sp ∧ mkP s = mkP t) code (fun _ _ => True) := by
  unfold code
  apply RelCT.frame (fun _ _ h => h.2.2.1)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp, hP⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.spLo
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.spLo
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq body1 rest1 =>
    cases e2 with
    | seq body2 rest2 =>
      obtain ⟨trB1, w1, runB1, wide1, res1⟩ := body_wide hs
      obtain ⟨trB2, w2, runB2, wide2, res2⟩ := body_wide ht
      obtain ⟨rfl, rfl⟩ := Exec.det body1 wide1
      obtain ⟨rfl, rfl⟩ := Exec.det body2 wide2
      have pre1 := in_k hs
      have pre2 := in_k ht
      rw [← hP] at pre2
      have trB := ((body_vp (P := mkP s0)).ct _ _ _ _ _ _
        ⟨_, _, ⟨pre1, pre1, rfl, rfl, rfl, Frame.refl _ _⟩, ⟨pre2, pre2, rfl, rfl, rfl, Frame.refl _ _⟩⟩
        runB1 runB2).1
      have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
        (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
        (by show w1.sp = w2.sp; rw [res1.1.sp, res2.1.sp]; show s0.sp - _ = t0.sp - _; rw [sp]) rest1 rest2).1
      exact ⟨by rw [trB, trR], trivial⟩

end VG.Proof.RsaKeyGen.Arm.Key
