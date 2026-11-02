module
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Rsa.Arm.RvTop2

import VerifiedGarbage.Proof.Rsa.Arm.RvTop4
import VerifiedGarbage.Proof.Rsa.Arm.RvTop3
public import VerifiedGarbage.Proof.Rsa.Arm.RvBody
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint5
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # `vg_rsa_recover_primes` on ARMv7: constant time (`rv_ct`)

Two calls with the same public parameters `mkP` (and the same pointer and
length of `n`) leak the same: the entry's addresses are on the stack and
`n`'s, the body's are the stage's (`body_vp`), and the restore's on the
stack. -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.Bignum.Arm

theorem entry_ct {s₀ t₀ : State} (hs : CIn s₀) (ht : CIn t₀) (sp : s₀.sp = t₀.sp)
    (a0 : stackArg s₀ 0 = stackArg t₀ 0) (a1 : stackArg s₀ 1 = stackArg t₀ 1) :
    RelCT isa (fun a b => a = pcPushed s₀ ∧ b = pcPushed t₀) (.block entry) (fun _ _ => True) := by
  rw [entry_eq]
  have head := ((VG.Proof.Rsa.Arm.setupChecked_ct [.str .r0 .r12 oP, .ldrSp .r4 aoN, .ldrSp .r6 aoK]
    (by decide) (by decide)).mono (P' := fun a b => a = pcPushed s₀ ∧ b = pcPushed t₀)
    (fun a b ⟨ha, hb⟩ => by subst ha; subst hb; simp only [pushed_sp, sp]) fun _ _ h => h).wp
    (F₁ := fun (u : State) => u.gpr .r4 = stackArg s₀ 0 ∧ u.gpr .r6 = stackArg s₀ 1)
    (F₂ := fun (u : State) => u.gpr .r4 = stackArg t₀ 0 ∧ u.gpr .r6 = stackArg t₀ 1) (fun a b ⟨ha, hb⟩ => by
      subst ha; subst hb
      exact ⟨WP.mono (head_run hs) fun u h => ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩,
        WP.mono (head_run ht) fun u h => ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩⟩)
  obtain ⟨_, hc⟩ := check_taint
  refine RelCT.block_append (head.seq (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r4, .r6]) ?_ hc))
  intro a b ⟨_, ⟨a4, a6⟩, b4, b6⟩
  apply Taint.agree_ofRegs
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · rw [a4, b4, a0]
  · rw [a6, b6, a1]

/-- The body's run, widened to the caller's regions. -/
theorem body_wideWith (body : Prog isa) (bodyProof : BodyVerified body) {s u : State} (h : CIn s) (usp : u.sp = s.sp - BitVec.ofNat 32 56) (urd : u.rd = s.rd)
    (uwr : u.wr = (pcPushed s).wr) (umem : u.mem = entryMem s)
    (uz : u.z = Spec.Rsa.modulusValid (mkP s).n (mkP s).K) :
    ∃ tr v, Exec isa body (u.withRegions u.rd (xRegs s)) tr v ∧
      Exec isa body u tr (v.withRegions u.rd u.wr) ∧ v.sp = s.sp - BitVec.ofNat 32 56 := by
  have pre := in_x h usp urd umem
  obtain ⟨tr, v, run, bo, _⟩ := bodyProof.wp _ _ ⟨⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩, uz⟩
  have cov := h.xCovers pre.sizes
  have run' := Exec.widen (rd := u.rd) (wr := u.wr) run
    (Covers.append (Covers.refl _) (by rw [uwr]; exact cov)) (by rw [uwr]; exact cov)
  simp only [State.withRegions_withRegions, State.withRegions_self] at run'
  exact ⟨tr, v, run, run', bo.sp.trans usp⟩

/-- Two calls with the same public parameters. -/
theorem rv_ctWith (body : Prog isa) (bodyProof : BodyVerified body) : RelCT isa (fun s t => CIn s ∧ CIn t ∧ s.sp = t.sp ∧ mkP s = mkP t ∧
    stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1) (codeWith body) (fun _ _ => True) := by
  unfold codeWith
  apply RelCT.frame (fun _ _ h => h.2.2.1)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp, hP, a0, a1⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.spLo
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.spLo
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      have trE := ((entry_ct hs ht sp a0 a1) _ _ _ _ _ _ ⟨rfl, rfl⟩ entry1 entry2).1
      obtain ⟨_, u1, run1, usp1, urd1, uwr1, umem1, uz1⟩ := entry_run hs
      obtain ⟨_, v1, run2, usp2, urd2, uwr2, umem2, uz2⟩ := entry_run ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      cases tail1 with
      | seq body1 rest1 =>
        cases tail2 with
        | seq body2 rest2 =>
          obtain ⟨trB1, w1, runB1, wide1, wsp1⟩ := body_wideWith body bodyProof hs usp1 urd1 uwr1 umem1 uz1
          obtain ⟨trB2, w2, runB2, wide2, wsp2⟩ := body_wideWith body bodyProof ht usp2 urd2 uwr2 umem2 uz2
          obtain ⟨rfl, rfl⟩ := Exec.det body1 wide1
          obtain ⟨rfl, rfl⟩ := Exec.det body2 wide2
          have pre1 := in_x hs usp1 urd1 umem1
          have pre2 := in_x ht usp2 urd2 umem2
          rw [← hP] at pre2
          have uz2' := uz2.trans (by rw [hP] : Spec.Rsa.modulusValid (mkP t0).n (mkP t0).K =
            Spec.Rsa.modulusValid (mkP s0).n (mkP s0).K)
          have trB := ((bodyProof (P := mkP s0)).ct _ _ _ _ _ _
            ⟨_, _, ⟨⟨pre1, rfl, rfl, rfl, Frame.refl _ _⟩, uz1⟩, ⟨⟨pre2, rfl, rfl, rfl, Frame.refl _ _⟩, uz2'⟩⟩
            runB1 runB2).1
          have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
            (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
            (by show w1.sp = w2.sp; rw [wsp1, wsp2, sp]) rest1 rest2).1
          exact ⟨by rw [trE, trB, trR], trivial⟩

/-- The original search also uses the shared ABI trace proof. -/
theorem rv_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] : RelCT isa (fun s t => CIn s ∧ CIn t ∧ s.sp = t.sp ∧ mkP s = mkP t ∧
    stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1) code (fun _ _ => True) :=
  rv_ctWith (.ite .eq valid fail) body_vp

end VG.Proof.Rsa.Arm.Recover
