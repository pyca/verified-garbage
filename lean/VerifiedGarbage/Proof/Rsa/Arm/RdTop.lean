module
public import VerifiedGarbage.Proof.Rsa.Arm.RdBody
public import VerifiedGarbage.Proof.Rsa.Arm.RvTop2
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Rsa.Arm.RvTop3
import VerifiedGarbage.Proof.Rsa.Arm.RvTop4
import VerifiedGarbage.Proof.Rsa.Arm.RvTop5
import VerifiedGarbage.Proof.Rsa.Arm.RvVerified
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.RecoverDet
meta import VerifiedGarbage.TCB.Arm.Target

/-! # `vg_rsa_recover_primes_det` on ARMv7 is verified against `recoverPrimesDetContract`

`vg_rsa_recover_primes`' push, entry and restore (`Recover.codeWith`) around
the body (`bodyD_vp`): a call's result (`rd_ok`), constant time with the
pointers, the lengths, `n` and `e` public (`rd_ct`), and the contract.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.RecoverDet (bodyD_vp ResD)

/-- The body after the entry. -/
abbrev bodyD : Prog isa := .ite .eq VG.Impl.Rsa.Arm.RecoverDet.valid fail

/-- The public parameters: `mkP` without the number of candidates. -/
abbrev mkPD (s : State) : RP := { mkP s with nt := 0 }

theorem In.withNt {P : RP} {σ : State} (h : In P σ) (t : Nat) : In { P with nt := t } σ := by
  exact ⟨h.sp, h.spFit, h.wr, h.rdN, h.rdE, h.rdD, h.rdA, h.k1, h.k2, h.el1, h.el2, h.dl1, h.dl2, h.scr, h.fP, h.fQ, h.fN, h.fE, h.fD, h.fS, h.sP, h.sQ, h.sN, h.sE, h.sD, h.sF, h.pQ, h.pN, h.pE, h.pD, h.pF, h.qN, h.qE, h.qD, h.qF, h.nF, h.eF, h.dF, h.wP, h.wQ, h.aN, h.aK, h.aE, h.aEl, h.aD, h.aDl, h.aS, h.nB, h.eB⟩

section
variable {s : State}

/-- A call's result. -/
theorem rd_ok [InvLaw] (h : CIn s) (he : (stackArg s 3).toNat ≤ 8) :
    WP isa VG.Impl.Rsa.Arm.RecoverDet.code s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenAll t.mem [(State.addr (s.gpr .r0), (stackArg s 1).toNat),
        (State.addr (s.gpr .r2), (stackArg s 1).toNat)] (t.gpr .r0)
        ((Spec.Rsa.primesKeyDet (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat)).map
          fun v => [v.1, v.2]) := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  unfold VG.Impl.Rsa.Arm.RecoverDet.code codeWith
  refine WP.frame (by decide) spLo (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (entry_run h) fun u ⟨usp, urd, uwr, umem, uz⟩ => ?_
  rw [WP.seq_iff]
  have pre := (in_x h usp urd umem).1
  have sz := pre.sizes
  obtain ⟨tr, v, run, bo, res⟩ := (bodyD_vp (P := mkP s) he).wp _ _ ⟨⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩, uz⟩
  have cov := h.xCovers sz
  have run' := Exec.widen (rd := u.rd) (wr := u.wr) run
    (Covers.append (Covers.refl _) (by rw [uwr]; exact cov)) (by rw [uwr]; exact cov)
  simp only [State.withRegions_withRegions, State.withRegions_self] at run'
  refine WP.mono (Q := fun x => x = v.withRegions u.rd u.wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have vsp : v.sp = s.sp - BitVec.ofNat 32 56 := bo.sp.trans usp
  have saved : Spill.Saved v.mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved :=
    h.savedE.frame (lo := 16) (hi := 56) (by decide) (by rw [← umem]; exact bo.frame) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact pre.sF.symm.sub_left (Offset.sub_base _ (by decide))
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact pre.pF.symm.sub_left (Offset.sub_base _ (by decide))
      · exact pre.qF.symm.sub_left (Offset.sub_base _ (by decide)))
  have fit : (v.withRegions u.rd u.wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show v.sp.toNat + 56 ≤ _; rw [vsp, spN]; omega
  have read : InRegions ((v.withRegions u.rd u.wr).rd ++ (v.withRegions u.rd u.wr).wr)
      (State.addr (v.withRegions u.rd u.wr).sp) 56 := by
    have m : (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) ∈ (v.withRegions u.rd u.wr).wr := by
      rw [State.withRegions_wr, uwr]; exact List.mem_cons_self
    refine ⟨_, List.mem_append_right _ m, ?_⟩
    rw [State.withRegions_sp, vsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ s.gpr fit read (by rw [State.withRegions_sp, vsp]; exact saved)) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by simp [pcCalleeSaved])
    · exact restored (.r5, 20) (by simp [pcCalleeSaved])
    · exact restored (.r6, 24) (by simp [pcCalleeSaved])
    · exact restored (.r7, 28) (by simp [pcCalleeSaved])
    · exact restored (.r8, 32) (by simp [pcCalleeSaved])
    · exact restored (.r9, 36) (by simp [pcCalleeSaved])
    · exact restored (.r10, 40) (by simp [pcCalleeSaved])
    · exact restored (.r11, 44) (by simp [pcCalleeSaved])
    · exact restored (.lr, 52) (by simp [pcCalleeSaved])
  · rw [popped_sp, restT.sp, State.withRegions_sp, vsp]
    exact BitVec.sub_add_cancel _ _
  · have dEq : dB (mkP s) (u.withRegions u.rd (xRegs s)) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat := by
      show Spec.Rsa.bytesAt u.mem _ _ = _
      rw [umem]; exact h.bytes (R := cD s) h.Fd (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
    simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret, State.withRegions_mem]
    rw [dEq] at res
    exact res

end

/-- The body's run, widened to the caller's regions. -/
theorem body_wideD [InvLaw] {s u : State} (h : CIn s) (he : (stackArg s 3).toNat ≤ 8) (usp : u.sp = s.sp - BitVec.ofNat 32 56) (urd : u.rd = s.rd)
    (uwr : u.wr = (pcPushed s).wr) (umem : u.mem = entryMem s)
    (uz : u.z = Spec.Rsa.modulusValid (mkP s).n (mkP s).K) :
    ∃ tr v, Exec isa bodyD (u.withRegions u.rd (xRegs s)) tr v ∧
      Exec isa bodyD u tr (v.withRegions u.rd u.wr) ∧ v.sp = s.sp - BitVec.ofNat 32 56 := by
  have pre := (in_x h usp urd umem).1
  obtain ⟨tr, v, run, bo, _⟩ := (bodyD_vp (P := mkP s) he).wp _ _ ⟨⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩, uz⟩
  have cov := h.xCovers pre.sizes
  have run' := Exec.widen (rd := u.rd) (wr := u.wr) run
    (Covers.append (Covers.refl _) (by rw [uwr]; exact cov)) (by rw [uwr]; exact cov)
  simp only [State.withRegions_withRegions, State.withRegions_self] at run'
  exact ⟨tr, v, run, run', bo.sp.trans usp⟩

/-- Two calls with the same public parameters. -/
theorem rd_ct [InvLaw] : RelCT isa (fun s t => (CIn s ∧ (stackArg s 3).toNat ≤ 8) ∧ CIn t ∧ s.sp = t.sp ∧
    mkPD s = mkPD t ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1) VG.Impl.Rsa.Arm.RecoverDet.code
    (fun _ _ => True) := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.code codeWith
  apply RelCT.frame (fun _ _ h => h.2.2.1)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨⟨hs, he⟩, ht, sp, hP, a0, a1⟩, ps, pt⟩ := hp
  have he' : (stackArg t0 3).toNat ≤ 8 := by
    have e : (mkPD s0).el = (mkPD t0).el := by rw [hP]
    change (stackArg s0 3).toNat = (stackArg t0 3).toNat at e
    omega
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
          obtain ⟨trB1, w1, runB1, wide1, wsp1⟩ := body_wideD hs he usp1 urd1 uwr1 umem1 uz1
          obtain ⟨trB2, w2, runB2, wide2, wsp2⟩ := body_wideD ht he' usp2 urd2 uwr2 umem2 uz2
          obtain ⟨rfl, rfl⟩ := Exec.det body1 wide1
          obtain ⟨rfl, rfl⟩ := Exec.det body2 wide2
          have pre1 := (in_x hs usp1 urd1 umem1).1.withNt 0
          have pre2 := (in_x ht usp2 urd2 umem2).1.withNt 0
          change In (mkPD t0) _ at pre2
          rw [← hP] at pre2
          have uz2' := uz2
          change _ = Spec.Rsa.modulusValid (mkPD t0).n (mkPD t0).K at uz2'
          rw [← hP] at uz2'
          have trB := ((bodyD_vp (P := mkPD s0) he).ct _ _ _ _ _ _
            ⟨_, _, ⟨⟨pre1, rfl, rfl, rfl, Frame.refl _ _⟩, uz1⟩, ⟨⟨pre2, rfl, rfl, rfl, Frame.refl _ _⟩, uz2'⟩⟩
            runB1 runB2).1
          have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
            (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
            (by show w1.sp = w2.sp; rw [wsp1, wsp2, sp]) rest1 rest2).1
          exact ⟨by rw [trE, trB, trR], trivial⟩


theorem cinD_of_pre (s : State) (h : (Spec.Rsa.recoverPrimesDetContract abi 56).pre s) :
    CIn s ∧ (stackArg s 3).toNat ≤ 8 := by
  sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, pq, pn, pe, pd, pS, pA, qn, qe, qd, qS, qA, nS, eS, dS, SA, Fp, Fq, Fn, Fe, Fd, FS, FA,
    fp, fq, fn, fe, fd, fS, valid, pl, ql, el1, el8, dl1, dl2, scr⟩ := h
  have hk := valid
  simp only [Spec.Rsa.lenValid] at hk
  exact ⟨⟨spLo, spHi, rd, wr, pq, pn, pe, pd, pS, pA, qn, qe, qd, qS, qA, nS, eS, dS, SA, Fp, Fq, Fn, Fe, Fd, FS, FA,
    fp, fq, fn, fe, fd, fS, valid, pl, ql, el1, by omega, dl1, dl2, scr⟩, el8⟩

theorem rd_contract_correct [InvLaw] (s : State) (h : (Spec.Rsa.recoverPrimesDetContract abi 56).pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.Arm.RecoverDet.code s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.recoverPrimesDetContract abi 56).post s t := by
  obtain ⟨hc, he⟩ := cinD_of_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := rd_ok hc he
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

/-- Calls with the same public arguments, `n` and `e` have the same public parameters. -/
theorem mkPD_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1) (a2 : stackArg s 2 = stackArg t 2)
    (a3 : stackArg s 3 = stackArg t 3) (a4 : stackArg s 4 = stackArg t 4) (a5 : stackArg s 5 = stackArg t 5)
    (a6 : stackArg s 6 = stackArg t 6) (a7 : stackArg s 7 = stackArg t 7)
    (hn : Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 0)) (stackArg t 1).toNat)
    (he : Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 2)) (stackArg t 3).toNat) :
    mkPD s = mkPD t := by
  unfold mkPD mkP
  rw [hn, he, sp, p0, p2, a0, a1, a2, a3, a4, a5, a6, a7]

theorem rd_contract_ct [InvLaw] : ConstantTime isa (Spec.Rsa.recoverPrimesDetContract abi 56).pre
    (Spec.Rsa.recoverPrimesDetContract abi 56).pub VG.Impl.Rsa.Arm.RecoverDet.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := cinD_of_pre s hs
  have it := (cinD_of_pre t ht).1
  sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, a0, a1, a2, a3, a4, a5, a6, a7⟩ := hp
  have b3 := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 bytes
  obtain ⟨hn, he⟩ := List.append_inj b3 (by
    simp only [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; rw [a1])
  exact (rd_ct s t tr1 tr2 u v ⟨is, it, sp, mkPD_eq sp p0 p2 a0 a1 a2 a3 a4 a5 a6 a7 hn he, a0, a1⟩ e1 e2).1

theorem rd_contract_sat : ∃ s, (Spec.Rsa.recoverPrimesDetContract abi 56).pre s := by
  sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
    [rvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using rvSatState

/-- `vg_rsa_recover_primes_det`. -/
theorem recover_primes_det_verified [InvLaw] :
    Verified target VG.Impl.Rsa.Arm.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi 56) :=
  ⟨rd_contract_correct, rd_contract_ct, rd_contract_sat⟩

end VG.Proof.Rsa.Arm.Recover
