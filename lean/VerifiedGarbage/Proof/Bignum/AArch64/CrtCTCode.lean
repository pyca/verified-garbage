import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode

/-!
# `vg_rsa_private_crt` on AArch64: constant time

`entry` and the modulus' check leak the same in runs that agree on the
public data (the arguments but the input and the key's values, and `n`),
and so do `fail` and `main` (`crtMain_ct`): `crtCode_ct`, and the contract's
`ConstantTime` (`crtCode_constantTime_of`), given that `n`'s setup is
constant time.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Rsa.AArch64 (crtA stackArgs_ten)

/-- The public data of `vg_rsa_private_crt`: `main`'s and the stack pointer. -/
structure CCPub where
  m : CrtPub
  sp : Addr

/-- A state the contract allows, with the public data `p`. -/
def CCRel (p : CCPub) (s : State) : Prop :=
  crtA.pre s ∧ s.sp = p.sp ∧ stackArg s 8 = p.m.B ∧ (stackArg s 9).toNat * 8 = p.m.Z ∧
    (s.gpr .x3).toNat = p.m.k ∧ s.gpr .x0 = p.m.op ∧ s.gpr .x2 = p.m.np ∧ s.gpr .x4 = p.m.ip ∧
    s.gpr .x6 = p.m.pp ∧ stackArg s 0 = p.m.qp ∧ stackArg s 2 = p.m.dpp ∧ stackArg s 4 = p.m.dqp ∧
    stackArg s 6 = p.m.qip ∧ (s.gpr .x7).toNat = p.m.pl ∧ (stackArg s 1).toNat = p.m.ql ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = p.m.nb

theorem CCRel.x3 {p : CCPub} {s : State} (h : CCRel p s) : s.gpr .x3 = BitVec.ofNat 64 p.m.k := by
  rw [← h.2.2.2.2.1, ofNat_toNat64]

/-- After `entry` and the modulus' check, from `s`. -/
def HeadPost (s t : State) : Prop :=
  ∃ t₁, CrtHeadPost s t₁ ∧ t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) (s.gpr .x3).toNat).toNat ∧
    t.mem = t₁.mem ∧ Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t

/-- `entry` and the modulus' check, as `crtCode_correct` runs them. -/
theorem crtHeadChk_ok {s : State} (c : CrtCtx s) : WP isa (.block (entry ++ invalid)) s (HeadPost s) := by
  have hk1 := c.hk1
  have hk2 := c.hk2
  rw [WP.block_append_iff]
  refine WP.mono (crtHead_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  exact WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok (h₁.keep.gpr .x2 (by decide))
    (by rw [h₁.keep.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2 (bytesAt_length _ _ _)
    (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ⟨t₁, h₁, hz₂, hm₂, k₂⟩

theorem head_split : entry ++ invalid = ([.ldrSp .x8 64] : List Instr) ++ (entry.drop 1 ++ invalid) := rfl

/-- After `entry`'s first instruction. -/
def CC1 (p : CCPub) (t : State) : Prop :=
  ∃ s, CCRel p s ∧ t.gpr .x8 = p.m.B ∧ t.gpr .x2 = p.m.np ∧ t.gpr .x3 = BitVec.ofNat 64 p.m.k ∧
    WP isa (.block (entry.drop 1 ++ invalid)) t (HeadPost s)

/-- After `entry` and the modulus' check. -/
def CC3 (p : CCPub) (t : State) : Prop := ∃ s, CCRel p s ∧ HeadPost s t

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem cc3_pre {p : CCPub} {t : State} (h : CC3 p t) :
    ∃ xb pb qb dpb dqb qib, CrtPre t p.m.B p.m.Z p.m.k p.m.op p.m.np p.m.ip p.m.pp p.m.qp p.m.dpp p.m.dqp
      p.m.qip p.m.pl p.m.ql p.m.nb xb pb qb dpb dqb qib := by
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql, hnb⟩, t₁, h, -, hm, k⟩ := h
  have := crtPre_of (crtCtx_of hpre) h hm k
  rw [hnb] at this
  rw [hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql] at this
  exact ⟨_, _, _, _, _, _, this⟩

/-- The validity of `n`, in `x9`. -/
theorem cc3_x9 {p : CCPub} {t : State} (h : CC3 p t) :
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid p.m.N p.m.k).toNat := by
  obtain ⟨s, ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hnb⟩, t₁, -, hz, -⟩ := h
  rw [hz, hnb, hk]

variable (M : Mont)

/-- `vg_rsa_private_crt` leaks the same in runs that agree on the public data,
given that `main`'s parts do. -/
theorem crtCode_ct (hN : RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) fun _ _ => True)
    (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) :
    RelCT isa (Two CCRel) (code M.mm) fun _ _ => True := by
  unfold code
  refine RelCT.seq (R := Two CC3) ?_ ?_
  · rw [head_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CC1) [.x2, .x3] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.1]
      · rw [h₁.x3, h₂.x3]) (by taint_decide) ?_)
      (two_piece [.x8, .x2, .x3] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]
        · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := crtCtx_of hs.1
    have hh : WP isa (.block (([.ldrSp .x8 64] : List Instr) ++ (entry.drop 1 ++ invalid))) s (HeadPost s) := by
      rw [← head_split]; exact crtHeadChk_ok c
    have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = stackArg s 8 := rfl
    have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := c.ha 8 (by decide)
    have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
    refine WP.mono (wp_and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 8)
      (by brun [exec_ldrSp ho ha8, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
        ⟨s, hs, h8.trans hs.2.2.1, (k.gpr .x2 (by decide)).trans hs.2.2.2.2.2.2.1,
          (k.gpr .x3 (by decide)).trans hs.x3, hw⟩
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, cc3_x9 h₁, cc3_x9 h₂]) ?_ ?_
  · -- `fail`.
    unfold Precomputed.fail
    have pin : ∀ p t, (CC3 p t ∧ isa.eval (.zero .x .x9) t = some true) → t.gpr .x0 = p.m.B := fun p t ⟨h, _⟩ => by
      obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3_pre h
      exact hpre.x0
    refine RelCT.seq (two_piece (Ψ := fun (p : CCPub) t => t.gpr .x1 = p.m.op + BitVec.ofNat 64 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 p.m.k ∧ t.gpr .x0 = p.m.B) [.x0]
      (pins_x0B (fun p : CCPub => p.m.B) pin) (by taint_decide) ?_)
      (two_taint [.x1, .x2, .x0] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3_pre h
    have hn := hpre.scr.nowrap
    have hk1 := hpre.k1
    have hk2 := hpre.k2
    have hZq := hpre.z
    have h8 := hdr_lt_slot ((p.m.k + 7) / 8) 8 (show 31 < 32 by decide)
    have hZ : 8 * 32 ≤ p.m.Z := by unfold offQ at hZq; omega
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.m.B (8 * i)) 8 := fun i hi => hpre.scr.ld (by omega)
    refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = p.m.op + BitVec.ofNat 64 0 ∧
        t'.gpr .x2 = BitVec.ofNat 64 p.m.k) (by
      brun [hpre.x0, hdr_enc (show Public.sOut < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hl Public.sOut (by decide), hl Public.sK (by decide), hpre.hO, hpre.hK]) (by decide) (by decide)
      (by decide +kernel))
      fun t' ⟨⟨h1, h2⟩, k'⟩ => ⟨h1, h2, (k'.gpr .x0 (by decide)).trans hpre.x0⟩
  · -- `main`.
    have toM : ∀ p t, CC3 p t ∧ isa.eval (.zero .x .x9) t = some false → Stage R0 p.m t := by
      rintro p t ⟨h, he⟩
      obtain ⟨xb, pb, qb, dpb, dqb, qib, hpre⟩ := cc3_pre h
      have hv : Spec.Rsa.modulusValid p.m.N p.m.k = true := by
        rw [eval_zero, cc3_x9 h] at he
        revert he
        cases Spec.Rsa.modulusValid p.m.N p.m.k <;> decide
      exact ⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, rfl⟩
    exact (crtMain_ct M hN hS hC hQ hP hF).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h) fun _ _ h => h

/-- The public data of a state. -/
def ccPubOf (s : State) : CCPub :=
  ⟨⟨stackArg s 8, (stackArg s 9).toNat * 8, (s.gpr .x3).toNat, s.gpr .x0, s.gpr .x2, s.gpr .x4, s.gpr .x6,
    stackArg s 0, stackArg s 2, stackArg s 4, stackArg s 6, (s.gpr .x7).toNat, (stackArg s 1).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat⟩, s.sp⟩

/-- `vg_rsa_private_crt` is constant time, given that `main`'s parts are. -/
theorem crtCode_constantTime_of (hN : RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) fun _ _ => True)
    (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) :
    ConstantTime isa crtA.pre crtA.pub (code M.mm) := by
  refine RelCT.constantTime ((crtCode_ct M hN hS hC hQ hP hF).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨ccPubOf s₁, ?_, ?_, hp.2.1⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, hsp, ha, hn⟩ := hp
    simp only [stackArgs_ten, List.cons.injEq, and_true] at ha
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha
    have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, hsp.symm, a8.symm, by rw [← a9]; rfl, by rw [r .x3 (by decide)]; rfl, r .x0 (by decide), r .x2 (by decide),
      r .x4 (by decide), r .x6 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, by rw [r .x7 (by decide)]; rfl,
      by rw [← a1]; rfl, hn.symm⟩

/-- `vg_rsa_private_crt` is constant time, given that `n`'s setup is. -/
theorem crtCode_constantTime_of_setup (hN : RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) fun _ _ => True) :
    ConstantTime isa crtA.pre crtA.pub (code M.mm) :=
  crtCode_constantTime_of M hN setup_ct checks_ct
    (qPhase_ct M (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_Q M) (by taint_decide)))
    (pPhase_ct M (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_P M) (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct

end VG.Proof.Bignum.AArch64
