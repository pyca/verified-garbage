module
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Finish

import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Correct
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Ffdh.AArch64.OutMask
meta import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Finish
meta import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Correct
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.OutMask
import Mathlib.Data.Int.ModEq

/-!
# `vg_ffdh_generate_key` on AArch64: constant time

Runs with the same public data (`GkP`: all but the random octets, and
whether the scalar is in range) leak the same (`gk_constantTime`): the
scalar's octets are cut by a loop over all of them, the exponentiation is
RSA's, constant time in the exponent, the only branch on the scalar is on
its range, which the status gives, and the key's flag only masks the
results.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (pins_nil)
open VG.Spec.Ffdh

/-- A stage of some random octets, with the outputs' regions. -/
def Ex (Φ : GkP → List Byte → State → Prop) (p : GkP) (t : State) : Prop := ∃ rb, Φ p rb t ∧ Dst p t

theorem ex_post {Φ Ψ : GkP → List Byte → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (Ex Φ)) c fun _ _ => True)
    (hw : ∀ p rb s, Φ p rb s → WP isa c s fun u => Ψ p rb u ∧ KX s u) : RelCT isa (Two (Ex Φ)) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨rb, h, hd⟩ => WP.mono (hw p rb s h) fun _ ⟨hu, k⟩ => ⟨rb, hu, hd.keep k⟩

theorem ex_postD {Φ Ψ : GkP → List Byte → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (Ex Φ)) c fun _ _ => True)
    (hw : ∀ p rb s, Φ p rb s → Dst p s → WP isa c s fun u => Ψ p rb u ∧ KX s u) :
    RelCT isa (Two (Ex Φ)) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨rb, h, hd⟩ => WP.mono (hw p rb s h hd) fun _ ⟨hu, k⟩ => ⟨rb, hu, hd.keep k⟩

theorem ex_post' {Φ Ψ : GkP → List Byte → State → Prop} {c : Prog isa} {P : GkP → State → Prop}
    (hct : RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c fun _ _ => True)
    (hw : ∀ p rb s, Φ p rb s → P p s → WP isa c s fun u => Ψ p rb u ∧ KX s u) :
    RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨⟨rb, h, hd⟩, hp⟩ => WP.mono (hw p rb s h hp) fun _ ⟨hu, k⟩ => ⟨rb, hu, hd.keep k⟩

theorem ex_postD' {Φ Ψ : GkP → List Byte → State → Prop} {c : Prog isa} {P : GkP → State → Prop}
    (hct : RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c fun _ _ => True)
    (hw : ∀ p rb s, Φ p rb s → P p s → Dst p s → WP isa c s fun u => Ψ p rb u ∧ KX s u) :
    RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨⟨rb, h, hd⟩, hp⟩ => WP.mono (hw p rb s h hp hd) fun _ ⟨hu, k⟩ => ⟨rb, hu, hd.keep k⟩

/-- The working space, as the arithmetic sees it. -/
abbrev GkP.ws (p : GkP) : Ws := ⟨off p.B (inner ((p.k + 7) / 8)), slot ((p.k + 7) / 8) 8, (p.k + 7) / 8⟩

/-- The inner workspace's base. -/
abbrev GkP.g (p : GkP) : Addr := off p.B (inner ((p.k + 7) / 8))

/-! ## The entry -/

/-- The entry's registers but `x8`. -/
def entryRegs (p : GkP) (r : Reg) : BitVec 64 :=
  if r = .x0 then p.xp else if r = .x2 then p.yp else if r = .x4 then p.dp else
    if r = .x5 then BitVec.ofNat 64 p.dl else if r = .x6 then BitVec.ofNat 64 p.k else if r = .x7 then p.rp
      else p.B

theorem cr_regs (p : GkP) (rb : List Byte) (s : State) (h : CR p rb s) :
    ∀ r ∈ [Reg.x0, .x2, .x4, .x5, .x6, .x7], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, -, -, hk, hdl, hdp, -, hxp, hyp, hrp, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hxp
  · exact hyp
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hrp

/-- After the entry's first instruction. -/
def EA (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∀ r ∈ [Reg.x0, .x2, .x4, .x5, .x6, .x7, .x8], t.gpr r = entryRegs p r) ∧
    WP isa (.block (GenerateKey.entry.drop 1)) t (G1 p rb)

theorem entry_split : GenerateKey.entry ++ domHead = ([.ldrSp .x8 8] : List Instr) ++ (GenerateKey.entry.drop 1 ++ domHead) := rfl

theorem cr_ea (p : GkP) (rb : List Byte) (s : State) (h : CR p rb s) :
    WP isa (.block [.ldrSp .x8 8]) s (EA p rb) := by
  have c := gkCtx_of h.1
  have hw := cr_g1 p rb s h
  rw [show GenerateKey.entry = [.ldrSp .x8 8] ++ GenerateKey.entry.drop 1 from rfl, WP.block_append_iff] at hw
  refine WP.mono (wp_and (ldrSp_ok h.2.2.1 c.ha1) hw) fun t ⟨⟨⟨h8, _⟩, k⟩, hr⟩ => ⟨fun r hr' => ?_,
    WP.mono hr fun u hu => hu.1⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    have hc := cr_regs p rb s h
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [h8]; rfl

/-- A stage of some random octets, without the outputs' regions (which it
includes). -/
def Ex' (Φ : GkP → List Byte → State → Prop) (p : GkP) (t : State) : Prop := ∃ rb, Φ p rb t

/-- The entry and the check of p. -/
theorem front_ct : RelCT isa (Two (Ex' CR)) (.block (GenerateKey.entry ++ domHead)) (Two (Ex GC)) := by
  rw [entry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex' EA) [] (pins_nil _) (by taint_decide)
    fun p s ⟨rb, h⟩ => WP.mono (cr_ea p rb s h) fun _ h' => ⟨rb, h'⟩)
    (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex' G1) [.x0, .x2, .x4, .x5, .x6, .x7, .x8]
      (pins_of entryRegs fun p s ⟨_, h⟩ => h.1) (by taint_decide) fun p s ⟨rb, h⟩ => WP.mono h.2 fun _ h' => ⟨rb, h'⟩)
    (two_post (two_map (fun p : GkP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨_, h⟩ => h.1.dhp) domHead_ct)
      fun p s ⟨rb, h⟩ => WP.mono (g1_gc p rb s h) fun u ⟨hu, _⟩ => ⟨rb, hu, hu.2.1⟩))))

/-! ## The scalar -/

/-- After the test of the domain's length. -/
def GQ (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₀ rb) mi t ∧ t.gpr .x3 = BitVec.ofNat 64 (p.dl - 2 * p.k)) ∧ Ok p rb

theorem gp_gq (p : GkP) (rb : List Byte) (t : State) (h : GP p rb t) :
    WP isa (.block qTest) t fun u => GQ p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP⟩, -, ho⟩ := h
  exact WP.mono hP.qtest fun u ⟨⟨h3, hm⟩, k⟩ => ⟨⟨⟨mi, hP.keep hm k (by decide), h3⟩, ho⟩, k.mono (by decide)⟩

theorem gq_eval {p : GkP} {rb : List Byte} {t : State} (h : GQ p rb t) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) := by
  obtain ⟨⟨_, _, h3⟩, _⟩ := h
  rw [eval_zero, h3]

theorem gq_gs (p : GkP) (rb : List Byte) (t : State) (h : GQ p rb t) (hd : Dst p t) {sp : Nat}
    (hsp : (p.D₀ rb).bs = sp) :
    WP isa (seqs (scan sp)) t fun u => GS p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, -⟩, ho⟩ := h
  subst hsp
  exact WP.mono hP.scanB fun u ⟨⟨hu, _, hEl, h3, _⟩, k⟩ => ⟨⟨⟨mi, hu, hEl, h3⟩, hd.keep k, ho⟩, k⟩

theorem gq_pre (p : GkP) (rb : List Byte) (t : State) (h : GQ p rb t) {sp : Nat} (hsp : (p.D₀ rb).bs = sp) :
    ScanPre sp (p.D₀ []).bsp t := by
  obtain ⟨⟨mi, hP, -⟩, -⟩ := h
  subst hsp
  exact hP.scanPreB

/-- The bound's scan. -/
theorem bound_ct : RelCT isa (Two (Ex GP)) (seqs GenerateKey.bound) (Two (Ex GS)) := by
  unfold GenerateKey.bound
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex GQ)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex GP p s) => by
      obtain ⟨_, ⟨⟨_, hP⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) gp_gq) ?_)
  rw [seqs_one]
  refine two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [gq_eval h₁, gq_eval h₂]) ?_ ?_
  · exact ex_postD' (two_map (fun p : GkP => (p.D₀ []).bsp) (fun p s ⟨⟨rb, h, _⟩, he⟩ =>
      gq_pre p rb s h (bs_n h.1.choose_spec.1.1 (Option.some.inj ((gq_eval h).symm.trans he))))
      (scan_ct (by taint_decide) (by taint_decide))) fun p rb s h he hd =>
        gq_gs p rb s h hd (bs_n h.1.choose_spec.1.1 (Option.some.inj ((gq_eval h).symm.trans he)))
  · exact ex_postD' (two_map (fun p : GkP => (p.D₀ []).bsp) (fun p s ⟨⟨rb, h, _⟩, he⟩ =>
      gq_pre p rb s h (bs_q h.1.choose_spec.1.1 (Option.some.inj ((gq_eval h).symm.trans he))))
      (scan_ct (by taint_decide) (by taint_decide))) fun p rb s h he hd =>
        gq_gs p rb s h hd (bs_q h.1.choose_spec.1.1 (Option.some.inj ((gq_eval h).symm.trans he)))

/-- x's range checks. -/
theorem scalar_ct :
    RelCT isa (Two (Ex G3)) (seqs (CheckPrivate.scalarRange)) (Two (Ex G8)) := by
  rw [scalarRange_eq]
  refine RelCT.seqs_append (by simp [isNonzero, geArr, cmpArr]) (by simp) (RelCT.seq (R := Two (Ex G4))
    (show RelCT isa (Two (Ex G3)) (seqs (isNonzero aXm)) (Two (Ex G4)) from
      ex_post (two_map GkP.ws (fun p s ⟨rb, ⟨⟨mi, hI, _⟩, _⟩, _⟩ => hI.goodW1.1)
        (geArr_ct (by decide) (by decide) (by taint_decide))) g3_g4) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex G5)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.g fun (p : GkP) s (h : Ex G4 p s) => by
      obtain ⟨_, ⟨⟨_, hI, _⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)) g4_g5) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex G6)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex G5 p s) => by
      obtain ⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) g5_g6) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex G7)) (two_ite
    (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [g6_eval h₁, g6_eval h₂]) ?_ ?_) ?_)
  · simp only [List.cons_append, List.nil_append]
    refine seqs_cons_ct (by simp [ltP, Crt.copyArr]) (RelCT.seq
      (R := Two (Ex fun p rb t => G6e p rb t ∧ p.dl = 2 * p.k)) (ex_post' (two_taint [.x0]
        (pins_x0B GkP.B fun (p : GkP) s (h : Ex G6 p s ∧ _) => by
          obtain ⟨⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide))
        fun p rb s h he => WP.mono (g6_e p rb s h) fun u ⟨hu, k⟩ =>
          ⟨⟨hu, h.1.choose_spec.1.1.noq (Option.some.inj ((g6_eval h).symm.trans he))⟩, k⟩) ?_)
    exact ex_post (two_map GkP.ws (fun p s ⟨rb, ⟨⟨⟨mi, hI, _⟩, _⟩, _⟩, _⟩ => hI.goodW1)
      (ltP_ct (by decide) (by decide) (by taint_decide) (by taint_decide))) fun p rb s h => e_g7n p rb s h.1 h.2
  · simp only [List.cons_append, List.nil_append]
    refine seqs_cons_ct (by simp [Crt.loadArr]) (RelCT.seq
      (R := Two (Ex fun p rb t => G6e p rb t ∧ p.dl = 3 * p.k)) (ex_post' (two_taint [.x0]
        (pins_x0B GkP.B fun (p : GkP) s (h : Ex G6 p s ∧ _) => by
          obtain ⟨⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide))
        fun p rb s h he => WP.mono (g6_e p rb s h) fun u ⟨hu, k⟩ =>
          ⟨⟨hu, h.1.choose_spec.1.1.q (Option.some.inj ((g6_eval h).symm.trans he))⟩, k⟩) ?_)
    refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [ltArr, cmpArr]) (RelCT.seq (R := Two (Ex G6q))
      (ex_post (two_map (fun p : GkP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩,
          p.dp + BitVec.ofNat 64 (2 * p.k), p.k⟩ : BPub)) (fun p s ⟨rb, h, _⟩ => e_lpreQ p rb s h.1 h.2)
        (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) fun p rb s h => e_q p rb s h.1 h.2) ?_)
    exact ex_post (two_map GkP.ws (fun p s ⟨rb, ⟨⟨mi, hI, _⟩, _⟩, _⟩ => hI.goodW1.1)
      (ltArr_ct (by decide) (by decide) (by taint_decide))) q_g7
  rw [seqs_one]
  exact ex_post (two_taint [.x0] (pins_x0B GkP.g fun (p : GkP) s (h : Ex G7 p s) => by
    obtain ⟨_, ⟨⟨_, hI, _⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)) g7_g8



/-! ## Zeros to the outputs -/

/-- The outer workspace, with the outputs' regions. -/
def FD' (p : GkP) (t : State) : Prop := Fz p t ∧ Dst p t

/-- `zeroOut sPtr sK`, to `x` or `y`. -/
theorem zo_ct {sPtr : Nat} (ptr : GkP → Addr) (hP : sPtr < 32)
    (hO : ∀ p t, Fz p t → word t.mem p.B (8 * sPtr) = ptr p)
    (hD : ∀ p t, Dst p t → ∀ j < p.k, InRegions t.wr (ptr p + BitVec.ofNat 64 j) 1 ∧
      p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 j))
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sPtr, ldh .x2 sK, movi .x3 0]) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x1, .x2]) (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1])
      hc₂).isSome = true) :
    RelCT isa (Two FD') (Keys.zeroOut sPtr sK) (Two FD') := by
  have post : ∀ p t, FD' p t → WP isa (Keys.zeroOut sPtr sK) t (FD' p) := fun p t ⟨hz, hd⟩ => by
    have hk1 := hz.k1
    have hk2 := hz.k2
    have hZ := hz.hZ
    refine WP.mono (VG.Proof.Rsa.AArch64.zeroOut_ok hz.scr hz.x0 (by omega) hP (by decide) (hO p t hz) hz.wK
      (by omega) (by omega) ⟨fun i hi => (hD p t hd i hi).1, fun i hi => (hD p t hd i hi).2⟩) fun u ⟨_, hfr, k⟩ => ?_
    exact ⟨hz.out (outside_of_frame (fun j hj => (hD p t hd j hj).2) hfr) k.wr (k.gpr .x0 (by decide)), hd.keep k⟩
  unfold Keys.zeroOut
  refine RelCT.seq (R := Two fun p t => (t.gpr .x1 = ptr p ∧ t.gpr .x2 = BitVec.ofNat 64 p.k) ∧
      WP isa (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1]) t (FD' p))
    (two_piece [.x0] (pins_x0B GkP.B fun _ _ h => h.1.x0) hT₁ fun p t h => ?_) ?_
  · have hz := h.1
    have hn := hz.scr.nowrap
    have hZ := hz.hZ
    have hw := post p t h
    unfold Keys.zeroOut at hw
    exact wp_and (zoBlk_ok hz.x0 hP (hO p t hz) hz.wK fun i hi => hz.scr.ld (by omega)) (WP.seq_iff.mp hw)
  · exact two_post (two_taint [.x1, .x2] (pins_of (fun (p : GkP) r => if r = .x1 then ptr p else
      BitVec.ofNat 64 p.k) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) hT₂) fun p t h => h.2

/-- Zeros to x and y, and 2 returned. -/
theorem fail_ct : RelCT isa (Two FD') (GenerateKey.fail 2) fun _ _ => True := by
  unfold GenerateKey.fail
  simp only [seqs]
  exact RelCT.seq (zo_ct GkP.xp (by decide) (fun _ _ h => h.wX) (fun p t h j hj => (h j hj).1)
    (by taint_decide) (by taint_decide))
    (RelCT.seq (zo_ct GkP.yp (by decide) (fun _ _ h => h.wY) (fun p t h j hj => (h j hj).2)
      (by taint_decide) (by taint_decide)) (two_taint [] (pins_nil _) (by taint_decide)))

end VG.Proof.Ffdh.AArch64.GenerateKey
