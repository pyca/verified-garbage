module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSAttempt
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Fn.lean`).
`randomSign_correct`: `vg_dsa_sign_random` meets `rsContract`. In its
frame, the entry (`entry_ok`), the scan of q (`prepareQ_ok`), the attempts
(`attempts_ok`, or none when `q ≤ 1`) and the exit (`finish_ok`) follow one
another; the result is `randomSignBytes`'s (`rsRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

theorem attempts_ok {s₀ : State} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) :
    ∀ a u t, AttInv s₀ a u t → WP isa attempts t (AttOut s₀) := by
  intro a u t hi
  unfold attempts
  refine WP.loop (M := isa) (fun n (t : State) => ∃ u, AttInv s₀ n u t) (fun n t ⟨u, hi⟩ =>
    WP.mono (attempt_ok h hq hi) fun t' ⟨e, ho, hc⟩ => ?_) a t ⟨u, hi⟩
  by_cases h4 : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u n = 4
  · obtain ⟨hn, hi'⟩ := hc h4
    exact .inr ⟨by rw [e, decide_eq_true h4], n - 1, by omega, _, hi'⟩
  · exact .inl ⟨by rw [e, decide_eq_false h4], ho h4⟩

/-- The specification's result is the attempts'. -/
theorem rsRes_eq {s₀ : State} (h : rsContract.pre s₀) : rsRes s₀ = resOf s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    lv, -, hkl, -⟩ := h
  simp only [rsRes, resOf, randomSignRemaining, inpOf, randOf, Spec.Dsa.randomSignBytes, List.drop_zero]
  rw [ite_eq_right (by
    simp only [decide_eq_true lv, Bool.not_true, VG.Proof.Bignum.bytesAt_length, hkl, Bool.false_or,
      bne_self_eq_false, Bool.false_eq_true, not_false_eq_true])]
  simp only [rlOf, RL.kl, hkl]

/-- The count loop of `zeroOut`: the `N` octets at `dst` (`t4`) := 0 (`a0`). -/
theorem zeroLoopA_ok {s : State} {dst : Addr} {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64)
    (ho : ∀ i < N, InRegions s.wr (off dst i) 1) (hno : dst.toNat + N ≤ 2 ^ 64)
    (h0 : s.gpr .a0 = 0) (h4 : s.gpr .t4 = dst) (h5 : s.gpr .t5 = BitVec.ofNat 64 N) :
    WP isa (Impl.Bignum.RISCV64.countLoop .t5 [.store .b .a0 .t4 0, .addi .t4 .t4 1]) s fun t =>
      (Spec.Rsa.bytesAt t.mem dst N = List.replicate N 0 ∧ Outside dst 0 N s.mem t.mem) ∧
        Keep [.t4, .t5] s t := by
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t4 = off dst i ∧ Outside dst 0 i s.mem t.mem ∧ (∀ i' < i, t.mem (off dst i') = 0) ∧
      Keep [.t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.store .b .a0 .t4 0, .addi .t4 .t4 1] ++
      ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := N) hN' hN Inv (fun i hi t ⟨t4, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [h4, off, BitVec.add_zero], Outside.refl _ _ _ _, fun _ h => absurd h (by omega), Keep.refl _ _⟩ h5)
    fun t ⟨_, tout, tb, tk⟩ => ⟨⟨?_, tout⟩, tk⟩
  · have t0 : t.gpr .a0 = 0 := (tk.gpr (by decide)).trans h0
    have hw : InRegions t.wr (off dst i) 1 := by rw [tk.2.2]; exact ho i hi
    have hst : WP isa (.block [.store .b .a0 .t4 0, .addi .t4 .t4 1, .addi .t5 .t5 (-1)]) t fun t' =>
        t' = (({ t with mem := t.mem.write (off dst i) 1 ((0 : BitVec 64).setWidth 8) } : State).write .t4
          (off dst (i + 1))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
      brun [t4, t0, hw, add_ofNat_zero]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw1 := write1_outside t.mem dst (d := i) ((0 : BitVec 64).setWidth 8) (by omega)
    refine ⟨⟨by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega)).trans (hw1.mono (by omega) (by omega))
    · intro i' hi'
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [ofs_off0 dst (by omega)]; omega)]; exact tb i' hi'
      · rw [write1_self]; rfl
    · exact Keep.trans' tk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))
  · rw [Spec.Rsa.bytesAt]
    refine List.eq_replicate_iff.mpr ⟨by simp, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact tb i (List.mem_range.mp hi)

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  a0 : t.gpr .a0 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
    R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)
  used : t.mem.readW (rlOf s₀).used 64 = BitVec.ofNat 64 R.used
  cs : ∀ i < 12, t.gpr (cs i) = s₀.gpr (cs i)
  ra : t.gpr .ra = s₀.gpr .ra
  sp : t.sp = (rlOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.RandomSignResult} (h : rsContract.pre s₀)
    (hc : Ctx (rlOf s₀) s₀ t) (h5 : t.gpr .s5 = BitVec.ofNat 64 R.used)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
      R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0))
    (hnone : R.status ≠ 1 → R.signature = none) :
    WP isa (finish (lenQ .t5 ++ ([.add .t5 .t5 .t5] : List Instr))) t (Fin s₀ R) := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (wp_sp (WP.keep (c := .block [.addi .a0 .s10 (-1)]) [.a0] (Q := fun t₁ =>
    t₁.mem = t.mem ∧ t₁.gpr .a0 = t.gpr .s10 - BitVec.ofNat 64 1) (by brun) (by decide) (by rfl)))
    fun t₁ ⟨⟨⟨m1, a0⟩, k1⟩, sp1⟩ => ?_)
  have hc₁ : Ctx (rlOf s₀) s₀ t₁ := hc.step hL sp1 k1.2.1 k1.2.2
    (fun r hr => k1.1 r (by revert r hr; decide)) (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  have hout : ∀ (P : State → Prop), (∀ t₂, Ctx (rlOf s₀) s₀ t₂ → Keep [.a0, .t3, .t4, .t5] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
        R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0) → P t₂) →
      WP isa (.ite (.zero .a0) (.block []) (zeroOut (lenQ .t5 ++ [.add .t5 .t5 .t5]))) t₁ P := by
    intro P hP
    refine WP.ite (decide (R.status = 1)) (by rw [Steps.eval_zero, a0, h10, sub1_beq _ (by omega)])
      (fun hs => ?_) (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (hP t₁ hc₁ (Keep.refl _ _) (by rw [m1]; exact hsig hs))
    · simp only [decide_eq_false_iff_not] at hs
      unfold zeroOut
      obtain ⟨i64, l64⟩ := hc₁.word hL rfl (d := 64) (by decide) (by decide)
      have o64 := hc₁.out
      simp only [oOut] at o64
      have e2 := lenQ_eq (pl := (rlOf s₀).pl) (ql := (rlOf s₀).ql) (by omega) (by omega)
      refine WP.seq (WP.mono (wp_sp (WP.keep [.t3, .t4, .t5, .a0] (Q := fun t₂ => t₂.gpr .a0 = 0 ∧
        t₂.gpr .t4 = (rlOf s₀).out ∧ t₂.gpr .t5 = BitVec.ofNat 64 (2 * (rlOf s₀).ql) ∧ t₂.mem = t₁.mem)
        (by
          brun [lenQ, hc₁.sp, hc₁.s2, e2, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, oOut, i64, l64,
            o64, exec_li_zero, ← BitVec.ofNat_add]
          congr 1; omega) (by decide) (by rfl)))
        fun t₂ ⟨⟨⟨b0, b4, b5, m2⟩, k2⟩, sp2⟩ => ?_)
      have ho : ∀ i < 2 * (rlOf s₀).ql, InRegions t₂.wr (off (rlOf s₀).out i) 1 := fun i hi =>
        ⟨(rlOf s₀).outR, by rw [k2.2.2, hc₁.wr, hwr]; simp,
          VG.Offset.contains_base _ (by omega) (by omega)⟩
      refine WP.mono (wp_sp (zeroLoopA_ok (by omega) (by omega) ho hL.nwOut b0 b4 b5))
        fun t₃ ⟨⟨⟨z3, o3⟩, k3⟩, sp3⟩ => ?_
      have k23 := k2.trans k3
      refine hP t₃ (hc₁.step hL (sp3.trans sp2) k23.2.1 k23.2.2
        (fun r hr => k23.1 r (by revert r hr; decide)) ?_) (k23.mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega)
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  have c5 : t₂.gpr .s5 = BitVec.ofNat 64 R.used := (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans h5)
  have c10 : t₂.gpr .s10 = BitVec.ofNat 64 R.status :=
    (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans h10)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (wp_sp (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)))
    fun t₃ ⟨⟨⟨t0, _, o3⟩, k3⟩, sp3⟩ => ?_
  have hc₃ : Ctx (rlOf s₀) s₀ t₃ := hc₂.step hL sp3 k3.2.1 k3.2.2 (fun r hr => k3.1 r (by revert r hr; decide))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  have hus : InRegions t₃.wr (rlOf s₀).used 8 := by
    rw [hc₃.wr, hwr]
    exact ⟨(rlOf s₀).usedR, by simp, Region.contains_self _ _⟩
  have hal := hL.alU
  obtain ⟨i72, l72⟩ := hc₃.word hL rfl (d := 72) (by decide) (by decide)
  have o72 := hc₃.used
  simp only [oUsed] at o72
  refine WP.mono (wp_sp (WP.keep (c := .block [.load .d .t4 .t0 oUsed, .store .d .s5 .t4 0, .addi .a0 .s10 0])
    [.t4, .a0] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW (rlOf s₀).used (BitVec.ofNat 64 R.used) ∧ t₄.gpr .a0 = BitVec.ofNat 64 R.status)
    (by
      brun [t0, oUsed, i72, l72, o72, BitVec.add_zero, (k3.1 _ (by decide)).trans c5,
        (k3.1 _ (by decide)).trans c10, hus, hal]) (by decide) (by rfl)))
    fun t₄ ⟨⟨⟨m4, a4⟩, k4⟩, sp4⟩ => ?_
  -- The used word apart from the frame and `out`.
  have huR : (rlOf s₀).usedR.Contains (rlOf s₀).used 8 := Region.contains_self _ _
  have fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (rlOf s₀).F d) 64 = t₃.mem.readW (off (rlOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (RL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  have hsw : SaveW t₄ (rlOf s₀).F := fun i hi =>
    frame_word hL rfl (by rw [k4.2.2, hc₃.wr]) (by simp only [oSave, frameBytes]; omega)
      (by simp only [oSave]; omega)
  refine WP.mono (restoreRegs_ok t₄ (sp4.trans hc₃.sp) hsw (v := fun i => if i < 12 then s₀.gpr (cs i) else s₀.gpr .ra)
    (fun i hi => by rw [ite_eq_left hi]; exact (fw _ (by simp only [oSave, frameBytes]; omega)).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.ra)) fun t₅ ⟨r5, ra5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, fun i hi => by rw [r5 i hi, ite_eq_left hi], ra5, sp5.trans (sp4.trans hc₃.sp),
    rd5.trans (k4.2.1.trans hc₃.rd), wr5.trans (k4.2.2.trans hc₃.wr)⟩
  · rw [o5 .a0 (by decide) (by decide) (by decide)]; exact a4
  · rw [m5, m4, bytes_frame (rs := [(rlOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by omega)]
    rw [bytes_outside (o3.mono (by omega) (by simp only [oNonce, frameBytes]; omega)) hL.dFO (by omega)]
    exact o2
  · rw [m5, m4, Mem.readW_writeW_self64]

theorem preserved_cs : ∀ r ∈ preserved, ∃ i < 12, r = cs i := by decide

/-- The exit's state, after the frame is freed, meets the contract. -/
theorem fin_post {s₀ t : State} (h : rsContract.pre s₀) (hf : Fin s₀ (rsRes s₀) t) :
    abiPreserved s₀ (freed frameBytes t) ∧ rsContract.post s₀ (freed frameBytes t) := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hst : (rsRes s₀).status ≤ 2 := by
    rw [rsRes_eq h]; exact Dsa.randomSignLoop_status_le _ _ _ _ _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hol, -, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.ra⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    obtain ⟨i, hi, rfl⟩ := preserved_cs r hr
    exact hf.cs i hi
  · simp only [freed, hf.sp, RL.F, rlOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.a0, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [freed]
    have e0 : s₀.gpr .a0 = (rlOf s₀).out := rfl
    have e1 : (s₀.gpr .a1).toNat = 2 * (rlOf s₀).ql := hol
    rw [e0, e1]; exact hf.out
  · simp only [freed, Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) hf.used

theorem randomSign_correct (s₀ : State) (h : rsContract.pre s₀) :
    ∃ tr t, Exec isa Impl.Dsa.RISCV64.RandomSign.code s₀ tr t ∧ abiPreserved s₀ t ∧ rsContract.post s₀ t := by
  show WP isa Impl.Dsa.RISCV64.RandomSign.code s₀ fun t => abiPreserved s₀ t ∧ rsContract.post s₀ t
  have hL := rlOf_ok h
  have hst : (resOf s₀).status ≤ 2 := Dsa.randomSignLoop_status_le _ _ _ _ _ _
  have hnone : (resOf s₀).status ≠ 1 → (resOf s₀).signature = none := fun hs => by
    have := Dsa.randomSignLoop_success (inpOf (rlOf s₀) s₀.mem).pLen (inpOf (rlOf s₀) s₀.mem).qLen
      (inpOf (rlOf s₀) s₀.mem).key (inpOf (rlOf s₀) s₀.mem).digest 8 ((inpOf (rlOf s₀) s₀.mem).rand.drop 0)
    cases hc : (resOf s₀).signature with
    | none => rfl
    | some _ => exact absurd (this.mpr (by simp only [resOf, randomSignRemaining] at hc ⊢; rw [hc]; rfl)) hs
  have hfin : ∀ t, Ctx (rlOf s₀) s₀ t → t.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
        (resOf s₀).signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)) →
      WP isa (finish (lenQ .t5 ++ [.add .t5 .t5 .t5])) t fun t' =>
        abiPreserved s₀ (freed frameBytes t') ∧ rsContract.post s₀ (freed frameBytes t') :=
    fun t hc h5 h10 hsig => WP.mono (finish_ok h hc h5 h10 hst hsig hnone) fun t' hf =>
      fin_post h (by rw [rsRes_eq h]; exact hf)
  unfold Impl.Dsa.RISCV64.RandomSign.code
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.RISCV64.RandomSign.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (prepareQ_ok h he.ctx) fun t₂ ⟨⟨sc, h0, m2, k2⟩, sp2⟩ => ?_)
  have c5 : t₂.gpr .s5 = BitVec.ofNat 64 0 := (k2.1 _ (by decide)).trans he.s5
  refine WP.seq (WP.ite (decide (¬ 1 < qOf s₀)) (by rw [Steps.eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_))
  · -- q ≤ 1: no attempt.
    simp only [decide_eq_true_eq] at hq
    refine WP.mono (wp_sp (WP.keep (c := .block [.li .s10 0]) [.s10] (Q := fun t₃ => t₃.mem = t₂.mem ∧
      t₃.gpr .s10 = BitVec.ofNat 64 0) (by brun [exec_li_zero]; rfl) (by decide) (by rfl)))
      fun t₃ ⟨⟨⟨m3, a10⟩, k3⟩, sp3⟩ => ?_
    have hd : (randomSignDraw (inpOf (rlOf s₀) s₀.mem) 0) = ⟨none, 0, [4]⟩ := by
      rw [draw_eq hL, show (128 : Nat) = 127 + 1 from rfl, Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega)]
    obtain ⟨-, rst, ru⟩ := (RandomSignResultRel.refl (inpOf (rlOf s₀) s₀.mem) 0 8 :
      RandomSignResultRel (inpOf (rlOf s₀) s₀.mem) 0 (resOf s₀) 0 (7 + 1)).sample_none
      (show (randomSignDraw (inpOf (rlOf s₀) s₀.mem) 0).scalar = none by rw [hd])
    rw [hd] at rst ru
    refine hfin t₃ (sc.ctx.step hL sp3 k3.2.1 k3.2.2 (fun r hr => k3.1 r (by revert r hr; decide))
      (by rw [m3]; exact Frame.refl _ _)) ?_ ?_ fun h1 => absurd (rst ▸ h1) (by decide)
    · rw [k3.1 _ (by decide), c5]; congr 1; simp only [resOf] at ru ⊢; omega
    · rw [a10, rst]; rfl
  · -- q > 1: the attempts.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    refine WP.mono (attempts_ok h hq 8 0 t₂ ⟨sc, c5, by omega, (k2.1 _ (by decide)).trans he.s6, by decide,
      by decide, fun j hj => ?_, RandomSignResultRel.refl _ _ _⟩) fun t₃ ao => hfin t₃ ao.sc.ctx ao.s5 ao.s10 ao.out
    rw [m2]
    have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    have := hE.Wq
    have := hL.ql
    have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
    exact he.nonce j (by omega)

end VG.Proof.Dsa.RISCV64.RS
