module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Attempt
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on PPC64LE: the function

`randomSign_correct`: `vg_dsa_sign_random` meets `rsContract`. In its frame,
the entry (`entry_ok`), the scan of q (`prepareQ_ok`), the attempts
(`attempts_ok`, or none when `q ≤ 1`) and the exit (`finish_ok`) follow one
another; the result is `randomSignBytes`'s (`rsRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining)
open VG.Proof.Dsa.Random (sampleStatus)

theorem attempts_ok {s₀ : State} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) :
    ∀ a u t, AttInv s₀ a u t → WP isa attempts t (AttOut s₀) := by
  intro a u t hi
  unfold attempts
  refine WP.loop (M := isa) (fun n (t : State) => ∃ u, AttInv s₀ n u t) (fun n t ⟨u, hi⟩ =>
    WP.mono (attempt_ok h hq hi) fun t' h' => ?_) a t ⟨u, hi⟩
  rcases h' with ⟨e, o⟩ | ⟨e, m, hm, u', hi'⟩
  · exact .inl ⟨e, o⟩
  · exact .inr ⟨e, m, hm, u', hi'⟩

/-- The specification's result is the attempts'. -/
theorem rsRes_eq {s₀ : State} (h : rsContract.pre s₀) : rsRes s₀ = resOf s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    lv, -, hkl, -⟩ := h
  simp only [rsRes, resOf, randomSignRemaining, inpOf, randOf, Spec.Dsa.randomSignBytes, List.drop_zero]
  rw [ite_eq_right (by
    simp only [decide_eq_true lv, Bool.not_true, VG.Proof.Bignum.bytesAt_length, hkl, Bool.false_or,
      bne_self_eq_false, Bool.false_eq_true, not_false_eq_true])]
  simp only [rlOf, RL.kl, hkl]

theorem ctx_012 : ∀ r ∈ ctxRegs, r ∉ ([.r0, .r12] : List Reg) := by decide

theorem ctx_z : ∀ r ∈ ctxRegs, r ∉ ([.r0, .r16, .r17] ++ [.r16, .r17] : List Reg) := by decide

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  r3 : t.gpr .r3 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
    R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)
  used : t.mem.readW (rlOf s₀).used 64 = BitVec.ofNat 64 R.used
  nv : ∀ i < 18, t.gpr (nv i) = s₀.gpr (nv i)
  r2 : t.gpr .r2 = s₀.gpr .r2
  lr : t.lr = s₀.lr
  sp : t.sp = (rlOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.RandomSignResult} (h : rsContract.pre s₀)
    (hc : Ctx (rlOf s₀) s₀ t) (h25 : t.gpr .r25 = BitVec.ofNat 64 R.used)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
      R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0))
    (hnone : R.status ≠ 1 → R.signature = none) :
    WP isa (finish [.add .r17 .r21 .r21]) t (Fin s₀ R) := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (WP.keep (c := .block [.subi .r3 .r31 1]) [.r3] (Q := fun t₁ => t₁.mem = t.mem ∧
    t₁.gpr .r3 = t.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₁ ⟨⟨m1, a3⟩, k1⟩ => ?_)
  have hc₁ : Ctx (rlOf s₀) s₀ t₁ := hc.step hL k1.sp k1.rd k1.wr (fun r hr => k1.gpr r (ctx_r3 r hr))
    (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  have hout : ∀ (P : State → Prop), (∀ t₂, Ctx (rlOf s₀) s₀ t₂ → Keep [.r0, .r3, .r16, .r17] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
        R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0) → P t₂) →
      WP isa (.ite (.zero .d .r3) (.block []) (zeroOut [.add .r17 .r21 .r21])) t₁ P := by
    intro P hP
    refine WP.ite (decide (R.status = 1)) (by rw [eval_zero, a3, h31, sub1_beq _ (by omega)]) (fun hs => ?_)
      (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (hP t₁ hc₁ (Keep.refl _ _) (by rw [m1]; exact hsig hs))
    · simp only [decide_eq_false_iff_not] at hs
      unfold zeroOut
      refine WP.seq (WP.mono (WP.keep [.r0, .r16, .r17] (Q := fun t₂ => t₂.gpr .r0 = 0 ∧
        t₂.gpr .r16 = off (rlOf s₀).out 0 ∧ t₂.gpr .r17 = BitVec.ofNat 64 (2 * (rlOf s₀).ql) ∧ t₂.mem = t₁.mem)
        (by prun [hc₁.r18, hc₁.r21, ← BitVec.ofNat_add]; exact ⟨rfl, by congr 1; omega⟩) (by decide))
        fun t₂ ⟨⟨b0, b16, b17, m2⟩, k2⟩ => ?_)
      have ho : Scr t₂ (rlOf s₀).out (2 * (rlOf s₀).ql) :=
        Scr.of_mem (by rw [k2.wr, hc₁.wr, hwr]; simp) hL.nwOut
      refine WP.mono (zeroLoop_ok (by omega) (by omega) ho b0 b16 b17) fun t₃ ⟨⟨z3, o3⟩, k3⟩ => ?_
      refine hP t₃ (hc₁.step hL (k2.trans k3).sp (k2.trans k3).rd (k2.trans k3).wr
        (fun r hr => (k2.trans k3).gpr r (ctx_z r hr)) ?_) ((k2.trans k3).mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega)
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  have c25 : t₂.gpr .r25 = BitVec.ofNat 64 R.used := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h25)
  have c31 : t₂.gpr .r31 = BitVec.ofNat 64 R.status := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h31)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)) fun t₃ ⟨⟨_, _, o3⟩, k3⟩ => ?_
  have hc₃ : Ctx (rlOf s₀) s₀ t₃ := hc₂.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_012 r hr))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  have hus : InRegions t₃.wr ((rlOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [hc₃.wr, hwr, BitVec.add_zero]
    exact ⟨(rlOf s₀).usedR, by simp, Region.contains_self _ _⟩
  have hus' : InRegions t₃.wr (rlOf s₀).used 8 := by rw [← BitVec.add_zero (rlOf s₀).used]; exact hus
  refine WP.mono (WP.keep (c := .block [.store .d .r25 .r30 0, .addi .r3 .r31 0]) [.r3] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW ((rlOf s₀).used + BitVec.ofNat 64 0) (BitVec.ofNat 64 R.used) ∧
      t₄.gpr .r3 = BitVec.ofNat 64 R.status)
    (by prun [hc₃.r30, (k3.gpr _ (by decide)).trans c25, (k3.gpr _ (by decide)).trans c31, hus, hus', add0]) (by decide))
    fun t₄ ⟨⟨m4, a3⟩, k4⟩ => ?_
  -- The used word apart from the frame and `out`.
  have huR : (rlOf s₀).usedR.Contains ((rlOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero]; exact Region.contains_self _ _
  have fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (rlOf s₀).F d) 64 = t₃.mem.readW (off (rlOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (RL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  have hin : ∀ i < 19, InRegions (t₄.rd ++ t₄.wr) (off (rlOf s₀).F (oSave + 8 * i)) 8 := fun i hi => by
    rw [k4.rd, k4.wr, hc₃.rd, hc₃.wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains hL rfl (by simp only [oSave]; omega)
      (by simp only [oSave, frameBytes]; omega)⟩
  refine WP.mono (restoreRegs_ok t₄ (k4.sp.trans hc₃.sp) hin
    (fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega)).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.lr)) fun t₅ ⟨r5, l5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, r5, ?_, l5, sp5.trans (k4.sp.trans hc₃.sp), rd5.trans (k4.rd.trans hc₃.rd),
    wr5.trans (k4.wr.trans hc₃.wr)⟩
  · rw [o5 .r3 (by decide) (by decide) (by decide)]; exact a3
  · rw [m5, m4, bytes_frame (rs := [(rlOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by omega)]
    rw [bytes_outside (o3.mono (by omega) (by simp only [oNonce, frameBytes]; omega)) hL.dFO (by omega)]
    exact o2
  · rw [m5, m4, BitVec.add_zero, Mem.readW_writeW_self64]
  · rw [o5 .r2 (by decide) (by decide) (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide)]; exact hc₂.r2

theorem ctx_31 : ∀ r ∈ ctxRegs, r ∉ ([.r31] : List Reg) := by decide

theorem preserved_nv : ∀ r ∈ preserved, r = .r2 ∨ ∃ i < 18, r = nv i := by decide

/-- The exit's state, after the frame is freed, meets the contract. -/
theorem fin_post {s₀ t : State} (h : rsContract.pre s₀) (hf : Fin s₀ (rsRes s₀) t) :
    abiPreserved s₀ (freed frameBytes t) ∧ rsContract.post s₀ (freed frameBytes t) := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hst : (rsRes s₀).status ≤ 2 := by
    rw [rsRes_eq h]; exact Dsa.randomSignLoop_status_le _ _ _ _ _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hol, -, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.lr⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    rcases preserved_nv r hr with rfl | ⟨i, hi, rfl⟩
    · exact hf.r2
    · exact hf.nv i hi
  · simp only [freed, hf.sp, RL.F, rlOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.r3, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [freed]
    have e3 : s₀.gpr .r3 = (rlOf s₀).out := rfl
    have e4 : (s₀.gpr .r4).toNat = 2 * (rlOf s₀).ql := hol
    rw [e3, e4]; exact hf.out
  · simp only [freed, Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) hf.used

end VG.Proof.Dsa.PPC64LE.RS

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining)
open VG.Proof.Dsa.Random (sampleStatus)

theorem randomSign_correct (s₀ : State) (h : rsContract.pre s₀) :
    ∃ tr t, Exec isa Impl.Dsa.PPC64LE.RandomSign.code s₀ tr t ∧ abiPreserved s₀ t ∧ rsContract.post s₀ t := by
  show WP isa Impl.Dsa.PPC64LE.RandomSign.code s₀ fun t => abiPreserved s₀ t ∧ rsContract.post s₀ t
  have hL := rlOf_ok h
  have hst : (resOf s₀).status ≤ 2 := Dsa.randomSignLoop_status_le _ _ _ _ _ _
  have hnone : (resOf s₀).status ≠ 1 → (resOf s₀).signature = none := fun hs => by
    have := Dsa.randomSignLoop_success (inpOf (rlOf s₀) s₀.mem).pLen (inpOf (rlOf s₀) s₀.mem).qLen
      (inpOf (rlOf s₀) s₀.mem).key (inpOf (rlOf s₀) s₀.mem).digest 8 ((inpOf (rlOf s₀) s₀.mem).rand.drop 0)
    cases hc : (resOf s₀).signature with
    | none => rfl
    | some _ => exact absurd (this.mpr (by simp only [resOf, randomSignRemaining] at hc ⊢; rw [hc]; rfl)) hs
  have hfin : ∀ t, Ctx (rlOf s₀) s₀ t → t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
        (resOf s₀).signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)) →
      WP isa (finish [.add .r17 .r21 .r21]) t fun t' =>
        abiPreserved s₀ (freed frameBytes t') ∧ rsContract.post s₀ (freed frameBytes t') :=
    fun t hc h25 h31 hsig => WP.mono (finish_ok h hc h25 h31 hst hsig hnone) fun t' hf =>
      fin_post h (by rw [rsRes_eq h]; exact hf)
  unfold Impl.Dsa.PPC64LE.RandomSign.code
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.PPC64LE.RandomSign.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (prepareQ_ok h he.ctx) fun t₂ ⟨sc, h0, m2, k2⟩ => ?_)
  have c25 : t₂.gpr .r25 = BitVec.ofNat 64 0 := (k2.gpr _ (by decide)).trans he.r25
  refine WP.seq (WP.ite (decide (¬ 1 < qOf s₀)) (by rw [eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_))
  · -- q ≤ 1: no attempt.
    simp only [decide_eq_true_eq] at hq
    refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₃ => t₃.mem = t₂.mem ∧
      t₃.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₃ ⟨⟨m3, a31⟩, k3⟩ => ?_
    have hd : (randomSignDraw (inpOf (rlOf s₀) s₀.mem) 0) = ⟨none, 0, [4]⟩ := by
      rw [draw_eq hL, show (128 : Nat) = 127 + 1 from rfl, Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega)]
    obtain ⟨-, rst, ru⟩ := (RandomSignResultRel.refl (inpOf (rlOf s₀) s₀.mem) 0 8 :
      RandomSignResultRel (inpOf (rlOf s₀) s₀.mem) 0 (resOf s₀) 0 (7 + 1)).sample_none
      (show (randomSignDraw (inpOf (rlOf s₀) s₀.mem) 0).scalar = none by rw [hd])
    rw [hd] at rst ru
    refine hfin t₃ (sc.ctx.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_31 r hr))
      (by rw [m3]; exact Frame.refl _ _)) ?_ ?_ fun h1 => absurd (rst ▸ h1) (by decide)
    · rw [k3.gpr _ (by decide), c25]; congr 1; simp only [resOf] at ru ⊢; omega
    · rw [a31, rst]; rfl
  · -- q > 1: the attempts.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    refine WP.mono (attempts_ok h hq 8 0 t₂ ⟨sc, c25, by omega, (k2.gpr _ (by decide)).trans he.r26, by decide,
      by decide, fun j hj => ?_, RandomSignResultRel.refl _ _ _⟩) fun t₃ ao => hfin t₃ ao.sc.ctx ao.r25 ao.r31 ao.out
    rw [m2]
    have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    have := hE.Wq
    have := hL.ql
    have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
    exact he.nonce j (by omega)

end VG.Proof.Dsa.PPC64LE.RS
