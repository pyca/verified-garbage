module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Draw
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Impl.Dsa.Arm.KeyRandom

/-!
# Sampling a nonce (32-bit ARM)

`draw_ok`: one draw is a step of `Spec.Dsa.Random.sample`, either the last
(a status other than 4, with what the sampling leaves, `SampleOut`) or a
rejection, after which the sampling continues from the next draw.
`sample_ok`: a budget of 128 draws is the specification's sampling.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)
open VG.Proof.Dsa (maskValue copied copiedList copiedList_length copiedList_getD)

theorem draw_ok {s₀ t : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) (hq : 1 < rq s₀)
    (hst : slot t.mem (rBase s₀) oStatus = 4) :
    WP isa KeyRandom.draw t fun u => RReady s₀ u ∧ Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u ∧
      ((slot u.mem (rBase s₀) oStatus = 4 ∧ 2 ≤ draws ∧ Smp s₀ (used + rWidth s₀) (draws - 1) u ∧
          (∀ S' base, SampleRel s₀ S' base used draws → SampleRel s₀ S' base (used + rWidth s₀) (draws - 1)) ∧
          (spl s₀ draws used).trace = 0 :: (spl s₀ (draws - 1) (used + rWidth s₀)).trace) ∨
        (slot u.mem (rBase s₀) oStatus ≠ 4 ∧
          (∀ S' base, SampleRel s₀ S' base used draws → SampleOut s₀ base S' u) ∧
          ((spl s₀ draws used).trace.head? ≠ some 0 ∨ draws = 1))) := by
  have hF : frameBytes = 112 := rfl
  have hon : oNonce = 64 := rfl
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  have hw1 : 1 ≤ rWidth s₀ := Nat.pos_of_ne_zero ((VG.Proof.Dsa.random_valid_scan (rQBytes s₀)).mp hq).1
  have h := S.ready
  have hub := S.usedBound
  obtain ⟨d', rfl⟩ : ∃ d', draws = d' + 1 := ⟨draws - 1, by omega⟩
  have hdw : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ := rWidth_eq s₀
  have hrlen : ((rInput s₀).rand.drop used).length = (rInput s₀).rand.length - used := List.length_drop
  unfold KeyRandom.draw
  refine WP.seq (WP.mono (drawHead_ok A S) fun t₃ ⟨S₃, m₃, k₃, c₃⟩ => ?_)
  have h₃ := S₃.ready
  by_cases hshort : (rInput s₀).rand.length - used < rWidth s₀
  · -- The tape is short.
    refine WP.ite true (by rw [eval_eq, c₃, decide_eq_true hshort]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine wp_mov (op2_imm (by decide)) fun t₄ u₄ => wp_st (h₃.upd u₄) (by decide) fun t₅ m₅ h₅ => WP.block_nil ?_
    have k₅ : Rest sampleRegs t t₅ := k₃.trans ((u₄.rest (by decide)).trans (m₅.rest _))
    have hm₅ : t₅.mem = t.mem.writeW (off (rBase s₀) oStatus) (2 : BitVec 32) := by rw [m₅.mem, u₄.gpr, u₄.mem, m₃]
    have S₅ : Smp s₀ used (d' + 1) t₅ := S.congr A h₅
      (by rw [hm₅]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true]))
      (by rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide)])
    have hspl : spl s₀ (d' + 1) used = ⟨none, 0, [2]⟩ :=
      VG.Proof.Dsa.Random.sample_short _ _ _ hq (by rw [hdw, hrlen]; exact hshort)
    refine ⟨h₅, by rw [hm₅]; exact store_outs _ _ _ (by decide), k₅, .inr ⟨?_, fun S' base R => ⟨?_, ?_, ?_⟩,
      .inl (by rw [hspl]; simp)⟩⟩
    · rw [hm₅, slot_write_self]; decide
    · exact ⟨d' + 1, by rw [R.usedEq, hspl]; exact S₅⟩
    · rw [hm₅, slot_write_self, R.statusEq, hspl]; rfl
    · intro k hk; rw [R.scalarEq, hspl] at hk; simp at hk
  · -- A complete KeyRandom.draw.
    refine WP.ite false (by rw [eval_eq, c₃, decide_eq_false hshort]) (fun e => Bool.noConfusion e) (fun _ => ?_)
    have hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length := by omega
    have hdl := drawBytes_length hfull
    -- The copy.
    refine WP.seq (WP.mono (drawCopy_ok A S₃ hfull hw1) fun t₄ ⟨S₄, hc₄, ho₄, k₄⟩ => ?_)
    -- The consumption.
    refine WP.seq (WP.mono (drawUsed_ok A S₄ hfull) fun t₇ ⟨S₇, hm₇, k₇⟩ => ?_)
    have h₇ := S₇.ready
    have o₇ : Outs (rBase s₀) [(oUsed, 4)] t₄.mem t₇.mem := by rw [hm₇]; exact store_outs _ _ _ (by decide)
    have hc₇ := drawUsed_bytes A hm₇ hc₄
    -- The comparison.
    let cs := copiedList (drawBytes s₀ used) (maskValue (rLead s₀).toNat) (rWidth s₀)
    refine WP.seq (WP.mono (inRange_ok A h₇ (cs := cs) S₇.q S₇.width (copiedList_length _ _ _) hw1
      fun i hi => by rw [copiedList_getD _ _ hi]; exact hc₇ i hi) fun t₈ ⟨_, z₈, m₈, h₈, k₈⟩ => ?_)
    have S₈ : Smp s₀ (used + rWidth s₀) (d' + 1) t₈ :=
      S₇.congr A h₈ (by rw [m₈]; exact Outs.refl _ _ _) (by rw [m₈]) (by rw [m₈])
    have hacc : accepts s₀ cs = decide (0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
        Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀) := accepts_candidate hdl hw1
    have htake : ((rInput s₀).rand.drop used).take (Spec.Dsa.Random.drawBytes (rq s₀)) = drawBytes s₀ used := by
      rw [hdw]
    refine WP.mono (drawFinish_ok A S₈ (by omega) hdb z₈) fun u ⟨k₉, h₉, o₉, hT, hF'⟩ => ?_
    have outs : Outs (rBase s₀) sampleRanges t.mem u.mem := by
      have e₁ : Outs (rBase s₀) sampleRanges t.mem t₃.mem := by rw [m₃]; exact Outs.refl _ _ _
      have e₂ : Outs (rBase s₀) sampleRanges t₃.mem t₄.mem := fun x hx => ho₄ x (by
        have := hx (oNonce, 32) (by decide)
        unfold drawPlace at *; omega)
      have e₃ : Outs (rBase s₀) sampleRanges t₄.mem t₇.mem := o₇.mono (by decide)
      have e₄ : Outs (rBase s₀) sampleRanges t₇.mem t₈.mem := by rw [m₈]; exact Outs.refl _ _ _
      exact (((e₁.trans e₂).trans e₃).trans e₄).trans (o₉.mono (by decide))
    have keeps : Rest sampleRegs t u :=
      (((k₃.trans k₄).trans k₇).trans (k₈.mono (by decide))).trans (k₉.mono (by decide))
    -- The nonce's bytes survive the stores of the slots.
    have hc₉ : ∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i := fun i hi => by
      have hle : ∀ r ∈ ([(oDraws, 4), (oStatus, 4)] : List (Nat × Nat)), r.1 + r.2 ≤ oNonce := by decide
      rw [o₉ _ fun r hr => by
        have := hle r hr
        rw [ofs_off0 _ (by unfold drawPlace; omega)]
        right; unfold drawPlace at *; omega, m₈]
      exact hc₇ i hi
    have st₈ : slot t₈.mem (rBase s₀) oStatus = 4 := by
      rw [m₈, hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide),
        slot_outs (Outs.of_outside ho₄ (List.mem_singleton_self _)) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; left; unfold drawPlace oStatus; omega) (by decide),
        m₃, hst]
    cases ha : accepts s₀ cs with
    | true =>
      obtain ⟨S₉, st₉⟩ := hT ha
      have hk : 0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
          Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀ := by
        rw [hacc] at ha; exact of_decide_eq_true ha
      have hspl : spl s₀ (d' + 1) used =
          ⟨some (Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used)), rWidth s₀, [1]⟩ := by
        rw [spl, VG.Proof.Dsa.Random.sample_accept _ _ _ hq (by rw [hdw, hrlen]; omega) (by rw [htake]; exact hk),
          htake, hdw]
      refine ⟨h₉, outs, keeps, .inr ⟨by rw [st₉]; decide, fun S' base R => ⟨?_, ?_, ?_⟩,
        .inl (by rw [hspl]; simp)⟩⟩
      · exact ⟨d' + 1, by rw [R.usedEq, hspl]; exact S₉⟩
      · rw [st₉, R.statusEq, hspl]; rfl
      · intro k hk'
        rw [R.scalarEq, hspl] at hk'
        cases hk'
        exact nonce_encodes A hdl hw1 S₉.pad hc₉
    | false =>
      obtain ⟨S₉, st₉⟩ := hF' ha
      have hk : ¬ (0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
          Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀) := by
        rw [hacc] at ha; exact of_decide_eq_false ha
      have hnext : ((rInput s₀).rand.drop used).drop (Spec.Dsa.Random.drawBytes (rq s₀)) =
          (rInput s₀).rand.drop (used + rWidth s₀) := by
        rw [List.drop_drop, hdw]
      have hspl : spl s₀ (d' + 1) used =
          { spl s₀ d' (used + rWidth s₀) with
            used := rWidth s₀ + (spl s₀ d' (used + rWidth s₀)).used,
            trace := 0 :: (spl s₀ d' (used + rWidth s₀)).trace } := by
        rw [spl, VG.Proof.Dsa.Random.sample_reject _ _ _ hq (by rw [hdw, hrlen]; omega) (by rw [htake]; exact hk),
          hnext, hdw]
      have hstatus : VG.Proof.Dsa.Random.sampleStatus (spl s₀ (d' + 1) used) =
          VG.Proof.Dsa.Random.sampleStatus (spl s₀ d' (used + rWidth s₀)) := by
        rw [hspl]; exact VG.Proof.Dsa.Random.sampleStatus_reject _ _ _ _
      have rel : ∀ S' base, SampleRel s₀ S' base used (d' + 1) → SampleRel s₀ S' base (used + rWidth s₀) d' :=
        fun S' base R => ⟨by rw [R.scalarEq, hspl], by rw [R.usedEq, hspl]; dsimp only; omega,
          R.statusEq.trans hstatus⟩
      by_cases h0 : d' = 0
      · subst h0
        refine ⟨h₉, outs, keeps, .inr ⟨by rw [st₉]; simp only [Nat.add_sub_cancel, ↓reduceIte]; decide,
          fun S' base R => ?_, .inr rfl⟩⟩
        have R' := rel S' base R
        have h0s : spl s₀ 0 (used + rWidth s₀) = ⟨none, 0, [3]⟩ := rfl
        refine ⟨⟨0, by rw [R'.usedEq, h0s]; exact S₉⟩, ?_, ?_⟩
        · rw [st₉, R'.statusEq, h0s]; simp only [Nat.add_sub_cancel, ↓reduceIte]; rfl
        · intro k hk'; rw [R'.scalarEq, h0s] at hk'; simp at hk'
      · refine ⟨h₉, outs, keeps, .inl ⟨?_, by omega, by simpa using S₉, fun S' base R => by simpa using rel S' base R,
          by rw [hspl, Nat.add_sub_cancel]⟩⟩
        rw [st₉]; simp only [Nat.add_sub_cancel, h0, ↓reduceIte]; exact st₈

theorem Smp.mem {s₀ t u : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hr : RReady s₀ u) (hm : u.mem = t.mem) : Smp s₀ used draws u :=
  S.congr A hr (by rw [hm]; exact Outs.refl _ _ _) (by rw [hm]) (by rw [hm])

theorem SampleOut.mem {s₀ v u : State} (A : KeyABI s₀) {base : Nat} {S : Spec.Dsa.Random.Sample}
    (O : SampleOut s₀ base S v) (hr : RReady s₀ u) (hm : u.mem = v.mem) : SampleOut s₀ base S u :=
  ⟨let ⟨d, Sd⟩ := O.smp; ⟨d, Sd.mem A hr hm⟩, by rw [hm]; exact O.status, by rw [hm]; exact O.nonce⟩

/-- A new budget of 128 draws. -/
theorem sampleInit_ok {s₀ t : State} (A : KeyABI s₀) {used d₀ : Nat} (S : Smp s₀ used d₀ t) :
    WP isa (.block [.mov .r0 (.imm 128), st .r0 oDraws, .mov .r0 (.imm 4), st .r0 oStatus]) t
      fun u => Smp s₀ used 128 u ∧ slot u.mem (rBase s₀) oStatus = 4 ∧
        Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem u.mem ∧ Rest sampleRegs t u := by
  have h := S.ready
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => wp_st (h.upd u₁) (by decide) fun t₂ m₂ h₂ =>
    wp_mov (op2_imm (by decide)) fun t₃ u₃ => wp_st (h₂.upd u₃) (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
  have hm₄ : t₄.mem = (t.mem.writeW (off (rBase s₀) oDraws) (128 : BitVec 32)).writeW
      (off (rBase s₀) oStatus) (4 : BitVec 32) := by rw [m₄.mem, u₃.gpr, u₃.mem, m₂.mem, u₁.gpr, u₁.mem]
  have k₄ : Rest sampleRegs t t₄ :=
    (u₁.rest (by decide)).trans ((m₂.rest _).trans ((u₃.rest (by decide)).trans (m₄.rest _)))
  have o₄ : Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem t₄.mem := by
    rw [hm₄]; exact (store_outs _ _ _ (by decide)).trans (store_outs _ _ _ (by decide))
  have S₄ : Smp s₀ used 128 t₄ := S.of A h₄ (o₄.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [drawRanges])
    (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide),
      slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.usedW)
    (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide), slot_write_self]; rfl) S.usedBound
  have st₄ : slot t₄.mem (rBase s₀) oStatus = 4 := by rw [hm₄, slot_write_self]
  exact ⟨S₄, st₄, o₄, k₄⟩

theorem status_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k - 4 == 0) = decide (k = 4) := by
  by_cases h : k = 4
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl,
      show (0 : BitVec 32).toNat = 0 from rfl] at this
    omega

theorem sample_ok {s₀ t : State} (A : KeyABI s₀) {used d₀ : Nat} (S : Smp s₀ used d₀ t)
    (hq : 1 < rq s₀) :
    WP isa KeyRandom.sample t fun u => SampleOut s₀ used (spl s₀ 128 used) u ∧
      u.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used)) ∧
      RReady s₀ u ∧ Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u := by
  unfold KeyRandom.sample
  refine WP.seq (WP.mono (sampleInit_ok A S) fun t₄ ⟨S₄, st₄, o₄, k₄⟩ => ?_)
  let S₀ := spl s₀ 128 used
  refine WP.seq (WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ used', 1 ≤ n ∧ n ≤ 128 ∧
      Smp s₀ used' n u ∧ slot u.mem (rBase s₀) oStatus = 4 ∧ SampleRel s₀ S₀ used used' n ∧
      Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u) (fun n u hu => ?_) 128 t₄
    ⟨used, by decide, by decide, S₄, st₄, ⟨rfl, rfl, rfl⟩, o₄.mono (by decide), k₄⟩)
  obtain ⟨used', hn1, hn, Sm, st, R, ou, ku⟩ := hu
  refine WP.seq (WP.mono (draw_ok A Sm hn1 hn hq st) fun v ⟨hv, ov, kv, hcase⟩ => ?_)
  refine wp_ld hv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
  have hv₂ : RReady s₀ v₂ := (hv.upd uv₁).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  have kv₂ : Rest sampleRegs t v₂ := ((ku.trans kv).trans (uv₁.rest (by decide))).trans (fv₂.rest _)
  have ov₂ : Outs (rBase s₀) sampleRanges t.mem v₂.mem := by rw [mv₂]; exact ou.trans ov
  rcases hcase with ⟨stv, h2, Sv, rel, _⟩ | ⟨stv, out, _⟩
  · right
    refine ⟨by rw [eval_eq, zv₂, uv₁.gpr, stv]; rfl, n - 1, by omega, used' + rWidth s₀, by omega, by omega,
      Sv.mem A hv₂ mv₂, by rw [mv₂]; exact stv, rel S₀ used R, ov₂, kv₂⟩
  · have O := out S₀ used R
    have hz : (slot v.mem (rBase s₀) oStatus - 4 == 0) = false := by
      have := sampleStatus_le S₀
      rw [O.status, status_beq (by omega), decide_eq_false (by omega)]
    left
    refine ⟨by rw [eval_eq, zv₂, uv₁.gpr, hz], ?_⟩
    refine wp_ld hv₂ (by decide) fun u uu => WP.block_nil ?_
    have hu : RReady s₀ u := hv₂.upd uu
    have mu : u.mem = v.mem := by rw [uu.mem, mv₂]
    refine ⟨O.mem A hu mu, by rw [uu.gpr, mv₂, O.status], hu, by rw [uu.mem]; exact ov₂,
      kv₂.trans (uu.rest (by decide))⟩

end VG.Proof.Dsa.Arm.Key
