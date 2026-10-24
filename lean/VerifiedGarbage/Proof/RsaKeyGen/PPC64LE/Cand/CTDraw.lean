module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTLoop
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTLoop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# A candidate on PPC64LE: a draw in constant time

`draw_ct`: two runs of a draw, from the same iteration of the loop, leak the
same trace. The taint analysis checks each piece from the registers the
correctness proofs pin (the working space's and the tape's addresses, the
lengths); the round is a call of verified code (`RelCT.call`), and whether
its witness passed is the same in both runs (`pass_agree`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hStat roundCall regsBack minv32)
open VG.Impl.RsaKeyGen.PPC64LE.Witness (draw load witness passed)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.MillerRabin.PPC64LE.Search (RcPost)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS wit)

/-- The loop's facts at a draw's start `sD`, `k` witnesses passed, `n + 1`
iterations left, with enough octets. -/
structure DCtx (n : Nat) (a : CD) (k : Nat) (s0 q sD : State) : Prop where
  lc : LCtx a s0 q
  ha : MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) k n
  st : St q (sB s0) (sL s0) (cw s0) (candOf s0) (rB s0) k sD
  av : 8 * cw s0 * (k + 1) + 8 * cw s0 ≤ (rB s0).length

theorem DCtx.drIn {n k : Nat} {a : CD} {s0 q sD : State} (h : DCtx n a k s0 q sD) :
    DrIn sD (sB s0) (s0.gpr .r10) (sL s0) (cw s0) (candOf s0) (8 * cw s0 * (k + 1))
      (mrS (candOf s0) (8 * cw s0) (rB s0) k).1 (mrS (candOf s0) (8 * cw s0) (rB s0) k).2
      (VG.Proof.RsaKeyGen.checksW (cw s0)) :=
  drIn_of h.lc.t3.lin h.st h.av

/-- A draw's start. -/
def LD (n : Nat) (ak : CD × Nat) (s : State) : Prop := ∃ s0 q, DCtx n ak.1 ak.2 s0 q s

/-- After `load`'s first block. -/
def LL1 (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q sD, DCtx n ak.1 ak.2 s0 q sD ∧ s.gpr .r12 = off (s0.gpr .r10) (8 * cw s0 * (ak.2 + 1)) ∧
    s.gpr .r6 = BitVec.ofNat 64 (8 * cw s0) ∧ s.gpr .r10 = off (sB s0) (slot (cw s0) 4) ∧
    s.gpr .r11 = sD.gpr .r11 ∧ s.gpr .r31 = sD.gpr .r31

/-- After `load`. -/
def LW (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q sD, DCtx n ak.1 ak.2 s0 q sD ∧
    DrL sD (sB s0) (s0.gpr .r10) (sL s0) (cw s0) (8 * cw s0 * (ak.2 + 1)) s

/-- At the round's start. -/
def LR (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q sD, DCtx n ak.1 ak.2 s0 q sD ∧
    PreRd sD (sB s0) (s0.gpr .r10) (sL s0) (cw s0) (candOf s0) (8 * cw s0 * (ak.2 + 1))
      (mrS (candOf s0) (8 * cw s0) (rB s0) ak.2).1 (mrS (candOf s0) (8 * cw s0) (rB s0) ak.2).2
      (VG.Proof.RsaKeyGen.checksW (cw s0)) s

/-- Where the round is called. -/
def LC (_n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0, KRel ak.1 s0 ∧ CallIn s (sB s0) (sL s0) (cw s0) (candOf s0)

/-- After the round's call. -/
def LC' (_n : Nat) (ak : CD × Nat) (s : State) : Prop := ∃ s0, KRel ak.1 s0 ∧ s.gpr .r31 = sB s0

/-- After the round. -/
def LP (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q sD sR, DCtx n ak.1 ak.2 s0 q sD ∧
    RcPost sR (sB s0) (sL s0) (cw s0) (candOf s0) (drX sD.mem (s0.gpr .r10) (cw s0) (candOf s0)
      (8 * cw s0 * (ak.2 + 1))).1 s

theorem DCtx.cw_eq {n k : Nat} {a : CD} {s0 q sD s0' q' sD' : State} (h : DCtx n a k s0 q sD)
    (h' : DCtx n a k s0' q' sD') : cw s0 = cw s0' := by
  simp only [cw, h.lc.krel.oL_eq h'.lc.krel]

theorem DCtx.sB_eq {n k : Nat} {a : CD} {s0 q sD s0' q' sD' : State} (h : DCtx n a k s0 q sD)
    (h' : DCtx n a k s0' q' sD') : sB s0 = sB s0' := h.lc.krel.arg h'.lc.krel (i := 1) (by decide)

theorem pins_LD {n : Nat} : Pins (LD n) [.r31, .r10, .r29] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, h⟩ ⟨s0', q', h'⟩ r hr
  have := env_agree h.lc.krel h'.lc.krel h.st.prep.env h'.st.prep.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact this _ (by simp)

theorem pins_LL1 {n : Nat} : Pins (LL1 n) [.r10, .r12, .r6, .r11, .r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, h, a12, a6, a10, a11, a31⟩ ⟨s0', q', sD', h', b12, b6, b10, b11, b31⟩ r hr
  have ea := env_agree h.lc.krel h'.lc.krel h.st.prep.env h'.st.prep.env
  have hw := h.cw_eq h'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10, h.sB_eq h', hw]
  · rw [a12, b12, h.lc.krel.reg h'.lc.krel (r := .r10) (by decide), hw]
  · rw [a6, b6, hw]
  · rw [a11, b11]; exact ea _ (by simp)
  · rw [a31, b31]; exact ea _ (by simp)

theorem pins_LW {n : Nat} : Pins (LW n) [.r10, .r11, .r29, .r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, h, ⟨⟨-, -, e, -⟩, -⟩⟩ ⟨s0', q', sD', h', ⟨⟨-, -, e', -⟩, -⟩⟩ r hr
  have := env_agree h.lc.krel h'.lc.krel e e'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact this _ (by simp)

theorem pins_LR {n : Nat} : Pins (LR n) [.r10, .r11, .r29, .r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, h, p⟩ ⟨s0', q', sD', h', p'⟩ r hr
  have := env_agree h.lc.krel h'.lc.krel p.prep.env p'.prep.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact this _ (by simp)

theorem pins_LC' {n : Nat} : Pins (LC' n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, k₁, h₁⟩ ⟨s0', k₂, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h₁, h₂]; exact k₁.arg k₂ (i := 1) (by decide)

theorem pins_LP {n : Nat} : Pins (LP n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, sR, h, p⟩ ⟨s0', q', sD', sR', h', p'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [p.prep.env.h31, p'.prep.env.h31]; exact h.sB_eq h'

/-! ## The pieces -/

theorem load_ct {n : Nat} : RelCT isa (Two (LD n)) load fun _ _ => True := by
  unfold load
  refine RelCT.seq (two_post (Ψ := LL1 n) (two_taint _ pins_LD (by taint_decide)) fun ⟨a, k⟩ s ⟨s0, q, h⟩ => ?_)
    (two_taint _ pins_LL1 (by taint_decide))
  have d := h.drIn
  exact WP.mono (load1_wp d.prep.env d.rand d.used d.kk) fun t ⟨a12, a6, a10, a11, a31⟩ =>
    ⟨s0, q, s, h, a12, a6, a10, a11, a31⟩

theorem witness_ct {n : Nat} : RelCT isa (Two (LW n)) witness fun _ _ => True :=
  two_taint _ pins_LW (by taint_decide)

theorem pins_and {α : Type} {Φ : α → State → Prop} {X : α → State → Prop} {rs : List Reg} (h : Pins Φ rs) :
    Pins (fun a s => Φ a s ∧ X a s) rs := fun a _ _ h₁ h₂ => h a _ _ h₁.1 h₂.1

/-- The round's call. -/
theorem call_ct (R : RoundImpl) {n : Nat} : RelCT isa (Two (LC n)) (.call R.name R.code) fun _ _ => True := by
  refine RelCT.callEx R.verified.1 R.verified.2.1 fun s₁ s₂ ⟨⟨a, k⟩, ⟨s0, k₁, c₁⟩, ⟨s0', k₂, c₂⟩, hsp⟩ => ?_
  have hB : sB s0 = sB s0' := k₁.arg k₂ (i := 1) (by decide)
  have hL : sL s0 = sL s0' := by simp only [sL, k₁.arg k₂ (i := 2) (by decide)]
  have hw : cw s0 = cw s0' := by simp only [cw, k₁.oL_eq k₂]
  rw [hB, hL, hw] at c₁
  refine ⟨[], [⟨sB s0', 8 * sL s0'⟩], [], [⟨sB s0', 8 * sL s0'⟩], c₁.pre, c₂.pre, c₁.pub c₂ hsp, ?_, ?_, ?_, ?_⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ (by
      simp only [List.nil_append, List.mem_singleton] at hr; rw [hr]; exact c₁.wr), hc⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton] at hr; rw [hr]; exact c₁.wr, hc⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ (by
      simp only [List.nil_append, List.mem_singleton] at hr; rw [hr]; exact c₂.wr), hc⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton] at hr; rw [hr]; exact c₂.wr, hc⟩

theorem roundCall_ct (R : RoundImpl) {n : Nat} :
    RelCT isa (Two (LR n)) (roundCall R.name R.code) fun _ _ => True := by
  unfold roundCall
  refine RelCT.assoc (RelCT.assoc (RelCT.seq (two_post (Ψ := LC n) (two_taint _ pins_LR (by taint_decide))
    fun ⟨a, k⟩ s ⟨s0, q, sD, h, p⟩ => WP.mono (preCall_wp p.prep p.wr p.sp p.stk) fun t ht =>
      ⟨s0, h.lc.krel, ht⟩) (RelCT.seq (two_post (Ψ := LC' n) (call_ct R) fun ⟨a, k⟩ s ⟨s0, k₀, c⟩ =>
      WP.mono (call_wp R c) fun t ht => ⟨s0, k₀, ht.trans c.prep.env.h31⟩)
    (two_taint _ pins_LC' (by taint_decide)))))

theorem pass_eval {n : Nat} : ∀ (ak : CD × Nat) (s₁ s₂ : State), LP n ak s₁ → LP n ak s₂ →
    isa.eval (.zero .d .r3) s₁ = isa.eval (.zero .d .r3) s₂ := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, sR, h, p⟩ ⟨s0', q', sD', sR', h', p'⟩
  rw [eval_zero_ofNat _ _ (by split <;> decide) p.r3, eval_zero_ofNat _ _ (by split <;> decide) p'.r3]
  have e₁ : drX sD.mem (s0.gpr .r10) (cw s0) (candOf s0) (8 * cw s0 * (k + 1)) =
      wit (candOf s0) (8 * cw s0) (rB s0) (8 * cw s0 * (k + 1)) := drX_eq h.lc.t3.lin h.st h.av
  have e₂ : drX sD'.mem (s0'.gpr .r10) (cw s0') (candOf s0') (8 * cw s0' * (k + 1)) =
      wit (candOf s0') (8 * cw s0') (rB s0') (8 * cw s0' * (k + 1)) := drX_eq h'.lc.t3.lin h'.st h'.av
  rw [e₁, e₂, round_eq, round_eq, pass_agree h.lc h'.lc h.ha h'.ha h.av]

theorem round_ct (R : RoundImpl) {n : Nat} :
    RelCT isa (Two (LR n)) (VG.Impl.RsaKeyGen.PPC64LE.Witness.round R.name R.code) fun _ _ => True := by
  unfold VG.Impl.RsaKeyGen.PPC64LE.Witness.round
  refine RelCT.seq (two_post (Ψ := LP n) (roundCall_ct R) fun ⟨a, k⟩ s ⟨s0, q, sD, h, p⟩ =>
    WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.roundCall_ok R p.prep p.a4 p.ac p.wr p.sp p.stk) fun t ht =>
      ⟨s0, q, sD, s, h, ht⟩) (two_ite pass_eval ?_ ?_)
  · exact two_taint _ (pins_and pins_LP) (by taint_decide)
  · exact two_taint _ (pins_and pins_LP) (by taint_decide)

theorem draw_ct (R : RoundImpl) {n : Nat} : RelCT isa (Two (LD n)) (draw R.name R.code) fun _ _ => True := by
  unfold draw
  exact RelCT.seq (two_post (Ψ := LW n) load_ct fun ⟨a, k⟩ s ⟨s0, q, h⟩ =>
    WP.mono (loadS h.drIn) fun t ht => ⟨s0, q, s, h, ht⟩)
    (RelCT.seq (two_post (Ψ := LR n) witness_ct fun ⟨a, k⟩ s ⟨s0, q, sD, h, hl⟩ =>
      WP.mono (witS h.drIn hl) fun t ht => ⟨s0, q, sD, h, ht⟩) (round_ct R))

end VG.Proof.RsaKeyGen.PPC64LE.Cand
