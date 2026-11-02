module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Keep
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.DrawRange
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.StCall
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Witnesses
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.RelCTChain

/-!
# An FFDH parameter candidate on PPC64LE: a draw

`draw_ok`: the witness `a = wA mb r u` drawn at `used = u`, its range
checked, and, in range, its round (`roundCount_ok`): `hStat` and `hIdx` as
`dStat` and `dIdx` say, `used` advanced, and `MSt` kept.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Proof.Mont (val32)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.Bignum.PPC64LE.Precompute (loadN copyWords)


/-- `hStat` after a draw of `a`, from 4. -/
def dStat (N K i a : Nat) : Nat :=
  if 2 ≤ a ∧ a < N - 1 then (if Proof.MillerRabin.Round.round N a then (if i + 1 < K then 4 else 1) else 2) else 4

/-- `hIdx` after a draw of `a`. -/
def dIdx (N i a : Nat) : Nat := if 2 ≤ a ∧ a < N - 1 ∧ Proof.MillerRabin.Round.round N a = true then i + 1 else i

theorem wp_then3 {a b c d e : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c d))) s P) (k : ∀ t, P t → WP isa e t Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun t ht => ?_
  rw [WP.seq_iff] at ht ⊢
  refine WP.mono ht fun t ht => ?_
  rw [WP.seq_iff] at ht ⊢
  exact WP.mono ht fun t ht => WP.seq (WP.mono ht k)

theorem WP.chain {l : List (Prog isa)} {rest : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (Prog.chain l (.block [])) rest) s Q) : WP isa (Prog.chain l rest) s Q := by
  induction l generalizing s with
  | nil => rw [Prog.chain, WP.seq_iff, WP.block_nil_iff] at h; exact h
  | cons a l ih => exact WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ih h)

/-- The draw's pieces between its head and its branches. -/
def drawMid : List (Prog isa) :=
  [loadN, .block (([.addi .r10 .r31 hdrBytes] : List Instr) ++ base .r5 4 ++ ([.lsl .r6 .r11 2,
    .add .r5 .r5 .r6, .subi .r5 .r5 8, ldh .r4 hTop, .load .d .r6 .r5 0, .logic .and .r6 .r6 .r4,
    .store .d .r6 .r5 0] : List Instr) ++ base .r5 4 ++ ([.load .d .r24 .r5 0, .lsr .d .r24 .r24 1,
    .addi .r5 .r5 8, .lsr .d .r6 .r11 1, .subi .r6 .r6 1] : List Instr)),
   countLoop .r6 [.load .d .r3 .r5 0, .logic .or .r24 .r24 .r3, .addi .r5 .r5 8],
   .block (base .r14 3 ++ base .r15 4), copyWords,
   .block (base .r5 3 ++ ([.load .d .r3 .r5 0, .li .r4 1, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0,
     .lsl .r6 .r11 2, .add .r5 .r5 .r6, .li .r0 0, .store .d .r0 .r5 0] : List Instr) ++ base .r8 3 ++ base .r9 6),
   subMod]

/-- The draw's branches: on the witness below 2, on its range, and the round. -/
def drawBranch (name : String) (roundCode : Prog isa) : Prog isa :=
  .ite (.zero .d .r24) (.block []) (.ite (.zero .d .r20) (.block []) (round name roundCode))

theorem draw_eq (name : String) (roundCode : Prog isa) :
    draw name roundCode = .seq (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK,
      .add .r3 .r3 .r6, sth .r3 hUsed] ++ base .r10 4)) (Prog.chain drawMid (drawBranch name roundCode)) := rfl

/-- Before the draw's branches: the witness `wA mb p.r u` in array 4, `r24`
zero exactly when it is below 2, `r20` exactly when it is not below
`N − 1`. -/
structure DMid (p : PP) (mb N u i : Nat) (t : State) : Prop where
  m : MSt p mb N t
  used : word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8)
  stat : word t.mem p.B 160 = BitVec.ofNat 64 4
  idx : word t.mem p.B 176 = BitVec.ofNat 64 i
  z24 : t.gpr .r24 = 0#64 ↔ wA mb p.r u < 2
  z20 : t.gpr .r20 = 0#64 ↔ ¬ wA mb p.r u < N - 1
  a4 : arr t.mem p.B (wOf mb) 4 = wA mb p.r u

theorem drawRest_ok {p : PP} {mb N u i : Nat} {s t : State} (h : MSt p mb N s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hroom : u + (mb + 7) / 8 ≤ p.r.length)
    (hI : word s.mem p.B 176 = BitVec.ofNat 64 i) (hS : word s.mem p.B 160 = BitVec.ofNat 64 4)
    (ht : DHead p mb u s t) :
    WP isa (Prog.chain drawMid (.block [])) t (DMid p mb N u i) := by
  obtain ⟨hw2, hw128, hZ⟩ := h.w
  have hnw := h.st.scr.nowrap
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  simp only [saveBytes] at hZ'
  have hD : DPre p mb N u s := ⟨h.st, h.ph, h.prep, hu, hroom, h.mb1, h.mb2⟩
  unfold drawMid
  refine WP.seq (WP.mono (dLoadN_ok hD ht) fun t₁ ⟨⟨v₁, a10₁, f₁, u₁⟩, k₁⟩ => ?_)
  have fr : ∀ r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
      (slot (wOf mb) 6, 8 * (wOf mb + 2))], Free (wOf mb) r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨by simp, rfl⟩
    · exact Or.inr ⟨4, by decide, by decide, rfl, by dsimp only; omega_arith⟩
    · exact Or.inr ⟨3, by decide, by decide, rfl, Nat.le_refl _⟩
    · exact Or.inr ⟨6, by decide, by decide, rfl, Nat.le_refl _⟩
  have s28 := es 28
  have wr : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm p.B rs m m' →
      (∀ r ∈ rs, r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
        (slot (wOf mb) 6, 8 * (wOf mb + 2))]) →
      ∀ d, Read (wOf mb) d → word m' p.B d = word m p.B d := fun hf hs d hd =>
    hf.word_eq (fun r hr => (fr r (hs r hr)).word hd) (by have := hd.le; omega_arith)
  have st₁ : St p t₁ := h.st.step (Frm.toMut f₁ fun r hr => Free.mut h (fr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))) k₁
  have sub1 : ∀ r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb)], r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb),
      (slot (wOf mb) 3, 8 * (wOf mb + 2)), (slot (wOf mb) 6, 8 * (wOf mb + 2))] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
  have top₁ : word t₁.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1) :=
    (wr f₁ sub1 192 (by simp [Read])).trans h.ph.topW
  -- The cut.
  refine WP.seq (WP.mono (dCut_ok st₁ h.mb1 h.mb2 ((k₁.gpr .r11 (by decide)).trans h.ph.r11)
    ((k₁.gpr .r29 (by decide)).trans h.ph.r29) top₁) fun t₂ ⟨⟨wv₂, r24₂, r5₂, r6₂, r10₂, f₂⟩, k₂⟩ => ?_)
  have ha₂ : wv t₂.mem p.B (slot (wOf mb) 4) (wOf mb) = wA mb p.r u := by
    rw [wv₂, ← Pre.val32_eq_wv, v₁]; rfl
  -- The scan.
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (dScan_ok (h.st.scr.congr k12.wr) r5₂ r6₂ r24₂ hw2 (by omega_arith) (by have := es 4; omega_arith))
    fun t₃ ⟨⟨z₃, m₃⟩, k₃⟩ => ?_)
  rw [ha₂] at z₃
  have k13 := k12.trans k₃
  have fs : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm p.B rs m m' →
      (∀ r ∈ rs, r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
        (slot (wOf mb) 6, 8 * (wOf mb + 2))]) → ∀ j, (j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 ∨ j = 27) →
      wv m' p.B (slot (wOf mb) j) (wOf mb) = wv m p.B (slot (wOf mb) j) (wOf mb) := fun hf hs j hj =>
    hf.wv_eq (fun r hr => (fr r (hs r hr)).arr hj) (by
      have := es 0; have := es 1; have := es 9; have := es 10; have := es 27
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega_arith)
  have sub2 : ∀ r ∈ [(slot (wOf mb) 4, 8 * wOf mb)], r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb),
      (slot (wOf mb) 3, 8 * (wOf mb + 2)), (slot (wOf mb) 6, 8 * (wOf mb + 2))] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl <;> simp
  have hN₃ : wv t₃.mem p.B (slot (wOf mb) 0) (wOf mb) = N := by
    rw [m₃, fs f₂ sub2 0 (by simp), fs f₁ sub1 0 (by simp), ← Pre.val32_eq_wv]; exact h.prep.n
  have hx₃ : wv t₃.mem p.B (slot (wOf mb) 4) (wOf mb) = wA mb p.r u := by rw [m₃]; exact ha₂
  have r10₃ : t₃.gpr .r10 = off p.B (slot (wOf mb) 0) := (k₃.gpr .r10 (by decide)).trans r10₂
  -- The range, and the round of a witness in it.
  refine wp_then3 (dRange_ok (h.st.scr.congr k13.wr) r10₃ ((k13.gpr .r29 (by decide)).trans h.ph.r29)
    ((k13.gpr .r11 (by decide)).trans h.ph.r11) hw2 hw128 (by have := es 7; omega_arith) hN₃ h.prep.odd hx₃)
    fun t₄ ⟨⟨z₄, f₄⟩, k₄⟩ => ?_
  rw [m₃] at f₄
  have sub4 : ∀ r ∈ [(slot (wOf mb) 3, 8 * (wOf mb + 2)), (slot (wOf mb) 6, 8 * (wOf mb + 2))],
      r ∈ [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
        (slot (wOf mb) 6, 8 * (wOf mb + 2))] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
  have F : Frm p.B [(152, 8), (slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
      (slot (wOf mb) 6, 8 * (wOf mb + 2))] s.mem t₄.mem :=
    ((f₁.mono sub1).trans (f₂.mono sub2)).trans (f₄.mono sub4)
  have k14 := k13.trans k₄
  have r10₄ : t₄.gpr .r10 = s.gpr .r10 := ((k₄.gpr .r10 (by decide)).trans r10₃).trans h.ph.r10.symm
  have M₄ : MSt p mb N t₄ := h.frm F fr k14 (by decide) r10₄ (k14.gpr .r11 (by decide))
    (k14.gpr .r29 (by decide))
  -- The header words the draw and the round read and write.
  have hdr : ∀ {d}, (d = 160 ∨ d = 176) → word t₄.mem p.B d = word s.mem p.B d := fun hd =>
    F.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 4; have := es 6
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have u₄ : word t₄.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) := by
    rw [← u₁]
    have G : Frm p.B [(slot (wOf mb) 4, 8 * wOf mb), (slot (wOf mb) 3, 8 * (wOf mb + 2)),
        (slot (wOf mb) 6, 8 * (wOf mb + 2))] t₁.mem t₄.mem :=
      (f₂.mono fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]).trans
        (f₄.mono fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
    exact G.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 4; have := es 6
      rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have r24₄ : t₄.gpr .r24 = t₃.gpr .r24 := k₄.gpr .r24 (by decide)
  rw [Prog.chain, WP.block_nil_iff]
  refine ⟨M₄, u₄, (hdr (Or.inl rfl)).trans hS, (hdr (Or.inr rfl)).trans hI, ?_, ?_, ?_⟩
  · rw [r24₄]; exact z₃
  · exact z₄
  · show val32 _ _ _ _ = _
    rw [Pre.val32_eq_wv, ← ha₂]
    exact f₄.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 4; have := es 6
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by have := es 4; omega_arith)

theorem drawTail_ok (R : RoundImpl) {p : PP} {mb N u i : Nat} {t₄ : State} (h : DMid p mb N u i t₄)
    (hi : i < 2 ^ 62) :
    WP isa (drawBranch R.name R.code) t₄ fun t => MSt p mb N t ∧
      word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N (Spec.Ffdh.primeChecks mb) i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := by
  obtain ⟨M₄, u₄, hS, hI, z₃, z₄, ha₄⟩ := h
  obtain ⟨hw2, hw128, hZ⟩ := M₄.w
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hnw := M₄.st.scr.nowrap
  have hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  simp only [saveBytes] at hZ'
  have out : ¬ (2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1) → MSt p mb N t₄ ∧
      word t₄.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t₄.mem p.B 160 = BitVec.ofNat 64 (dStat N (Spec.Ffdh.primeChecks mb) i (wA mb p.r u)) ∧
      word t₄.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := fun hn =>
    ⟨M₄, u₄, by rw [hS, dStat, ite_eq_right hn], by
      rw [hI, dIdx, ite_eq_right fun ⟨a, b, _⟩ => hn ⟨a, b⟩]⟩
  unfold drawBranch
  refine WP.ite (t₄.gpr .r24 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [WP.block_nil_iff]
    have h0 : t₄.gpr .r24 = 0#64 := beq_iff_eq.mp hb
    exact out fun ⟨a, _⟩ => by have := z₃.mp h0; omega_arith
  refine WP.ite (t₄.gpr .r20 == 0) (eval_zero _ _) (fun hb' => ?_) (fun hb' => ?_)
  · rw [WP.block_nil_iff]
    exact out fun ⟨_, b⟩ => z₄.mp (beq_iff_eq.mp hb') b
  -- A witness in range: its round.
  have ha2 : 2 ≤ wA mb p.r u := by
    by_contra hc
    have : (t₄.gpr .r24 == 0) = true := beq_iff_eq.mpr (z₃.mpr (by omega_arith))
    rw [hb] at this; exact absurd this (by decide)
  have haN : wA mb p.r u < N - 1 := by
    by_contra hc
    have : (t₄.gpr .r20 == 0) = true := beq_iff_eq.mpr (z₄.mpr hc)
    rw [hb'] at this; exact absurd this (by decide)
  have hK : Spec.Ffdh.primeChecks mb < 2 ^ 62 := by unfold Spec.Ffdh.primeChecks; split <;> omega_arith
  have hsp₄ := M₄.st.sp
  refine WP.mono (roundCount_ok R M₄.prep ha₄ (show wA mb p.r u < N by omega) (by rw [hsp₄]; exact M₄.st.stk)
    (by rw [hsp₄]; exact M₄.st.stkB) hI M₄.ph.checksW hi hK)
    fun t ht => ⟨M₄.round ht, ?_⟩
  obtain ⟨v, hv, tm, -⟩ := ht
  have hn₄ : 8 * p.n = p.Z := rfl
  have u₅ : word v.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) :=
    (keeps_hdr (i := 19) hv.keeps (by decide) (by decide) (by omega_arith)).trans u₄
  simp only [word, off] at u₅ ⊢
  have ht2 : 2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1 := ⟨ha2, haN⟩
  cases hr : Proof.MillerRabin.Round.round N (wA mb p.r u) <;> simp only [hr, Bool.false_eq_true, ↓reduceIte] at tm <;>
    rw [tm] <;> refine ⟨?_, ?_, ?_⟩
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact u₅
  · rw [rw_self, dStat, ite_eq_left ht2, hr]; rfl
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), dIdx, ite_eq_right (by simp [hr])]
    exact (keeps_hdr (i := 22) hv.keeps (by decide) (by decide) (by omega_arith)).trans hI
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact u₅
  · rw [rw_self, dStat, ite_eq_left ht2, hr]; rfl
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self, dIdx, ite_eq_left ⟨ha2, haN, hr⟩]


theorem draw_ok (R : RoundImpl) {p : PP} {mb N u i : Nat} {s : State} (h : MSt p mb N s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hroom : u + (mb + 7) / 8 ≤ p.r.length)
    (hI : word s.mem p.B 176 = BitVec.ofNat 64 i) (hS : word s.mem p.B 160 = BitVec.ofNat 64 4)
    (hi : i < 2 ^ 62) :
    WP isa (draw R.name R.code) s fun t => MSt p mb N t ∧
      word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N (Spec.Ffdh.primeChecks mb) i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := by
  have hD : DPre p mb N u s := ⟨h.st, h.ph, h.prep, hu, hroom, h.mb1, h.mb2⟩
  rw [draw_eq]
  exact WP.seq (WP.mono (dHead_ok hD) fun t ht => WP.chain (WP.seq (WP.mono (drawRest_ok h hu hroom hI hS ht)
    fun t₄ h₄ => drawTail_ok R h₄ hi)))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
