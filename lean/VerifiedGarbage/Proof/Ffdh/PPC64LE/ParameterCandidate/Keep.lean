module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.StCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Round

/-!
# An FFDH parameter candidate on PPC64LE: the tests' state

`MSt`: between the witnesses of a modulus `N` of `mb` bits, the candidate's
invariant (`St`), the modulus's header (`Ph`) and its Montgomery constants
(`Prep`). `MSt.frm`: it survives a change of `Free` ranges (the draw's
header words and working arrays); `MSt.call`: and the round.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

structure MSt (p : PP) (mb N : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb s
  prep : Prep s p.B p.n (wOf mb) N
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits

/-- The words `Ph` and `Prep` read. -/
def Read (w d : Nat) : Prop :=
  d = 0 ∨ d = 48 ∨ d = 56 ∨ d = 168 ∨ d = 192 ∨ d = 216 ∨ d = 224 ∨ d = 248 ∨ (∃ j < 8, d = 8 * (8 + j)) ∨
    d = slot w 0 ∨ d = slot w 27 + 8 * w

theorem Read.arr {w j : Nat} (hj : j < 8) : Read w (8 * (8 + j)) := by
  unfold Read; right; right; right; right; right; right; right; right; left; exact ⟨j, hj, rfl⟩

theorem Ph.keep {p : PP} {mb : Nat} {s t : State} (h : Ph p mb s)
    (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11) (r29 : t.gpr .r29 = s.gpr .r29)
    (hw : ∀ d, Read (wOf mb) d → word t.mem p.B d = word s.mem p.B d) : Ph p mb t :=
  ⟨r10.trans h.r10, r11.trans h.r11, r29.trans h.r29, (hw 248 (by simp [Read])).trans h.mbW,
    (hw 216 (by simp [Read])).trans h.kW, (hw 48 (by simp [Read])).trans h.wW,
    (hw 224 (by simp [Read])).trans h.strideW,
    fun j hj => (hw _ (Read.arr hj)).trans (h.arrW j hj),
    (hw 168 (by simp [Read])).trans h.checksW, (hw 192 (by simp [Read])).trans h.topW⟩

/-- A range the draw or the round's bookkeeping changes: the header words
`hUsed`, `hStat`, `hIdx` and `hBad`, or arrays 2 to 6. -/
def Free (w : Nat) (r : Nat × Nat) : Prop :=
  ((r.1 = 152 ∨ r.1 = 160 ∨ r.1 = 176 ∨ r.1 = 200) ∧ r.2 = 8) ∨
    (∃ j, 2 ≤ j ∧ j ≤ 6 ∧ r.1 = slot w j ∧ r.2 ≤ 8 * (w + 2))

theorem Free.word {w d : Nat} {r : Nat × Nat} (h : Free w r) (hd : Read w d) :
    d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  unfold Read at hd
  rcases h with ⟨h1, h2⟩ | ⟨j, hj1, hj2, h1, h2⟩
  · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;>
      (try rw [es]) <;> omega
  · rw [h1]
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;>
      simp only [es] <;> (try have := Nat.mul_le_mul_right (8 * (w + 2)) hj2) <;>
      (try have := Nat.mul_le_mul_right (8 * (w + 2)) hj1) <;> omega

theorem Free.arr {w j : Nat} {r : Nat × Nat} (h : Free w r) (hj : j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 ∨ j = 27) :
    slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  rcases h with ⟨h1, h2⟩ | ⟨k, hk1, hk2, h1, h2⟩
  · right; rcases hj with rfl | rfl | rfl | rfl | rfl <;> rw [es] <;> omega
  · rw [h1]
    have a := Nat.mul_le_mul_right (8 * (w + 2)) hk2
    have b := Nat.mul_le_mul_right (8 * (w + 2)) hk1
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [es] <;> omega

theorem MSt.w {p : PP} {mb N : Nat} {s : State} (h : MSt p mb N s) :
    2 ≤ wOf mb ∧ wOf mb ≤ 128 ∧ slot (wOf mb) 28 + saveBytes ≤ p.Z := by
  have hn := h.st.dims.n
  have hb := h.st.dims.b2
  have := h.mb1; have := h.mb2
  simp only [wOf, slot, hdrBytes, saveBytes, PP.Z, PP.L] at hn ⊢
  omega

theorem Free.mut {p : PP} {mb N : Nat} {s : State} (h : MSt p mb N s) {r : Nat × Nat} (hr : Free (wOf mb) r) :
    InMut p.n r := by
  obtain ⟨hw2, -, hZ⟩ := h.w
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  rcases hr with ⟨h1, h2⟩ | ⟨j, hj1, hj2, h1, h2⟩
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩ <;> dsimp only <;>
      omega
  · refine InMut.arrays (by rw [h1, es]; omega) ?_
    simp only [es, PP.Z] at hZ h1 ⊢
    have := Nat.mul_le_mul_right (8 * (wOf mb + 2)) hj2
    rw [h1]; omega

theorem Read.le {w d : Nat} (hd : Read w d) : d + 8 ≤ slot w 28 := by
  have e0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  have e27 : slot w 27 = 256 + 27 * (8 * (w + 2)) := rfl
  have e28 : slot w 28 = 256 + 28 * (8 * (w + 2)) := rfl
  unfold Read at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega

theorem MSt.frm {p : PP} {mb N : Nat} {s t : State} (h : MSt p mb N s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hr : ∀ r ∈ rs, Free (wOf mb) r) {regs : List Reg} (k : Keep regs s t)
    (h31 : Reg.r31 ∉ regs) (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11)
    (r29 : t.gpr .r29 = s.gpr .r29) (h2 : Reg.r2 ∉ regs := by decide) : MSt p mb N t := by
  obtain ⟨hw2, hw128, hZ⟩ := h.w
  have hnw := h.st.scr.nowrap
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  have hw : ∀ d, Read (wOf mb) d → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr' => (hr r hr').word hd) (by have := hd.le; omega)
  refine ⟨h.st.step (Frm.toMut hf fun r hr' => Free.mut h (hr r hr')) k h31 h2,
    h.ph.keep r10 r11 r29 hw, ?_, h.mb1, h.mb2⟩
  refine h.prep.keep ⟨h.prep.env.hs.congr k.wr, r10.trans h.prep.env.h10,
    r29.trans h.prep.env.h29, r11.trans h.prep.env.h11,
    (k.gpr _ h31).trans h.prep.env.h31, h.prep.env.hw, h.prep.env.hw', h.prep.env.hZ⟩
    (fun d hd => hw d (by
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      · unfold Read; simp
      · unfold Read; simp
      · unfold Read; simp
      · unfold Read; simp
      · exact Read.arr hj
      · unfold Read; simp
      · unfold Read; simp)) (fun j hj => ?_)
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv]
  exact hf.wv_eq (fun r hr' => (hr r hr').arr hj) (by
    have := es 0; have := es 1; have := es 9; have := es 10; have := es 27
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [saveBytes] at hZ' <;> omega)

theorem Read.kept {w d : Nat} (hd : Read w d) : ∀ i, d ≤ i → i < d + 8 → Kept w i := by
  intro i h1 h2
  have e0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have := es 2; have := es 3; have := es 5; have := es 6; have := es 8; have := es 11; have := es 27
  unfold Read at hd
  refine ⟨fun k hk => ?_, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega
  · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega

/-- `MSt` survives a witness's round. -/
theorem MSt.round {p : PP} {mb N a i K : Nat} {s t : State} (h : MSt p mb N s)
    (hR : RdPost s p.B p.n (wOf mb) N a i K t) : MSt p mb N t := by
  obtain ⟨u, hu, tm, kt⟩ := hR
  obtain ⟨hw2, -, hZ⟩ := h.w
  have stu : St p u := h.st.call hu.keeps (by have := hu.frame; rw [h.st.sp] at this; exact this) hu.rd hu.wr
    hu.sp hu.prep.env.h31 hZ (hu.cs .r2 (by decide) (by decide))
  have phu : Ph p mb u := h.ph.keep (hu.prep.env.h10.trans h.ph.r10.symm) (hu.prep.env.h11.trans h.ph.r11.symm)
    (hu.prep.env.h29.trans h.ph.r29.symm) fun d hd => keeps_word hu.keeps (by
      have := hd.le; simp only [PP.Z, saveBytes] at hZ; omega) hd.kept
  have mu : MSt p mb N u := ⟨stu, phu, hu.prep, h.mb1, h.mb2⟩
  have hf : Frm p.B [(176, 8), (160, 8)] u.mem t.mem := by
    rw [tm]
    split
    · exact frm_writeW (a := 160) (frm_writeW (a := 176) (Frm.refl _ _ _) _
        ⟨_, List.mem_cons_self, by decide, by decide⟩ (by decide)) _
        ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by decide)
    · exact frm_writeW (a := 160) (Frm.refl _ _ _) _
        ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by decide)
  exact mu.frm hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl ⟨by simp, rfl⟩) kt (by decide) (kt.gpr _ (by decide))
    (kt.gpr _ (by decide)) (kt.gpr _ (by decide))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
