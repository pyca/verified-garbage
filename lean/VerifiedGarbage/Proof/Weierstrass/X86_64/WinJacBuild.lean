import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState

/-!
# The Jacobian window method on x86-64: the table

`T = P` with `Z = Z² = Z³ = 1`, stored as entry 1 (`buildInit_ok`); `T = 2 P`
by the co-Z doubling DBLU, which leaves `D = P` with `T`'s `Z`, stored as
entry 2 (`jbuildDblu_ok`); then `T = T + D` by the co-Z addition ZADDU,
which leaves `D = P` with the sum's `Z` and is never exceptional for
`2 ≤ m ≤ 15` (`zaddu_x`, from `tbl_noexc`), stored as entry `m + 1`
(`jbuildStep_ok`), to entry 16 (`jbuild_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The table's invariant at `rbx = m`: entries `1 … m`, and `T = [m]P`. -/
structure JBInv (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State) (m : Nat)
    (s : State) : Prop where
  fr : JFrame K C base size s₀ s
  tbl : JTblOk K C base P m s
  T : JPt C K.M.n base s (TS K) (mul m P)
  rbx : s.gpr .rbx = BitVec.ofNat 64 m

/-- Grid slots `i ≠ j`, as apartness for words. -/
theorem jg_sep (K : JacWinCfg) {i j : Nat} (h : i ≠ j) :
    jg K i + 8 * K.M.n ≤ jg K j ∨ jg K j + 8 * K.M.n ≤ jg K i := jg_apart K h

/-- The region of entry `m` (`1 ≤ m ≤ 16`) misses `T` and the other entries. -/
theorem entry_sep (hL : JacWinLay K size) {m i : Nat} (h1 : 1 ≤ m) (h16 : m ≤ 16)
    (hi : i < 5 * (m - 1) ∨ 5 * m ≤ i) :
    jg K i + 8 * K.M.n ≤ jg K (5 * (m - 1)) ∨ jg K (5 * (m - 1)) + 40 * K.M.n ≤ jg K i := by
  have h4 := hL.n4
  unfold jg; rw [h4]
  rcases hi with hi | hi
  · left; have := Nat.mul_le_mul_left 32 (show i + 1 ≤ 5 * (m - 1) by omega); omega
  · right; have := Nat.mul_le_mul_left 32 (show 5 * (m - 1) + 5 ≤ i by omega); omega

/-- `T = P` and entry 1. -/
theorem buildInit_ok (hL : JacWinLay K size) (hC : Law C) {P : Point C} {s : State} {base : Addr}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) {k : Nat}
    (hF : JacWinFixed K C base s P k) :
    WP isa (.block (copyPt K.M.n K.E K.P ++ copy K.M.n K.z2 K.P.z ++ copy K.M.n (K.z2 + 8 * K.M.n) K.P.z ++
      ([.mov32 .rbx (.imm 1)] : List Instr) ++ K.storeEntry)) s (JBInv K C base size P s 1) := by
  have hn := hs.nowrap
  have h4 := hL.n4
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  have hPro : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ jwRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have hPs : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ jwSlots K := fun x hx => ro_mem (hPro x hx)
  have Tne : ∀ c < 5, ∀ x ∈ [K.P.x, K.P.y, K.P.z], jg K (80 + c) ≠ x := fun c hc x hx e =>
    hL.jg_ne (List.mem_append_left _ (hPro x hx)) (i := 80 + c) (by omega) e.symm
  have Tap : ∀ c < 5, ∀ x ∈ [K.P.x, K.P.y, K.P.z],
      jg K (80 + c) + 8 * K.M.n ≤ x ∨ x + 8 * K.M.n ≤ jg K (80 + c) := fun c hc x hx =>
    (hL.jg_apart (List.mem_append_left _ (hPro x hx)) (i := 80 + c) (by omega)).symm
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- `T`'s coordinates.
  refine WP.mono (copyPt_ok hs (n := K.M.n) (o := K.E) (a := K.P) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | h | h | h
      · exact hL.le mx
      · exact hL.le my
      · exact hL.le mz
      all_goals exact hL.le (hPs _ (by simp [h])))
    (fun x hx y hy hxy => by
      simp only [hL.Tx, hL.Ty, hL.Tz] at hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases List.mem_append.mp (show y ∈ [jg K 80, jg K 81, jg K 82] ++ [K.P.x, K.P.y, K.P.z] by
        simpa using hy) with hy | hy
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          first | exact absurd rfl hxy | (refine jg_sep K ?_; decide)
      · rcases hx with rfl | rfl | rfl
        · exact Tap 0 (by decide) y hy
        · exact Tap 1 (by decide) y hy
        · exact Tap 2 (by decide) y hy)
    (fun x hx hy => by
      rw [hL.Tx, hL.Ty, hL.Tz] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact Tne 0 (by decide) _ hy rfl
      · exact Tne 1 (by decide) _ hy rfl
      · exact Tne 2 (by decide) _ hy rfl)
    (by obtain ⟨a, b, c, -⟩ := jw_T_ne hL; exact ⟨a, b, c⟩)) fun s₁ ⟨ex₁, ey₁, ez₁, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have zP : K.z2 + 8 * K.M.n ≤ K.P.z ∨ K.P.z + 8 * K.M.n ≤ K.z2 := by
    rw [hL.Tz2]; exact Tap 3 (by decide) _ (by simp)
  have zP' : K.z2 + 8 * K.M.n + 8 * K.M.n ≤ K.P.z ∨ K.P.z + 8 * K.M.n ≤ K.z2 + 8 * K.M.n := by
    rw [hL.Tz3]; exact Tap 4 (by decide) _ (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok K.M.n hs₁ (o := K.z2) (a := K.P.z) (hL.le m2) (hL.le (hPs _ (by simp)))
    (by omega)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok K.M.n hs₂ (o := K.z2 + 8 * K.M.n) (a := K.P.z) (hL.le m3) (hL.le (hPs _ (by simp)))
    (by omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mov32Rbx_ok s₃ (j := 1) (by decide)) fun s₄ ⟨b₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (jstoreEntry_ok hL hs₄ b₄ (Nat.le_refl _) (by decide)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  -- `P`'s numbers survive.
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega
  have hPz₁ : wordsVal s₁.mem base K.P.z K.M.n = wordsVal s.mem base K.P.z K.M.n := by
    refine U₁.wordsVal (fun w hw => ?_) (b64 _ (hPs _ (by simp)))
    rw [hL.Tx, hL.Ty, hL.Tz] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact (Tap 0 (by decide) _ (by simp)).symm
    · exact (Tap 1 (by decide) _ (by simp)).symm
    · exact (Tap 2 (by decide) _ (by simp)).symm
  -- `T`'s words at `s₄`.
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have hT3 : ∀ i < 3, wordsVal s₄.mem base (jg K (80 + i)) K.M.n = wordsVal s₁.mem base (jg K (80 + i)) K.M.n :=
    fun i hi => by
      rw [m₄, O₃.wordsVal (by rw [hL.Tz3]; refine jg_sep K ?_; omega) (b64 _ (jg_mem (by omega))),
        O₂.wordsVal (by rw [hL.Tz2]; refine jg_sep K ?_; omega) (b64 _ (jg_mem (by omega)))]
  have t0 : wordsVal s₄.mem base (TS K 0) K.M.n = wordsVal s.mem base K.P.x K.M.n := by
    rw [hT3 0 (by decide), ← hL.Tx, ex₁]
  have t1 : wordsVal s₄.mem base (TS K 1) K.M.n = wordsVal s.mem base K.P.y K.M.n := by
    rw [hT3 1 (by decide), ← hL.Ty, ey₁]
  have t2 : wordsVal s₄.mem base (TS K 2) K.M.n = wordsVal s.mem base K.P.z K.M.n := by
    rw [hT3 2 (by decide), ← hL.Tz, ez₁]
  have t3 : wordsVal s₄.mem base (TS K 3) K.M.n = wordsVal s.mem base K.P.z K.M.n := by
    rw [show TS K 3 = K.z2 from hL.Tz2.symm, m₄,
      O₃.wordsVal (Or.inl (Nat.le_refl _)) (b64 _ m2), e₂, hPz₁]
  have t4 : wordsVal s₄.mem base (TS K 4) K.M.n = wordsVal s.mem base K.P.z K.M.n := by
    rw [show TS K 4 = K.z2 + 8 * K.M.n from hL.Tz3.symm, m₄, e₃,
      O₂.wordsVal zP.symm (b64 _ (hPs _ (by simp))), hPz₁]
  have tv : ∀ {x y : Nat}, wordsVal s₄.mem base x K.M.n = wordsVal s.mem base y K.M.n →
      tmv C K.M.n base s₄ x = tmv C K.M.n base s y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  have J₄ : JPt C K.M.n base s₄ (TS K) (mul 1 P) := by
    rw [mul_one_pt]
    have l := hF.ro_lt
    refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
    · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · rw [t0]; exact l _ (by simp)
      · rw [t1]; exact l _ (by simp)
      · rw [t2]; exact l _ (by simp)
      · rw [t3]; exact l _ (by simp)
      · rw [t4]; exact l _ (by simp)
    · rw [tv t0, tv t1, tv t2]; exact InvJ.of_rep01 hF.pt (Or.inl hF.pz)
    · rw [tv t2, hF.pz]; exact hC.one_ne_zero
    · rw [tv t3, tv t2, hF.pz]; exact (Lean.Grind.Semiring.mul_one 1).symm
    · rw [tv t4, tv t3, tv t2, hF.pz]; exact (Lean.Grind.Semiring.mul_one 1).symm
  -- Entry 1, and `T` kept.
  have O₅' := outside_grid5 hL (b := 0) O₅
  have J₅ : JPt C K.M.n base s₅ (TS K) (mul 1 P) :=
    J₄.unchT hL O₅' hn fun w hw c hc => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
      refine jg_sep K ?_; have := List.mem_range.mp hd; omega
  have hT₅ : JTblOk K C base P 1 s₅ := fun m h1 hm => by
    obtain rfl : m = 1 := by omega
    exact J₄.congr fun c hc => e₅ c hc
  have F₁ := (JFrame.refl (K := K) (C := C) hs hM).next hL hs₁ (k₁.mono (sub_powClob (by decide))) U₁ (by
    intro w hw
    obtain ⟨wx, wy, wz, -, -⟩ := hL.T_ws
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact mem_jwW_ws wx
    · exact mem_jwW_ws wy
    · exact mem_jwW_ws wz)
  have F₂ := F₁.next hL hs₂ (k₂.mono (sub_powClob (by decide))) O₂.unch (by
    intro w hw; simp only [List.mem_singleton] at hw; subst hw; exact mem_jwW_ws hL.T_ws.2.2.2.1)
  have F₃ := F₂.next hL hs₃ (k₃.mono (sub_powClob (by decide))) O₃.unch (by
    intro w hw; simp only [List.mem_singleton] at hw; subst hw; exact mem_jwW_ws hL.T_ws.2.2.2.2)
  have F₄ := F₃.next hL hs₄ ((Keeps.regs k₄).mono (sub_powClob (by decide))) (W := []) (by rw [m₄]; exact Unch.refl _ _ _)
    (by simp)
  have F₅ := F₄.next hL hs₅ (k₅.mono (sub_powClob (by decide))) O₅' (grid5_jwW (by decide))
  exact ⟨F₅, hT₅, J₅, by rw [k₅.gpr _ (by decide), b₄]⟩

/-- A program's writes keep entries `1 … M` if the loop may write them. -/
theorem JTblOk.loopW (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat} {s s' : State}
    (hT : JTblOk K C base P M s) (hU : Unch base (jwLoopW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hM : M ≤ 16) : JTblOk K C base P M s' :=
  hT.unch hL hU hn hM fun w hw i hi => loopW_apart hL (by omega) w hw

/-- Storing entry `M + 1` keeps entries `1 … M`. -/
theorem JTblOk.store (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat} {s s' : State}
    (hT : JTblOk K C base P M s)
    (hO : Outside base (jg K (5 * M)) (40 * K.M.n) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hM : M ≤ 15) : JTblOk K C base P M s' :=
  hT.unch hL (outside_grid5 hL hO) hn (by omega) fun w hw i hi => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    refine jg_sep K ?_; omega

/-- `T`, apart from entry `m`'s region. -/
theorem JPt.store (hL : JacWinLay K size) {base : Addr} {Q : Point C} {s s' : State} {b : Nat} (hb : b + 5 ≤ 80)
    (hT : JPt C K.M.n base s (TS K) Q) (hO : Outside base (jg K b) (40 * K.M.n) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : JPt C K.M.n base s' (TS K) Q :=
  hT.unchT hL (outside_grid5 hL hO) hn fun w hw c hc => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
    refine jg_sep K ?_; have := List.mem_range.mp hd; omega

/-- The program's frame as registers. -/
theorem ProgKeep.regs {base : Addr} {W : List Nat} {s t : State} (h : ProgKeep K.M base W s t) :
    KeepRegs (powClob K.M.n) s t := (⟨h.gpr, h.rd, h.wr⟩ : KeepRegs (clob K.M.n) s t).mono clob_powClob

theorem _root_.VG.Proof.Mont.X86_64.OpKeep.regs {base : Addr} {o : Nat} {s t : State} (h : OpKeep K.M base o s t) :
    KeepRegs (powClob K.M.n) s t := (⟨h.gpr, h.rd, h.wr⟩ : KeepRegs (clob K.M.n) s t).mono clob_powClob

/-- `P` as a Jacobian triple with `Z = 1`, at any state of the frame. -/
theorem JacWinFixed.jac (hL : JacWinLay K size) {base : Addr} {s₀ s : State} {P : Point C} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) (hf : JFrame K C base size s₀ s) :
    InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) 1 P := by
  rw [hf.ro_tmv hL (by jw_mem), hf.ro_tmv hL (by jw_mem), ← hF.pz]
  exact InvJ.of_rep01 hF.pt (Or.inl hF.pz)

theorem JacWinFixed.lt (hL : JacWinLay K size) {base : Addr} {s₀ s : State} {P : Point C} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) (hf : JFrame K C base size s₀ s) :
    ∀ x ∈ [K.P.x, K.P.y, K.P.z], wordsVal s.mem base x K.M.n < C.p := by
  intro x hx
  have hro : x ∈ jwRo K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  rw [hf.ro hL hro]
  exact hF.ro_lt x hx

/-- What the table's formulas write, the loop may write. -/
theorem tblW_loopW (hL : JacWinLay K size) : ∀ x ∈ tblW K, (x, 8 * K.M.n) ∈ jwLoopW K := by
  intro x hx
  rw [tblW_eq hL] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact other_loopW (tblW_other x hx)
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact T_loopW K (List.mem_range.mp hc)

/-- The table's invariant from entry 2: `JBInv`, and `D` a triple of `P` sharing
`T`'s `Z`. -/
structure JBInvZ (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State) (m : Nat)
    (s : State) : Prop where
  inv : JBInv K C base size P s₀ m s
  lt : ∀ x ∈ [K.D.x, K.D.y], wordsVal s.mem base x K.M.n < C.p
  d : InvJ C (tmv C K.M.n base s K.D.x) (tmv C K.M.n base s K.D.y) (tmv C K.M.n base s K.E.z) P

/-- A slot the method writes, but the grid's, misses entry `m`. -/
theorem other_entry (hL : JacWinLay K size) {x : Nat} (hx : x ∈ jwOther K) {m : Nat} (hm : m ≤ 16) :
    x + 8 * K.M.n ≤ jg K (5 * (m - 1)) ∨ jg K (5 * (m - 1)) + 40 * K.M.n ≤ x := by
  have := hL.tbl x (List.mem_append_right _ hx)
  have h4 := hL.n4
  unfold jg; rw [h4] at this ⊢
  omega

/-- Storing entry `e` keeps `D` and `T`'s `Z`. -/
theorem dz_store (hL : JacWinLay K size) {base : Addr} {m m' : Mem} {e : Nat} (h1 : 1 ≤ e) (h16 : e ≤ 16)
    (hO : Outside base (jg K (5 * (e - 1))) (40 * K.M.n) m m') (hn : base.toNat + size ≤ 2 ^ 64) :
    ∀ x ∈ [K.D.x, K.D.y, K.E.z], wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact hO.wordsVal (other_entry hL (by jw_mem) h16)
      (by have := hL.le (other_mem (by jw_mem : K.D.x ∈ jwOther K)); omega)
  · exact hO.wordsVal (other_entry hL (by jw_mem) h16)
      (by have := hL.le (other_mem (by jw_mem : K.D.y ∈ jwOther K)); omega)
  · rw [hL.Tz]
    exact hO.wordsVal (entry_sep hL h1 h16 (Or.inr (by omega)))
      (by have := hL.le (jg_mem (K := K) (i := 82) (by decide)); omega)

/-- The table's slots `tblσ K i`. -/
theorem tblσ_eq (K : JacWinCfg) :
    tblσ K 0 = K.D.x ∧ tblσ K 1 = K.D.y ∧ tblσ K 2 = K.S.t0 ∧ tblσ K 3 = K.S.t1 ∧ tblσ K 4 = K.S.t2 ∧
      tblσ K 5 = K.S.t3 ∧ tblσ K 6 = K.S.t4 ∧ tblσ K 7 = K.S.t5 ∧ tblσ K 8 = K.E.x ∧ tblσ K 9 = K.E.y ∧
      tblσ K 10 = K.E.z ∧ tblσ K 11 = K.z2 ∧ tblσ K 12 = K.z2 + 8 * K.M.n ∧ tblσ K 13 = K.P.x ∧
      tblσ K 14 = K.P.y ∧ tblσ K 15 = K.P.z :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A table program's values, read back from the slots it writes. -/
theorem tbl_val {N : List FOp} {base : Addr} {V : List Nat} {E : Nat → Fe C} {t : State}
    (hI : Inv K.M base size C.p (· ∈ jwSlots K) (validAfter (N.map (FOp.rename (tblσ K))) V)
      (runOps (N.map (FOp.rename (tblσ K))) E) t)
    (hv : ∀ i, runOps (N.map (FOp.rename (tblσ K))) E (tblσ K i) = runOps N (fun y => E (tblσ K y)) i)
    {i : Nat} (h : i ∈ N.map FOp.out) :
    tmv C K.M.n base t (tblσ K i) = runOps N (fun y => E (tblσ K y)) i ∧
      wordsVal t.mem base (tblσ K i) K.M.n < C.p ∧ tblσ K i ∈ jwSlots K :=
  ⟨(hI.val _ (tbl_valid h)).trans (hv i), hI.lt _ (tbl_valid h), hI.sl _ (tbl_valid h)⟩

/-- `T = 2 P` and `D = P` sharing its `Z` by DBLU, from `T = P`, and entry 2. -/
theorem jbuildDblu_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hn17 : 17 ≤ C.n) {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixed K C base s₀ P k) {s : State}
    (hI : JBInv K C base size P s₀ 1 s) :
    WP isa (ForwardField.programB K.M K.dbluOps) s fun s₁ =>
      WP isa (.block (copy K.M.n K.D.x K.S.t3 ++ copy K.M.n K.D.y K.S.t2 ++
        ([.mov32 .rbx (.imm 2)] : List Instr) ++ K.storeEntry)) s₁ (JBInvZ K C base size P s₀ 2) := by
  have hs := hI.fr.scr
  have hn := hs.nowrap
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨-, -, -, -, σ4, σ5, -, -, σ8, σ9, σ10, σ11, σ12, σ13, σ14, σ15⟩ := tblσ_eq K
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  have hPs : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ jwSlots K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ro_mem (by jw_mem)
  have I0 : Inv K.M base size C.p (· ∈ jwSlots K) [K.P.x, K.P.y, K.P.z] (tmv C K.M.n base s) s :=
    ⟨hs, hI.fr.mod, hPs, hF.lt hL hI.fr, fun _ _ => rfl⟩
  rw [dblu_eq]
  refine WP.mono (tblProg_ok hL hp dbluN_out dbluN_reads I0 (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [σ13]; simp
    · rw [σ14]; simp
    · rw [σ15]; simp)) fun s₁ ⟨k₁, I₁, v₁⟩ => ?_
  have F₁ := hI.fr.next hL (k₁.scr hs) k₁.regs (k₁.loopW (tblW_loopW hL)) (jwLoopW_sub K)
  have val := fun {i : Nat} (h : i ∈ dbluN.map FOp.out) => tbl_val I₁ v₁ h
  -- The point.
  have h15 : tmv C K.M.n base s (tblσ K 15) = 1 := by rw [σ15, hI.fr.ro_tmv hL (by jw_mem)]; exact hF.pz
  obtain ⟨hT, h11, h12, h5, h4⟩ := dbluN_run (fun y => tmv C K.M.n base s (tblσ K y)) h15
  generalize runOps dbluN (fun y => tmv C K.M.n base s (tblσ K y)) = r at val hT h11 h12 h5 h4
  have JP := hF.jac hL hI.fr
  rw [← σ13, ← σ14] at JP
  have J2 := InvJ.dbl' hC hM3 hP JP hT
  rw [show Spec.Weierstrass.add P P = mul 2 P by
    rw [show Spec.Weierstrass.add P P = Spec.Weierstrass.add (mul 1 P) (mul 1 P) by rw [mul_one_pt],
      hC.add_mul_mul hP]] at J2
  have hz : r 10 ≠ 0 := fun h =>
    Window5.mul_ne_infinity hO hP hP0 (m := 2) (by decide) (by omega) ((J2.z_zero_iff hC).mp h)
  have JD : InvJ C (r 5) (r 4) (r 10) P := JP.rescale hC hz hC.one_ne_zero h5 h4 (by grind)
  -- The values at `s₁`.
  have v4 := val (i := 4) (by decide); have v5 := val (i := 5) (by decide)
  have v8 := val (i := 8) (by decide); have v9 := val (i := 9) (by decide)
  have v10 := val (i := 10) (by decide); have v11 := val (i := 11) (by decide)
  have v12 := val (i := 12) (by decide)
  rw [σ4] at v4; rw [σ5] at v5; rw [σ8] at v8; rw [σ9] at v9; rw [σ10] at v10; rw [σ11] at v11
  rw [σ12] at v12
  have I₁' : Inv K.M base size C.p (· ∈ jwSlots K) [K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₁) s₁ := by
    refine ⟨F₁.scr, F₁.mod, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact v4.2.1 | exact v5.2.1 | exact v8.2.1 | exact v9.2.1 | exact v10.2.1 | exact v11.2.1
      | exact v12.2.1 | exact v4.2.2 | exact v5.2.2 | exact v8.2.2 | exact v9.2.2 | exact v10.2.2
      | exact v11.2.2 | exact v12.2.2
  -- `D = (S, 8 L)`.
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyField_ok hL.lay I₁' (o := K.D.x) (a := K.S.t3) (by jw_mem) (by simp))
    fun s₂ ⟨k₂, I₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL.lay I₂ (o := K.D.y) (a := K.S.t2) (by jw_mem) (by simp))
    fun s₃ ⟨k₃, I₃⟩ => ?_
  have F₃ := (F₁.next hL (k₂.scr F₁.scr) k₂.regs (k₂.loopW (other_loopW (by jw_mem))) (jwLoopW_sub K)).next hL
    (k₃.scr (k₂.scr F₁.scr)) k₃.regs (k₃.loopW (other_loopW (by jw_mem))) (jwLoopW_sub K)
  have dyx : K.D.y ≠ K.D.x := o 4 3 (by decide) (by decide) (by decide)
  have t2x : K.S.t2 ≠ K.D.x := o 9 3 (by decide) (by decide) (by decide)
  have tD : ∀ c < 5, jg K (80 + c) ≠ K.D.x ∧ jg K (80 + c) ≠ K.D.y := fun c hc =>
    ⟨fun e => hL.jg_ne (List.mem_append_right _ (by jw_mem)) (i := 80 + c) (by omega) e.symm,
      fun e => hL.jg_ne (List.mem_append_right _ (by jw_mem)) (i := 80 + c) (by omega) e.symm⟩
  have e₃ : ∀ x ∈ [K.D.y, K.D.x, K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n],
      tmv C K.M.n base s₃ x = Function.update (Function.update (tmv C K.M.n base s₁) K.D.x
        (tmv C K.M.n base s₁ K.S.t3)) K.D.y
        (Function.update (tmv C K.M.n base s₁) K.D.x (tmv C K.M.n base s₁ K.S.t3) K.S.t2) x ∧
      wordsVal s₃.mem base x K.M.n < C.p := fun x hx => ⟨I₃.val x hx, I₃.lt x hx⟩
  have eT : ∀ c < 5, tmv C K.M.n base s₃ (TS K c) = tmv C K.M.n base s₁ (TS K c) ∧
      wordsVal s₃.mem base (TS K c) K.M.n < C.p := fun c hc => by
    have hx : TS K c ∈ [K.D.y, K.D.x, K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n] := by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · rw [tx]; simp
      · rw [ty]; simp
      · rw [tz]; simp
      · rw [t2]; simp
      · rw [t3]; simp
    refine ⟨(e₃ _ hx).1.trans ?_, (e₃ _ hx).2⟩
    rw [Function.update_of_ne (tD c hc).2, Function.update_of_ne (tD c hc).1]
  have dx₃ := e₃ K.D.x (by simp)
  have dy₃ := e₃ K.D.y (by simp)
  rw [Function.update_of_ne (Ne.symm dyx), Function.update_self] at dx₃
  rw [Function.update_self, Function.update_of_ne t2x] at dy₃
  -- `T`.
  have J₃ : JPt C K.M.n base s₃ (TS K) (mul 2 P) := by
    refine ⟨fun c hc => (eT c hc).2, ?_, ?_, ?_, ?_⟩
    · rw [(eT 0 (by decide)).1, (eT 1 (by decide)).1, (eT 2 (by decide)).1, tx, ty, tz, v8.1, v9.1, v10.1]
      exact J2
    · rw [(eT 2 (by decide)).1, tz, v10.1]; exact hz
    · rw [(eT 3 (by decide)).1, (eT 2 (by decide)).1, t2, tz, v11.1, v10.1]; exact h11
    · rw [(eT 4 (by decide)).1, (eT 3 (by decide)).1, (eT 2 (by decide)).1, t3, t2, tz, v12.1, v11.1, v10.1]
      exact h12
  have T₃ : JTblOk K C base P 1 s₃ :=
    ((hI.tbl.loopW hL (k₁.loopW (tblW_loopW hL)) hn (by decide)).loopW hL
      (k₂.loopW (other_loopW (by jw_mem))) hn (by decide)).loopW hL (k₃.loopW (other_loopW (by jw_mem))) hn
      (by decide)
  -- Entry 2.
  rw [WP.block_append_iff]
  refine WP.mono (mov32Rbx_ok s₃ (j := 2) (by decide)) fun s₄ ⟨b₄, k₄⟩ => ?_
  have hs₄ := F₃.scr.of_keeps k₄ (by decide)
  refine WP.mono (jstoreEntry_ok hL hs₄ b₄ (by decide) (by decide)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have J₄ : JPt C K.M.n base s₄ (TS K) (mul 2 P) := J₃.congr fun c _ => by rw [m₄]
  have F₅ := (F₃.next hL hs₄ ((Keeps.regs k₄).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₄]; exact Unch.refl _ _ _) (by simp)).next hL (hs₄.of_keepRegs k₅ (by decide))
    (k₅.mono (sub_powClob (by decide))) (outside_grid5 hL O₅) (grid5_jwW (by decide))
  rw [m₄] at O₅
  have K₅ := dz_store hL (e := 2) (by decide) (by decide) O₅ hn
  have tv₅ : ∀ x ∈ [K.D.x, K.D.y, K.E.z], tmv C K.M.n base s₅ x = tmv C K.M.n base s₃ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [K₅ x hx]
  refine ⟨⟨F₅, fun m h1 hm => ?_, J₃.store hL (b := 5) (by decide) O₅ hn, by rw [k₅.gpr _ (by decide), b₄]⟩,
    fun x hx => ?_, ?_⟩
  · rcases Nat.lt_or_ge m 2 with h | h
    · exact T₃.store hL (M := 1) O₅ hn (by decide) m h1 (by omega)
    · obtain rfl : m = 2 := by omega
      exact J₄.congr fun c hc => e₅ c hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [K₅ _ (by simp)]; exact dx₃.2
    · rw [K₅ _ (by simp)]; exact dy₃.2
  · rw [tv₅ _ (by simp), tv₅ _ (by simp), tv₅ _ (by simp), dx₃.1, dy₃.1, ← tz, (eT 2 (by decide)).1, tz,
      v10.1, v5.1, v4.1]
    exact JD

/-- ZADDU is not exceptional: for `2 ≤ m ≤ 15`, triples of `P` and `[m]P`
sharing `Z ≠ 0` have different `X`. -/
theorem zaddu_x (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n) {m : Nat} (h2 : 2 ≤ m) (h15 : m ≤ 15) {X1 Y1 X2 Y2 Z : Fe C}
    (h1 : InvJ C X1 Y1 Z P) (hm : InvJ C X2 Y2 Z (mul m P)) (hz : Z ≠ 0) : X1 - X2 ≠ 0 := by
  intro hx
  obtain ⟨ne1, ne2⟩ := Window5.tbl_noexc hC hO hP hP0 hn17 h2 h15
  have hx' : X1 * (Z * Z) - X2 * (Z * Z) = 0 := by
    have e : X1 * (Z * Z) - X2 * (Z * Z) = (X1 - X2) * (Z * Z) := by grind
    rw [e, hx]; grind
  by_cases hy : Y1 * Z * (Z * Z) - Y2 * Z * (Z * Z) = 0
  · exact ne1 (hm.same hC h1 hz hz hx' hy)
  · exact ne2 (hm.opposite hC (hC.onCurve_mul hP m) hP h1 hz hz hx' hy)

/-- An entry of the table: `T = T + D` by ZADDU, `D = P` with the sum's `Z`,
stored as entry `m + 1`. -/
theorem jbuildStep_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hn17 : 17 ≤ C.n) {base : Addr} {s₀ : State} {m : Nat} (h2 : 2 ≤ m) (h15 : m ≤ 15) {s : State}
    (hI : JBInvZ K C base size P s₀ m s) :
    WP isa K.buildStep s fun s' =>
      JBInvZ K C base size P s₀ (m + 1) s' ∧ s'.zf = some (decide (m + 1 = 16)) := by
  have hs := hI.inv.fr.scr
  have hn := hs.nowrap
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨σ0, σ1, -, -, -, -, -, -, σ8, σ9, σ10, σ11, σ12, -⟩ := tblσ_eq K
  rw [JacWinCfg.buildStep]
  refine WP.seq (WP.mono (addRbx_ok s (c := 1) (by decide) hI.inv.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have F₁ := hI.inv.fr.next hL hs₁ ((Keeps.regs k₁).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₁]; exact Unch.refl _ _ _) (by simp)
  have tv₁ : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m₁]
  obtain ⟨mx, my, mz, m2, -⟩ := hL.T_mem
  have I₁ : Inv K.M base size C.p (· ∈ jwSlots K) [K.D.x, K.D.y, K.E.x, K.E.y, K.E.z, K.z2]
      (tmv C K.M.n base s₁) s₁ := by
    refine ⟨hs₁, F₁.mod, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · jw_mem
    · jw_mem
    · exact mx
    · exact my
    · exact mz
    · exact m2
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁, ← tx]; exact hI.inv.T.lt 0 (by decide)
    · rw [m₁, ← ty]; exact hI.inv.T.lt 1 (by decide)
    · rw [m₁, ← tz]; exact hI.inv.T.lt 2 (by decide)
    · rw [m₁, ← t2]; exact hI.inv.T.lt 3 (by decide)
  rw [zaddu_eq]
  refine WP.seq (WP.mono (tblProg_ok hL hp zadduN_out zadduN_reads I₁ (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [σ0]; simp
    · rw [σ1]; simp
    · rw [σ8]; simp
    · rw [σ9]; simp
    · rw [σ10]; simp
    · rw [σ11]; simp)) fun s₂ ⟨k₂, I₂, v₂⟩ => ?_)
  have F₂ := F₁.next hL (k₂.scr hs₁) k₂.regs (k₂.loopW (tblW_loopW hL)) (jwLoopW_sub K)
  have val := fun {i : Nat} (h : i ∈ zadduN.map FOp.out) => tbl_val I₂ v₂ h
  obtain ⟨hZ, h11, h12⟩ := zadduN_run (fun y => tmv C K.M.n base s₁ (tblσ K y))
  generalize runOps zadduN (fun y => tmv C K.M.n base s₁ (tblσ K y)) = r at val hZ h11 h12
  simp only [σ0, σ1, σ8, σ9, σ10, σ11, tv₁] at hZ h11
  -- The point.
  have JT : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)
      (mul m P) := by
    rw [← tx, ← ty, ← tz]; exact hI.inv.T.jac
  have hz : tmv C K.M.n base s K.E.z ≠ 0 := by rw [← tz]; exact hI.inv.T.z
  have hx := zaddu_x hC hO hP hP0 hn17 h2 h15 hI.d JT hz
  obtain ⟨JS, JD⟩ := InvJ.zaddu hC hM3 hP (hC.onCurve_mul hP m) hI.d JT hz hx
  rw [← hZ] at JS JD
  rw [show Spec.Weierstrass.add (mul m P) P = mul (m + 1) P by
    rw [show Spec.Weierstrass.add (mul m P) P = Spec.Weierstrass.add (mul m P) (mul 1 P) by
      rw [mul_one_pt], hC.add_mul_mul hP]] at JS
  have h11' := h11 (by rw [← tz, ← t2]; exact hI.inv.T.z2)
  have v0 := val (i := 0) (by decide); have v1 := val (i := 1) (by decide)
  have v8 := val (i := 8) (by decide); have v9 := val (i := 9) (by decide)
  have v10 := val (i := 10) (by decide); have v11 := val (i := 11) (by decide)
  have v12 := val (i := 12) (by decide)
  rw [σ0] at v0; rw [σ1] at v1; rw [σ8] at v8; rw [σ9] at v9; rw [σ10] at v10; rw [σ11] at v11
  rw [σ12] at v12
  have hm1 : mul (m + 1) P ≠ .infinity := Window5.mul_ne_infinity hO hP hP0 (by omega) (by omega)
  have J₂ : JPt C K.M.n base s₂ (TS K) (mul (m + 1) P) := by
    refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
    · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · rw [tx]; exact v8.2.1
      · rw [ty]; exact v9.2.1
      · rw [tz]; exact v10.2.1
      · rw [t2]; exact v11.2.1
      · rw [t3]; exact v12.2.1
    · rw [tx, ty, tz, v8.1, v9.1, v10.1]; exact JS
    · rw [tz, v10.1]; exact fun h => hm1 ((JS.z_zero_iff hC).mp h)
    · rw [t2, tz, v11.1, v10.1]; exact h11'
    · rw [t3, t2, tz, v12.1, v11.1, v10.1]; exact h12
  have T₂ : JTblOk K C base P m s₂ :=
    (hI.inv.tbl.loopW hL (by rw [m₁]; exact Unch.refl _ _ _) hn (by omega)).loopW hL
      (k₂.loopW (tblW_loopW hL)) hn (by omega)
  -- The entry.
  have hb₂ : s₂.gpr .rbx = BitVec.ofNat 64 (m + 1) := by rw [k₂.gpr _ (rbx_not_clob _), b₁]
  rw [WP.block_append_iff]
  refine WP.mono (jstoreEntry_ok hL F₂.scr hb₂ (by omega) (by omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have K₃ := dz_store hL (e := m + 1) (by omega) (by omega) O₃ hn
  rw [Nat.add_sub_cancel] at e₃ O₃
  have hs₃ := F₂.scr.of_keepRegs k₃ (by decide)
  refine WP.mono (cmpRbxJ_ok s₃ (j := m + 1) (i := 16) (by decide) (by omega)
    (by rw [k₃.gpr _ (by decide), hb₂])) fun s₄ ⟨z₄, k₄⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have F₄ := (F₂.next hL hs₃ (k₃.mono (sub_powClob (by decide))) (outside_grid5 hL O₃)
    (grid5_jwW (by omega))).next hL (hs₃.of_keeps k₄ (by decide)) ((Keeps.regs k₄).mono (by simp))
    (W := []) (by rw [m₄]; exact Unch.refl _ _ _) (by simp)
  have tv₄ : ∀ x ∈ [K.D.x, K.D.y, K.E.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [m₄, K₃ x hx]
  refine ⟨⟨⟨F₄, fun j h1 hj => ?_, (J₂.store hL (b := 5 * m) (by omega) O₃ hn).congr fun c _ => by rw [m₄],
    by rw [k₄.1 _ (by simp), k₃.gpr _ (by decide), hb₂]⟩, fun x hx => ?_, ?_⟩, z₄⟩
  · rcases Nat.lt_or_ge j (m + 1) with h | h
    · exact ((T₂.store hL O₃ hn (by omega)) j h1 (by omega)).congr fun c _ => by rw [m₄]
    · obtain rfl : j = m + 1 := by omega
      exact J₂.congr fun c hc => by rw [m₄]; exact e₃ c hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [m₄, K₃ _ (by simp)]; exact v0.2.1
    · rw [m₄, K₃ _ (by simp)]; exact v1.2.1
  · rw [tv₄ _ (by simp), tv₄ _ (by simp), tv₄ _ (by simp), v0.1, v1.1, v10.1]
    exact JD

/-- The table `[1 … 16]P`. -/
theorem jbuild_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hn17 : 17 ≤ C.n) {base : Addr} {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    {k : Nat} (hF : JacWinFixed K C base s P k) :
    WP isa K.build s fun s' => JFrame K C base size s s' ∧ JTblOk K C base P 16 s' := by
  rw [JacWinCfg.build]
  refine WP.seq (WP.mono (buildInit_ok hL hC hs hM hF) fun s₁ I₁ => ?_)
  refine WP.seq (WP.mono (jbuildDblu_ok hL hp hC hM3 hO hP hP0 hn17 hF I₁) fun s₂ h₂ =>
    WP.seq (WP.mono h₂ fun s₃ I₃ => ?_))
  exact countLoop_ok (Inv := fun j t => JBInvZ K C base size P s (16 - j) t) (n := 14)
    (fun j t h1 h2 hi => WP.mono (jbuildStep_ok hL hp hC hM3 hO hP hP0 hn17 (m := 16 - j) (by omega)
      (by omega) hi) fun u ⟨I, z⟩ => ⟨by rw [show 16 - (j - 1) = 16 - j + 1 by omega]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega⟩)
    (fun t hi => ⟨hi.inv.fr, hi.inv.tbl⟩) (by decide) I₃

end VG.Proof.Weierstrass.X86_64
