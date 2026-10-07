import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState

/-!
# The Jacobian window method on x86-64: the table

`T = P` with `Z = Z² = Z³ = 1`, stored as entry 1 (`buildInit_ok`); `T = 2 T`
by the doubling given, its powers, stored as entry 2 (`buildDbl_ok`); then
`T = T + P` by the mixed addition, which is never exceptional for
`2 ≤ m ≤ 15` (`tbl_noexc`), stored as entry `m + 1` (`buildStep_ok`), to
entry 16 (`build_ok`).
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
  tbl : TblOk K C base P m s
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
      [.mov32 .rbx (.imm 1)] ++ K.storeEntry)) s (JBInv K C base size P s 1) := by
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
  refine WP.mono (storeEntry_ok hL hs₄ b₄ (Nat.le_refl _) (by decide)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
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
  have hT₅ : TblOk K C base P 1 s₅ := fun m h1 hm => by
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

/-- The slots a doubling of `T` writes are distinct. -/
theorem JacWinLay.rcbW_E (hL : JacWinLay K size) : (rcbW K.S K.E).Nodup := by
  have hn0 := hL.n0
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  have ht : ∀ i, 7 ≤ i → (hi : i < 13) → ∀ c < 5, (jwOther K)[i]'hi ≠ jg K (80 + c) := fun i h7 hi c hc =>
    hL.jg_ne (List.mem_append_right _ (List.getElem_mem hi)) (by omega)
  simp only [rcbW, hL.Tx, hL.Ty, hL.Tz, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true]
  refine ⟨⟨o 7 8 (by decide) (by decide) (by decide), o 7 9 (by decide) (by decide) (by decide),
    o 7 10 (by decide) (by decide) (by decide), o 7 11 (by decide) (by decide) (by decide),
    o 7 12 (by decide) (by decide) (by decide), ht 7 (by decide) (by decide) 0 (by decide),
    ht 7 (by decide) (by decide) 1 (by decide), ht 7 (by decide) (by decide) 2 (by decide)⟩,
    ⟨o 8 9 (by decide) (by decide) (by decide), o 8 10 (by decide) (by decide) (by decide),
    o 8 11 (by decide) (by decide) (by decide), o 8 12 (by decide) (by decide) (by decide),
    ht 8 (by decide) (by decide) 0 (by decide), ht 8 (by decide) (by decide) 1 (by decide),
    ht 8 (by decide) (by decide) 2 (by decide)⟩,
    ⟨o 9 10 (by decide) (by decide) (by decide), o 9 11 (by decide) (by decide) (by decide),
    o 9 12 (by decide) (by decide) (by decide), ht 9 (by decide) (by decide) 0 (by decide),
    ht 9 (by decide) (by decide) 1 (by decide), ht 9 (by decide) (by decide) 2 (by decide)⟩,
    ⟨o 10 11 (by decide) (by decide) (by decide), o 10 12 (by decide) (by decide) (by decide),
    ht 10 (by decide) (by decide) 0 (by decide), ht 10 (by decide) (by decide) 1 (by decide),
    ht 10 (by decide) (by decide) 2 (by decide)⟩,
    ⟨o 11 12 (by decide) (by decide) (by decide), ht 11 (by decide) (by decide) 0 (by decide),
    ht 11 (by decide) (by decide) 1 (by decide), ht 11 (by decide) (by decide) 2 (by decide)⟩,
    ⟨ht 12 (by decide) (by decide) 0 (by decide), ht 12 (by decide) (by decide) 1 (by decide),
    ht 12 (by decide) (by decide) 2 (by decide)⟩, ?_, ?_⟩
  · refine ⟨fun e => ?_, fun e => ?_⟩ <;> unfold jg at e <;>
      have := Nat.eq_of_mul_eq_mul_left (show 0 < 8 * K.M.n by omega) (Nat.add_left_cancel e) <;> omega
  · refine ⟨fun e => ?_, not_false⟩; unfold jg at e
    have := Nat.eq_of_mul_eq_mul_left (show 0 < 8 * K.M.n by omega) (Nat.add_left_cancel e); omega

theorem JacWinLay.rcbW_E_sl (hL : JacWinLay K size) : ∀ x ∈ rcbW K.S K.E, x ∈ jwSlots K := by
  obtain ⟨mx, my, mz, -, -⟩ := hL.T_mem
  intro x hx
  simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · jw_mem
  · jw_mem
  · jw_mem
  · jw_mem
  · jw_mem
  · jw_mem
  · exact mx
  · exact my
  · exact mz

theorem JacWinLay.E_ne_z (hL : JacWinLay K size) :
    ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ≠ K.z2 ∧ x ≠ K.z2 + 8 * K.M.n := by
  intro x hx
  have hn0 := hL.n0
  rw [hL.Tz3, hL.Tz2]
  simp only [hL.Tx, hL.Ty, hL.Tz, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> refine ⟨fun e => ?_, fun e => ?_⟩ <;> unfold jg at e <;>
    have := Nat.eq_of_mul_eq_mul_left (show 0 < 8 * K.M.n by omega) (Nat.add_left_cancel e) <;> omega

/-- A program's writes keep entries `1 … M` if the loop may write them. -/
theorem TblOk.loopW (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat} {s s' : State}
    (hT : TblOk K C base P M s) (hU : Unch base (jwLoopW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hM : M ≤ 16) : TblOk K C base P M s' :=
  hT.unch hL hU hn hM fun w hw i hi => loopW_apart hL (by omega) w hw

/-- Storing entry `M + 1` keeps entries `1 … M`. -/
theorem TblOk.store (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat} {s s' : State}
    (hT : TblOk K C base P M s)
    (hO : Outside base (jg K (5 * M)) (40 * K.M.n) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hM : M ≤ 15) : TblOk K C base P M s' :=
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

/-- `T = 2 T` from `T = P`, its powers, and entry 2. -/
theorem buildDbl_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n) {base : Addr} {s₀ s : State}
    (hI : JBInv K C base size P s₀ 1 s) :
    WP isa (dbl K.E) s fun s₁ => WP isa (ForwardField.programB K.M K.cacheOps) s₁ fun s₂ =>
      WP isa (.block ([.mov32 .rbx (.imm 2)] ++ K.storeEntry)) s₂ (JBInv K C base size P s₀ 2) := by
  have hs := hI.fr.scr
  have hn := hs.nowrap
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  obtain ⟨lx, ly, lz, l2, l3⟩ := hL.T_lw
  have I0 : Inv K.M base size C.p (· ∈ jwSlots K) [K.E.x, K.E.y, K.E.z] (tmv C K.M.n base s) s := by
    refine ⟨hs, hI.fr.mod, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [← tx]; exact hI.T.lt 0 (by decide)
      · rw [← ty]; exact hI.T.lt 1 (by decide)
      · rw [← tz]; exact hI.T.lt 2 (by decide)
  have J0 : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)
      (mul 1 P) := by rw [← tx, ← ty, ← tz]; exact hI.T.jac
  refine WP.mono (hD hL.lay hL.rcbW_E hL.rcbW_E_sl I0 (hC.onCurve_mul hP 1) J0)
    fun s₁ ⟨k₁, E₁, I₁, J₁⟩ => ?_
  refine WP.mono (cacheOps_ok hL hp I₁ (by simp)) fun s₂ ⟨k₂, E₂, I₂, f₂, z₂, z₃⟩ => ?_
  have nz := hL.E_ne_z
  have v2 : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base s₂ x = E₁ x := fun x hx =>
    (I₂.val x (List.mem_append_right _ hx)).trans (f₂ x (nz x hx).1 (nz x hx).2)
  have hm2 : mul 2 P ≠ .infinity := Window5.mul_ne_infinity hO hP hP0 (by decide) (by omega)
  rw [hC.add_mul_mul hP] at J₁
  have J₂ : JPt C K.M.n base s₂ (TS K) (mul 2 P) := by
    have hz : E₁ K.E.z ≠ 0 := fun h => hm2 ((J₁.z_zero_iff hC).mp h)
    have e2 : tmv C K.M.n base s₂ K.z2 = E₂ K.z2 := I₂.val _ (by simp)
    have e3 : tmv C K.M.n base s₂ (K.z2 + 8 * K.M.n) = E₂ (K.z2 + 8 * K.M.n) := I₂.val _ (by simp)
    have ez : tmv C K.M.n base s₂ K.E.z = E₁ K.E.z := v2 _ (by simp)
    refine ⟨fun c hc => I₂.lt _ ?_, ?_, ?_, ?_, ?_⟩
    · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · rw [tx]; simp
      · rw [ty]; simp
      · rw [tz]; simp
      · rw [t2]; simp
      · rw [t3]; simp
    · rw [tx, ty, tz, v2 _ (by simp), v2 _ (by simp), v2 _ (by simp)]; exact J₁
    · rw [tz, v2 _ (by simp)]; exact hz
    · rw [t2, tz, e2, ez, z₂]
    · rw [t3, t2, tz, e3, e2, ez, z₃]
  have U₁ : Unch base (jwLoopW K) s.mem s₁.mem := k₁.loopW (rcbW_loopW (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption))
  have U₂ : Unch base (jwLoopW K) s₁.mem s₂.mem := k₂.loopW (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  have F₂ := (hI.fr.next hL (k₁.scr hs) ((⟨k₁.gpr, k₁.rd, k₁.wr⟩ : KeepRegs (clob K.M.n) s s₁).mono
    clob_powClob) U₁ (jwLoopW_sub K)).next hL (k₂.scr (k₁.scr hs))
    ((⟨k₂.gpr, k₂.rd, k₂.wr⟩ : KeepRegs (clob K.M.n) s₁ s₂).mono clob_powClob) U₂ (jwLoopW_sub K)
  have T₂ : TblOk K C base P 1 s₂ := (hI.tbl.loopW hL U₁ hn (by decide)).loopW hL U₂ hn (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mov32Rbx_ok s₂ (j := 2) (by decide)) fun s₃ ⟨b₃, k₃⟩ => ?_
  have hs₃ := F₂.scr.of_keeps k₃ (by decide)
  refine WP.mono (storeEntry_ok hL hs₃ b₃ (by decide) (by decide)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  have J₃ : JPt C K.M.n base s₃ (TS K) (mul 2 P) := J₂.congr fun c _ => by rw [m₃]
  have F₄ := (F₂.next hL hs₃ ((Keeps.regs k₃).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₃]; exact Unch.refl _ _ _) (by simp)).next hL (hs₃.of_keepRegs k₄ (by decide))
    (k₄.mono (sub_powClob (by decide))) (outside_grid5 hL O₄) (grid5_jwW (by decide))
  refine ⟨F₄, fun m h1 hm => ?_, J₃.store hL (b := 5) (by decide) O₄ hn, by rw [k₄.gpr _ (by decide), b₃]⟩
  rcases Nat.lt_or_ge m 2 with h | h
  · have T₄ : TblOk K C base P 1 s₄ := T₂.store hL (M := 1) (s' := s₄) (by rw [← m₃]; exact O₄) hn (by decide)
    exact T₄ m h1 (by omega)
  · obtain rfl : m = 2 := by omega
    exact J₃.congr fun c hc => e₄ c hc

end VG.Proof.Weierstrass.X86_64
