module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# The co-Z table's field programs

The co-Z programs (`CoZ.dblu`, `CoZ.zaddu`) on the window method's slots
(`coZσ`): their slots are the window method's, the slots they write are
distinct and written by the loop, so a program's values are its numbered
program's (`coZ_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- The slots' numbers among the window method's (`winCode`). -/
def coZCodes : List Nat := [3, 4, 7, 8, 9, 10, 11, 12, 0, 1, 2, 13, 14, 19, 20, 21]

theorem coZσ_code (K : WinCfg) {i : Nat} (hi : i < 16) : coZσ K i = winCode K (coZCodes.getD i 0) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

theorem coZσ_big (K : WinCfg) {i : Nat} (hi : 16 ≤ i) : coZσ K i = K.P.x := by
  simp only [coZσ, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl

theorem winCode_slot (K : WinCfg) {c : Nat} (hc : c < 22) : winCode K c ∈ winRo K ++ winOther K := by
  unfold winCode
  split
  · exact List.mem_append_right _ (winCode_getD_mem (by rw [show (winOther K).length = 16 from rfl]; omega))
  · exact List.mem_append_left _ (winCode_getD_mem (by rw [show (winRo K).length = 6 from rfl]; omega))

theorem coZσ_slot (K : WinCfg) (i : Nat) : coZσ K i ∈ winRo K ++ winOther K := by
  by_cases hi : i < 16
  · rw [coZσ_code K hi]
    apply winCode_slot
    have : ∀ i < 16, coZCodes.getD i 0 < 22 := by decide
    exact this i hi
  · rw [coZσ_big K (by omega)]
    exact List.mem_append_left _ (by simp [winRo])

/-- A slot written (`i < 11`) is written by the loop. -/
theorem coZσ_other (K : WinCfg) {i : Nat} (hi : i < 11) : coZσ K i ∈ winOther K := by
  rw [coZσ_code K (by omega)]
  have : ∀ i < 11, coZCodes.getD i 0 < 16 := by decide
  have hc := this i hi
  unfold winCode
  simp only [hc, ↓reduceIte]
  exact winCode_getD_mem (by rw [show (winOther K).length = 16 from rfl]; omega)

/-- No other slot is renamed to a slot written. -/
theorem coZσ_inj {K : WinCfg} {size : Nat} (hL : WinLay K size) {o : Nat} (ho : o < 11) (y : Nat)
    (h : coZσ K y = coZσ K o) : y = o := by
  by_cases hy : y < 16
  · rw [coZσ_code K hy, coZσ_code K (by omega)] at h
    by_contra hne
    have hc : ∀ o < 11, ∀ y < 16, o ≠ y → coZCodes.getD o 0 < 16 ∧ coZCodes.getD y 0 < 22 ∧
        coZCodes.getD o 0 ≠ coZCodes.getD y 0 := by decide
    obtain ⟨c1, c2, c3⟩ := hc o ho y hy (Ne.symm hne)
    exact hL.code_ne c1 c2 c3 h.symm
  · rw [coZσ_big K (by omega)] at h
    exact absurd (h ▸ coZσ_other K ho) (hL.ro _ (by simp [winRo]))

theorem coZ_rename_eq (K : WinCfg) (N : List FOp) :
    N.map (CoZ.rename (coZσ K)) = N.map (FOp.rename (coZσ K)) :=
  List.map_congr_left fun op _ => CoZTable.rename_eq _ op

/-- A co-Z program on the window method's slots: what it keeps, the invariant
on the slots it wrote, and its values, the numbered program's. -/
theorem coZ_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {N : List FOp} (hout : ∀ op ∈ N, op.out < 11)
    {Rd : List Nat} (hR : readsOk N Rd = true) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hv : ∀ i ∈ Rd, coZσ K i ∈ V) :
    WP isa (fprogB K.M (N.map (CoZ.rename (coZσ K)))) s fun t =>
      KeepRegs (clob K.M.n) s t ∧ Unch base (loopW K) s.mem t.mem ∧
      Inv K.M base size C.p (· ∈ winSlots K) (validAfter (N.map (FOp.rename (coZσ K))) V)
        (runOps (N.map (FOp.rename (coZσ K))) E) t ∧
      ∀ i, runOps (N.map (FOp.rename (coZσ K))) E (coZσ K i) = runOps N (fun j => E (coZσ K j)) i := by
  rw [coZ_rename_eq]
  have hsl : ∀ x ∈ winRo K ++ winOther K, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · exact winOther_mem hx
  have hops : ∀ op ∈ N.map (FOp.rename (coZσ K)), ∀ x ∈ op.out :: op.ins, x ∈ winRo K ++ winOther K := by
    intro op hop x _
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at * <;>
      rcases ‹_› with rfl | rfl | rfl <;> exact coZσ_slot K _
  refine WP.mono (fprogB_ok hL.win.lay hL.al.al hp _ hI (fun op hop x hx => hsl x (hops op hop x hx))
    (fun op hop => hL.al.low (hops op hop))
    (readsOk_mono (readsOk_rename (coZσ K) hR) (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hv i hi)))
    fun t ⟨hk, hI'⟩ => ⟨⟨hk.gpr, hk.rd, hk.wr, hk.sp⟩, hk.unch.mono fun w hw => ?_, hI',
      fun i => congrFun (runOps_rename (coZσ K) N E fun op hop y => coZσ_inj hL.win (hout op hop) y) i⟩
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · refine Or.inl ⟨y, ?_, rfl⟩
    obtain ⟨op, ⟨op', hop', rfl⟩, rfl⟩ := hy
    have := coZσ_other K (hout op' hop')
    cases op' <;> exact this
  · exact Or.inr rfl

end VG.Proof.Weierstrass.AArch64.PubNaf
