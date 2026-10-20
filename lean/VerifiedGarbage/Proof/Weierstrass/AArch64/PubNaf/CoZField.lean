module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch

/-!
# The co-Z table's field programs

The co-Z programs (`CoZ.dblu`, `CoZ.zaddu`) on the window method's slots
(`Ren`): their slots are the window method's, the slots they write are
distinct and written by the loop, so a program's values are its numbered
program's (`coZ_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- A renaming of a co-Z program's slots onto the window method's: every
slot is one of its slots, a slot written (`i < 11`) is written by the loop,
and no other slot is renamed to it. -/
structure Ren (K : WinCfg) (σ : Nat → Nat) : Prop where
  slot : ∀ i, σ i ∈ winRo K ++ winOther K
  other : ∀ i < 11, σ i ∈ winOther K
  inj : ∀ o < 11, ∀ y, σ y = σ o → y = o

theorem winCode_slot (K : WinCfg) {c : Nat} (hc : c < 22) : winCode K c ∈ winRo K ++ winOther K := by
  unfold winCode
  split
  · exact List.mem_append_right _ (winCode_getD_mem (by rw [show (winOther K).length = 16 from rfl]; omega))
  · exact List.mem_append_left _ (winCode_getD_mem (by rw [show (winRo K).length = 6 from rfl]; omega))

theorem winCode_other (K : WinCfg) {c : Nat} (hc : c < 16) : winCode K c ∈ winOther K := by
  unfold winCode
  simp only [hc, ↓reduceIte]
  exact winCode_getD_mem (by rw [show (winOther K).length = 16 from rfl]; omega)

/-- The codes (`winCode`) of a renaming's first sixteen slots, the others `P.x`. -/
def CodesOk (cs : List Nat) : Prop :=
  (∀ i < 16, cs.getD i 0 < 22) ∧ (∀ i < 11, cs.getD i 0 < 16) ∧
    (∀ o < 11, ∀ y < 16, o ≠ y → cs.getD o 0 ≠ cs.getD y 0)

instance (cs : List Nat) : Decidable (CodesOk cs) := by unfold CodesOk; infer_instance

theorem Ren.of_codes {K : WinCfg} {size : Nat} (hL : WinLay K size) {σ : Nat → Nat} {cs : List Nat}
    (hc : CodesOk cs) (h : ∀ i < 16, σ i = winCode K (cs.getD i 0)) (hb : ∀ i, 16 ≤ i → σ i = K.P.x) :
    Ren K σ := by
  obtain ⟨c22, c16, cne⟩ := hc
  have hPx : K.P.x ∈ winRo K := by simp [winRo]
  have oth : ∀ i < 11, σ i ∈ winOther K := fun i hi => by
    rw [h i (by omega)]; exact winCode_other K (c16 i hi)
  refine ⟨fun i => ?_, oth, fun o ho y hy => ?_⟩
  · by_cases hi : i < 16
    · rw [h i hi]; exact winCode_slot K (c22 i hi)
    · rw [hb i (by omega)]; exact List.mem_append_left _ hPx
  · by_cases hy16 : y < 16
    · rw [h y hy16, h o (by omega)] at hy
      by_contra hne
      exact hL.code_ne (c16 o ho) (c22 y hy16) (cne o ho y hy16 (Ne.symm hne)) hy.symm
    · rw [hb y (by omega)] at hy
      exact absurd (hy ▸ oth o ho) (hL.ro _ hPx)

theorem getD16 {α : Type _} {l : List α} {d : α} (hl : l.length = 16) {i : Nat} (hi : 16 ≤ i) :
    l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem coZσ_ren {K : WinCfg} {size : Nat} (hL : WinLay K size) : Ren K (coZσ K) :=
  Ren.of_codes hL (cs := [3, 4, 7, 8, 9, 10, 11, 12, 0, 1, 2, 13, 14, 19, 20, 21]) (by decide)
    (fun i hi => by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
          i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> rfl)
    (fun _ hi => getD16 rfl hi)

theorem dbluσ_ren {K : WinCfg} {size : Nat} (hL : WinLay K size) : Ren K (dbluσ K) :=
  Ren.of_codes hL (cs := [11, 12, 7, 8, 1, 0, 9, 10, 3, 4, 2, 13, 14, 19, 20, 21]) (by decide)
    (fun i hi => by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
          i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> rfl)
    (fun _ hi => getD16 rfl hi)

theorem coZ_rename_eq (σ : Nat → Nat) (N : List FOp) :
    N.map (CoZ.rename σ) = N.map (FOp.rename σ) :=
  List.map_congr_left fun op _ => CoZTable.rename_eq _ op

/-- A co-Z program on the window method's slots: what it keeps, the invariant
on the slots it wrote, and its values, the numbered program's. -/
theorem coZ_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {σ : Nat → Nat} (hσ : Ren K σ) {N : List FOp}
    (hout : ∀ op ∈ N, op.out < 11)
    {Rd : List Nat} (hR : readsOk N Rd = true) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hv : ∀ i ∈ Rd, σ i ∈ V) :
    WP isa (fprogB K.M (N.map (CoZ.rename σ))) s fun t =>
      KeepRegs (clob K.M.n) s t ∧ Unch base (loopW K) s.mem t.mem ∧
      Inv K.M base size C.p (· ∈ winSlots K) (validAfter (N.map (FOp.rename σ)) V)
        (runOps (N.map (FOp.rename σ)) E) t ∧
      ∀ i, runOps (N.map (FOp.rename σ)) E (σ i) = runOps N (fun j => E (σ j)) i := by
  rw [coZ_rename_eq]
  have hsl : ∀ x ∈ winRo K ++ winOther K, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · exact winOther_mem hx
  have hops : ∀ op ∈ N.map (FOp.rename (σ)), ∀ x ∈ op.out :: op.ins, x ∈ winRo K ++ winOther K := by
    intro op hop x _
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at * <;>
      rcases ‹_› with rfl | rfl | rfl <;> exact hσ.slot _
  refine WP.mono (fprogB_ok hL.win.lay hL.al.al hp _ hI (fun op hop x hx => hsl x (hops op hop x hx))
    (fun op hop => hL.al.low (hops op hop))
    (readsOk_mono (readsOk_rename (σ) hR) (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hv i hi)))
    fun t ⟨hk, hI'⟩ => ⟨⟨hk.gpr, hk.rd, hk.wr, hk.sp⟩, hk.unch.mono fun w hw => ?_, hI',
      fun i => congrFun (runOps_rename σ N E fun op hop y => hσ.inj _ (hout op hop) y) i⟩
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · refine Or.inl ⟨y, ?_, rfl⟩
    obtain ⟨op, ⟨op', hop', rfl⟩, rfl⟩ := hy
    have := hσ.other _ (hout op' hop')
    cases op' <;> exact this
  · exact Or.inr rfl

end VG.Proof.Weierstrass.AArch64.PubNaf
