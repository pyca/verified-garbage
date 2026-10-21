module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCoZ
import VerifiedGarbage.Proof.Weierstrass.CoZTable

/-!
# The co-Z table's field programs, on x86-64

The co-Z programs (`CoZ.dblu`, `CoZ.zaddu`) on the window method's slots
(`CoZRen`): their slots are the window method's, the slots they write are
distinct and the loop's, so a program's values are its numbered program's
(`nafCoZ_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- A renaming of a co-Z program's slots onto the window method's: every
slot is one of its slots, a slot written (`i < 11`) is one the loop writes,
and no other slot is renamed to it. -/
structure CoZRen (K : WinCfg) (σ : Nat → Nat) : Prop where
  slot : ∀ i, σ i ∈ winRo K ++ winOther K
  other : ∀ i < 11, σ i ∈ winOther K
  inj : ∀ o < 11, ∀ y, σ y = σ o → y = o

theorem winCode_slot' (K : WinCfg) {c : Nat} (hc : c < 22) : winCode K c ∈ winRo K ++ winOther K := by
  unfold winCode
  split
  · exact List.mem_append_right _ (winCode_getD_mem (by rw [show (winOther K).length = 16 from rfl]; omega))
  · exact List.mem_append_left _ (winCode_getD_mem (by rw [show (winRo K).length = 6 from rfl]; omega))

theorem winCode_other' (K : WinCfg) {c : Nat} (hc : c < 16) : winCode K c ∈ winOther K := by
  unfold winCode
  simp only [hc, ↓reduceIte]
  exact winCode_getD_mem (by rw [show (winOther K).length = 16 from rfl]; omega)

/-- The codes (`winCode`) of a renaming's first sixteen slots, the others `P.x`. -/
def CoZCodesOk (cs : List Nat) : Prop :=
  (∀ i < 16, cs.getD i 0 < 22) ∧ (∀ i < 11, cs.getD i 0 < 16) ∧
    (∀ o < 11, ∀ y < 16, o ≠ y → cs.getD o 0 ≠ cs.getD y 0)

instance (cs : List Nat) : Decidable (CoZCodesOk cs) := by unfold CoZCodesOk; infer_instance

theorem CoZRen.of_codes {K : WinCfg} {size : Nat} (hL : WinLay K size) {σ : Nat → Nat} {cs : List Nat}
    (hc : CoZCodesOk cs) (h : ∀ i < 16, σ i = winCode K (cs.getD i 0))
    (hb : ∀ i, 16 ≤ i → σ i = K.P.x) : CoZRen K σ := by
  obtain ⟨c22, c16, cne⟩ := hc
  have hPx : K.P.x ∈ winRo K := by simp [winRo]
  have oth : ∀ i < 11, σ i ∈ winOther K := fun i hi => by
    rw [h i (by omega)]; exact winCode_other' K (c16 i hi)
  refine ⟨fun i => ?_, oth, fun o ho y hy => ?_⟩
  · by_cases hi : i < 16
    · rw [h i hi]; exact winCode_slot' K (c22 i hi)
    · rw [hb i (by omega)]; exact List.mem_append_left _ hPx
  · by_cases hy16 : y < 16
    · rw [h y hy16, h o (by omega)] at hy
      by_contra hne
      exact hL.code_ne (c16 o ho) (c22 y hy16) (cne o ho y hy16 (Ne.symm hne)) hy.symm
    · rw [hb y (by omega)] at hy
      exact absurd (hy ▸ oth o ho) (hL.ro _ hPx)

theorem coZ_getD16 {α : Type _} {l : List α} {d : α} (hl : l.length = 16) {i : Nat} (hi : 16 ≤ i) :
    l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem nafCoZσ_ren {K : WinCfg} {size : Nat} (hL : WinLay K size) : CoZRen K (Naf.coZσ K) :=
  CoZRen.of_codes hL (cs := [3, 4, 7, 8, 9, 10, 11, 12, 0, 1, 2, 13, 14, 19, 20, 21]) (by decide)
    (fun i hi => by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
          i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> rfl)
    (fun _ hi => coZ_getD16 rfl hi)

theorem nafDbluσ_ren {K : WinCfg} {size : Nat} (hL : WinLay K size) : CoZRen K (Naf.dbluσ K) :=
  CoZRen.of_codes hL (cs := [11, 12, 7, 8, 1, 0, 9, 10, 3, 4, 2, 13, 14, 19, 20, 21]) (by decide)
    (fun i hi => by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
          i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> rfl)
    (fun _ hi => coZ_getD16 rfl hi)

theorem nafCoZ_rename_eq (σ : Nat → Nat) (N : List FOp) :
    N.map (CoZ.rename σ) = N.map (FOp.rename σ) :=
  List.map_congr_left fun op _ => CoZTable.rename_eq _ op

/-- A co-Z program on the window method's slots: what it keeps, the invariant
on the slots it wrote, and its values, the numbered program's. -/
theorem nafCoZ_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {σ : Nat → Nat} (hσ : CoZRen K σ)
    {N : List FOp} (hout : ∀ op ∈ N, op.out < 11)
    {Rd : List Nat} (hR : readsOk N Rd = true) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ nafSlots K) V E s) (hv : ∀ i ∈ Rd, σ i ∈ V) :
    WP isa (fprogB K.M (N.map (CoZ.rename σ))).inline s fun t =>
      ProgKeep K.M base (winOther K) s t ∧
      Inv K.M base size C.p (· ∈ nafSlots K) (validAfter (N.map (FOp.rename σ)) V)
        (runOps (N.map (FOp.rename σ)) E) t ∧
      ∀ i, runOps (N.map (FOp.rename σ)) E (σ i) = runOps N (fun j => E (σ j)) i := by
  rw [nafCoZ_rename_eq]
  have hsl : ∀ x ∈ winRo K ++ winOther K, x ∈ nafSlots K := fun x hx =>
    List.mem_append_left _ hx
  have hops : ∀ op ∈ N.map (FOp.rename σ), ∀ x ∈ op.out :: op.ins, x ∈ winRo K ++ winOther K := by
    intro op hop x _
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at * <;>
      rcases ‹_› with rfl | rfl | rfl <;> exact hσ.slot _
  refine WP.mono (fprogB_ok hL.lay hp _ hI (fun op hop x hx => hsl x (hops op hop x hx))
    (readsOk_mono (readsOk_rename σ hR) (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hv i hi)))
    fun t ⟨hk, hI'⟩ => ⟨hk.mono fun x hx => ?_, hI',
      fun i => congrFun (runOps_rename σ N E fun op hop y => hσ.inj _ (hout op hop) y) i⟩
  rw [List.map_map] at hx
  obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hx
  have := hσ.other _ (hout op' hop')
  cases op' <;> exact this

end VG.Proof.Weierstrass.X86_64
