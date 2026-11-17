module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableState
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCoZ
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafArith
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

/-! ### `Weierstrass.X86_64.NafCoZField`, which this module and modules that import it used -/

section

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
  · exact List.mem_append_right _ (winCode_getD_mem (by rw [show (winOther K).length = 16 from rfl]; omega_arith))
  · exact List.mem_append_left _ (winCode_getD_mem (by rw [show (winRo K).length = 6 from rfl]; omega_using [hc]))

theorem winCode_other' (K : WinCfg) {c : Nat} (hc : c < 16) : winCode K c ∈ winOther K := by
  unfold winCode
  simp only [hc, ↓reduceIte]
  exact winCode_getD_mem (by rw [show (winOther K).length = 16 from rfl]; omega_using [hc])

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
    rw [h i (by omega_using [hi])]; exact winCode_other' K (c16 i hi)
  refine ⟨fun i => ?_, oth, fun o ho y hy => ?_⟩
  · by_cases hi : i < 16
    · rw [h i hi]; exact winCode_slot' K (c22 i hi)
    · rw [hb i (by omega_using [hi])]; exact List.mem_append_left _ hPx
  · by_cases hy16 : y < 16
    · rw [h y hy16, h o (by omega_using [ho])] at hy
      by_contra hne
      exact hL.code_ne (c16 o ho) (c22 y hy16) (cne o ho y hy16 (Ne.symm hne)) hy.symm
    · rw [hb y (by omega_using [hy16])] at hy
      exact absurd (hy ▸ oth o ho) (hL.ro _ hPx)

theorem coZ_getD16 {α : Type _} {l : List α} {d : α} (hl : l.length = 16) {i : Nat} (hi : 16 ≤ i) :
    l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega_using [hl, hi])]
  rfl

theorem nafCoZσ_ren {K : WinCfg} {size : Nat} (hL : WinLay K size) : CoZRen K (Naf.coZσ K) :=
  CoZRen.of_codes hL (cs := [3, 4, 7, 8, 9, 10, 11, 12, 0, 1, 2, 13, 14, 19, 20, 21]) (by decide)
    (fun i hi => by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
          i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega_using [hi]
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> rfl)
    (fun _ hi => coZ_getD16 rfl hi)

theorem nafDbluσ_ren {K : WinCfg} {size : Nat} (hL : WinLay K size) : CoZRen K (Naf.dbluσ K) :=
  CoZRen.of_codes hL (cs := [11, 12, 7, 8, 1, 0, 9, 10, 3, 4, 2, 13, 14, 19, 20, 21]) (by decide)
    (fun i hi => by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
          i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega_using [hi]
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

end

end

/-!
# The public NAF's table by co-Z arithmetic, on x86-64

`Naf.tableCoZ` leaves what `Naf.table` does (`NafTableInv … 8`): `P, 3P, …,
15P` in the table and `2P` in its ninth entry (`nafTableCoZ_ok`), for an
affine `P` (its `z` one) on a curve of prime order `n ≥ 17`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

/-- The slots holding values while the table is built: `2P`'s `x`, `y` in
`E`, the last entry in `R` (with their `z`), and the first `m` entries. -/
def coZLive (K : WinCfg) (m : Nat) : List Nat :=
  winRo K ++ [K.E.x, K.E.y] ++ jacCoords K.R ++ nafTableSlots K m

/-- The table after `m` entries: `2P` and `(2m - 1)P` at one nonzero `Z`. -/
structure CoZTableInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (s₀ s : State) (m : Nat) : Prop where
  field : Inv K.M base size C.p (·∈nafSlots K) (coZLive K m) (tmv C K.M.n base s) s
  twice : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y)
    (tmv C K.M.n base s K.R.z) (mul 2 P)
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul (2*m-1) P)
  z : tmv C K.M.n base s K.R.z ≠ 0
  table : ∀ a,1≤a → a≤m → InvJ C (tmv C K.M.n base s (K.tblPt a).x)
    (tmv C K.M.n base s (K.tblPt a).y) (tmv C K.M.n base s (K.tblPt a).z) (mul (2*a-1) P)
  counter : s.gpr .rbx=BitVec.ofNat 64 m
  keep : KeepRegs (nafTableClob K) s₀ s
  unch : Unch base (nafTableWrites K) s₀.mem s.mem

theorem coZ_rename_outs (σ : Nat → Nat) (N : List FOp) :
    (N.map (FOp.rename σ)).map FOp.out = (N.map FOp.out).map σ := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun op _ => by cases op <;> rfl

theorem coZ_validAfter_out {σ : Nat → Nat} {N : List FOp} {V : List Nat} {i : Nat}
    (h : i ∈ N.map FOp.out) : σ i ∈ validAfter (N.map (FOp.rename σ)) V :=
  (mem_validAfter _ _).mpr (Or.inr (by rw [coZ_rename_outs]; exact List.mem_map_of_mem h))

theorem coZ_tbl_slots (K : WinCfg) {a : Nat} (ha : 1≤a) (h9 : a≤9) :
    ∀ x∈jacCoords (K.tblPt a), x∈nafTblSlots K := by
  intro x hx
  simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · rw [tblPt_x]; exact nafTbl_slot K (by omega_arith)
  · rw [tblPt_y]; exact nafTbl_slot K (by omega_arith)
  · rw [tblPt_z]; exact nafTbl_slot K (by omega_arith)

theorem coZ_tbl_writes (K : WinCfg) {a : Nat} (ha : 1≤a) (h9 : a≤9) :
    ∀ x∈jacCoords (K.tblPt a), x∈nafWrites K :=
  fun x hx => List.mem_append_right _ (coZ_tbl_slots K ha h9 x hx)

theorem coZ_tbl_sep {K : WinCfg} {size : Nat} (hL : NafLay K size) {a : Nat} (ha : 1≤a) (h9 : a≤9) :
    ∀ x∈jacCoords (K.tblPt a), x∉winRo K ++ winOther K := by
  intro x hx hy
  obtain hs := hL.tbl x hy
  have := hL.n
  have := entry_end_le (24*K.M.n) (show a-1<9 by omega_arith)
  simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hx
  omega_arith

theorem coZ_tbl_other {K : WinCfg} {size : Nat} (hL : NafLay K size) {a : Nat} (ha : 1≤a) (h9 : a≤9) :
    ∀ x∈jacCoords (K.tblPt a), x∉winOther K :=
  fun x hx hy => coZ_tbl_sep hL ha h9 x hx (List.mem_append_right _ hy)

theorem coZ_tbl_ne {K : WinCfg} {size : Nat} (hL : NafLay K size) {a b : Nat} (ha : 1≤a) (hb : 1≤b)
    (hab : a≠b) :
    ∀ x∈jacCoords (K.tblPt a), x∉jacCoords (K.tblPt b) := by
  intro x hx hy
  have := hL.n
  simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases Nat.lt_or_gt_of_ne (show a-1≠b-1 by omega_arith) with h|h
  · have := entry_end_le (24*K.M.n) h; omega_arith
  · have := entry_end_le (24*K.M.n) h; omega_arith

theorem coZ_R_other (K : WinCfg) : ∀ x∈jacCoords K.R, x∈winOther K := by
  intro x hx
  simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem coZ_D_other (K : WinCfg) : ∀ x∈jacCoords (Naf.coZD K), x∈winOther K := by
  intro x hx
  simp only [jacCoords,Naf.coZD,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false] at hx ⊢
  grind

theorem coZ_P_ro (K : WinCfg) : ∀ x∈jacCoords K.P, x∈winRo K := by
  intro x hx
  simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem coZ_other_slots (K : WinCfg) : ∀ x∈winOther K, x∈nafSlots K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)

theorem coZ_ro_slots (K : WinCfg) : ∀ x∈winRo K, x∈nafSlots K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)

theorem coZLive_next (K : WinCfg) (m : Nat) :
    ∀ x∈coZLive K (m+1), x∈jacCoords (K.tblPt (m+1))++coZLive K m := by
  intro x hx
  simp only [coZLive,List.mem_append] at hx
  rcases hx with ((h|h)|h)|h
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ h))
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    obtain hi' := List.mem_range.mp hi
    by_cases h' : i<3*m
    · exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i,List.mem_range.mpr h',rfl⟩))
    · apply List.mem_append_left
      simp only [jacCoords,tblPt_x,tblPt_y,tblPt_z,Nat.add_sub_cancel,List.mem_cons,
        List.not_mem_nil,or_false]
      obtain rfl|rfl|rfl : i=3*m ∨ i=3*m+1 ∨ i=3*m+2 := by omega_arith
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

theorem coZLive_R (K : WinCfg) (m : Nat) : ∀ x∈jacCoords K.R,x∈coZLive K m := by
  intro x hx
  simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [coZLive,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind

theorem coZLive_D (K : WinCfg) (m : Nat) : ∀ x∈jacCoords (Naf.coZD K),x∈coZLive K m := by
  intro x hx
  simp only [jacCoords,Naf.coZD,List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [coZLive,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind

/-- The slots DBLU leaves holding values. -/
theorem coZLive_dblu (K : WinCfg) : ∀ x∈coZLive K 1,
    x∈validAfter (CoZ.dblu.map (FOp.rename (Naf.dbluσ K))) (jacCoords (K.tblPt 1)++winRo K) := by
  have vo (i : Nat) (h : i∈CoZ.dblu.map FOp.out) :=
    coZ_validAfter_out (σ:=Naf.dbluσ K) (V:=jacCoords (K.tblPt 1)++winRo K) h
  intro x hx
  simp only [coZLive,jacCoords,nafTableSlots,List.range_succ,List.range_zero,
    List.map_append,List.map_cons,List.map_nil,List.nil_append,Nat.mul_one,
    Nat.mul_zero,Nat.add_zero,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with ((h|h)|h)|h
  · exact (mem_validAfter _ _).mpr (Or.inl (List.mem_append_right _ h))
  · rcases h with rfl|rfl
    · exact vo 8 (by decide)
    · exact vo 9 (by decide)
  · rcases h with rfl|rfl|rfl
    · exact vo 5 (by decide)
    · exact vo 4 (by decide)
    · exact vo 10 (by decide)
  · refine (mem_validAfter _ _).mpr (Or.inl (List.mem_append_left _ ?_))
    simp only [jacCoords,WinCfg.tblPt,Nat.sub_self,Nat.mul_zero,Nat.add_zero,List.mem_cons,
      List.not_mem_nil,or_false]
    have : 8*K.M.n*2=16*K.M.n := by omega_arith
    rw [this] at h
    exact or_assoc.mp h

/-- The table's slots, from those the last copy leaves. -/
theorem coZLive_twice (K : WinCfg) :
    ∀ x∈nafTableLive K 8,x∈jacCoords (Naf.twice K)++coZLive K 8 := by
  intro x hx
  simp only [nafTableLive,List.mem_append] at hx
  rcases hx with ((h|h)|h)|h
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ h)))
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ h))
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- A slot apart from what a program writes keeps its value. -/
theorem ProgKeep.tmv_eq {K : WinCfg} {size : Nat} {C : Curve} {base : Addr} {W : List Nat}
    {s t : State} (hL : NafLay K size) (hs : Scr s base size) (hk : ProgKeep K.M base W s t)
    (hW : ∀ x∈W, x∈nafSlots K) {x : Nat} (hx : x∈nafSlots K) (hn : x∉W) :
    tmv C K.M.n base t x=tmv C K.M.n base s x := by
  unfold tmv; rw [hk.slot hL.lay hs hW hx hn]

theorem coZ_lift {K : WinCfg} {base : Addr} {W : List Nat} {u v : State}
    (k : ProgKeep K.M base W u v) : KeepRegs (nafTableClob K) u v :=
  KeepRegs.mono ⟨k.gpr,k.rd,k.wr⟩ (fun _ hx => List.mem_append_left _ hx)

section
variable {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (hO : PrimeOrder C) (hn : 17≤C.n) (ha : AM3 C)
include hL hJ hm hC hO hn ha

/-- `P` into the first entry, the counter, then DBLU: `2P` and `P` at one `Z`. -/
theorem nafTableCoZ_init_ok {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) (h1 : tmv C K.M.n base s K.P.z=1) :
    WP isa (Code.seq (.block (copyPt K.M.n (K.tblPt 1) K.P++([.mov32 .rbx (.imm 1)] : List Instr)))
      (fprogB K.M (Naf.dbluOps K))).inline s (fun t => CoZTableInv K C base size P s t 1) := by
  simp only [Code.inline]
  obtain hW := hL.toWinLay hJ
  obtain ts := nafTblPt_mem K (a:=1) (by decide) (by decide)
  obtain t1 := coZ_tbl_sep hL (a:=1) (by decide) (by decide)
  obtain pr := coZ_P_ro K
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (copyPointFields_ok hL.lay (q:=K.P) (o:=K.tblPt 1)
    (by have := hL.n; simp [jacCoords,WinCfg.tblPt] <;> omega_arith)
    (fun x hx y hy he => t1 y hy (List.mem_append_left _ (he ▸ pr x hx))) ts hI pr)
    fun a ⟨ea,ka,ia,va⟩ => ?_
  obtain pd : ∀ x∈jacCoords K.P,x∉jacCoords (K.tblPt 1) :=
    fun x hx hy => t1 x hy (List.mem_append_left _ (pr x hx))
  obtain jb : InvJ C (tmv C K.M.n base a (K.tblPt 1).x) (tmv C K.M.n base a (K.tblPt 1).y)
      (tmv C K.M.n base a (K.tblPt 1).z) P := by
    apply ia.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at va
    rw [va.1,va.2.1,va.2.2]; exact hJP
  obtain pa := ka.invJ hL.lay hI.scr ts (fun x hx => coZ_ro_slots K x (pr x hx)) pd hJP
  obtain za : tmv C K.M.n base a K.P.z=1 :=
    (ka.tmv_eq hL hI.scr ts (coZ_ro_slots K _ (pr _ (by simp [jacCoords])))
      (pd _ (by simp [jacCoords]))).trans h1
  refine WP.mono (nafTable_initCounter_ok a) fun b ⟨cb,kb⟩ => ?_
  obtain ib := (ia.of_keeps kb (by decide)).to_tmv
  have eb (x : Nat) : tmv C K.M.n base b x=tmv C K.M.n base a x := by unfold tmv; rw [kb.2.1]
  obtain hv : ∀ i∈[13,14,15],Naf.dbluσ K i∈jacCoords (K.tblPt 1)++winRo K := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> simp [Naf.dbluσ,winRo]
  refine WP.mono (nafCoZ_ok hL hm (nafDbluσ_ren hW) CoZTable.dblu_out CoZTable.dblu_reads ib hv)
    fun t ⟨kt,it,et⟩ => ?_
  obtain h15 : (fun j => tmv C K.M.n base b (Naf.dbluσ K j)) 15=1 := (eb _).trans za
  obtain hj : InvJ C ((fun j => tmv C K.M.n base b (Naf.dbluσ K j)) 13)
      ((fun j => tmv C K.M.n base b (Naf.dbluσ K j)) 14) 1 P := by
    have h := pa
    rw [za] at h
    show InvJ C (tmv C K.M.n base b (Naf.dbluσ K 13)) (tmv C K.M.n base b (Naf.dbluσ K 14)) 1 P
    rw [eb,eb]; exact h
  obtain ⟨j2,j1,jz⟩ := CoZTable.dblu_pts hC hO hn ha hP
    (e:=fun j => tmv C K.M.n base b (Naf.dbluσ K j)) h15 hj
  rw [← et 8,← et 9,← et 10] at j2
  rw [← et 5,← et 4,← et 10] at j1
  rw [← et 10] at jz
  have vo (i : Nat) (h : i∈CoZ.dblu.map FOp.out) :=
    coZ_validAfter_out (σ:=Naf.dbluσ K) (V:=jacCoords (K.tblPt 1)++winRo K) h
  obtain rt := it.point_tmv (p:=K.R) (fun x hx => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact vo 5 (by decide)
    · exact vo 4 (by decide)
    · exact vo 10 (by decide)) j1
  obtain dt := it.point_tmv (p:=Naf.coZD K) (fun x hx => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact vo 8 (by decide)
    · exact vo 9 (by decide)
    · exact vo 10 (by decide)) j2
  obtain zt : tmv C K.M.n base t K.R.z≠0 := fun h0 =>
    jz ((it.val _ (vo 10 (by decide))).symm.trans h0)
  have ka' := kt
  obtain jbb : InvJ C (tmv C K.M.n base b (K.tblPt 1).x) (tmv C K.M.n base b (K.tblPt 1).y)
      (tmv C K.M.n base b (K.tblPt 1).z) P := by simp only [eb]; exact jb
  obtain tt := ka'.invJ hL.lay ib.scr (coZ_other_slots K) ts (coZ_tbl_other hL (by decide) (by decide))
    jbb
  refine ⟨?_,dt,?_,zt,?_,?_,?_,?_⟩
  · exact it.to_tmv.sub (coZLive_dblu K)
  · rw [show 2*1-1=1 from rfl,mul_one_pt]; exact rt
  · intro a ha ha1
    obtain rfl : a=1 := by omega_arith
    rw [show 2*1-1=1 from rfl,mul_one_pt]; exact tt
  · rw [kt.gpr _ (rbx_not_clob _)]; exact cb
  · exact (coZ_lift ka).trans ((VG.Proof.Mont.X86_64.Keeps.regs kb).mono
      (fun _ hx => List.mem_append_right _ hx) |>.trans (coZ_lift kt))
  · have ua := nafTable_progUnch ka (coZ_tbl_writes K (a:=1) (by decide) (by decide))
    obtain ut := nafTable_progUnch ka' (fun x hx => List.mem_append_left _ hx)
    rw [kb.2.1] at ut
    exact (ua.trans ut).mono (by intro w hw; simpa only [List.mem_append,or_self] using hw)

/-- ZADDU: `R = R + 2P`, `E = 2P` at the new `Z`, stored in the next entry. -/
theorem nafTableCoZ_step_ok (ht : K.tbl<2^31) {P : Point C} (hP : onCurve C P=true)
    (hP0 : P≠.infinity) {m : Nat} (hm1 : 1≤m) (hm7 : m≤7) {s₀ s : State}
    (hI : CoZTableInv K C base size P s₀ s m) :
    WP isa (Naf.tableCoZStep K).inline s fun t =>
      CoZTableInv K C base size P s₀ t (m+1) ∧ t.cf=some (decide (m+1<8)) := by
  obtain hW := hL.toWinLay hJ
  have hf := hI.field
  unfold Naf.tableCoZStep
  simp only [Code.inline]
  apply WP.seq
  obtain hv : ∀ i∈[0,1,8,9,10],Naf.coZσ K i∈coZLive K m := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp [Naf.coZσ,coZLive,jacCoords]
  refine WP.mono (nafCoZ_ok hL hm (nafCoZσ_ren hW) CoZTable.zaddu_out CoZTable.zaddu_reads hf hv)
    fun u ⟨ku,iu,eu⟩ => ?_
  obtain ⟨jr,jd,jz⟩ := CoZTable.zaddu_pts hC hO hn ha hP hP0 (k:=m-1) (by omega_arith)
    (e:=fun j => tmv C K.M.n base s (Naf.coZσ K j)) hI.twice
    (by rw [show 2*(m-1)+1=2*m-1 by omega_arith]; exact hI.point) hI.z
  rw [← eu 8,← eu 9,← eu 10,show 2*(m-1+1)+1=2*(m+1)-1 by omega_arith] at jr
  rw [← eu 0,← eu 1,← eu 10] at jd
  rw [← eu 10] at jz
  obtain va : ∀ x∈coZLive K m,x∈validAfter (CoZ.zaddu.map (FOp.rename (Naf.coZσ K))) (coZLive K m) :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  obtain rL := coZLive_R K m
  obtain dL := coZLive_D K m
  obtain ru := iu.point_tmv (p:=K.R) (fun x hx => va x (rL x hx)) jr
  obtain du := iu.point_tmv (p:=Naf.coZD K) (fun x hx => va x (dL x hx)) jd
  obtain zu : tmv C K.M.n base u K.R.z≠0 := fun h0 =>
    jz ((iu.val K.R.z (va _ (rL _ (by simp [jacCoords])))).symm.trans h0)
  obtain iu' := iu.to_tmv.sub va
  obtain ku' := ku.mono (W':=winOther K) (fun _ hx => hx)
  have tu (a : Nat) (ha1 : 1≤a) (ham : a≤m) := ku.invJ hL.lay hf.scr (coZ_other_slots K)
    (nafTblPt_mem K ha1 (by omega_arith)) (coZ_tbl_other hL ha1 (by omega_arith)) (hI.table a ha1 ham)
  obtain cu : u.gpr .rbx=BitVec.ofNat 64 m := (ku.gpr _ (rbx_not_clob _)).trans hI.counter
  obtain sep : K.R.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.R.x := by
    obtain hx := hL.tbl K.R.x (List.mem_append_right _ (coZ_R_other K _ (by simp [jacCoords])))
    obtain hz := hL.tbl K.R.z (List.mem_append_right _ (coZ_R_other K _ (by simp [jacCoords])))
    rw [hL.rxz] at hz
    omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (nafTablePoint_ok hL.lay hL.n hL.rxy hL.rxz iu' (by omega_arith : m<8) cu ht
    (by have := hL.table_le; omega_arith) (nafTblPt_mem K (a:=m+1) (by omega_arith) (by omega_arith))
    rL sep ru) fun v ⟨kv,iv,jv⟩ => ?_
  obtain tS := nafTblPt_mem K (a:=m+1) (by omega_arith) (by omega_arith)
  obtain tn := coZ_tbl_other hL (a:=m+1) (by omega_arith) (by omega_arith)
  have ss := iu'.scr
  obtain rv := kv.invJ hL.lay ss tS (fun x hx => coZ_other_slots K x (coZ_R_other K x hx))
    (fun x hx hy => tn x hy (coZ_R_other K x hx)) ru
  obtain dv := kv.invJ hL.lay ss tS (fun x hx => coZ_other_slots K x (coZ_D_other K x hx))
    (fun x hx hy => tn x hy (coZ_D_other K x hx)) du
  obtain zv : tmv C K.M.n base v K.R.z≠0 := by
    rw [kv.tmv_eq hL ss tS (coZ_other_slots K _ (coZ_R_other K _ (by simp [jacCoords])))
      (fun hy => tn _ hy (coZ_R_other K _ (by simp [jacCoords])))]
    exact zu
  have tv (a : Nat) (ha1 : 1≤a) (ham : a≤m) := kv.invJ hL.lay ss tS
    (nafTblPt_mem K ha1 (by omega_arith)) (coZ_tbl_ne hL ha1 (by omega_arith) (show a≠m+1 by omega_arith)) (tu a ha1 ham)
  obtain cv : v.gpr .rbx=BitVec.ofNat 64 m := (kv.gpr _ (rbx_not_clob _)).trans cu
  refine WP.mono (nafTable_advance_ok (by omega_arith) cv) fun t ⟨hc,cf,kc⟩ => ?_
  have et (x : Nat) : tmv C K.M.n base t x=tmv C K.M.n base v x := by unfold tmv; rw [kc.2.1]
  refine ⟨⟨(iv.of_keeps kc (by decide)).to_tmv.sub (coZLive_next K m),?_,?_,?_,?_,hc,?_,?_⟩,cf⟩
  · simpa only [et,Naf.coZD] using dv
  · simpa only [et] using rv
  · rw [et]; exact zv
  · intro a ha1 ham
    by_cases he : a=m+1
    · subst a; simpa only [et] using jv
    · simpa only [et] using tv a ha1 (by omega_arith)
  · exact hI.keep.trans ((coZ_lift ku).trans ((coZ_lift kv).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kc).mono (fun _ hx => List.mem_append_right _ hx))))
  · have uu := nafTable_progUnch ku' (fun x hx => List.mem_append_left _ hx)
    obtain uv := nafTable_progUnch kv (coZ_tbl_writes K (a:=m+1) (by omega_arith) (by omega_arith))
    rw [kc.2.1]
    exact ((hI.unch.trans uu).trans uv).mono
      (by intro w hw; simpa only [List.mem_append,or_self] using hw)

omit hJ hm hC hO hn ha in
/-- `2P` into the ninth entry: the table `Naf.table` leaves. -/
theorem nafTableCoZ_twice_ok {P : Point C} {s₀ s : State} (hI : CoZTableInv K C base size P s₀ s 8) :
    WP isa (.block (Naf.coZTwice K)) s (fun t => NafTableInv K C base size P s₀ t 8) := by
  have hf := hI.field
  obtain tS := nafTblPt_mem K (a:=9) (by decide) (by decide)
  obtain tn := coZ_tbl_other hL (a:=9) (by decide) (by decide)
  obtain dL := coZLive_D K 8
  refine WP.mono (copyPointFields_ok hL.lay (q:=Naf.coZD K) (o:=Naf.twice K)
    (by have := hL.n; simp only [Naf.twice]; simp [jacCoords,WinCfg.tblPt] <;> omega_arith)
    (fun x hx y hy he => tn y hy (he ▸ coZ_D_other K x hx)) tS hf dL)
    fun t ⟨E',kt,it,vt⟩ => ?_
  obtain jt : InvJ C (tmv C K.M.n base t (Naf.twice K).x) (tmv C K.M.n base t (Naf.twice K).y)
      (tmv C K.M.n base t (Naf.twice K).z) (mul 2 P) := by
    apply it.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at vt
    rw [vt.1,vt.2.1,vt.2.2]; exact hI.twice
  refine ⟨?_,?_,jt,?_,?_,hI.keep.trans (coZ_lift kt),?_⟩
  · exact it.to_tmv.sub (coZLive_twice K)
  · exact kt.invJ hL.lay hf.scr tS (fun x hx => coZ_other_slots K x (coZ_R_other K x hx))
      (fun x hx hy => tn x hy (coZ_R_other K x hx)) hI.point
  · intro a ha1 ha8
    exact kt.invJ hL.lay hf.scr tS (nafTblPt_mem K ha1 (by omega_arith))
      (coZ_tbl_ne hL ha1 (by omega_arith) (show a≠9 by omega_arith)) (hI.table a ha1 ha8)
  · exact (kt.gpr _ (rbx_not_clob _)).trans hI.counter
  · exact (hI.unch.trans (nafTable_progUnch kt (coZ_tbl_writes K (a:=9) (by decide) (by decide)))).mono
      (by intro w hw; simpa only [List.mem_append,or_self] using hw)

/-- The table by co-Z arithmetic: `P, 3P, …, 15P`, and `2P` in the ninth entry. -/
theorem nafTableCoZ_ok (ht : K.tbl<2^31) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) (h1 : tmv C K.M.n base s K.P.z=1) :
    WP isa (Naf.tableCoZ K).inline s (fun t => NafTableInv K C base size P s t 8) := by
  obtain hP0 : P≠.infinity := fun hh => by
    rw [h1] at hJP; exact hC.one_ne_zero ((hJP.z_zero_iff hC).mpr hh)
  unfold Naf.tableCoZ
  simp only [Code.inline]
  apply WP.assoc
  refine WP.seq (WP.mono (nafTableCoZ_init_ok hL hJ hm hC hO hn ha hP hI hJP h1) fun a ia => ?_)
  apply WP.seq
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j≤7 ∧ CoZTableInv K C base size P s t (8-j))
    (fun j u ⟨hj,hj7,hu⟩ => ?_) 7 a ⟨by decide,by decide,ia⟩
  refine WP.mono (nafTableCoZ_step_ok hL hJ hm hC hO hn ha ht hP hP0 (by omega_arith) (by omega_arith) hu)
    fun t ⟨it,cf⟩ => ?_
  by_cases hj1 : j=1
  · subst j
    exact Or.inl ⟨cf,nafTableCoZ_twice_ok hL it⟩
  · refine Or.inr ⟨?_,j-1,by omega_arith,by omega_arith,by omega_arith,?_⟩
    · change t.cf=some true
      rw [cf]; congr 1; exact decide_eq_true (by omega_arith)
    · rw [show 8-(j-1)=8-j+1 from by omega_arith]
      exact it

end

end VG.Proof.Weierstrass.X86_64
