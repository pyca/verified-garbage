module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.InvIdx
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: pass 1

Pass 1 of the inverse (`invPass1Body`, blocks `b < 8`): the 32 coefficients
of block `b` from `f`, narrowed to halfwords; layers 1 and 2 (`firstTwo_ok`),
3, a reduction, and 4 (`irepI_gs`); stored into `scratch` at `64b`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## The table -/

theorem length_invBlockHalves (b : Nat) : (invBlockHalves b).length = 32 := by
  simp [invBlockHalves]

theorem invTableHalves_get {b : Nat} (hb : b < 8) {i : Nat} (hi : i < 32) :
    invTableHalves.getD (32 * b + i) 0 = (invBlockHalves b).getD i 0 :=
  flatMap_getD _ length_invBlockHalves 8 b i hb hi

theorem length_invTableHalves : invTableHalves.length = 256 :=
  length_flatMap_range _ length_invBlockHalves 8

/-- The zetas of block `b`'s `Zs` for the inverse. -/
def izsOf (b : Nat) : List Nat :=
  [Impl.MlKem.AArch64.Ntt16.zeta (15 - b), Impl.MlKem.AArch64.Ntt16.zeta (31 - 2 * b),
    Impl.MlKem.AArch64.Ntt16.zeta (30 - 2 * b), 0, Impl.MlKem.AArch64.Ntt16.zeta (63 - 4 * b - 0),
    Impl.MlKem.AArch64.Ntt16.zeta (63 - 4 * b - 1), Impl.MlKem.AArch64.Ntt16.zeta (63 - 4 * b - 2),
    Impl.MlKem.AArch64.Ntt16.zeta (63 - 4 * b - 3)]

theorem invBlockHalves_get (b : Nat) {e : Nat} (he : e < 8) :
    (invBlockHalves b).getD e 0 = (izsOf b).getD e 0 ∧
    (invBlockHalves b).getD (8 + e) 0 = tw ((izsOf b).getD e 0) ∧
    (invBlockHalves b).getD (16 + e) 0 = Impl.MlKem.AArch64.Ntt16.zeta (127 - 8 * b - e) ∧
    (invBlockHalves b).getD (24 + e) 0 = tw (Impl.MlKem.AArch64.Ntt16.zeta (127 - 8 * b - e)) := by
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [invBlockHalves, izsOf, List.range_succ]

/-! ## A block -/

/-- After `b` blocks of pass 1 of the inverse. -/
structure LI1 (s₀ : State) (b : Nat) (s : State) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = coeffAddr (fP s₀) (32 * b)
  x3 : s.gpr .x3 = sP s₀ + BitVec.ofNat 64 (64 * b)
  x6 : s.gpr .x6 = sP s₀ + BitVec.ofNat 64 (512 + 64 * b)
  x5 : (s.gpr .x5).toNat = 8 - b
  frame : Frame [polyRegion (sP s₀)] s₀.mem s.mem
  tab : ∀ j < 64, s.mem.readW (sP s₀ + BitVec.ofNat 64 (512 + 8 * j)) 64 = hw4 invTableHalves j
  scr : ∀ r < b, ∀ i < 4, Rep (s.mem.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * i)) 16)
    (fun e => (nttInvL 4 (P₀ s₀))[32 * r + 8 * i + e]!) (2 * 3329)
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10
  c0 : Cst (s.v .v29) fun _ => 0

section
variable {rest : List Instr} {Q : State → Prop}

/-- The registers of the loads of a block of the inverse. -/
abbrev ildRegs : List VReg := [.v20, .v21, .v0, .v1, .v2, .v3]

theorem row_mem_ild {r : Nat} (hr : r < 4) : row r ∈ ildRegs := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ => decide

/-- The four vectors of block `b` from the polynomial `P` at `f`. -/
theorem i_loads {s₀ : State} (hp : Pre s₀) {P : Poly} {b : Nat} (hb : b < 8) {s : State}
    (hst : St s₀ s) (hx2 : s.gpr .x2 = coeffAddr (fP s₀) (32 * b)) (hpoly : PolyIs s.mem (fP s₀) P)
    (k : ∀ s', VChg ildRegs s s' → (∀ i < 4, IRepI P 0 (32 * b) (seg (8 * i)) 3329 (s'.v (row i))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 4).flatMap fun i =>
      [.ldrq .v20 .x2 (32 * i), .ldrq .v21 .x2 (32 * i + 16),
       .vop (.perm .uzp1 .h8 (row i) .v20 .v21)]) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => VChg ildRegs s s' ∧ ∀ i < n, IRepI P 0 (32 * b) (seg (8 * i)) 3329 (s'.v (row i)))
    (fun r w hr ⟨cw, hw⟩ => ?_) 4 (Nat.le_refl _) s ⟨VChg.refl _ _, fun r hr => absurd hr (Nat.not_lt_zero r)⟩)
    fun s' ⟨c', h'⟩ => k s' c' h'
  have hj : 32 * b + 8 * r + 8 ≤ 256 := by omega
  have st := hst.vchg cw
  refine wp_ldrq (a := coeffAddr (fP s₀) (32 * b + 8 * r)) (by omega)
    (by rw [cw.gpr, hx2, coeffAddr, coeffAddr, ptr_add]; congr 2; omega) (inF hp st (by omega))
    fun w₁ h₁ => ?_
  refine wp_ldrq (a := coeffAddr (fP s₀) (32 * b + 8 * r + 4)) (by omega)
    (by rw [h₁.gpr, cw.gpr, hx2, coeffAddr, coeffAddr, ptr_add]; congr 2; omega)
    (by rw [h₁.rd, h₁.wr]; exact inF hp st (by omega)) fun w₂ h₂ => ?_
  refine wp_vop rfl fun w₃ h₃ => wp_nil ⟨(cw.trans ((h₁.chg.trans h₂.chg).trans h₃.chg)).mono
    fun x hx => ?_, fun r' hr' => ?_⟩
  · simp only [List.mem_append] at hx
    rcases hx with hx | (hx | hx) | hx
    · exact hx
    · rw [List.mem_singleton.mp hx]; decide
    · rw [List.mem_singleton.mp hx]; decide
    · rw [List.mem_singleton.mp hx]; exact row_mem_ild hr
  · by_cases e : r' = r
    · subst e
      rw [h₃.v, h₂.v, h₂.get .v20, h₁.v, h₁.mem, cw.mem]
      refine (rep_load hpoly hj).congr fun e he => ?_
      rw [seg_getD _ he, Nat.add_assoc]; rfl
    · have nr := row_ne (show r' < 8 by omega)
      rw [h₃.get _ (fun h => e (row_inj r' (by omega) r (by omega) h)), h₂.get _ nr.2.2.2.2.2.2.2.2.1,
        h₁.get _ nr.2.2.2.2.2.2.2.1]
      exact hw r' (by omega)

end

/-! ## Zetas -/

theorem izrep_zip2 {x : BitVec 128} {b : Nat} (hb : b < 8)
    (hx : ∀ e < 8, vhalf x e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 0 + e) 0)) :
    ZRep (VPermOp.eval .zip2 .h8 x x) (60 - 4 * b) [3, 3, 2, 2, 1, 1, 0, 0] := fun e he => by
  rw [vhalf_perm_h8 _ _ _ he]
  simp only [ite_self]
  rw [hx _ (by omega), show 8 * 0 + (4 + e / 2) = 4 + e / 2 by omega,
    (invBlockHalves_get b (e := 4 + e / 2) (by omega)).1]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [izsOf, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceDiv, Nat.reduceAdd]
    exact congrArg _ (congrArg _ (by omega))

theorem itrep_zip2 {x : BitVec 128} {b : Nat} (hb : b < 8)
    (hx : ∀ e < 8, vhalf x e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 1 + e) 0)) :
    TRep (VPermOp.eval .zip2 .h8 x x) (60 - 4 * b) [3, 3, 2, 2, 1, 1, 0, 0] := fun e he => by
  rw [vhalf_perm_h8 _ _ _ he]
  simp only [ite_self]
  rw [hx _ (by omega), show 8 * 1 + (4 + e / 2) = 8 + (4 + e / 2) by omega,
    (invBlockHalves_get b (e := 4 + e / 2) (by omega)).2.1]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [izsOf, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceDiv, Nat.reduceAdd]
    exact congrArg _ (congrArg _ (congrArg _ (by omega)))

theorem izrep_z7 {x : BitVec 128} {b : Nat} (hb : b < 8)
    (hx : ∀ e < 8, vhalf x e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 2 + e) 0)) :
    ZRep x (120 - 8 * b) [7, 6, 5, 4, 3, 2, 1, 0] := fun e he => by
  dsimp only
  rw [hx e he, show 8 * 2 + e = 16 + e by omega, (invBlockHalves_get b he).2.2.1]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact congrArg _ (congrArg _ (by omega))

theorem itrep_z7 {x : BitVec 128} {b : Nat} (hb : b < 8)
    (hx : ∀ e < 8, vhalf x e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 3 + e) 0)) :
    TRep x (120 - 8 * b) [7, 6, 5, 4, 3, 2, 1, 0] := fun e he => by
  dsimp only
  rw [hx e he, show 8 * 3 + e = 24 + e by omega, (invBlockHalves_get b he).2.2.2]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact congrArg _ (congrArg _ (congrArg _ (by omega)))

/-- The zeta `K` and its `tw` in lane `k` of the inverse's table vectors. -/
theorem ilane_zt {s : State} {b k K : Nat} {x y : VReg}
    (hx : ∀ e < 8, vhalf (s.v x) e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 0 + e) 0))
    (hy : ∀ e < 8, vhalf (s.v y) e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 1 + e) 0))
    (hk : k < 8) (hK : (izsOf b).getD k 0 = Impl.MlKem.AArch64.Ntt16.zeta K) :
    vhalf (s.v x) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta K) ∧
    vhalf (s.v y) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta K)) := by
  rw [hx k hk, hy k hk, show 8 * 0 + k = k by omega, (invBlockHalves_get b hk).1,
    (invBlockHalves_get b hk).2.1, hK]
  exact ⟨rfl, rfl⟩

end VG.Proof.MlKem.AArch64.Ntt16
