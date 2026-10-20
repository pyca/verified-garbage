module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.InvIdx
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass2
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block

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

/-- `invBlockHalves`, for any zetas `z` and twist `t`: the kernel cannot
unfold a variable, so the lanes below are read off the list's shape alone. -/
def invBlockHalvesG (z t : Nat → Nat) (b : Nat) : List Nat :=
  let zs := [z (15 - b), z (31 - 2 * b), z (30 - 2 * b), 0] ++
    (List.range 4).map fun j => z (63 - 4 * b - j)
  let z7 := (List.range 8).map fun j => z (127 - 8 * b - j)
  zs ++ zs.map t ++ z7 ++ z7.map t

/-- `izsOf`, for any zetas `z`. -/
def izsOfG (z : Nat → Nat) (b : Nat) : List Nat :=
  [z (15 - b), z (31 - 2 * b), z (30 - 2 * b), 0, z (63 - 4 * b - 0), z (63 - 4 * b - 1), z (63 - 4 * b - 2),
    z (63 - 4 * b - 3)]

theorem invBlockHalvesG_get (z t : Nat → Nat) (b : Nat) {e : Nat} (he : e < 8) :
    (invBlockHalvesG z t b).getD e 0 = (izsOfG z b).getD e 0 ∧
    (invBlockHalvesG z t b).getD (8 + e) 0 = t ((izsOfG z b).getD e 0) ∧
    (invBlockHalvesG z t b).getD (16 + e) 0 = z (127 - 8 * b - e) ∧
    (invBlockHalvesG z t b).getD (24 + e) 0 = t (z (127 - 8 * b - e)) := by
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => exact ⟨rfl, rfl, rfl, rfl⟩

theorem invBlockHalves_get (b : Nat) {e : Nat} (he : e < 8) :
    (invBlockHalves b).getD e 0 = (izsOf b).getD e 0 ∧
    (invBlockHalves b).getD (8 + e) 0 = tw ((izsOf b).getD e 0) ∧
    (invBlockHalves b).getD (16 + e) 0 = Impl.MlKem.AArch64.Ntt16.zeta (127 - 8 * b - e) ∧
    (invBlockHalves b).getD (24 + e) 0 = tw (Impl.MlKem.AArch64.Ntt16.zeta (127 - 8 * b - e)) :=
  invBlockHalvesG_get Impl.MlKem.AArch64.Ntt16.zeta tw b he

/-! ## A block -/

/-- After `b` blocks of pass 1 of the inverse. -/
structure LI1 (s₀ : State) (b : Nat) (s : State) (t : Addr := sP s₀+BitVec.ofNat 64 512) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = coeffAddr (fP s₀) (32 * b)
  x3 : s.gpr .x3 = sP s₀ + BitVec.ofNat 64 (64 * b)
  x6 : s.gpr .x6 = t + BitVec.ofNat 64 (64 * b)
  x5 : (s.gpr .x5).toNat = 8 - b
  frame : Frame [polyRegion (sP s₀)] s₀.mem s.mem
  tableRead : ∀ o, o+16≤512 → InRegions (s₀.rd++s₀.wr) (t+BitVec.ofNat 64 o) 16
  tableApart : t=sP s₀+BitVec.ofNat 64 512 ∨ (polyRegion (sP s₀)).Disjoint ⟨t,512⟩
  tab : ∀ j < 64, s.mem.readW (t + BitVec.ofNat 64 (8 * j)) 64 = hw4 invTableHalves j
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

/-- The registers of a block's arithmetic in pass 1 of the inverse. -/
abbrev iarRegs : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v16, .v17, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28]

/-- The first four layers of the inverse on block `b` (`invPass1Arith`), from its four vectors
and its table at `t`. -/
theorem ip1_arith {rest : List Instr} {Q : State → Prop} {P : Poly} {b : Nat} (hb : b < 8) {s : State}
    {t : Addr}
    (a6 : ∀ i < 4, s.gpr .x6 + BitVec.ofNat 64 (16 * i) = t + BitVec.ofNat 64 (64 * b + 16 * i))
    (i6 : ∀ i < 4, InRegions (s.rd ++ s.wr) (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16)
    (tl : ∀ i < 4, ∀ e < 8, vhalf (s.mem.read (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16) e =
      BitVec.ofNat 16 ((invBlockHalves b).getD (8 * i + e) 0))
    (R : ∀ i < 4, IRepI P 0 (32 * b) (seg (8 * i)) 3329 (s.v (row i)))
    (hq : Cst (s.v .v31) fun _ => 3329) (h10 : Cst (s.v .v30) fun _ => 10)
    (kk : ∀ s₃₀, VChg iarRegs s s₃₀ →
      (∀ i < 4, IRepI P 4 (32 * b) (seg (8 * i)) (2 * 3329) (s₃₀.v (row i))) →
      WP isa (.block rest) s₃₀ Q) :
    WP isa (.block (invPass1Arith ++ rest)) s Q := by
  simp only [invPass1Arith, List.cons_append, List.nil_append, List.append_assoc, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  have hb0 : 32 * b % 32 = 0 := by omega
  have hb1 : 32 * b + 32 ≤ 256 := by omega
  refine ld_step (VChg.refl [] s) (by decide) (a6 0 (by decide)) (i6 0 (by decide)) fun s₁ c₁ v₁ o₁ => ?_
  refine ld_step c₁ (by decide) (a6 1 (by decide)) (i6 1 (by decide)) fun s₂ c₂ v₂ o₂ => ?_
  refine ld_step c₂ (by decide) (a6 2 (by decide)) (i6 2 (by decide)) fun s₃ c₃ v₃ o₃ => ?_
  refine ld_step c₃ (by decide) (a6 3 (by decide)) (i6 3 (by decide)) fun s₄ c₄ v₄ o₄ => ?_
  have t20 : ∀ e < 8, vhalf (s₄.v .v20) e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 0 + e) 0) :=
    fun e he => by rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), v₁]; exact tl 0 (by decide) e he
  have t21 : ∀ e < 8, vhalf (s₄.v .v21) e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 1 + e) 0) :=
    fun e he => by rw [o₄ _ (by decide), o₃ _ (by decide), v₂]; exact tl 1 (by decide) e he
  have t22 : ∀ e < 8, vhalf (s₄.v .v22) e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 2 + e) 0) :=
    fun e he => by rw [o₄ _ (by decide), v₃]; exact tl 2 (by decide) e he
  have t23 : ∀ e < 8, vhalf (s₄.v .v23) e = BitVec.ofNat 16 ((invBlockHalves b).getD (8 * 3 + e) 0) :=
    fun e he => by rw [v₄]; exact tl 3 (by decide) e he
  have C₄ : VChg [.v20, .v21, .v22, .v23] s s₄ := c₄.mono (by decide)
  -- the zetas of layers 1 and 2 for the first half
  refine wp_vop rfl fun s₅ h₅ => wp_vop rfl fun s₆ h₆ => wp_vop rfl fun s₇ h₇ =>
    wp_vop rfl fun s₈ h₈ => wp_vop rfl fun s₉ h₉ => wp_vop rfl fun s₁₀ h₁₀ => ?_
  have cz : VChg [.v24, .v25, .v28, .v19, .v26, .v27] s₄ s₁₀ :=
    ((((h₅.chg.trans h₆.chg).trans h₇.chg).trans h₈.chg).trans h₉.chg).trans h₁₀.chg |>.mono
  have z24 : ZRep (s₁₀.v .v24) (60 - 4 * b) [3, 3, 2, 2, 1, 1, 0, 0] := by
    rw [h₁₀.get .v24, h₉.get .v24, h₈.get .v24, h₇.get .v24, h₆.get .v24, h₅.v]
    exact izrep_zip2 hb t20
  have t25 : TRep (s₁₀.v .v25) (60 - 4 * b) [3, 3, 2, 2, 1, 1, 0, 0] := by
    rw [h₁₀.get .v25, h₉.get .v25, h₈.get .v25, h₇.get .v25, h₆.v, h₅.get .v21]
    exact itrep_zip2 hb t21
  have z22 : ZRep (s₁₀.v .v22) (120 - 8 * b) [7, 6, 5, 4, 3, 2, 1, 0] := by
    rw [cz.get .v22]; exact izrep_z7 hb t22
  have t23' : TRep (s₁₀.v .v23) (120 - 8 * b) [7, 6, 5, 4, 3, 2, 1, 0] := by
    rw [cz.get .v23]; exact itrep_z7 hb t23
  have z28 : ZRep (s₁₀.v .v28) (120 - 8 * b) [7, 7, 6, 6, 5, 5, 4, 4] := by
    rw [h₁₀.get .v28, h₉.get .v28, h₈.get .v28, h₇.v, h₆.get .v22, h₅.get .v22]
    exact zrep_perm (src_h8 .zip1 _ _) (by decide) (izrep_z7 hb t22) (izrep_z7 hb t22) (by decide)
  have t19 : TRep (s₁₀.v .v19) (120 - 8 * b) [7, 7, 6, 6, 5, 5, 4, 4] := by
    rw [h₁₀.get .v19, h₉.get .v19, h₈.v, h₇.get .v23, h₆.get .v23, h₅.get .v23]
    exact trep_perm (src_h8 .zip1 _ _) (by decide) (itrep_z7 hb t23) (itrep_z7 hb t23) (by decide)
  have z26 : ZRep (s₁₀.v .v26) (60 - 4 * b) [3, 3, 3, 3, 2, 2, 2, 2] := by
    have z : ZRep (s₈.v .v24) (60 - 4 * b) [3, 3, 2, 2, 1, 1, 0, 0] := by
      rw [h₈.get .v24, h₇.get .v24, h₆.get .v24, h₅.v]; exact izrep_zip2 hb t20
    rw [h₁₀.get .v26, h₉.v]
    exact zrep_perm (src_s4 .zip1 _ _) (by decide) z z (by decide)
  have t27 : TRep (s₁₀.v .v27) (60 - 4 * b) [3, 3, 3, 3, 2, 2, 2, 2] := by
    have t : TRep (s₉.v .v25) (60 - 4 * b) [3, 3, 2, 2, 1, 1, 0, 0] := by
      rw [h₉.get .v25, h₈.get .v25, h₇.get .v25, h₆.v, h₅.get .v21]; exact itrep_zip2 hb t21
    rw [h₁₀.v]
    exact trep_perm (src_s4 .zip1 _ _) (by decide) t t (by decide)
  have q₁₀ : Cst (s₁₀.v .v31) fun _ => 3329 := by rw [cz.get .v31, C₄.get .v31]; exact hq
  have r0 : IRepI P 0 (32 * b) (seg 0) 3329 (s₁₀.v .v0) := by
    rw [cz.get .v0, C₄.get .v0]; exact R 0 (by decide)
  have r1 : IRepI P 0 (32 * b) (seg 8) 3329 (s₁₀.v .v1) := by
    rw [cz.get .v1, C₄.get .v1]; exact R 1 (by decide)
  refine firstTwo_ok (p := .v0) (q' := .v1) (z7 := .v28) (t7 := .v19) (z6 := .v26) (t6 := .v27)
    (op := seg 0) (oq := seg 8) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK7 := by simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hK6 := by simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hp := r0) (hq' := r1) (hz7 := z28) (ht7 := t19) (hz6 := z26) (ht6 := t27) (hq := q₁₀)
    (k := fun s₁₁ c₁₁ e0 e1 => ?_)
  -- the zetas of layers 1 and 2 for the second half
  refine wp_vop rfl fun s₁₂ h₁₂ => wp_vop rfl fun s₁₃ h₁₃ => wp_vop rfl fun s₁₄ h₁₄ =>
    wp_vop rfl fun s₁₅ h₁₅ => ?_
  have cw : VChg [.v28, .v19, .v26, .v27] s₁₁ s₁₅ :=
    (((h₁₂.chg.trans h₁₃.chg).trans h₁₄.chg).trans h₁₅.chg).mono
  have g₁₁ : ∀ r, r ∉ lastRegs .v0 .v1 → s₁₁.v r = s₁₀.v r := fun r hr => c₁₁.get r hr
  have z28' : ZRep (s₁₅.v .v28) (120 - 8 * b) [3, 3, 2, 2, 1, 1, 0, 0] := by
    rw [h₁₅.get .v28, h₁₄.get .v28, h₁₃.get .v28, h₁₂.v, g₁₁ .v22 (by decide)]
    exact zrep_perm (src_h8 .zip2 _ _) (by decide) z22 z22 (by decide)
  have t19' : TRep (s₁₅.v .v19) (120 - 8 * b) [3, 3, 2, 2, 1, 1, 0, 0] := by
    rw [h₁₅.get .v19, h₁₄.get .v19, h₁₃.v, h₁₂.get .v23, g₁₁ .v23 (by decide)]
    exact trep_perm (src_h8 .zip2 _ _) (by decide) t23' t23' (by decide)
  have z26' : ZRep (s₁₅.v .v26) (60 - 4 * b) [1, 1, 1, 1, 0, 0, 0, 0] := by
    rw [h₁₅.get .v26, h₁₄.v, h₁₃.get .v24, h₁₂.get .v24, g₁₁ .v24 (by decide)]
    exact zrep_perm (src_s4 .zip2 _ _) (by decide) z24 z24 (by decide)
  have t27' : TRep (s₁₅.v .v27) (60 - 4 * b) [1, 1, 1, 1, 0, 0, 0, 0] := by
    rw [h₁₅.v, h₁₄.get .v25, h₁₃.get .v25, h₁₂.get .v25, g₁₁ .v25 (by decide)]
    exact trep_perm (src_s4 .zip2 _ _) (by decide) t25 t25 (by decide)
  have q₁₅ : Cst (s₁₅.v .v31) fun _ => 3329 := by rw [cw.get .v31, g₁₁ .v31 (by decide)]; exact q₁₀
  refine firstTwo_ok (p := .v2) (q' := .v3) (z7 := .v28) (t7 := .v19) (z6 := .v26) (t6 := .v27)
    (op := seg 16) (oq := seg 24) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK7 := by simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hK6 := by simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hp := by rw [cw.get .v2, g₁₁ .v2 (by decide), cz.get .v2, C₄.get .v2]; exact R 2 (by decide))
    (hq' := by rw [cw.get .v3, g₁₁ .v3 (by decide), cz.get .v3, C₄.get .v3]; exact R 3 (by decide))
    (hz7 := z28') (ht7 := t19') (hz6 := z26') (ht6 := t27') (hq := q₁₅)
    (k := fun s₁₆ c₁₆ e2 e3 => ?_)
  have g₁₆ : ∀ r, r ∉ [VReg.v4, .v5, .v16, .v17, .v2, .v3, .v28, .v19, .v26, .v27] →
      s₁₆.v r = s₁₁.v r := fun r hr => by
    rw [c₁₆.get r (by simp_all), cw.get r (by simp_all)]
  have tt : ∀ r ∈ [VReg.v20, .v21, .v30, .v31], s₁₆.v r = s₄.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₁₆ _ (by decide), g₁₁ _ (by decide), cz.get _ (by decide)]
  have q₁₆ : Cst (s₁₆.v .v31) fun _ => 3329 := by
    rw [g₁₆ .v31 (by decide), g₁₁ .v31 (by decide)]; exact q₁₀
  -- layer 3
  have Z1 := ilane_zt (s := s₄) (k := 1) (K := 31 - 2 * b) t20 t21 (by decide) rfl
  have Z2 := ilane_zt (s := s₄) (k := 2) (K := 30 - 2 * b) t20 t21 (by decide) rfl
  have Z0 := ilane_zt (s := s₄) (k := 0) (K := 15 - b) t20 t21 (by decide) rfl
  refine wp_vop (eval_dupE (by decide)) fun s₁₇ h₁₇ => wp_vop (eval_dupE (by decide)) fun s₁₈ h₁₈ => ?_
  have c₁₈ : VChg [.v24, .v25] s₁₆ s₁₈ := h₁₇.chg.trans h₁₈.chg
  refine irepI_gs (x := .v0) (y := .v1) (z := .v24) (t := .v25) (j := 2) (K₀ := 30 - 2 * b)
    (ox := seg 0) (oy := seg 8) (kz := List.replicate 8 1) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK := by simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hx := by rw [c₁₈.get .v0, g₁₆ .v0 (by decide)]; exact e0)
    (hy := by rw [c₁₈.get .v1, g₁₆ .v1 (by decide)]; exact e1)
    (hz := by rw [h₁₈.get .v24, h₁₇.v, tt .v20 (by simp)]
              exact zrep_dup Z1.1 fun e he => by simp only [getD_rep_lt he]; omega)
    (ht := by rw [h₁₈.v, h₁₇.get .v21, tt .v21 (by simp)]
              exact trep_dup Z1.2 fun e he => by simp only [getD_rep_lt he]; omega)
    (hq := by rw [c₁₈.get .v31]; exact q₁₆) (hB := by decide) (k := fun s₁₉ c₁₉ f0 f1 => ?_)
  refine wp_vop (eval_dupE (by decide)) fun s₂₀ h₂₀ => wp_vop (eval_dupE (by decide)) fun s₂₁ h₂₁ => ?_
  have c₂₁ : VChg [.v24, .v25] s₁₉ s₂₁ := h₂₀.chg.trans h₂₁.chg
  have tt₁₉ : ∀ r ∈ [VReg.v20, .v21, .v30, .v31, .v2, .v3], s₁₉.v r = s₁₆.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [c₁₉.get _ (by decide), c₁₈.get _ (by decide)]
  refine irepI_gs (x := .v2) (y := .v3) (z := .v24) (t := .v25) (j := 2) (K₀ := 30 - 2 * b)
    (ox := seg 16) (oy := seg 24) (kz := List.replicate 8 0) (hok := by decide) (hb := hb0)
    (hb' := hb1) (hK := by simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hx := by rw [c₂₁.get .v2, tt₁₉ .v2 (by simp)]; exact e2)
    (hy := by rw [c₂₁.get .v3, tt₁₉ .v3 (by simp)]; exact e3)
    (hz := by rw [h₂₁.get .v24, h₂₀.v, tt₁₉ .v20 (by simp), tt .v20 (by simp)]
              exact zrep_dup Z2.1 fun e he => by simp only [getD_rep_lt he]; omega)
    (ht := by rw [h₂₁.v, h₂₀.get .v21, tt₁₉ .v21 (by simp), tt .v21 (by simp)]
              exact trep_dup Z2.2 fun e he => by simp only [getD_rep_lt he]; omega)
    (hq := by rw [c₂₁.get .v31, tt₁₉ .v31 (by simp)]; exact q₁₆) (hB := by decide)
    (k := fun s₂₂ c₂₂ f2 f3 => ?_)
  -- the reductions
  have tt₂₂ : ∀ r ∈ [VReg.v20, .v21, .v30, .v31, .v0, .v1], s₂₂.v r = s₁₉.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [c₂₂.get _ (by decide), c₂₁.get _ (by decide)]
  have k₂₂ : Cst (s₂₂.v .v30) fun _ => 10 := by
    rw [tt₂₂ .v30 (by simp), tt₁₉ .v30 (by simp), tt .v30 (by simp), C₄.get .v30]
    exact h10
  have q₂₂ : Cst (s₂₂.v .v31) fun _ => 3329 := by rw [tt₂₂ .v31 (by simp), tt₁₉ .v31 (by simp)]; exact q₁₆
  refine reduce_ok (x := .v0) (hx := by rw [tt₂₂ .v0 (by simp)]; exact f0) (hB := by decide)
    (h10 := k₂₂) (hq := q₂₂) (k := fun s₂₃ c₂₃ g0 => ?_)
  refine reduce_ok (x := .v1) (hx := by rw [c₂₃.get .v1, tt₂₂ .v1 (by simp)]; exact f1)
    (hB := by decide) (h10 := by rw [c₂₃.get .v30]; exact k₂₂) (hq := by rw [c₂₃.get .v31]; exact q₂₂)
    (k := fun s₂₄ c₂₄ g1 => ?_)
  refine reduce_ok (x := .v2) (hx := by rw [c₂₄.get .v2, c₂₃.get .v2]; exact f2)
    (hB := by decide) (h10 := by rw [c₂₄.get .v30, c₂₃.get .v30]; exact k₂₂)
    (hq := by rw [c₂₄.get .v31, c₂₃.get .v31]; exact q₂₂) (k := fun s₂₅ c₂₅ g2 => ?_)
  refine reduce_ok (x := .v3) (hx := by rw [c₂₅.get .v3, c₂₄.get .v3, c₂₃.get .v3]; exact f3)
    (hB := by decide) (h10 := by rw [c₂₅.get .v30, c₂₄.get .v30, c₂₃.get .v30]; exact k₂₂)
    (hq := by rw [c₂₅.get .v31, c₂₄.get .v31, c₂₃.get .v31]; exact q₂₂) (k := fun s₂₆ c₂₆ g3 => ?_)
  -- layer 4
  have cr : VChg [.v16, .v0, .v16, .v1, .v16, .v2, .v16, .v3] s₂₂ s₂₆ :=
    (((c₂₃.trans c₂₄).trans c₂₅).trans c₂₆).mono
  refine wp_vop (eval_dupE (by decide)) fun s₂₇ h₂₇ => wp_vop (eval_dupE (by decide)) fun s₂₈ h₂₈ => ?_
  have c₂₈ : VChg [.v24, .v25] s₂₆ s₂₈ := h₂₇.chg.trans h₂₈.chg
  have t20' : s₂₆.v .v20 = s₄.v .v20 := by
    rw [cr.get .v20, tt₂₂ .v20 (by simp), tt₁₉ .v20 (by simp), tt .v20 (by simp)]
  have t21' : s₂₇.v .v21 = s₄.v .v21 := by
    rw [h₂₇.get .v21, cr.get .v21, tt₂₂ .v21 (by simp), tt₁₉ .v21 (by simp), tt .v21 (by simp)]
  have q₂₈ : Cst (s₂₈.v .v31) fun _ => 3329 := by rw [c₂₈.get .v31, cr.get .v31]; exact q₂₂
  refine irepI_gs (x := .v0) (y := .v2) (z := .v24) (t := .v25) (j := 3) (K₀ := 15 - b)
    (ox := seg 0) (oy := seg 16) (kz := List.replicate 8 0) (hok := by decide) (hb := hb0)
    (hb' := hb1) (hK := by simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hx := by rw [c₂₈.get .v0, c₂₆.get .v0, c₂₅.get .v0, c₂₄.get .v0]; exact g0)
    (hy := by rw [c₂₈.get .v2, c₂₆.get .v2]; exact g2)
    (hz := by rw [h₂₈.get .v24, h₂₇.v, t20']
              exact zrep_dup Z0.1 fun e he => by simp only [getD_rep_lt he]; omega)
    (ht := by rw [h₂₈.v, t21']
              exact trep_dup Z0.2 fun e he => by simp only [getD_rep_lt he]; omega)
    (hq := q₂₈) (hB := by decide) (k := fun s₂₉ c₂₉ k0 k2 => ?_)
  refine irepI_gs (x := .v1) (y := .v3) (z := .v24) (t := .v25) (j := 3) (K₀ := 15 - b)
    (ox := seg 8) (oy := seg 24) (kz := List.replicate 8 0) (hok := by decide) (hb := hb0)
    (hb' := hb1) (hK := by simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hx := by rw [c₂₉.get .v1, c₂₈.get .v1, c₂₆.get .v1, c₂₅.get .v1]; exact g1)
    (hy := by rw [c₂₉.get .v3, c₂₈.get .v3]; exact g3)
    (hz := by rw [c₂₉.get .v24, h₂₈.get .v24, h₂₇.v, t20']
              exact zrep_dup Z0.1 fun e he => by simp only [getD_rep_lt he]; omega)
    (ht := by rw [c₂₉.get .v25, h₂₈.v, t21']
              exact trep_dup Z0.2 fun e he => by simp only [getD_rep_lt he]; omega)
    (hq := by rw [c₂₉.get .v31]; exact q₂₈) (hB := by decide) (k := fun s₃₀ c₃₀ k1 k3 => ?_)
  have rows : ∀ i < 4, IRepI P 4 (32 * b) (seg (8 * i)) (2 * 3329) (s₃₀.v (row i)) := by
    intro i hi
    match i, hi with
    | 0, _ => rw [show row 0 = .v0 from rfl, c₃₀.get .v0]; exact k0
    | 1, _ => exact k1
    | 2, _ => rw [show row 2 = .v2 from rfl, c₃₀.get .v2]; exact k2.mono (by decide)
    | 3, _ => exact k3.mono (by decide)
  exact kk s₃₀ ((((((((((((C₄.trans cz).trans c₁₁).trans cw).trans c₁₆).trans c₁₈).trans
    c₁₉).trans c₂₁).trans c₂₂).trans cr).trans c₂₈).trans c₂₉).trans c₃₀).mono rows

theorem ip1_body {s₀ : State} (hp : Pre s₀) {b : Nat} (hb : b < 8) {sb : State} {t : Addr} (h : LI1 s₀ b sb t) :
    WP isa (.block invPass1Body) sb fun s' => LI1 s₀ (b + 1) s' t ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ b + 1 ≠ 8) := by
  simp only [invPass1Body, List.append_assoc]
  have hpoly : PolyIs sb.mem (fP s₀) (P₀ s₀) :=
    polyIs_frame h.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩
  refine i_loads hp hb h.st h.x2 hpoly fun s c₀ R => ?_
  have st := h.st.vchg c₀
  have a6 : ∀ i < 4, s.gpr .x6 + BitVec.ofNat 64 (16 * i) =
      t + BitVec.ofNat 64 (64 * b + 16 * i) := fun i _ => by rw [c₀.gpr, h.x6, ptr_add]
  have i6 : ∀ i < 4, InRegions (s.rd ++ s.wr) (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16 :=
    fun i hi => by rw [st.rd,st.wr]; exact h.tableRead _ (by omega)
  have tl : ∀ i < 4, ∀ e < 8, vhalf (s.mem.read (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16) e =
      BitVec.ofNat 16 ((invBlockHalves b).getD (8 * i + e) 0) := fun i hi e he => by
    have ht : ∀ j < 64, s.mem.readW (t + BitVec.ofNat 64 (8 * j)) 64 = hw4 invTableHalves j :=
      fun j hj => by rw [c₀.mem]; exact h.tab j hj
    have := vhalf_table (off:=0) (by simpa only [Nat.zero_add] using ht) (i := 4 * b + i) (by omega) he
    rw [show 0 + 16 * (4 * b + i) = 64 * b + 16 * i by omega,
      show 8 * (4 * b + i) + e = 32 * b + (8 * i + e) by omega, invTableHalves_get hb (by omega)] at this
    exact this
  refine ip1_arith hb a6 i6 tl R (by rw [c₀.get .v31]; exact h.q) (by rw [c₀.get .v30]; exact h.c10)
    fun s₃₀ C' rows => ?_
  have CC := c₀.trans C'
  have st₃₀ : St s₀ s₃₀ := h.st.vchg CC
  refine wp_stores (p := sP s₀) (base := fun r => 64 * b + 16 * r)
    (fun r _ => by rw [CC.gpr, h.x3, ptr_add]) (fun r hr => ⟨by omega, by omega⟩)
    (fun r hr => by omega) (fun r hr r' hr' e => by omega) (fun r hr => inS hp st₃₀ (by omega))
    fun s₃₁ h₃₁ => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x3, .x6, .x5] s₃₁ w' ∧ w'.mem = s₃₁.mem ∧
      w'.gpr .x2 = s₃₁.gpr .x2 + BitVec.ofNat 64 128 ∧ w'.gpr .x3 = s₃₁.gpr .x3 + BitVec.ofNat 64 64 ∧
      w'.gpr .x6 = s₃₁.gpr .x6 + BitVec.ofNat 64 64 ∧ w'.gpr .x5 = s₃₁.gpr .x5 - BitVec.ofNat 64 1)
    (by decide)
    (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_addImm (by decide) fun w₃ k₃ e₃ => wp_subImm (by decide) fun w₄ k₄ e₄ =>
        wp_nil ⟨(((k₁.keep.trans k₂.keep).trans k₃.keep).trans k₄.keep).mono,
          by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem],
          by rw [k₄.gpr .x2 (by decide), k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), e₁],
          by rw [k₄.gpr .x3 (by decide), k₃.gpr .x3 (by decide), e₂, k₁.gpr .x3 (by decide)],
          by rw [k₄.gpr .x6 (by decide), e₃, k₂.gpr .x6 (by decide), k₁.gpr .x6 (by decide)],
          by rw [e₄, k₃.gpr .x5 (by decide), k₂.gpr .x5 (by decide), k₁.gpr .x5 (by decide)]⟩))
    fun w ⟨⟨kw, mw, e2, e3, e6, e5⟩, hv⟩ => ?_
  have gw : s₃₁.gpr = sb.gpr := by rw [h₃₁.gpr, CC.gpr]
  have x5' : (w.gpr .x5).toNat = 8 - (b + 1) := by
    rw [e5, gw, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  have vv : ∀ r ∈ [VReg.v29, .v30, .v31], w.v r = sb.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [hv, h₃₁.v, CC.get _ (by decide)]
  refine ⟨⟨(st₃₀.keep h₃₁.keep).keep kw, by rw [e2, gw, h.x2, coeffAddr, coeffAddr, ptr_add]; congr 2,
    by rw [e3, gw, h.x3, ptr_add]; congr 2, by rw [e6, gw, h.x6, ptr_add]; congr 2, x5',
    by rw [mw]; exact h.frame.trans (by rw [← CC.mem]; exact h₃₁.frame), h.tableRead, h.tableApart, fun j hj => ?_,
    fun r hr i hi => ?_, by rw [vv .v31 (by decide)]; exact h.q, by rw [vv .v30 (by decide)]; exact h.c10,
    by rw [vv .v29 (by decide)]; exact h.c0⟩, by rw [x5']; omega⟩
  · rcases h.tableApart with ht | hd
    · have hh := h.tab j hj
      rw [ht,BitVec.add_assoc,←BitVec.ofNat_add] at hh ⊢
      simp only [Mem.readW] at hh ⊢
      rw [mw,h₃₁.other _ (64/8) (by omega) (fun r hr => Or.inr (by omega)),CC.mem]
      exact hh
    · rw [mw,h₃₁.frame.readW (r:=⟨t,512⟩) (contains_off (by omega) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.symm) (by decide),CC.mem]
      exact h.tab j hj
  · rw [mw]
    by_cases e : r = b
    · subst e
      rw [h₃₁.st i hi]
      refine (rows i hi).congr fun e he => ?_
      rw [seg_getD _ he, Nat.add_assoc]
    · rw [h₃₁.other _ 16 (by omega) (fun r' hr' => by omega), CC.mem]
      exact h.scr r (by omega) i hi

end VG.Proof.MlKem.AArch64.Ntt16
