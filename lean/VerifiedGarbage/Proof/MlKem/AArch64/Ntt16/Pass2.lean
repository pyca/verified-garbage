module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass1
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Idx
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Block

/-!
# ML-KEM's 16-bit NTT on AArch64: pass 2

Pass 2 (`pass2Body`, blocks `b < 8`): the 32 coefficients of block `b` from
`scratch`, after the first three layers, and the zetas of the block from
the table at `scratch + 512` (`blockHalves`); layers 4 and 5 (`irep_bf`), 6
and 7 (`lastTwo_ok`), each lane reduced to `[0, q)` (`norm_ok`) and stored
back into `f` as `u32`s.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## The table -/

theorem length_flatMap_range (f : Nat → List Nat) (hf : ∀ b, (f b).length = 32) :
    ∀ n, ((List.range n).flatMap f).length = 32 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
      length_flatMap_range f hf n, hf]
    omega

theorem flatMap_getD (f : Nat → List Nat) (hf : ∀ b, (f b).length = 32) :
    ∀ n b i, b < n → i < 32 → ((List.range n).flatMap f).getD (32 * b + i) 0 = (f b).getD i 0 := by
  intro n
  induction n with
  | zero => intro b i hb; omega
  | succ n ih =>
    intro b i hb hi
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl := length_flatMap_range f hf n
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    by_cases h : b < n
    · rw [ite_eq_left (by omega), ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
      exact ih b i h hi
    · have : b = n := by omega
      subst this
      rw [ite_eq_right (by omega), show 32 * b + i - 32 * b = i by omega]

theorem length_blockHalves (b : Nat) : (blockHalves b).length = 32 := by
  simp [blockHalves]

/-- The zetas of block `b`'s `Zs`. -/
def zsOf (b : Nat) : List Nat :=
  [Impl.MlKem.AArch64.Ntt16.zeta (8 + b), Impl.MlKem.AArch64.Ntt16.zeta (16 + 2 * b),
    Impl.MlKem.AArch64.Ntt16.zeta (17 + 2 * b), 0, Impl.MlKem.AArch64.Ntt16.zeta (32 + 4 * b),
    Impl.MlKem.AArch64.Ntt16.zeta (32 + 4 * b + 1), Impl.MlKem.AArch64.Ntt16.zeta (32 + 4 * b + 2),
    Impl.MlKem.AArch64.Ntt16.zeta (32 + 4 * b + 3)]

/-- `blockHalves`, for any zetas `z` and twist `t`: the kernel cannot unfold a
variable, so the lanes below are read off the list's shape alone. -/
def blockHalvesG (z t : Nat → Nat) (b : Nat) : List Nat :=
  let zs := [z (8 + b), z (16 + 2 * b), z (17 + 2 * b), 0] ++
    (List.range 4).map fun j => z (32 + 4 * b + j)
  let z7 := (List.range 8).map fun j => z (64 + 8 * b + j)
  zs ++ zs.map t ++ z7 ++ z7.map t

/-- `zsOf`, for any zetas `z`. -/
def zsOfG (z : Nat → Nat) (b : Nat) : List Nat :=
  [z (8 + b), z (16 + 2 * b), z (17 + 2 * b), 0, z (32 + 4 * b), z (32 + 4 * b + 1), z (32 + 4 * b + 2),
    z (32 + 4 * b + 3)]

theorem blockHalvesG_get (z t : Nat → Nat) (b : Nat) {e : Nat} (he : e < 8) :
    (blockHalvesG z t b).getD e 0 = (zsOfG z b).getD e 0 ∧
    (blockHalvesG z t b).getD (8 + e) 0 = t ((zsOfG z b).getD e 0) ∧
    (blockHalvesG z t b).getD (16 + e) 0 = z (64 + 8 * b + e) ∧
    (blockHalvesG z t b).getD (24 + e) 0 = t (z (64 + 8 * b + e)) := by
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => exact ⟨rfl, rfl, rfl, rfl⟩

theorem blockHalves_get (b : Nat) {e : Nat} (he : e < 8) :
    (blockHalves b).getD e 0 = (zsOf b).getD e 0 ∧
    (blockHalves b).getD (8 + e) 0 = tw ((zsOf b).getD e 0) ∧
    (blockHalves b).getD (16 + e) 0 = Impl.MlKem.AArch64.Ntt16.zeta (64 + 8 * b + e) ∧
    (blockHalves b).getD (24 + e) 0 = tw (Impl.MlKem.AArch64.Ntt16.zeta (64 + 8 * b + e)) :=
  blockHalvesG_get Impl.MlKem.AArch64.Ntt16.zeta tw b he

theorem tableHalves_get {b : Nat} (hb : b < 8) {i : Nat} (hi : i < 32) :
    tableHalves.getD (32 * b + i) 0 = (blockHalves b).getD i 0 :=
  flatMap_getD _ length_blockHalves 8 b i hb hi

/-! ## Offsets -/

/-- The offsets `a, a + 1, …, a + 7`. -/
def seg (a : Nat) : List Nat := (List.range 8).map (a + ·)

theorem seg_getD (a : Nat) {e : Nat} (he : e < 8) : (seg a).getD e 0 = a + e := by
  rw [seg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]; rfl

/-! ## A block -/

/-- After `b` blocks of pass 2, from the memory `mB` that pass 1 left. -/
structure L2 (s₀ : State) (mB : Mem) (b : Nat) (s : State) (t : Addr := sP s₀ + BitVec.ofNat 64 512) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = sP s₀ + BitVec.ofNat 64 (64 * b)
  x6 : s.gpr .x6 = t + BitVec.ofNat 64 (64 * b)
  x4 : s.gpr .x4 = coeffAddr (fP s₀) (32 * b)
  x5 : (s.gpr .x5).toNat = 8 - b
  frame : Frame [polyRegion (fP s₀)] mB s.mem
  tableRead : ∀ o, o+16≤512 → InRegions (s₀.rd++s₀.wr) (t+BitVec.ofNat 64 o) 16
  tableApart : (polyRegion (fP s₀)).Disjoint ⟨t,512⟩
  tab : ∀ j < 64, mB.readW (t + BitVec.ofNat 64 (8 * j)) 64 = hw4 tableHalves j
  scr : ∀ r < 8, ∀ c' < 4, Rep (mB.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * c')) 16)
    (fun e => (nttL 3 (P₀ s₀))[32 * r + 8 * c' + e]!) (4 * 3329)
  out : CoeffsUpTo s.mem (fP s₀) (32 * b)
    (fun i => BitVec.ofNat 32 ((nttL 7 (P₀ s₀))[i]!).val) fun i => coeffAt mB (fP s₀) i
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10
  c0 : Cst (s.v .v29) fun _ => 0

/-- `scratch` as pass 1 left it. -/
theorem L2.read {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} {s : State} {t : Addr} (h : L2 s₀ mB b s t) {o : Nat}
    (ho : o + 16 ≤ 1024) :
    s.mem.read (sP s₀ + BitVec.ofNat 64 o) 16 = mB.read (sP s₀ + BitVec.ofNat 64 o) 16 :=
  h.frame.read (r := polyRegion (sP s₀)) (contains_off ho (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)

theorem L2.readW {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} {s : State} {t : Addr} (h : L2 s₀ mB b s t)
    {o : Nat} (ho : o + 8 ≤ 1024) :
    s.mem.readW (sP s₀ + BitVec.ofNat 64 o) 64 = mB.readW (sP s₀ + BitVec.ofNat 64 o) 64 :=
  h.frame.readW (r := polyRegion (sP s₀)) (contains_off ho (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)

/-- The four vectors of block `b` in `scratch`. -/
theorem L2.ld {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} (hb : b < 8) {s : State} {t : Addr} (h : L2 s₀ mB b s t)
    {i : Nat} (hi : i < 4) :
    IRep (P₀ s₀) 3 (32 * b) (seg (8 * i)) (s.mem.read (sP s₀ + BitVec.ofNat 64 (64 * b + 16 * i)) 16) := by
  rw [h.read hp (by omega)]
  refine (h.scr b hb i hi).congr fun e he => ?_
  rw [seg_getD _ he, Nat.add_assoc]

/-- The table of block `b`. -/
theorem L2.tl {s₀ : State} (_hp : Pre s₀) {mB : Mem} {b : Nat} (hb : b < 8) {s : State} {t : Addr} (h : L2 s₀ mB b s t)
    {i : Nat} (hi : i < 4) {e : Nat} (he : e < 8) :
    vhalf (s.mem.read (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16) e =
      BitVec.ofNat 16 ((blockHalves b).getD (8 * i + e) 0) := by
  have ht : ∀ j < 64, s.mem.readW (t + BitVec.ofNat 64 (8 * j)) 64 = hw4 tableHalves j :=
    fun j hj => by
      rw [h.frame.readW (r:=⟨t,512⟩) (contains_off (by omega) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.tableApart.symm) (by decide)]
      exact h.tab j hj
  have := vhalf_table (off:=0) (by simpa only [Nat.zero_add] using ht) (i := 4 * b + i) (by omega) he
  rw [show 0 + 16 * (4 * b + i) = 64 * b + 16 * i by omega,
    show 8 * (4 * b + i) + e = 32 * b + (8 * i + e) by omega, tableHalves_get hb (by omega)] at this
  exact this

section
variable {rest : List Instr} {Q : State → Prop}

/-- The registers of a block's loads. -/
abbrev ld2Regs : List VReg := [.v0, .v1, .v2, .v3, .v20, .v21, .v22, .v23]

/-- A load, from a state `w` that differs from `s` only in vector registers. -/
theorem ld_step {s w : State} {rs : List VReg} (cw : VChg rs s w) {t : VReg} {n : Reg} {off : Nat}
    {a : Addr} (ho : off % 16 = 0 ∧ off < 4096 * 16) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ w', VChg (rs ++ [t]) s w' → w'.v t = s.mem.read a 16 → (∀ r, r ≠ t → w'.v r = w.v r) →
      WP isa (.block rest) w' Q) :
    WP isa (.block (.ldrq t n off :: rest)) w Q := by
  rw [← cw.gpr] at ha
  rw [← cw.rd, ← cw.wr] at hin
  refine wp_ldrq ho ha hin fun w' h' => k w' (cw.trans h'.chg) (by rw [h'.v, cw.mem]) h'.other

/-- The four vectors of block `b` and its table, from where they are in memory. -/
theorem p2_loadsOf {P : Poly} {b : Nat} {sP t : Addr} {s : State}
    (a2 : ∀ i < 4, s.gpr .x2 + BitVec.ofNat 64 (16 * i) = sP + BitVec.ofNat 64 (64 * b + 16 * i))
    (a6 : ∀ i < 4, s.gpr .x6 + BitVec.ofNat 64 (16 * i) = t + BitVec.ofNat 64 (64 * b + 16 * i))
    (i2 : ∀ i < 4, InRegions (s.rd ++ s.wr) (sP + BitVec.ofNat 64 (64 * b + 16 * i)) 16)
    (i6 : ∀ i < 4, InRegions (s.rd ++ s.wr) (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16)
    (hld : ∀ i < 4, IRep P 3 (32 * b) (seg (8 * i)) (s.mem.read (sP + BitVec.ofNat 64 (64 * b + 16 * i)) 16))
    (htl : ∀ i < 4, ∀ e < 8, vhalf (s.mem.read (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16) e =
      BitVec.ofNat 16 ((blockHalves b).getD (8 * i + e) 0))
    (k : ∀ s', VChg ld2Regs s s' →
      IRep P 3 (32 * b) (seg 0) (s'.v .v0) → IRep P 3 (32 * b) (seg 8) (s'.v .v1) →
      IRep P 3 (32 * b) (seg 16) (s'.v .v2) → IRep P 3 (32 * b) (seg 24) (s'.v .v3) →
      (∀ e < 8, vhalf (s'.v .v20) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 0 + e) 0)) →
      (∀ e < 8, vhalf (s'.v .v21) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 1 + e) 0)) →
      (∀ e < 8, vhalf (s'.v .v22) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 2 + e) 0)) →
      (∀ e < 8, vhalf (s'.v .v23) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 3 + e) 0)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrq .v0 .x2 0 :: .ldrq .v1 .x2 16 :: .ldrq .v2 .x2 32 :: .ldrq .v3 .x2 48 ::
      .ldrq .v20 .x6 0 :: .ldrq .v21 .x6 16 :: .ldrq .v22 .x6 32 :: .ldrq .v23 .x6 48 :: rest)) s Q := by
  refine ld_step (VChg.refl [] s) (by decide) (a2 0 (by decide)) (i2 0 (by decide)) fun s₁ c₁ v₁ o₁ => ?_
  refine ld_step c₁ (by decide) (a2 1 (by decide)) (i2 1 (by decide)) fun s₂ c₂ v₂ o₂ => ?_
  refine ld_step c₂ (by decide) (a2 2 (by decide)) (i2 2 (by decide)) fun s₃ c₃ v₃ o₃ => ?_
  refine ld_step c₃ (by decide) (a2 3 (by decide)) (i2 3 (by decide)) fun s₄ c₄ v₄ o₄ => ?_
  refine ld_step c₄ (by decide) (a6 0 (by decide)) (i6 0 (by decide)) fun s₅ c₅ v₅ o₅ => ?_
  refine ld_step c₅ (by decide) (a6 1 (by decide)) (i6 1 (by decide)) fun s₆ c₆ v₆ o₆ => ?_
  refine ld_step c₆ (by decide) (a6 2 (by decide)) (i6 2 (by decide)) fun s₇ c₇ v₇ o₇ => ?_
  refine ld_step c₇ (by decide) (a6 3 (by decide)) (i6 3 (by decide)) fun s₈ c₈ v₈ o₈ => ?_
  refine k s₈ (c₈.mono (by decide)) ?_ ?_ ?_ ?_ (fun e he => ?_) (fun e he => ?_) (fun e he => ?_)
    (fun e he => ?_)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide),
      o₃ _ (by decide), o₂ _ (by decide), v₁]
    exact hld 0 (by decide)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide),
      o₃ _ (by decide), v₂]
    exact hld 1 (by decide)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide), v₃]
    exact hld 2 (by decide)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), v₄]
    exact hld 3 (by decide)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), v₅]
    exact htl 0 (by decide) e he
  · rw [o₈ _ (by decide), o₇ _ (by decide), v₆]
    exact htl 1 (by decide) e he
  · rw [o₈ _ (by decide), v₇]
    exact htl 2 (by decide) e he
  · rw [v₈]
    exact htl 3 (by decide) e he

/-- The four vectors of block `b` and its table. -/
theorem p2_loads {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} (hb : b < 8) {s : State}
    {t : Addr} (h : L2 s₀ mB b s t)
    (k : ∀ s', VChg ld2Regs s s' →
      IRep (P₀ s₀) 3 (32 * b) (seg 0) (s'.v .v0) → IRep (P₀ s₀) 3 (32 * b) (seg 8) (s'.v .v1) →
      IRep (P₀ s₀) 3 (32 * b) (seg 16) (s'.v .v2) → IRep (P₀ s₀) 3 (32 * b) (seg 24) (s'.v .v3) →
      (∀ e < 8, vhalf (s'.v .v20) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 0 + e) 0)) →
      (∀ e < 8, vhalf (s'.v .v21) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 1 + e) 0)) →
      (∀ e < 8, vhalf (s'.v .v22) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 2 + e) 0)) →
      (∀ e < 8, vhalf (s'.v .v23) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 3 + e) 0)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrq .v0 .x2 0 :: .ldrq .v1 .x2 16 :: .ldrq .v2 .x2 32 :: .ldrq .v3 .x2 48 ::
      .ldrq .v20 .x6 0 :: .ldrq .v21 .x6 16 :: .ldrq .v22 .x6 32 :: .ldrq .v23 .x6 48 :: rest)) s Q := by
  have a2 : ∀ i < 4, s.gpr .x2 + BitVec.ofNat 64 (16 * i) = sP s₀ + BitVec.ofNat 64 (64 * b + 16 * i) :=
    fun i _ => by rw [h.x2, ptr_add]
  have a6 : ∀ i < 4, s.gpr .x6 + BitVec.ofNat 64 (16 * i) =
      t + BitVec.ofNat 64 (64 * b + 16 * i) := fun i _ => by rw [h.x6, ptr_add]
  have i2 : ∀ i < 4, InRegions (s.rd ++ s.wr) (sP s₀ + BitVec.ofNat 64 (64 * b + 16 * i)) 16 :=
    fun i _ => inS' hp h.st (by omega)
  have i6 : ∀ i < 4, InRegions (s.rd ++ s.wr) (t + BitVec.ofNat 64 (64 * b + 16 * i)) 16 :=
    fun i hi => by
      rw [h.st.rd,h.st.wr]
      exact h.tableRead _ (by omega)
  exact p2_loadsOf a2 a6 i2 i6 (fun i hi => h.ld hp hb hi) (fun i hi e he => h.tl hp hb hi he) k

/-! ## Zetas -/

theorem zrep_dup {x : BitVec 128} {k K K₀ : Nat} {kz : List Nat}
    (hx : vhalf x k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta K))
    (hK : ∀ e < 8, K₀ + kz.getD e 0 = K) : ZRep (ofVHalves fun _ => vhalf x k) K₀ kz :=
  fun e he => by dsimp only; rw [vhalf_ofVHalves _ he, hx, hK e he]

theorem trep_dup {x : BitVec 128} {k K K₀ : Nat} {kz : List Nat}
    (hx : vhalf x k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta K)))
    (hK : ∀ e < 8, K₀ + kz.getD e 0 = K) : TRep (ofVHalves fun _ => vhalf x k) K₀ kz :=
  fun e he => by dsimp only; rw [vhalf_ofVHalves _ he, hx, hK e he]

theorem zrep_zip2_tab {x : BitVec 128} {b : Nat}
    (hx : ∀ e < 8, vhalf x e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 0 + e) 0)) :
    ZRep (VPermOp.eval .zip2 .h8 x x) (32 + 4 * b) [0, 0, 1, 1, 2, 2, 3, 3] := fun e he => by
  rw [vhalf_perm_h8 _ _ _ he]
  simp only [ite_self]
  rw [hx _ (by omega), show 8 * 0 + (4 + e / 2) = 4 + e / 2 by omega,
    (blockHalves_get b (e := 4 + e / 2) (by omega)).1]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

theorem trep_zip2_tab {x : BitVec 128} {b : Nat}
    (hx : ∀ e < 8, vhalf x e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 1 + e) 0)) :
    TRep (VPermOp.eval .zip2 .h8 x x) (32 + 4 * b) [0, 0, 1, 1, 2, 2, 3, 3] := fun e he => by
  rw [vhalf_perm_h8 _ _ _ he]
  simp only [ite_self]
  rw [hx _ (by omega), show 8 * 1 + (4 + e / 2) = 8 + (4 + e / 2) by omega,
    (blockHalves_get b (e := 4 + e / 2) (by omega)).2.1]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

theorem zrep_z7 {x : BitVec 128} {b : Nat}
    (hx : ∀ e < 8, vhalf x e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 2 + e) 0)) :
    ZRep x (64 + 8 * b) (seg 0) := fun e he => by
  dsimp only
  rw [hx e he, seg_getD _ he, Nat.zero_add, show 8 * 2 + e = 16 + e by omega,
    (blockHalves_get b he).2.2.1]

theorem trep_z7 {x : BitVec 128} {b : Nat}
    (hx : ∀ e < 8, vhalf x e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 3 + e) 0)) :
    TRep x (64 + 8 * b) (seg 0) := fun e he => by
  dsimp only
  rw [hx e he, seg_getD _ he, Nat.zero_add, show 8 * 3 + e = 24 + e by omega,
    (blockHalves_get b he).2.2.2]

theorem row_ne2425 : ∀ i < 8, row i ≠ .v24 ∧ row i ≠ .v25 := by decide

/-- The registers of a block's arithmetic. -/
abbrev arRegs : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v16, .v17, .v19, .v24, .v25, .v26, .v27, .v28]

/-- The zeta `K` and its `tw` in lane `k` of the table vectors. -/
theorem lane_zt {s : State} {b k K : Nat} {x y : VReg}
    (hx : ∀ e < 8, vhalf (s.v x) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 0 + e) 0))
    (hy : ∀ e < 8, vhalf (s.v y) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 1 + e) 0))
    (hk : k < 8) (hK : (zsOf b).getD k 0 = Impl.MlKem.AArch64.Ntt16.zeta K) :
    vhalf (s.v x) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta K) ∧
    vhalf (s.v y) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta K)) := by
  rw [hx k hk, hy k hk, show 8 * 0 + k = k by omega, (blockHalves_get b hk).1, (blockHalves_get b hk).2.1, hK]
  exact ⟨rfl, rfl⟩

/-- The four layers of block `b` and the reduction of each lane (`pass2Arith`), from its four
vectors after pass 1 and its table. -/
theorem p2_arith {rest : List Instr} {Q : State → Prop} {P : Poly} {b : Nat} (hb : b < 8) {s : State}
    (a0 : IRep P 3 (32 * b) (seg 0) (s.v .v0)) (a1 : IRep P 3 (32 * b) (seg 8) (s.v .v1))
    (a2 : IRep P 3 (32 * b) (seg 16) (s.v .v2)) (a3 : IRep P 3 (32 * b) (seg 24) (s.v .v3))
    (t20 : ∀ e < 8, vhalf (s.v .v20) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 0 + e) 0))
    (t21 : ∀ e < 8, vhalf (s.v .v21) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 1 + e) 0))
    (t22 : ∀ e < 8, vhalf (s.v .v22) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 2 + e) 0))
    (t23 : ∀ e < 8, vhalf (s.v .v23) e = BitVec.ofNat 16 ((blockHalves b).getD (8 * 3 + e) 0))
    (hq : Cst (s.v .v31) fun _ => 3329) (h10 : Cst (s.v .v30) fun _ => 10)
    (kk : ∀ s₂₆, VChg arRegs s s₂₆ →
      (∀ i < 4, ∀ e < 8, (vhalf (s₂₆.v (row i)) e).toNat = ((nttL 7 P)[32 * b + 8 * i + e]!).val) →
      WP isa (.block rest) s₂₆ Q) :
    WP isa (.block (pass2Arith ++ rest)) s Q := by
  simp only [pass2Arith, List.cons_append, List.nil_append, List.append_assoc, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  have hb0 : 32 * b % 32 = 0 := by omega
  have hb1 : 32 * b + 32 ≤ 256 := by omega
  have Z0 := lane_zt (k := 0) (K := 8 + b) t20 t21 (by decide) rfl
  have Z1 := lane_zt (k := 1) (K := 16 + 2 * b) t20 t21 (by decide) rfl
  have Z2 := lane_zt (k := 2) (K := 17 + 2 * b) t20 t21 (by decide) rfl
  -- layer 4
  refine wp_vop (eval_dupE (by decide)) fun s₁ h₁ => wp_vop (eval_dupE (by decide)) fun s₂ h₂ => ?_
  have c₂ : VChg [.v24, .v25] s s₂ := h₁.chg.trans h₂.chg
  refine irep_bf (x := .v0) (y := .v2) (z := .v24) (t := .v25) (ox := seg 0) (oy := seg 16) (j := 3) (K₀ := 8 + b) (kz := List.replicate 8 0) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK := by simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hx := by rw [c₂.get .v0]; exact a0) (hy := by rw [c₂.get .v2]; exact a2)
    (hz := by rw [h₂.get .v24, h₁.v]; exact zrep_dup Z0.1 fun e he => by simp only [getD_rep_lt he]; omega)
    (ht := by rw [h₂.v, h₁.get .v21]; exact trep_dup Z0.2 fun e he => by simp only [getD_rep_lt he]; omega)
    (hq := by rw [c₂.get .v31]; exact hq) (k := fun s₃ c₃ b0 b2 => ?_)
  refine irep_bf (x := .v1) (y := .v3) (z := .v24) (t := .v25) (ox := seg 8) (oy := seg 24) (j := 3) (K₀ := 8 + b) (kz := List.replicate 8 0) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK := by simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hx := by rw [c₃.get .v1, c₂.get .v1]; exact a1) (hy := by rw [c₃.get .v3, c₂.get .v3]; exact a3)
    (hz := by rw [c₃.get .v24, h₂.get .v24, h₁.v]; exact zrep_dup Z0.1 fun e he => by simp only [getD_rep_lt he]; omega)
    (ht := by rw [c₃.get .v25, h₂.v, h₁.get .v21]; exact trep_dup Z0.2 fun e he => by simp only [getD_rep_lt he]; omega)
    (hq := by rw [c₃.get .v31, c₂.get .v31]; exact hq) (k := fun s₄ c₄ b1 b3 => ?_)
  have C₄ : VChg ([.v24, .v25] ++ [.v16, .v17, .v16, .v2, .v0] ++ [.v16, .v17, .v16, .v3, .v1]) s s₄ :=
    (c₂.trans c₃).trans c₄
  -- layer 5
  refine wp_vop (eval_dupE (by decide)) fun s₅ h₅ => wp_vop (eval_dupE (by decide)) fun s₆ h₆ => ?_
  have c₆ : VChg [.v24, .v25] s₄ s₆ := h₅.chg.trans h₆.chg
  refine irep_bf (x := .v0) (y := .v1) (z := .v24) (t := .v25) (ox := seg 0) (oy := seg 8) (j := 4) (K₀ := 16 + 2 * b) (kz := List.replicate 8 0) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK := by simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hx := by rw [c₆.get .v0, c₄.get .v0]; exact b0) (hy := by rw [c₆.get .v1]; exact b1)
    (hz := by rw [h₆.get .v24, h₅.v, C₄.get .v20]; exact zrep_dup Z1.1 fun e he => by simp only [getD_rep_lt he]; omega)
    (ht := by rw [h₆.v, h₅.get .v21, C₄.get .v21]; exact trep_dup Z1.2 fun e he => by simp only [getD_rep_lt he]; omega)
    (hq := by rw [c₆.get .v31, C₄.get .v31]; exact hq) (k := fun s₇ c₇ d0 d1 => ?_)
  refine wp_vop (eval_dupE (by decide)) fun s₈ h₈ => wp_vop (eval_dupE (by decide)) fun s₉ h₉ => ?_
  have C₇ : VChg ([.v24, .v25] ++ [.v16, .v17, .v16, .v1, .v0]) s₄ s₇ := c₆.trans c₇
  have c₉ : VChg [.v24, .v25] s₇ s₉ := h₈.chg.trans h₉.chg
  refine irep_bf (x := .v2) (y := .v3) (z := .v24) (t := .v25) (ox := seg 16) (oy := seg 24) (j := 4) (K₀ := 16 + 2 * b) (kz := List.replicate 8 1) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK := by simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hx := by rw [c₉.get .v2, C₇.get .v2, c₄.get .v2]; exact b2) (hy := by rw [c₉.get .v3, C₇.get .v3]; exact b3)
    (hz := by rw [h₉.get .v24, h₈.v, C₇.get .v20, C₄.get .v20]; exact zrep_dup Z2.1 fun e he => by simp only [getD_rep_lt he]; omega)
    (ht := by rw [h₉.v, h₈.get .v21, C₇.get .v21, C₄.get .v21]; exact trep_dup Z2.2 fun e he => by simp only [getD_rep_lt he]; omega)
    (hq := by rw [c₉.get .v31, C₇.get .v31, C₄.get .v31]; exact hq) (k := fun s₁₀ c₁₀ d2 d3 => ?_)
  have C₁₀ : VChg ([.v24, .v25] ++ [.v16, .v17, .v16, .v3, .v2]) s₇ s₁₀ := c₉.trans c₁₀
  have g₁₀ : ∀ r, r ∉ [VReg.v0, .v1, .v2, .v3, .v16, .v17, .v24, .v25] → s₁₀.v r = s.v r := fun r hr => by
    rw [C₁₀.get r (by simp_all), C₇.get r (by simp_all), C₄.get r (by simp_all)]
  -- the zetas of layers 6 and 7 for the first half
  refine wp_vop rfl fun s₁₁ h₁₁ => wp_vop rfl fun s₁₂ h₁₂ => wp_vop rfl fun s₁₃ h₁₃ =>
    wp_vop rfl fun s₁₄ h₁₄ => wp_vop rfl fun s₁₅ h₁₅ => wp_vop rfl fun s₁₆ h₁₆ => ?_
  have cz : VChg [.v24, .v25, .v26, .v27, .v28, .v19] s₁₀ s₁₆ :=
    ((((h₁₁.chg.trans h₁₂.chg).trans h₁₃.chg).trans h₁₄.chg).trans h₁₅.chg).trans h₁₆.chg |>.mono
  have z24 : ZRep (s₁₆.v .v24) (32 + 4 * b) [0, 0, 1, 1, 2, 2, 3, 3] := by
    rw [h₁₆.get .v24, h₁₅.get .v24, h₁₄.get .v24, h₁₃.get .v24, h₁₂.get .v24, h₁₁.v]
    exact zrep_zip2_tab fun e he => by rw [g₁₀ .v20 (by decide)]; exact t20 e he
  have t25 : TRep (s₁₆.v .v25) (32 + 4 * b) [0, 0, 1, 1, 2, 2, 3, 3] := by
    rw [h₁₆.get .v25, h₁₅.get .v25, h₁₄.get .v25, h₁₃.get .v25, h₁₂.v, h₁₁.get .v21]
    exact trep_zip2_tab fun e he => by rw [g₁₀ .v21 (by decide)]; exact t21 e he
  have z22 : ZRep (s₁₆.v .v22) (64 + 8 * b) (seg 0) := by
    rw [cz.get .v22, g₁₀ .v22 (by decide)]; exact zrep_z7 t22
  have t23' : TRep (s₁₆.v .v23) (64 + 8 * b) (seg 0) := by
    rw [cz.get .v23, g₁₀ .v23 (by decide)]; exact trep_z7 t23
  have z26 : ZRep (s₁₆.v .v26) (32 + 4 * b) [0, 0, 0, 0, 1, 1, 1, 1] := by
    rw [h₁₆.get .v26, h₁₅.get .v26, h₁₄.get .v26, h₁₃.v, h₁₂.get .v24]
    have z := (by rw [h₁₆.get .v24, h₁₅.get .v24, h₁₄.get .v24, h₁₃.get .v24, h₁₂.get .v24] at z24
                  exact z24 : ZRep (s₁₁.v .v24) _ _)
    exact zrep_perm (src_s4 .zip1 _ _) (by decide) z z (by decide)
  have t27 : TRep (s₁₆.v .v27) (32 + 4 * b) [0, 0, 0, 0, 1, 1, 1, 1] := by
    rw [h₁₆.get .v27, h₁₅.get .v27, h₁₄.v, h₁₃.get .v25]
    have t := (by rw [h₁₆.get .v25, h₁₅.get .v25, h₁₄.get .v25, h₁₃.get .v25] at t25
                  exact t25 : TRep (s₁₂.v .v25) _ _)
    exact trep_perm (src_s4 .zip1 _ _) (by decide) t t (by decide)
  have z28 : ZRep (s₁₆.v .v28) (64 + 8 * b) [0, 0, 1, 1, 2, 2, 3, 3] := by
    rw [h₁₆.get .v28, h₁₅.v, h₁₄.get .v22, h₁₃.get .v22, h₁₂.get .v22, h₁₁.get .v22, g₁₀ .v22 (by decide)]
    exact zrep_perm (src_h8 .zip1 _ _) (by decide) (zrep_z7 t22) (zrep_z7 t22) (by decide)
  have t19 : TRep (s₁₆.v .v19) (64 + 8 * b) [0, 0, 1, 1, 2, 2, 3, 3] := by
    rw [h₁₆.v, h₁₅.get .v23, h₁₄.get .v23, h₁₃.get .v23, h₁₂.get .v23, h₁₁.get .v23,
      g₁₀ .v23 (by decide)]
    exact trep_perm (src_h8 .zip1 _ _) (by decide) (trep_z7 t23) (trep_z7 t23) (by decide)
  have q₁₆ : Cst (s₁₆.v .v31) fun _ => 3329 := by rw [cz.get .v31, g₁₀ .v31 (by decide)]; exact hq
  refine lastTwo_ok (p := .v0) (q' := .v1) (z6 := .v26) (t6 := .v27) (z7 := .v28) (t7 := .v19)
    (op := seg 0) (oq := seg 8) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK6 := by simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hK7 := by simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hp := by rw [cz.get .v0, C₁₀.get .v0]; exact d0) (hq' := by rw [cz.get .v1, C₁₀.get .v1]; exact d1)
    (hz6 := z26) (ht6 := t27) (hz7 := z28) (ht7 := t19) (hq := q₁₆) (k := fun s₁₇ c₁₇ e0 e1 => ?_)
  -- the zetas of layers 6 and 7 for the second half
  refine wp_vop rfl fun s₁₈ h₁₈ => wp_vop rfl fun s₁₉ h₁₉ => wp_vop rfl fun s₂₀ h₂₀ =>
    wp_vop rfl fun s₂₁ h₂₁ => ?_
  have cw : VChg [.v26, .v27, .v28, .v19] s₁₇ s₂₁ :=
    (((h₁₈.chg.trans h₁₉.chg).trans h₂₀.chg).trans h₂₁.chg).mono
  have g₁₇ : ∀ r, r ∉ lastRegs .v0 .v1 → s₁₇.v r = s₁₆.v r := fun r hr => c₁₇.get r hr
  have z26' : ZRep (s₂₁.v .v26) (32 + 4 * b) [2, 2, 2, 2, 3, 3, 3, 3] := by
    rw [h₂₁.get .v26, h₂₀.get .v26, h₁₉.get .v26, h₁₈.v, g₁₇ .v24 (by decide)]
    exact zrep_perm (src_s4 .zip2 _ _) (by decide) z24 z24 (by decide)
  have t27' : TRep (s₂₁.v .v27) (32 + 4 * b) [2, 2, 2, 2, 3, 3, 3, 3] := by
    rw [h₂₁.get .v27, h₂₀.get .v27, h₁₉.v, h₁₈.get .v25, g₁₇ .v25 (by decide)]
    exact trep_perm (src_s4 .zip2 _ _) (by decide) t25 t25 (by decide)
  have z28' : ZRep (s₂₁.v .v28) (64 + 8 * b) [4, 4, 5, 5, 6, 6, 7, 7] := by
    rw [h₂₁.get .v28, h₂₀.v, h₁₉.get .v22, h₁₈.get .v22, g₁₇ .v22 (by decide)]
    exact zrep_perm (src_h8 .zip2 _ _) (by decide) z22 z22 (by decide)
  have t19' : TRep (s₂₁.v .v19) (64 + 8 * b) [4, 4, 5, 5, 6, 6, 7, 7] := by
    rw [h₂₁.v, h₂₀.get .v23, h₁₉.get .v23, h₁₈.get .v23, g₁₇ .v23 (by decide)]
    exact trep_perm (src_h8 .zip2 _ _) (by decide) t23' t23' (by decide)
  refine lastTwo_ok (p := .v2) (q' := .v3) (z6 := .v26) (t6 := .v27) (z7 := .v28) (t7 := .v19)
    (op := seg 16) (oq := seg 24) (hok := by decide) (hb := hb0) (hb' := hb1)
    (hK6 := by simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hK7 := by simp only [Nat.reduceShiftRight, Nat.reduceMul, Nat.reduceDiv]; omega)
    (hp := by rw [cw.get .v2, g₁₇ .v2 (by decide), cz.get .v2]; exact d2)
    (hq' := by rw [cw.get .v3, g₁₇ .v3 (by decide), cz.get .v3]; exact d3)
    (hz6 := z26') (ht6 := t27') (hz7 := z28') (ht7 := t19')
    (hq := by rw [cw.get .v31, g₁₇ .v31 (by decide)]; exact q₁₆) (k := fun s₂₂ c₂₂ e2 e3 => ?_)
  -- each lane reduced
  have g₂₂ : ∀ r, r ∉ [VReg.v4, .v5, .v16, .v17, .v2, .v3, .v26, .v27, .v28, .v19] →
      s₂₂.v r = s₁₇.v r := fun r hr => by
    rw [c₂₂.get r (by simp_all), cw.get r (by simp_all)]
  have hB : (7 + 1) * 3329 ≤ 32768 := by decide
  have q₂₂ : Cst (s₂₂.v .v31) fun _ => 3329 := by rw [g₂₂ .v31 (by decide), g₁₇ .v31 (by decide)]; exact q₁₆
  have k₂₂ : Cst (s₂₂.v .v30) fun _ => 10 := by
    rw [g₂₂ .v30 (by decide), g₁₇ .v30 (by decide), cz.get .v30, g₁₀ .v30 (by decide)]; exact h10
  refine norm_ok (x := .v0) (hx := by rw [g₂₂ .v0 (by decide)]; exact e0) (hB := hB) (h10 := k₂₂)
    (hq := q₂₂) (k := fun s₂₃ c₂₃ n0 => ?_)
  refine norm_ok (x := .v1) (hx := by rw [c₂₃.get .v1, g₂₂ .v1 (by decide)]; exact e1) (hB := hB)
    (h10 := by rw [c₂₃.get .v30]; exact k₂₂) (hq := by rw [c₂₃.get .v31]; exact q₂₂)
    (k := fun s₂₄ c₂₄ n1 => ?_)
  refine norm_ok (x := .v2) (hx := by rw [c₂₄.get .v2, c₂₃.get .v2]; exact e2) (hB := hB)
    (h10 := by rw [c₂₄.get .v30, c₂₃.get .v30]; exact k₂₂)
    (hq := by rw [c₂₄.get .v31, c₂₃.get .v31]; exact q₂₂) (k := fun s₂₅ c₂₅ n2 => ?_)
  refine norm_ok (x := .v3) (hx := by rw [c₂₅.get .v3, c₂₄.get .v3, c₂₃.get .v3]; exact e3) (hB := hB)
    (h10 := by rw [c₂₅.get .v30, c₂₄.get .v30, c₂₃.get .v30]; exact k₂₂)
    (hq := by rw [c₂₅.get .v31, c₂₄.get .v31, c₂₃.get .v31]; exact q₂₂) (k := fun s₂₆ c₂₆ n3 => ?_)
  have out : ∀ i < 4, ∀ e < 8,
      (vhalf (s₂₆.v (row i)) e).toNat = ((nttL 7 P)[32 * b + 8 * i + e]!).val := by
    intro i hi e he
    have fix : ∀ a, (nttL 7 P)[32 * b + (seg a).getD e 0]! = (nttL 7 P)[32 * b + a + e]! :=
      fun a => by rw [seg_getD _ he, Nat.add_assoc]
    match i, hi with
    | 0, _ => rw [show row 0 = .v0 from rfl, c₂₆.get .v0, c₂₅.get .v0, c₂₄.get .v0, n0 e he, fix]
    | 1, _ => rw [show row 1 = .v1 from rfl, c₂₆.get .v1, c₂₅.get .v1, n1 e he, fix]
    | 2, _ => rw [show row 2 = .v2 from rfl, c₂₆.get .v2, n2 e he, fix]
    | 3, _ => rw [show row 3 = .v3 from rfl, n3 e he, fix]
  exact kk s₂₆ ((((((((((C₄.trans C₇).trans C₁₀).trans cz).trans c₁₇).trans cw).trans c₂₂).trans
    c₂₃).trans c₂₄).trans c₂₅).trans c₂₆).mono out

theorem p2_body {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} (hb : b < 8) {sb : State}
    {t : Addr} (h : L2 s₀ mB b sb t) :
    WP isa (.block pass2Body) sb fun s' => L2 s₀ mB (b + 1) s' t ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ b + 1 ≠ 8) := by
  simp only [pass2Body, pass2Loads, List.cons_append, List.nil_append, List.append_assoc]
  refine p2_loads hp hb h fun s c₀ a0 a1 a2 a3 t20 t21 t22 t23 => ?_
  refine p2_arith hb a0 a1 a2 a3 t20 t21 t22 t23 (by rw [c₀.get .v31]; exact h.q)
    (by rw [c₀.get .v30]; exact h.c10) fun s₂₆ C' out => ?_
  have CC := c₀.trans C'
  have st₂₆ : St s₀ s₂₆ := h.st.vchg CC
  have z29 : ∀ e < 8, vhalf (s₂₆.v .v29) e = 0 := fun e he => by
    rw [CC.get .v29 (by simp)]; exact h.c0 e he
  -- the stores
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun i w => w.gpr = s₂₆.gpr ∧ w.rd = s₂₆.rd ∧
      w.wr = s₂₆.wr ∧ w.sp = s₂₆.sp ∧ (∀ r, r ≠ .v24 → r ≠ .v25 → w.v r = s₂₆.v r) ∧
      Frame [polyRegion (fP s₀)] s₂₆.mem w.mem ∧
      CoeffsUpTo w.mem (fP s₀) (32 * b + 8 * i)
        (fun i => BitVec.ofNat 32 ((nttL 7 (P₀ s₀))[i]!).val) fun i => coeffAt mB (fP s₀) i)
    (fun i w hi ⟨g, r, wr, sp, v, fr, co⟩ => ?_) 4 (Nat.le_refl _) s₂₆
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _, by
      rw [Nat.add_zero, CC.mem]; exact h.out⟩) fun w ⟨g, r, wr, sp, v, fr, co⟩ => ?_
  · have st : St s₀ w := ⟨by rw [r, st₂₆.rd], by rw [wr, st₂₆.wr], by rw [sp, st₂₆.sp],
      by rw [g, st₂₆.x0], by rw [g, st₂₆.x1]⟩
    have x4 : w.gpr .x4 = coeffAddr (fP s₀) (32 * b) := by
      rw [g, CC.gpr]; exact h.x4
    have hi8 : 32 * b + 8 * i + 8 ≤ 256 := by omega
    refine wp_vop rfl fun w₁ h₁ => wp_vop rfl fun w₂ h₂ => ?_
    refine wp_strq (a := coeffAddr (fP s₀) (32 * b + 8 * i)) (by omega)
      (by rw [h₂.gpr, h₁.gpr, x4, coeffAddr, coeffAddr, ptr_add]; congr 2; omega)
      (by rw [h₂.wr, h₁.wr]; exact inF' hp st (by omega)) fun w₃ h₃ => ?_
    refine wp_strq (a := coeffAddr (fP s₀) (32 * b + 8 * i + 4)) (by omega)
      (by rw [h₃.gpr, h₂.gpr, h₁.gpr, x4, coeffAddr, coeffAddr, ptr_add]; congr 2; omega)
      (by rw [h₃.wr, h₂.wr, h₁.wr]; exact inF' hp st (by omega)) fun w₄ h₄ => wp_nil ?_
    have rn := row_ne2425 i (by omega)
    have row_i : w.v (row i) = s₂₆.v (row i) := v _ rn.1 rn.2
    have v29 : w.v .v29 = s₂₆.v .v29 := v _ (by decide) (by decide)
    have zz := fun k (hk : k < 4) => vword_zip_zero (x := w.v (row i)) (z := w.v .v29)
      (by rw [v29]; exact z29) hk
    have hv : ∀ e < 8, ((nttL 7 (P₀ s₀))[32 * b + 8 * i + e]!).val < 2 ^ 32 := fun e _ => by
      have := val_lt ((nttL 7 (P₀ s₀))[32 * b + 8 * i + e]!); omega
    refine ⟨by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, g], by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd, r],
      by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, wr], by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp, sp],
      fun r' a1 a2 => by rw [h₄.v, h₃.v, h₂.get r' a2, h₁.get r' a1, v r' a1 a2], ?_, ?_⟩
    · rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
      exact (fr.write (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))).write
        (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))
    · rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₃.v, show 32 * b + 8 * (i + 1) = 32 * b + 8 * i + 4 + 4 by omega]
      refine (co.write16 (by omega) fun e he => ?_).write16 (by omega) fun e he => ?_
      · rw [h₂.get .v24, h₁.v]
        apply BitVec.eq_of_toNat_eq
        rw [(zz e he).1, BitVec.toNat_ofNat, row_i, out i hi e (by omega), Nat.mod_eq_of_lt (hv e (by omega))]
      · rw [h₂.v, h₁.get (row i) rn.1, h₁.get .v29]
        apply BitVec.eq_of_toNat_eq
        rw [(zz e he).2, BitVec.toNat_ofNat, row_i, out i hi (4 + e) (by omega),
          show 32 * b + 8 * i + 4 + e = 32 * b + 8 * i + (4 + e) by omega,
          Nat.mod_eq_of_lt (hv (4 + e) (by omega))]
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x6, .x4, .x5] w w' ∧ w'.mem = w.mem ∧
      w'.gpr .x2 = w.gpr .x2 + BitVec.ofNat 64 64 ∧ w'.gpr .x6 = w.gpr .x6 + BitVec.ofNat 64 64 ∧
      w'.gpr .x4 = w.gpr .x4 + BitVec.ofNat 64 128 ∧ w'.gpr .x5 = w.gpr .x5 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_addImm (by decide) fun w₃ k₃ e₃ => wp_subImm (by decide) fun w₄ k₄ e₄ =>
        wp_nil ⟨(((k₁.keep.trans k₂.keep).trans k₃.keep).trans k₄.keep).mono,
          by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem],
          by rw [k₄.gpr .x2 (by decide), k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), e₁],
          by rw [k₄.gpr .x6 (by decide), k₃.gpr .x6 (by decide), e₂, k₁.gpr .x6 (by decide)],
          by rw [k₄.gpr .x4 (by decide), e₃, k₂.gpr .x4 (by decide), k₁.gpr .x4 (by decide)],
          by rw [e₄, k₃.gpr .x5 (by decide), k₂.gpr .x5 (by decide), k₁.gpr .x5 (by decide)]⟩))
    fun w' ⟨⟨kw, mw, e2, e6, e4, e5⟩, hv⟩ => ?_
  have gw : w.gpr = sb.gpr := by rw [g, CC.gpr]
  have x5' : (w'.gpr .x5).toNat = 8 - (b + 1) := by
    rw [e5, gw, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  have st : St s₀ w := ⟨by rw [r, st₂₆.rd], by rw [wr, st₂₆.wr], by rw [sp, st₂₆.sp],
    by rw [g, st₂₆.x0], by rw [g, st₂₆.x1]⟩
  have vv : ∀ r ∈ [VReg.v29, .v30, .v31], w'.v r = sb.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [hv, v _ (by decide) (by decide), CC.get _ (by decide)]
  refine ⟨⟨st.keep kw, by rw [e2, gw, h.x2, ptr_add]; congr 2,
    by rw [e6, gw, h.x6, ptr_add]; congr 2,
    by rw [e4, gw, h.x4, coeffAddr, coeffAddr, ptr_add]; congr 2, x5',
    by rw [mw]; exact h.frame.trans (by rw [← CC.mem]; exact fr), h.tableRead, h.tableApart, h.tab, h.scr,
    by rw [mw, show 32 * (b + 1) = 32 * b + 8 * 4 by omega]; exact co,
    by rw [vv .v31 (by decide)]; exact h.q, by rw [vv .v30 (by decide)]; exact h.c10,
    by rw [vv .v29 (by decide)]; exact h.c0⟩, by rw [x5']; omega⟩

end

end VG.Proof.MlKem.AArch64.Ntt16
