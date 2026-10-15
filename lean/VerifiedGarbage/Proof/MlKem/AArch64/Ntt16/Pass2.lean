module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass1
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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

theorem blockHalves_get (b : Nat) {e : Nat} (he : e < 8) :
    (blockHalves b).getD e 0 = (zsOf b).getD e 0 ∧
    (blockHalves b).getD (8 + e) 0 = tw ((zsOf b).getD e 0) ∧
    (blockHalves b).getD (16 + e) 0 = Impl.MlKem.AArch64.Ntt16.zeta (64 + 8 * b + e) ∧
    (blockHalves b).getD (24 + e) 0 = tw (Impl.MlKem.AArch64.Ntt16.zeta (64 + 8 * b + e)) := by
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [blockHalves, zsOf, List.range_succ]

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
structure L2 (s₀ : State) (mB : Mem) (b : Nat) (s : State) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = sP s₀ + BitVec.ofNat 64 (64 * b)
  x6 : s.gpr .x6 = sP s₀ + BitVec.ofNat 64 (512 + 64 * b)
  x4 : s.gpr .x4 = coeffAddr (fP s₀) (32 * b)
  x5 : (s.gpr .x5).toNat = 8 - b
  frame : Frame [polyRegion (fP s₀)] mB s.mem
  tab : ∀ j < 64, mB.readW (sP s₀ + BitVec.ofNat 64 (512 + 8 * j)) 64 = hw4 tableHalves j
  scr : ∀ r < 8, ∀ c' < 4, Rep (mB.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * c')) 16)
    (fun e => (nttL 3 (P₀ s₀))[32 * r + 8 * c' + e]!) (4 * 3329)
  out : CoeffsUpTo s.mem (fP s₀) (32 * b)
    (fun i => BitVec.ofNat 32 ((nttL 7 (P₀ s₀))[i]!).val) fun i => coeffAt mB (fP s₀) i
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10
  c0 : Cst (s.v .v29) fun _ => 0

/-- `scratch` as pass 1 left it. -/
theorem L2.read {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} {s : State} (h : L2 s₀ mB b s) {o : Nat}
    (ho : o + 16 ≤ 1024) :
    s.mem.read (sP s₀ + BitVec.ofNat 64 o) 16 = mB.read (sP s₀ + BitVec.ofNat 64 o) 16 :=
  h.frame.read (r := polyRegion (sP s₀)) (contains_off ho (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)

theorem L2.readW {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} {s : State} (h : L2 s₀ mB b s)
    {o : Nat} (ho : o + 8 ≤ 1024) :
    s.mem.readW (sP s₀ + BitVec.ofNat 64 o) 64 = mB.readW (sP s₀ + BitVec.ofNat 64 o) 64 :=
  h.frame.readW (r := polyRegion (sP s₀)) (contains_off ho (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)

/-- The four vectors of block `b` in `scratch`. -/
theorem L2.ld {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} (hb : b < 8) {s : State} (h : L2 s₀ mB b s)
    {i : Nat} (hi : i < 4) :
    IRep (P₀ s₀) 3 (32 * b) (seg (8 * i)) (s.mem.read (sP s₀ + BitVec.ofNat 64 (64 * b + 16 * i)) 16) := by
  rw [h.read hp (by omega)]
  refine (h.scr b hb i hi).congr fun e he => ?_
  rw [seg_getD _ he, Nat.add_assoc]

/-- The table of block `b`. -/
theorem L2.tl {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} (hb : b < 8) {s : State} (h : L2 s₀ mB b s)
    {i : Nat} (hi : i < 4) {e : Nat} (he : e < 8) :
    vhalf (s.mem.read (sP s₀ + BitVec.ofNat 64 (512 + 64 * b + 16 * i)) 16) e =
      BitVec.ofNat 16 ((blockHalves b).getD (8 * i + e) 0) := by
  have ht : ∀ j < 64, s.mem.readW (sP s₀ + BitVec.ofNat 64 (512 + 8 * j)) 64 = hw4 tableHalves j :=
    fun j hj => by rw [h.readW hp (by omega)]; exact h.tab j hj
  have := vhalf_table ht (i := 4 * b + i) (by omega) he
  rw [show 512 + 16 * (4 * b + i) = 512 + 64 * b + 16 * i by omega,
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

/-- The four vectors of block `b` and its table. -/
theorem p2_loads {s₀ : State} (hp : Pre s₀) {mB : Mem} {b : Nat} (hb : b < 8) {s : State}
    (h : L2 s₀ mB b s)
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
      sP s₀ + BitVec.ofNat 64 (512 + 64 * b + 16 * i) := fun i _ => by rw [h.x6, ptr_add]
  have i2 : ∀ i < 4, InRegions (s.rd ++ s.wr) (sP s₀ + BitVec.ofNat 64 (64 * b + 16 * i)) 16 :=
    fun i _ => inS' hp h.st (by omega)
  have i6 : ∀ i < 4, InRegions (s.rd ++ s.wr) (sP s₀ + BitVec.ofNat 64 (512 + 64 * b + 16 * i)) 16 :=
    fun i _ => inS' hp h.st (by omega)
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
    exact h.ld hp hb (i := 0) (by decide)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide),
      o₃ _ (by decide), v₂]
    exact h.ld hp hb (i := 1) (by decide)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide), v₃]
    exact h.ld hp hb (i := 2) (by decide)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), v₄]
    exact h.ld hp hb (i := 3) (by decide)
  · rw [o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), v₅]
    exact h.tl hp hb (i := 0) (by decide) he
  · rw [o₈ _ (by decide), o₇ _ (by decide), v₆]
    exact h.tl hp hb (i := 1) (by decide) he
  · rw [o₈ _ (by decide), v₇]
    exact h.tl hp hb (i := 2) (by decide) he
  · rw [v₈]
    exact h.tl hp hb (i := 3) (by decide) he

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

end

end VG.Proof.MlKem.AArch64.Ntt16
