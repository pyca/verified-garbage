module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTCall
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillState
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillInput
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillDep
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTCall
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillState
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.InitialCT
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCache
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillInput
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillDep
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTBase

/-!
# Argon2 on RISC-V: the random word, in two runs

`W`: the public doublewords of the filling loops' frame (the parameters, the
position and the counter), which `Two.leafF` makes public for the taint
analysis, with any registers the runs agree on. A store of a secret through
a register other than `s3` makes the analysis forget the frame, so the
pieces are cut after such stores (and around the calls of G), and the runs
related again from what correctness says the frame and registers hold.
`randomSource_rel`: the random word's trace depends only on the position.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd wp_addi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.RISCV64.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff counterOff
  strideOff st)

/-- An empty block. -/
theorem RelCT.nil {P Q : State → State → Prop} (h : ∀ x y, P x y → Q x y) :
    RelCT isa P (.block []) Q := by
  intro x y t₁ t₂ x' y' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, h _ _ hp⟩

/-- The public doublewords of the filling loops' frame. -/
structure W (s₀ : State) (pass slice lane index ctr : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  ctr : lw s₀ s counterOff = BitVec.ofNat 64 ctr

theorem FS.w {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) : W s₀ pass slice lane index ctr s :=
  ⟨h.inv, h.pr, h.pos, h.cache.2.1⟩

theorem W.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    {ds : List Reg} (k : Only ds s t) (hd : ∀ r ∈ ds, Free r := by decide) :
    W s₀ pass slice lane index ctr t :=
  ⟨h.inv.only k hd, h.pr.of_mem k.mem, h.pos.of_mem k.mem, by rw [lw_mem k.mem]; exact h.ctr⟩

/-- The doublewords `W` is about. -/
abbrev wsW : List Nat := [passOff, laneOff, sliceOff, indexOff, counterOff, laneLenOff, strideOff, segLenOff]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

theorem prm_lw {s₁ s₂ : State} (p₁ : Prm s₀₁ s₁) (p₂ : Prm s₀₂ s₂) :
    lw s₀₁ s₁ laneLenOff = lw s₀₂ s₂ laneLenOff ∧ lw s₀₁ s₁ strideOff = lw s₀₂ s₂ strideOff ∧
      lw s₀₁ s₁ segLenOff = lw s₀₂ s₂ segLenOff :=
  ⟨by rw [p₁.laneLen, p₂.laneLen, T.pb.prm_eq], by rw [p₁.stride, p₂.stride, T.pb.prm_eq],
    by rw [p₁.segLen, p₂.segLen, T.pb.prm_eq]⟩

theorem words {pass slice lane index ctr : Nat} {s₁ s₂ : State} (h₁ : W s₀₁ pass slice lane index ctr s₁)
    (h₂ : W s₀₂ pass slice lane index ctr s₂) : ∀ d ∈ wsW, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  obtain ⟨a, b, c⟩ := T.prm_lw h₁.pr h₂.pr
  intro d hd
  simp only [wsW, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pos.pass.trans h₂.pos.pass.symm
  · exact h₁.pos.lane.trans h₂.pos.lane.symm
  · exact h₁.pos.slice.trans h₂.pos.slice.symm
  · exact h₁.pos.index.trans h₂.pos.index.symm
  · exact h₁.ctr.trans h₂.ctr.symm
  · exact a
  · exact b
  · exact c

/-- A piece the taint analysis proves from the public doublewords `W`, those
at `ex`, and the registers `rs`, which both runs agree on. -/
theorem leafF {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (ex : List Nat)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, W s₀₁ pass slice lane index ctr s₁ ∧
      W s₀₂ pass slice lane index ctr s₂) ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      ∀ d ∈ ex, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∃ hc, (VG.Taint.check frameTaint (τF (wsW ++ ex) rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  T.leaf (wsW ++ ex) rs (fun s₁ s₂ h =>
    let ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr, he⟩ := hag s₁ s₂ h
    ⟨w₁.inv, w₂.inv, fun d hd => (List.mem_append.mp hd).elim (T.words w₁ w₂ d) (he d), hr⟩) hc

end Two

/-! ## The address block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
theorem Inv.base4 {s : State} (h : Inv s₀ s) : Base s₀ s .s4 0 := ⟨.inl rfl, by rw [h.s4]; simp⟩

omit hp in
theorem Inv.base0 {s : State} (h : Inv s₀ s) : Base s₀ s .s0 2048 := ⟨.inr rfl, h.s0⟩

omit hp in
/-- The instructions before G's call in `stage (bx, x) (by, y) (bo, o)`. -/
theorem stageBlk_ok {s : State} (h : Inv s₀ s) {bx by' bo : Reg} {Bx By Bo x y o : Nat}
    (hx : Base s₀ s bx Bx) (hy : Base s₀ s by' By) (hob : Base s₀ s bo Bo)
    (hxi : x < 2048) (hyi : y < 2048) (hoi : o < 2048) :
    WP isa (.block ([.addi .a0 bx x, .addi .a1 by' y, .addi .a2 bo o] ++
      Impl.Argon2.RISCV64.Derive.gScratch)) s fun t =>
      Inv s₀ t ∧ t.gpr .a3 = gwP s₀ ∧ t.gpr .a0 = scrP s₀ + BitVec.ofNat 64 (Bx + x) ∧
      t.gpr .a1 = scrP s₀ + BitVec.ofNat 64 (By + y) ∧ t.gpr .a2 = scrP s₀ + BitVec.ofNat 64 (Bo + o) := by
  unfold Impl.Argon2.RISCV64.Derive.gScratch
  simp only [List.cons_append, List.nil_append]
  refine wp_addi hxi fun s₁ u₁ => wp_addi hyi fun s₂ u₂ =>
    wp_addi hoi fun s₃ u₃ => wp_addi (imm := 1024) (by decide) fun s₄ u₄ =>
    wp_addi (imm := 1024) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have nb : ∀ b : Reg, (b = .s4 ∨ b = .s0) → b ≠ .a0 ∧ b ≠ .a1 ∧ b ≠ .a2 ∧ b ≠ .a3 := by
    intro b hb; rcases hb with rfl | rfl <;> decide
  obtain ⟨y1, -, -, -⟩ := nb by' hy.1
  obtain ⟨o1, o2, -, -⟩ := nb bo hob.1
  have off : ∀ (B d : Nat), scrP s₀ + BitVec.ofNat 64 B + BitVec.ofNat 64 d =
      scrP s₀ + BitVec.ofNat 64 (B + d) := fun B d => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅, ?_, ?_, ?_, ?_⟩
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.s0, off, off]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, hx.2, off]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ y1, hy.2, off]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ o2,
      u₁.other _ o1, hob.2, off]

omit hp in
/-- The counter, stored. -/
theorem stctr_w {s : State} {pass slice lane index ctr c : Nat} (h : W s₀ pass slice lane index ctr s)
    (ha : s.gpr .a0 = BitVec.ofNat 64 c) :
    WP isa (.block [st counterOff .a0]) s (W s₀ pass slice lane index c) :=
  wp_stloc h.inv (d := counterOff) (by decide) fun t it vt ot _ _ => WP.block_nil
    ⟨it, Prm.of_lw h.pr fun d h₁ h₂ => ot d (by omega) (.inl (by simp only [counterOff]; omega)),
      h.pos.of_lw fun d h₁ h₂ => ot d (by omega) (.inr (by simp only [counterOff]; omega)), by rw [vt, ha]⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `dependentWord` leaks the same trace in two runs at the same position. -/
theorem dependentWord_rel {pass slice lane index ctr : Nat} :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index ctr s₁ ∧ W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.RISCV64.Derive.dependentWord fun _ _ => True :=
  T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp, by simp⟩) ⟨_, by taint_decide⟩

/-- `stage (bx, x) (by, y) (bo, o)` leaks the same trace in two runs. -/
theorem stage_rel {bx by' bo : Reg} {Bx By Bo x y o : Nat}
    (bX : ∀ {s₀ s : State}, Inv s₀ s → Base s₀ s bx Bx) (bY : ∀ {s₀ s : State}, Inv s₀ s → Base s₀ s by' By)
    (bO : ∀ {s₀ s : State}, Inv s₀ s → Base s₀ s bo Bo)
    (hxi : x < 2048) (hyi : y < 2048) (hoi : o < 2048)
    (ho' : Bo + o + 1024 ≤ 4096) (ho8 : (Bo + o) % 8 = 0)
    (hx' : Bx + x + 1024 ≤ 4096) (hx8 : (Bx + x) % 8 = 0)
    (hxo : Bx + x + 1024 ≤ Bo + o ∨ Bo + o + 1024 ≤ Bx + x)
    (hy' : By + y + 1024 ≤ 4096) (hy8 : (By + y) % 8 = 0)
    (hyo : By + y + 1024 ≤ Bo + o ∨ Bo + o + 1024 ≤ By + y)
    (hc : ∃ hc, (VG.Taint.check frameTaint (τF [] []) (.block ([.addi .a0 bx x, .addi .a1 by' y,
      .addi .a2 bo o] ++ Impl.Argon2.RISCV64.Derive.gScratch)) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) (Impl.Argon2.RISCV64.Derive.stage (bx, x) (by', y) (bo, o))
      fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.Derive.stage
  refine RelCT.seqW (T.leaf [] [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp, by simp⟩) hc)
    (fun s h => stageBlk_ok h (bX h) (bY h) (bO h) hxi hyi hoi)
    (fun s h => stageBlk_ok h (bX h) (bY h) (bO h) hxi hyi hoi) ?_
  refine T.ccall_rel ho' ho8 fun s₁ s₂ ⟨⟨i₁, d₁, a₁, e₁, c₁⟩, ⟨i₂, d₂, a₂, e₂, c₂⟩⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inr ⟨Bx + x, hx', hx8, hxo, rfl⟩,
        by rw [e₁]; exact .inr ⟨By + y, hy', hy8, hyo, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inr ⟨Bx + x, hx', hx8, hxo, rfl⟩,
        by rw [e₂]; exact .inr ⟨By + y, hy', hy8, hyo, rfl⟩⟩,
     by rw [a₁, a₂, T.pb.scrP_eq], by rw [e₁, e₂, T.pb.scrP_eq]⟩

/-- `addressCalls` leaks the same trace in two runs at the same position. -/
theorem addressCalls_rel {pass slice lane index c : Nat} :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index c s₁ ∧ W s₀₂ pass slice lane index c s₂)
      Impl.Argon2.RISCV64.Derive.addressCalls fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.Derive.addressCalls
  refine RelCT.seqW (T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => (input_ok T.hp₁ h.inv h.pos h.ctr).mono fun t ht => ht.1)
    (fun s h => (input_ok T.hp₂ h.inv h.pos h.ctr).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.stage_rel (bx := .s0) (by' := .s4) (bo := .s4) (Bx := 2048) (By := 0) (Bo := 0)
      (x := 1024) (y := 1024) (o := 0) Inv.base0 Inv.base4 Inv.base4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ⟨_, by taint_decide⟩)
    (fun s h => (stage_ok T.hp₁ h h.base0 h.base4 h.base4 (x := 1024) (y := 1024) (o := 0) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).mono fun t ht => ht.1)
    (fun s h => (stage_ok T.hp₂ h h.base0 h.base4 h.base4 (x := 1024) (y := 1024) (o := 0) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).mono fun t ht => ht.1) ?_
  exact T.stage_rel (bx := .s0) (by' := .s4) (bo := .s0) (Bx := 2048) (By := 0) (Bo := 2048)
    (x := 1024) (y := 0) (o := 0) Inv.base0 Inv.base4 Inv.base0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, by taint_decide⟩

/-- `addressCache` leaks the same trace in two runs at the same position. -/
theorem addressCache_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState}
    (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.RISCV64.Derive.addressCache fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  unfold Impl.Argon2.RISCV64.Derive.addressCache
  refine RelCT.seqW (T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => cacheCheck_ok T.hp₁ h hi) (fun s h => cacheCheck_ok T.hp₂ h hi₂) ?_
  refine RelCT.seqW (RelCT.iteF (fun s₁ s₂ h₁ h₂ =>
      (h₁.2.2.trans (by rw [h₁.1.cache.2.1, h₂.1.cache.2.1])).trans h₂.2.2.symm)
    (RelCT.nil fun _ _ _ => trivial) ?_)
    (fun s h => cacheFill_ok T.hp₁ h.1 hi h.2.1 h.2.2)
    (fun s h => cacheFill_ok T.hp₂ h.1 hi₂ h.2.1 h.2.2)
    (T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by simp, by simp⟩) ⟨_, by taint_decide⟩)
  refine RelCT.seqW (G₁ := W s₀₁ pass slice lane index (index / 128 + 1))
    (G₂ := W s₀₂ pass slice lane index (index / 128 + 1))
    (T.leafF [.a0] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.1, h.2.2.1], by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => stctr_w h.1.w h.2.1) (fun s h => stctr_w h.1.w h.2.1) ?_
  exact T.addressCalls_rel

/-- `randomSource` leaks the same trace in two runs at the same position. -/
theorem randomSource_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.RISCV64.Derive.randomSource fun _ _ => True := by
  have pe := T.pb.prm_eq
  unfold Impl.Argon2.RISCV64.Derive.randomSource
  refine RelCT.seqW (T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp, by simp⟩)
      ⟨_, by taint_decide⟩)
    (G₁ := fun t => FS s₀₁ pass slice lane index ctr st₁ t ∧
      VG.RISCV64.eval (.nonzero .a5) t = some (!Spec.Argon2.independent (prm s₀₁) pass slice))
    (G₂ := fun t => FS s₀₂ pass slice lane index ctr st₂ t ∧
      VG.RISCV64.eval (.nonzero .a5) t = some (!Spec.Argon2.independent (prm s₀₂) pass slice))
    (fun s h => (addressMode_ok T.hp₁ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_only k, z⟩)
    (fun s h => (addressMode_ok T.hp₂ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_only k, z⟩) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => (h₁.2.trans (by rw [pe])).trans h₂.2.symm)
    (T.dependentWord_rel.mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩) fun _ _ h => h)
    ((T.addressCache_rel hi).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)

end Two

end VG.Proof.Argon2.RISCV64.Derive
