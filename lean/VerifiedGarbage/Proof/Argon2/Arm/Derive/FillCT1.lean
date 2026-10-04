import VerifiedGarbage.Proof.Argon2.Arm.Derive.MemCT

/-!
# Argon2 on ARMv7: the random word, in two runs

`W`: the public words of the filling loops' locals (the parameters, the
position and the counter), which `Two.leafF` makes public for the taint
analysis, with any registers the runs agree on. A store of a secret through
a register that is not `r11` makes the analysis forget every public word, so
the pieces are cut after such stores (and around the calls of G), and the
runs related again from what correctness says the locals and registers hold.
`randomSource_rel`: the random word's trace depends only on the position.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_imm op2_reg)
open VG.Proof.Sha512.Arm (Only)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff ld st)

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

/-- The public words of the filling loops' locals. -/
structure W (s₀ : State) (pass slice lane index ctr : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  ctr : lw s₀ s counterOff = BitVec.ofNat 32 ctr

theorem FS.w {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) : W s₀ pass slice lane index ctr s :=
  ⟨h.inv, h.pr, h.pos, h.cache.2.1⟩

theorem W.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    {ds : List Reg} (k : Only ds s t) (h11 : Reg.r11 ∉ ds) : W s₀ pass slice lane index ctr t :=
  ⟨h.inv.only k h11, h.pr.of_mem k.mem, h.pos.of_mem k.mem, by rw [lw_mem k.mem]; exact h.ctr⟩

/-- The words `W` is about. -/
abbrev ws0 : List Nat := [72, 76, 80, 84, 88, 92, 96, 100, 132]

/-- Their slots. -/
abbrev sl0 : List (Nat × Nat × Nat) := [(0, 72, 32), (0, 132, 4)]

theorem slotsOk0 (rs : List Reg) : VG.Arm.Taint.SlotsOk (τB sl0 rs) := by
  intro x hx
  simp only [τB, sl0, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

theorem words {pass slice lane index ctr : Nat} {s₁ s₂ : State} (h₁ : W s₀₁ pass slice lane index ctr s₁)
    (h₂ : W s₀₂ pass slice lane index ctr s₂) : ∀ d ∈ ws0, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [ws0, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pos.pass.trans h₂.pos.pass.symm
  · exact h₁.pos.lane.trans h₂.pos.lane.symm
  · exact h₁.pos.slice.trans h₂.pos.slice.symm
  · exact h₁.pos.index.trans h₂.pos.index.symm
  · exact h₁.ctr.trans h₂.ctr.symm
  · exact (h₁.pr.laneLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.laneLen) pe)).trans
      h₂.pr.laneLen.symm
  · exact (h₁.pr.stride.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 (p.laneLen * 1024)) pe)).trans
      h₂.pr.stride.symm
  · exact (h₁.pr.segLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.segmentLen) pe)).trans
      h₂.pr.segLen.symm
  · exact (h₁.pr.divisor.trans (congrArg (fun n : Nat => BitVec.ofNat 32 (4 * n)) le)).trans h₂.pr.divisor.symm

/-- A piece the taint analysis proves from the public words `W` and the
registers `rs`, which both runs agree on. -/
theorem leafF {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, W s₀₁ pass slice lane index ctr s₁ ∧
      W s₀₂ pass slice lane index ctr s₂) ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB sl0 rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  T.leaf ws0 sl0 rs (slotsOk0 rs) (by decide) (fun s₁ s₂ h =>
    let ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr⟩ := hag s₁ s₂ h
    ⟨w₁.inv, w₂.inv, T.words w₁ w₂, hr⟩) hc

end Two

/-! ## The address block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before G's call in `stage x y o`. -/
theorem stageBlk_ok {s : State} (h : Inv s₀ s) {x y o : Nat} (ex : encodable (BitVec.ofNat 32 x) = true)
    (ey : encodable (BitVec.ofNat 32 y) = true) (eo : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block [ld .r3 (argOff 15), .dp .add .r0 .r3 (.imm (BitVec.ofNat 32 x)),
      .dp .add .r1 .r3 (.imm (BitVec.ofNat 32 y)), .dp .add .r2 .r3 (.imm (BitVec.ofNat 32 o))]) s fun t =>
      Inv s₀ t ∧ t.gpr .r3 = scrP s₀ ∧ t.gpr .r0 = scrP s₀ + BitVec.ofNat 32 x ∧
      t.gpr .r1 = scrP s₀ + BitVec.ofNat 32 y ∧ t.gpr .r2 = scrP s₀ + BitVec.ofNat 32 o := by
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm ex) fun s₂ u₂ =>
    wp_add (op2_imm ey) fun s₃ u₃ => wp_add (op2_imm eo) fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]

/-- The counter, stored. -/
theorem stctr_w {s : State} {pass slice lane index ctr c : Nat} (h : W s₀ pass slice lane index ctr s)
    (ha : s.gpr .r0 = BitVec.ofNat 32 c) :
    WP isa (.block [st counterOff .r0]) s (W s₀ pass slice lane index c) :=
  wp_stloc hp h.inv (d := counterOff) (by decide) fun t it vt ot _ _ => WP.block_nil
    ⟨it, Prm.of_lw h.pr fun d hd => ot d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h.pos.of_lw fun d hd => ot d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> decide),
    by rw [vt, ha]⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `dependentWord` leaks the same trace in two runs at the same position. -/
theorem dependentWord_rel {pass slice lane index ctr : Nat} :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index ctr s₁ ∧ W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.Arm.Derive.dependentWord fun _ _ => True :=
  T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩

/-- `stage x y o` leaks the same trace in two runs. -/
theorem stage_rel {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y)
    (ex : encodable (BitVec.ofNat 32 x) = true) (ey : encodable (BitVec.ofNat 32 y) = true)
    (eo : encodable (BitVec.ofNat 32 o) = true)
    (hc : ∃ hc, (VG.Taint.check taint (τB [] []) (.block [ld .r3 (argOff 15),
      .dp .add .r0 .r3 (.imm (BitVec.ofNat 32 x)), .dp .add .r1 .r3 (.imm (BitVec.ofNat 32 y)),
      .dp .add .r2 .r3 (.imm (BitVec.ofNat 32 o))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) (Impl.Argon2.Arm.Derive.stage x y o) fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.stage
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) hc)
    (fun s h => stageBlk_ok T.hp₁ h ex ey eo) (fun s h => stageBlk_ok T.hp₂ h ex ey eo) ?_
  refine T.ccall_rel ho ho' fun s₁ s₂ ⟨⟨i₁, d₁, a₁, e₁, c₁⟩, ⟨i₂, d₂, a₂, e₂, c₂⟩⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₁]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₂]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     by rw [a₁, a₂, T.pb.scrP_eq], by rw [e₁, e₂, T.pb.scrP_eq]⟩

/-- `addressCalls` leaks the same trace in two runs at the same position. -/
theorem addressCalls_rel {pass slice lane index c : Nat} (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32)
    (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index c s₁ ∧ W s₀₂ pass slice lane index c s₂)
      Impl.Argon2.Arm.Derive.addressCalls fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.addressCalls
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (input_ok T.hp₁ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1)
    (fun s h => (input_ok T.hp₂ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => (stage_ok T.hp₁ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
      fun t ht => ht.1)
    (fun s h => (stage_ok T.hp₂ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
      fun t ht => ht.1) ?_
  exact T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩

/-- `addressCache` leaks the same trace in two runs at the same position. -/
theorem addressCache_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.Arm.Derive.addressCache fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have sl := segLen_lt T.hp₁
  have hlt := T.hp₁.lanes_lt
  unfold Impl.Argon2.Arm.Derive.addressCache
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => cacheCheck_ok T.hp₁ h hi) (fun s h => cacheCheck_ok T.hp₂ h hi₂) ?_
  refine RelCT.seqW (RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show VG.Arm.eval .eq s₁ = VG.Arm.eval .eq s₂
      rw [h₁.2.2, h₂.2.2, h₁.1.cache.2.1, h₂.1.cache.2.1])
    (RelCT.nil fun _ _ _ => trivial) ?_)
    (fun s h => cacheFill_ok T.hp₁ h.1 hpass hl hs hi h.2.1 h.2.2)
    (fun s h => cacheFill_ok T.hp₂ h.1 hpass hl₂ hs hi₂ h.2.1 h.2.2)
    (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
  refine RelCT.seqW (G₁ := W s₀₁ pass slice lane index (index / 128 + 1))
    (G₂ := W s₀₂ pass slice lane index (index / 128 + 1))
    (T.leafF [.r0] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.1, h.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun s h => stctr_w T.hp₁ h.1.w h.2.1) (fun s h => stctr_w T.hp₂ h.1.w h.2.1) ?_
  exact T.addressCalls_rel hpass (by omega) (by omega) (by omega)

/-- `randomSource` leaks the same trace in two runs at the same position. -/
theorem randomSource_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.Arm.Derive.randomSource fun _ _ => True := by
  have pe := T.pb.prm_eq
  unfold Impl.Argon2.Arm.Derive.randomSource
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => FS s₀₁ pass slice lane index ctr st₁ t ∧
      VG.Arm.eval .eq t = some (!Spec.Argon2.independent (prm s₀₁) pass slice))
    (G₂ := fun t => FS s₀₂ pass slice lane index ctr st₂ t ∧
      VG.Arm.eval .eq t = some (!Spec.Argon2.independent (prm s₀₂) pass slice))
    (fun s h => (addressMode_ok T.hp₁ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_only k (by decide), z⟩)
    (fun s h => (addressMode_ok T.hp₂ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_only k (by decide), z⟩) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show VG.Arm.eval .eq s₁ = VG.Arm.eval .eq s₂
      rw [h₁.2, h₂.2, pe])
    (T.dependentWord_rel.mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩) fun _ _ h => h)
    ((T.addressCache_rel hpass hl hs hi).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)

end Two

end VG.Proof.Argon2.Arm.Derive
