import VerifiedGarbage.Proof.X25519.X86.Field32.CallCT
import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Framework.X86.TaintErase
import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
import VerifiedGarbage.Impl.Ed25519.X86.PointLoop

/-!
# Field programs with calls on x86 (32-bit): two runs

The constant time of field programs whose products call
`vg_gf25519_r32_mul` is proven run by run (`RF`,
`Proof/X25519/X86/Field32/CallCT.lean`): a call by `mulCall_rf`, and every
other field operation by the taint analysis from `esp` and `edi` public
(`op_check`: its code differs from that of the operation on slot 0 only in
its displacements and immediates, so it is analysed once, `check_erase`),
keeping `RF` by its correctness. Lists of them (`fieldProg_rf`), the loops
of squarings (`sqn_rf`) and the addition chains (`power250_rf`, `invert_rf`,
`rootPower_rf`) follow.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Proof.X25519.X86.Field32 (RF RF.agree mulCall_rf)
open VG.Impl.X25519.X86.Field32 (mulCall)

theorem offset_bound (o : Slot) : offset o + 32 ≤ 768 := by
  have := o.isLt; simp only [offset]; omega

/-- A block that keeps `Keep`, analysed from `esp` and `edi` public, keeps `RF`. -/
theorem block_rf (x : BitVec 32) {is : List Instr}
    (hc : (taint.check (τr [.esp, .edi]) (.block is) (.block [] 256)).isSome = true)
    (hw : ∀ s, Ctx x s → WP isa (.block is) s fun t => Keep s t) :
    RelCT isa (RF x) (.block is) (RF x) := by
  refine ((RelCT.taint (A := taint) (P := RF x) (τr [.esp, .edi]) (fun _ _ h => RF.agree h) hc).wpDep
    (F := fun s t => Keep s t) fun s₁ s₂ h => ⟨hw s₁ h.1, hw s₂ h.2.1⟩).mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨-, s₁, s₂, ⟨c₁, c₂, e⟩, k₁, k₂⟩
  exact ⟨k₁.ctx c₁, k₂.ctx c₂, by rw [k₁.esp, k₂.esp, e]⟩

/-- Code that differs from `c₀` only in displacements and immediates is
analysed as `c₀` is, from a taint that knows no region bases. -/
theorem check_of_erase' {τ : VG.X86.Taint.T} (hn : Taint.noBases τ = true) {c c₀ : Prog isa}
    (e : Code.erase c = Code.erase c₀)
    (h₀ : (taint.check τ (Code.erase c₀) (.block [] 256)).isSome = true) :
    (taint.check τ c (.block [] 256)).isSome = true := by
  have h := Taint.check_erase c τ (.block [] 256) hn rfl
  rw [e] at h
  exact (congrArg Option.isSome h).symm.trans h₀

theorem check_of_erase {c c₀ : Prog isa} (e : Code.erase c = Code.erase c₀)
    (h₀ : (taint.check (τr [.esp, .edi]) (Code.erase c₀) (.block [] 256)).isSome = true) :
    (taint.check (τr [.esp, .edi]) c (.block [] 256)).isSome = true :=
  check_of_erase' rfl e h₀

/-- The trace of a field operation but a product. -/
theorem op_check (op : FieldOp) (hm : ∀ o a b, op ≠ .mul o a b) :
    (taint.check (τr [.esp, .edi]) (.block op.code) (.block [] 256)).isSome = true := by
  cases op with
  | copy o a => exact check_of_erase (c₀ := .block (FieldOp.copy 0 0).code) rfl (by decide +kernel)
  | const o v => exact check_of_erase (c₀ := .block (FieldOp.const 0 0).code) rfl (by decide +kernel)
  | add o a b => exact check_of_erase (c₀ := .block (FieldOp.add 0 0 0).code) rfl (by decide +kernel)
  | sub o a b => exact check_of_erase (c₀ := .block (FieldOp.sub 0 0 0).code) rfl (by decide +kernel)
  | mul o a b => exact absurd rfl (hm o a b)

theorem fieldOp_rf (x : BitVec 32) (op : FieldOp) : RelCT isa (RF x) op.prog (RF x) := by
  cases op with
  | mul o a b => exact mulCall_rf x (offset_bound o) (offset_bound a) (offset_bound b)
  | copy o a =>
    exact block_rf x (op_check (.copy o a) nofun) fun s h => WP.mono (fieldOp_ok h _) fun _ h => h.1.keep
  | const o v =>
    exact block_rf x (op_check (.const o v) nofun) fun s h => WP.mono (fieldOp_ok h _) fun _ h => h.1.keep
  | add o a b =>
    exact block_rf x (op_check (.add o a b) nofun) fun s h => WP.mono (fieldOp_ok h _) fun _ h => h.1.keep
  | sub o a b =>
    exact block_rf x (op_check (.sub o a b) nofun) fun s h => WP.mono (fieldOp_ok h _) fun _ h => h.1.keep

theorem fieldProg_rf (x : BitVec 32) (ops : List FieldOp) : RelCT isa (RF x) (fieldProg ops) (RF x) := by
  induction ops with
  | nil => exact RelCT.nil fun _ _ h => h
  | cons op ops ih => exact RelCT.seq (fieldOp_rf x op) ih

/-! ## Squarings in a loop -/

/-- `m` squarings left, the counter at `m` in both runs. -/
def SqRel (x : BitVec 32) (m : Nat) (t₁ t₂ : State) : Prop :=
  RF x t₁ t₂ ∧ t₁.gpr .esi = BitVec.ofNat 32 m ∧ t₂.gpr .esi = BitVec.ofNat 32 m ∧ 1 ≤ m ∧ m < 2 ^ 32

/-- The counter set to `k`. -/
theorem setCounter_rf (x : BitVec 32) {k : Nat} (h1 : 1 ≤ k) (h2 : k < 2 ^ 32) :
    RelCT isa (RF x) (.block [.mov .esi (.imm (BitVec.ofNat 32 k))]) (SqRel x k) := by
  refine ((RelCT.taint (A := taint) (P := RF x) (τr [.esp, .edi]) (fun _ _ h => RF.agree h)
    (check_of_erase (c := .block [.mov .esi (.imm (BitVec.ofNat 32 k))])
      (c₀ := .block [.mov .esi (.imm 0)]) rfl (by decide +kernel))).wpDep
    (F := fun s t => Wp.Upd s t .esi (BitVec.ofNat 32 k))
    fun s₁ s₂ _ => ⟨Wp.wp_movi fun t ht => WP.block_nil ht, Wp.wp_movi fun t ht => WP.block_nil ht⟩).mono
    (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨-, s₁, s₂, ⟨c₁, c₂, e⟩, u₁, u₂⟩
  exact ⟨⟨c₁.keep (u₁.other _ (by decide)) u₁.wr (u₁.other _ (by decide)),
    c₂.keep (u₂.other _ (by decide)) u₂.wr (u₂.other _ (by decide)),
    by rw [u₁.other _ (by decide), u₂.other _ (by decide), e]⟩, u₁.gpr, u₂.gpr, h1, h2⟩

/-- A loop's body: code keeping `RF` and the counter, then the counter decremented. -/
theorem countBody_wp {x : BitVec 32} {c : Prog isa}
    (hw : ∀ s, Ctx x s → WP isa c s fun t => Ctx x t ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .esi = s.gpr .esi)
    {s : State} (hc : Ctx x s) {m : Nat} (h1 : 1 ≤ m) (h2 : m < 2 ^ 32) (hb : s.gpr .esi = BitVec.ofNat 32 m) :
    WP isa (.seq c (.block [.alu .sub .esi (.imm 1)])) s
      fun t => Ctx x t ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .esi = BitVec.ofNat 32 (m - 1) ∧
        isa.eval .ne t = some (!decide (m - 1 = 0)) := by
  refine WP.seq (WP.mono (hw s hc) fun t ⟨ct, pt, it⟩ => ?_)
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  refine ⟨ct.keep (hu.other _ (by decide)) hu.wr (hu.other _ (by decide)),
    (hu.other _ (by decide)).trans pt, by rw [hu.gpr, it, hb]; exact Wp.ofNat_pred h1, ?_⟩
  show u.zf.map (!·) = _
  rw [hz, it, hb, Wp.ofNat_pred h1, Wp.ofNat_beq_zero (by omega)]
  rfl

/-- A loop counting `esi` down to zero, around code keeping `RF` and the counter. -/
theorem countLoop_rf (x : BitVec 32) {c : Prog isa} (htr : RelCT isa (RF x) c (RF x))
    (hw : ∀ s, Ctx x s → WP isa c s fun t => Ctx x t ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .esi = s.gpr .esi)
    (m : Nat) : RelCT isa (SqRel x m) (.loop (.seq c (.block [.alu .sub .esi (.imm 1)])) .ne) (RF x) := by
  refine RelCT.loop (M := isa) (SqRel x) ?_ m
  intro m
  have tr : RelCT isa (SqRel x m) (.seq c (.block [.alu .sub .esi (.imm 1)])) fun _ _ => True :=
    RelCT.seq (htr.mono (fun _ _ h => h.1) fun _ _ h => h)
      (RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ h => RF.agree h) (by taint_decide))
  refine (tr.wpDep (F := fun (s t : State) => Ctx x t ∧ t.gpr .esp = s.gpr .esp ∧
      t.gpr .esi = BitVec.ofNat 32 (m - 1) ∧ isa.eval .ne t = some (!decide (m - 1 = 0)))
    fun s₁ s₂ h => ⟨countBody_wp hw h.1.1 h.2.2.2.1 h.2.2.2.2 h.2.1,
      countBody_wp hw h.1.2.1 h.2.2.2.1 h.2.2.2.2 h.2.2.1⟩).mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨-, s₁, s₂, h, ⟨c₁, p₁, b₁, z₁⟩, ⟨c₂, p₂, b₂, z₂⟩⟩
  have hsp : t₁.gpr .esp = t₂.gpr .esp := by rw [p₁, p₂, h.1.2.2]
  refine ⟨by rw [z₁, z₂], fun hz => ⟨c₁, c₂, hsp⟩, fun hz => ?_⟩
  have hm : m - 1 ≠ 0 := fun h0 => by rw [z₁, h0] at hz; cases hz
  have := h.2.2.2.2
  exact ⟨m - 1, by omega, ⟨c₁, c₂, hsp⟩, b₁, b₂, by omega, by omega⟩

/-- A field program keeps what a loop around it needs. -/
theorem fieldProg_count {x : BitVec 32} (ops : List FieldOp) (s : State) (hc : Ctx x s) :
    WP isa (fieldProg ops) s fun t => Ctx x t ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .esi = s.gpr .esi :=
  WP.mono (fieldProg_ok ops hc) fun _ ⟨k, _⟩ => ⟨k.ctx hc, k.keep.esp, k.keep.esi⟩

theorem sqn_rf (x : BitVec 32) (o a : Slot) {n : Nat} (hn : 2 ≤ n) (hn' : n < 2 ^ 32) :
    RelCT isa (RF x) (sqn (offset o) (offset a) n) (RF x) :=
  RelCT.seq (RelCT.seq (fieldOp_rf x (.mul o a a)) (setCounter_rf x (k := n - 1) (by omega) (by omega)))
    (countLoop_rf x (fieldOp_rf x (.mul o o o))
      (fun s hc => WP.mono (mulProg_ok hc o o o) fun _ ⟨k, _⟩ => ⟨k.ctx hc, k.keep.esp, k.keep.esi⟩) _)

/-! ## The addition chains -/

theorem power250_rf (x : BitVec 32) : RelCT isa (RF x) power250 (RF x) := by
  have m := fun (o a b : Slot) => fieldOp_rf x (.mul o a b)
  have q := fun (o a : Slot) (n : Nat) (hn : 2 ≤ n) (hn' : n < 2 ^ 32) => sqn_rf x o a hn hn'
  exact (m 14 2 2).seq <| (m 15 14 14).seq <| (m 15 15 15).seq <| (m 15 2 15).seq <| (m 14 14 15).seq <|
    (m 16 14 14).seq <| (m 15 15 16).seq <| (q 16 15 5 (by decide) (by decide)).seq <| (m 15 16 15).seq <|
    (q 16 15 10 (by decide) (by decide)).seq <| (m 16 16 15).seq <|
    (q 17 16 20 (by decide) (by decide)).seq <| (m 16 17 16).seq <|
    (q 16 16 10 (by decide) (by decide)).seq <| (m 15 16 15).seq <|
    (q 16 15 50 (by decide) (by decide)).seq <| (m 16 16 15).seq <|
    (q 17 16 100 (by decide) (by decide)).seq <| (m 16 17 16).seq <|
    (q 16 16 50 (by decide) (by decide)).seq (m 15 16 15)

theorem invert_rf (x : BitVec 32) : RelCT isa (RF x) invert (RF x) :=
  (power250_rf x).seq <| (sqn_rf x 15 15 (n := 5) (by decide) (by decide)).seq (fieldOp_rf x (.mul 15 15 14))

theorem rootPower_rf (x : BitVec 32) : RelCT isa (RF x) rootPower (RF x) :=
  (power250_rf x).seq <| (sqn_rf x 15 15 (n := 2) (by decide) (by decide)).seq (fieldOp_rf x (.mul 15 15 2))

theorem pointAffine_rf (x : BitVec 32) : RelCT isa (RF x) pointAffine (RF x) :=
  (invert_rf x).seq (fieldProg_rf x affineOps)

/-! ## Doublings in a loop -/

theorem double16_rf (x : BitVec 32) : RelCT isa (RF x) double16 (RF x) :=
  (setCounter_rf x (k := 16) (by decide) (by decide)).seq
    (countLoop_rf x (fieldProg_rf x pointDoubleOps) (fun s hc => fieldProg_count pointDoubleOps s hc) _)

end VG.Proof.Ed25519.X86
