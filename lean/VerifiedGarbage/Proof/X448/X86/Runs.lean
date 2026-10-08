import VerifiedGarbage.Proof.X448.X86.CallCT
import VerifiedGarbage.Proof.X448.X86.Square

/-!
# Field arithmetic on x86 (32-bit): two runs, piece by piece

The constant time of code calling the field functions is proven run by run
(`RelCT`): each piece's trace agrees in two runs from what each run's
correctness proof says of its own state. `Runs P₀ F` relates two runs from
entry states that `P₀` relates (the contract's precondition in both and its
public data), each in a state `F` says of its own run; `Runs.then` and
`Runs.step` relate a piece whose trace agrees, by determinism, with what
each run's correctness says of its result.

`FE bs σ` is what field arithmetic keeps in a run from the entry state `σ`
with the working space at `bs σ`: `FInv`, `esp` and the writable regions,
and the memory but the writable regions and the 20 bytes of stack below the
return address, where the calls of the field functions put their arguments.
Field operations (`ops_tr`) leak the same in two runs in it.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- Two runs from entry states `P₀` relates, each in a state `F` says of its own run. -/
def Runs (P₀ F : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, P₀ σ₁ σ₂ ∧ F σ₁ s₁ ∧ F σ₂ s₂

/-- Code whose traces agree in runs `P` relates (which `Runs P₀ F` relates
too), with what each run's correctness says of it. -/
theorem Runs.then {P₀ F G P R Q : State → State → Prop} {c : Prog isa}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Runs P₀ F s₁ s₂) (htr : RelCT isa P c R)
    (hw : ∀ σ s, F σ s → WP isa c s (G σ))
    (hq : ∀ σ₁ σ₂ t₁ t₂, P₀ σ₁ σ₂ → R t₁ t₂ → G σ₁ t₁ → G σ₂ t₂ → Q t₁ t₂) :
    RelCT isa P c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hr⟩ := htr _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨σ₁, σ₂, hP', f₁, f₂⟩ := hP _ _ hp
  obtain ⟨_, u₁, x₁, g₁⟩ := hw _ _ f₁
  obtain ⟨_, u₂, x₂, g₂⟩ := hw _ _ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, hq _ _ _ _ hP' hr g₁ g₂⟩

theorem Runs.step {P₀ F G R : State → State → Prop} {c : Prog isa}
    (htr : RelCT isa (Runs P₀ F) c R) (hw : ∀ σ s, F σ s → WP isa c s (G σ)) :
    RelCT isa (Runs P₀ F) c (Runs P₀ G) :=
  Runs.then (fun _ _ h => h) htr hw fun _ _ _ _ hP _ g₁ g₂ => ⟨_, _, hP, g₁, g₂⟩

/-- What field arithmetic keeps in a run from the entry state `σ`. -/
structure FE (bs : State → Addr) (σ t : State) : Prop where
  fin : FInv (bs σ) t
  sp : t.gpr .esp = σ.gpr .esp
  wr : t.wr = σ.wr
  frame : Frame (σ.wr ++ [below (σ.gpr .esp) 20]) σ.mem t.mem

/-- What the calls of the field functions need of a run from the entry state `σ`. -/
def FS (bs : State → Addr) (σ t : State) : Prop := FInv (bs σ) t ∧ t.gpr .esp = σ.gpr .esp

theorem FE.fs {bs : State → Addr} {σ t : State} (h : FE bs σ t) : FS bs σ t := ⟨h.fin, h.sp⟩

theorem FS.rf {bs : State → Addr} {σ₁ σ₂ t₁ t₂ : State} (hb : bs σ₁ = bs σ₂)
    (hs : σ₁.gpr .esp = σ₂.gpr .esp) (h₁ : FS bs σ₁ t₁) (h₂ : FS bs σ₂ t₂) : RF (bs σ₁) t₁ t₂ :=
  ⟨h₁.1, hb ▸ h₂.1, h₁.2.trans (hs.trans h₂.2.symm)⟩

/-- Code that keeps the field arithmetic's invariant, `esp` and the writable
regions, and uses at most 20 bytes of stack, keeps `FE`. -/
theorem FE.wp {bs : State → Addr} {σ s : State} (h : FE bs σ s) {c : Prog isa} (hc : NoSp c)
    (hu : stackUse c ≤ 20) {Q : State → Prop}
    (hw : WP isa c s fun t => FInv (bs σ) t ∧ t.gpr .esp = s.gpr .esp ∧ t.wr = s.wr ∧ Q t) :
    WP isa c s fun t => FE bs σ t ∧ Q t := by
  have room : 20 ≤ (σ.gpr .esp).toNat := h.sp ▸ h.fin.ctx.sp
  refine WP.mono (WP.withFrame hc (by rw [h.sp]; exact Nat.le_trans hu room) hw)
    fun t ⟨⟨f, sp, wr, q⟩, fr⟩ => ⟨⟨f, sp.trans h.sp, wr.trans h.wr, h.frame.trans ?_⟩, q⟩
  rw [h.sp, h.wr] at fr
  exact Frame.below_mono fr hu room

theorem call3_nosp {name : String} {body : Prog isa} (hb : NoSp body) (o a b : Nat) :
    NoSp (call3 name body o a b) := by
  intro i hi
  simp only [call3, instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl) | (rfl | hi) | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hb i hi
  · rfl

theorem call2_nosp {name : String} {body : Prog isa} (hb : NoSp body) (o a : Nat) :
    NoSp (call2 name body o a) := by
  intro i hi
  simp only [call2, instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl) | (rfl | hi) | rfl
  · rfl
  · rfl
  · rfl
  · exact hb i hi
  · rfl

theorem op_nosp (op : FieldOp) : NoSp op.impl.code := by
  cases op with
  | mul o a b => exact call3_nosp (NoSp.of_all (by decide +kernel)) _ _ _
  | add o a b => exact call3_nosp (NoSp.of_all (by decide +kernel)) _ _ _
  | sub o a b => exact call3_nosp (NoSp.of_all (by decide +kernel)) _ _ _
  | mulSmall o a => exact call2_nosp (NoSp.of_all (by decide +kernel)) _ _
  | copy o a =>
    intro i hi
    simp only [FieldOp.impl, Op.code, instrs, copy, List.mem_flatMap, List.mem_range] at hi
    obtain ⟨j, -, hj⟩ := hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> rfl

theorem op_stack (op : FieldOp) : stackUse op.impl.code ≤ 20 := by
  cases op <;> exact Nat.le_of_ble_eq_true rfl

theorem ops_nosp (xs : List FieldOp) : NoSp (ops (xs.map FieldOp.impl)) := by
  induction xs with
  | nil => intro i hi; simp only [List.map_nil, ops, instrs, List.not_mem_nil] at hi
  | cons op xs ih =>
    intro i hi
    change i ∈ instrs op.impl.code ++ instrs (ops (xs.map FieldOp.impl)) at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact op_nosp op i hi
    · exact ih i hi

theorem ops_stack (xs : List FieldOp) : stackUse (ops (xs.map FieldOp.impl)) ≤ 20 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons op xs ih => exact Nat.max_le.mpr ⟨op_stack op, ih⟩

/-- Field operations keep `FE`. -/
theorem ops_FE {bs : State → Addr} {σ s : State} (h : FE bs σ s) (xs : List FieldOp) :
    WP isa (ops (xs.map FieldOp.impl)) s fun t => FE bs σ t ∧ Keep (bs σ) s t ∧
      E t.mem (bs σ) = applyOps xs (E s.mem (bs σ)) :=
  h.wp (ops_nosp xs) (ops_stack xs) (WP.mono (ops_ok h.fin.scr h.fin.ctx h.fin.bounded xs)
    fun _ ⟨k, b, e⟩ => ⟨⟨k.scr h.fin.scr, k.ctx h.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, k, e⟩)

/-- The traces of field operations agree in two runs in `FE`. -/
theorem ops_tr {P₀ F : State → State → Prop} {bs : State → Addr}
    (hP : ∀ σ₁ σ₂, P₀ σ₁ σ₂ → bs σ₁ = bs σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp)
    (hF : ∀ σ s, F σ s → FS bs σ s) (xs : List FieldOp) :
    RelCT isa (Runs P₀ F) (ops (xs.map FieldOp.impl)) fun _ _ => True :=
  (RelCT.exists_ fun b => (ops_rel (base := b) xs).mono (fun _ _ h => h) fun _ _ _ => trivial).mono
    (fun _ _ ⟨_, _, hp, f₁, f₂⟩ => ⟨_, FS.rf (hP _ _ hp).1 (hP _ _ hp).2 (hF _ _ f₁) (hF _ _ f₂)⟩)
    fun _ _ h => h

/-! ## The inversion -/

theorem FInv.of_counter {base : Addr} {s t : State} (hf : FInv base s)
    (hg : ∀ r, r ≠ .esi → t.gpr r = s.gpr r) (hm : t.mem = s.mem) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) : FInv base t :=
  let k := counter_keep (base := base) hg hm hr hw
  ⟨k.scr hf.scr, k.ctx hf.ctx, hm ▸ hf.bounded⟩

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some (!b) := by
  change s.zf.map (!·) = _
  rw [h]; rfl

/-- `m + 1` squarings left. -/
def SqRel (base : Addr) (m : Nat) (t₁ t₂ : State) : Prop :=
  FInv base t₁ ∧ FInv base t₂ ∧ t₁.gpr .esp = t₂.gpr .esp ∧
    t₁.gpr .esi = BitVec.ofNat 32 (m + 1) ∧ t₂.gpr .esi = BitVec.ofNat 32 (m + 1) ∧ m + 1 < 2 ^ 16

theorem SqRel.rf {base : Addr} {m : Nat} {t₁ t₂ : State} (h : SqRel base m t₁ t₂) : RF base t₁ t₂ :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem sqBody_ok {base : Addr} (o : Index) {m : Nat} (hm : m + 1 < 2 ^ 16) {s : State}
    (hf : FInv base s) (he : s.gpr .esi = BitVec.ofNat 32 (m + 1)) :
    WP isa (.seq (mulCall (slot o.val) (slot o.val) (slot o.val)) (.block [.alu .sub .esi (.imm 1)])) s
      fun t => FInv base t ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .esi = BitVec.ofNat 32 m ∧
        t.zf = some (decide (m = 0)) := by
  rw [WP.seq_iff]
  refine WP.mono (mulE hf.scr hf.ctx hf.bounded o o o) fun v ⟨kv, bv, _⟩ => ?_
  have cv : v.gpr .esi = BitVec.ofNat 32 (m + 1) := (kv.regs.1 _ (by decide)).trans he
  refine WP.mono (decCounter_ok (k := m) (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
  exact ⟨FInv.of_counter ⟨kv.scr hf.scr, kv.ctx hf.ctx, bv⟩ wg wm wr ww,
    (wg _ (by decide)).trans (kv.regs.1 _ (by decide)), cw, wz⟩

theorem sqn_rel (base : Addr) (o : Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    RelCT isa (RF base) (Impl.X448.X86.sqn (slot o.val) n) (RF base) := by
  refine RelCT.seq (R := SqRel base (n - 1)) ?_ (RelCT.loop (M := isa) (SqRel base) ?_ (n - 1))
  · refine ((RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ h => h.agree) (hc := .block [] 256)
        (by rfl)).wpDep
      (F := fun (s t : State) => t.gpr .esi = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .esi → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr)
      fun s₁ s₂ _ => ⟨setCounter_ok s₁ n hn', setCounter_ok s₂ n hn'⟩).mono (fun _ _ h => h) ?_
    rintro t₁ t₂ ⟨-, s₁, s₂, ⟨f₁, f₂, e⟩, ⟨c₁, g₁, m₁, r₁, w₁⟩, ⟨c₂, g₂, m₂, r₂, w₂⟩⟩
    have hn1 : n - 1 + 1 = n := by omega
    refine ⟨FInv.of_counter f₁ g₁ m₁ r₁ w₁, FInv.of_counter f₂ g₂ m₂ r₂ w₂, ?_, by rw [hn1]; exact c₁,
      by rw [hn1]; exact c₂, by omega⟩
    rw [g₁ _ (by decide), g₂ _ (by decide), e]
  · intro m
    have tr : RelCT isa (SqRel base m)
        (.seq (mulCall (slot o.val) (slot o.val) (slot o.val)) (.block [.alu .sub .esi (.imm 1)]))
        fun _ _ => True :=
      RelCT.seq ((fieldOp_rel (.mul o o o)).mono (fun _ _ h => h.rf) fun _ _ h => h)
        (RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ h => RF.agree h) (by taint_decide))
    refine (tr.wpDep (F := fun (s t : State) => FInv base t ∧ t.gpr .esp = s.gpr .esp ∧
        t.gpr .esi = BitVec.ofNat 32 m ∧ t.zf = some (decide (m = 0)))
      fun s₁ s₂ h => ⟨sqBody_ok o h.2.2.2.2.2 h.1 h.2.2.2.1, sqBody_ok o h.2.2.2.2.2 h.2.1 h.2.2.2.2.1⟩).mono
      (fun _ _ h => h) ?_
    rintro t₁ t₂ ⟨-, s₁, s₂, h, ⟨f₁, p₁, c₁, z₁⟩, ⟨f₂, p₂, c₂, z₂⟩⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun hz => ⟨f₁, f₂, by rw [p₁, p₂, h.2.2.1]⟩, fun hz => ?_⟩
    have hm0 : m ≠ 0 := fun h0 => by simp [h0] at hz
    refine ⟨m - 1, by omega, f₁, f₂, by rw [p₁, p₂, h.2.2.1], ?_, ?_, by have := h.2.2.2.2.2; omega⟩
    · rw [show m - 1 + 1 = m by omega]; exact c₁
    · rw [show m - 1 + 1 = m by omega]; exact c₂

theorem invert_rel (base : Addr) : RelCT isa (RF base) Impl.X448.X86.invert (RF base) := by
  have h : RelCT isa (RF base) _ (RF base) :=
    (ops_rel [.copy 14 2]).seq <|
    (sqn_rel base 14 (n := 1) (by decide) (by decide)).seq <|
    (ops_rel [.mul 14 14 2, .copy 15 14]).seq <|
    (sqn_rel base 15 (n := 2) (by decide) (by decide)).seq <|
    (ops_rel [.mul 15 15 14, .copy 16 15]).seq <|
    (sqn_rel base 16 (n := 4) (by decide) (by decide)).seq <|
    (ops_rel [.mul 16 16 15, .copy 17 16]).seq <|
    (sqn_rel base 17 (n := 8) (by decide) (by decide)).seq <|
    (ops_rel [.mul 17 17 16, .copy 18 17]).seq <|
    (sqn_rel base 18 (n := 16) (by decide) (by decide)).seq <|
    (ops_rel [.mul 18 18 17, .copy 19 18]).seq <|
    (sqn_rel base 19 (n := 32) (by decide) (by decide)).seq <|
    (ops_rel [.mul 19 19 18, .copy 20 19]).seq <|
    (sqn_rel base 20 (n := 64) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 19]).seq <|
    (sqn_rel base 20 (n := 64) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 19]).seq <|
    (sqn_rel base 20 (n := 16) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 17]).seq <|
    (sqn_rel base 20 (n := 8) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 16]).seq <|
    (sqn_rel base 20 (n := 4) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 15]).seq <|
    (sqn_rel base 20 (n := 2) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 14, .copy 21 20]).seq <|
    (sqn_rel base 21 (n := 1) (by decide) (by decide)).seq <|
    (ops_rel [.mul 21 21 2]).seq <|
    (sqn_rel base 21 (n := 225) (by decide) (by decide)).seq <|
    (sqn_rel base 20 (n := 2) (by decide) (by decide)).seq <|
    (ops_rel [.mul 20 20 2, .mul 21 21 20])
  exact h

/-- The traces of code that keeps `RF` agree in two runs in `FE`. -/
theorem rf_tr {P₀ F : State → State → Prop} {bs : State → Addr}
    (hP : ∀ σ₁ σ₂, P₀ σ₁ σ₂ → bs σ₁ = bs σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp)
    (hF : ∀ σ s, F σ s → FS bs σ s) {c : Prog isa} (h : ∀ b, RelCT isa (RF b) c (RF b)) :
    RelCT isa (Runs P₀ F) c fun _ _ => True :=
  (RelCT.exists_ fun b => (h b).mono (fun _ _ h => h) fun _ _ _ => trivial).mono
    (fun _ _ ⟨_, _, hp, f₁, f₂⟩ => ⟨_, FS.rf (hP _ _ hp).1 (hP _ _ hp).2 (hF _ _ f₁) (hF _ _ f₂)⟩)
    fun _ _ h => h

/-! ## Code reading the arguments -/

/-- An argument's byte, in a run of field arithmetic, is that on entry. -/
theorem FE.argByte {bs : State → Addr} {σ s : State} (h : FE bs σ s) {n : Nat}
    (hfit : (σ.gpr .esp).toNat + 4 + n ≤ 2 ^ 32)
    (hd : ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20], (⟨argAddr σ 0, n⟩ : Region).Disjoint r) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < 4 + n) :
    s.mem (VG.X86.Taint.argByte s k) = σ.mem (VG.X86.Taint.argByte σ k) := by
  have e : VG.X86.Taint.argByte s k = argAddr σ 0 + BitVec.ofNat 64 (k - 4) := by
    simp only [argAddr, Nat.mul_zero, Nat.add_zero]
    rw [show (σ.gpr .esp + BitVec.ofNat 32 4).setWidth 64 = addr (σ.gpr .esp) 4 from rfl,
      addr_eq (by omega)]
    simp only [VG.X86.Taint.argByte, h.sp]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hc : (⟨argAddr σ 0, n⟩ : Region).Contains (VG.X86.Taint.argByte s k) 1 := by
    rw [e]; exact Offset.contains_base _ (by omega) (by omega)
  rw [h.frame _ fun r hr hr' => hd r hr _ hc hr']
  simp only [VG.X86.Taint.argByte, h.sp]

/-- What code reading `n - 4` bytes of arguments needs public: `esp`, `edi`
and the arguments. -/
def τa (n : Nat) : VG.X86.Taint.T := { regs := .ofList [.esp, .edi], flags := false, argLen := n }

theorem FE.wfA {bs : State → Addr} {σ s : State} (h : FE bs σ s) {n : Nat}
    (hfit : (σ.gpr .esp).toNat + n ≤ 2 ^ 32)
    (hwr : ∀ r ∈ σ.wr, Region.Disjoint ⟨(σ.gpr .esp).setWidth 64, n⟩ r) : VG.X86.Taint.Wf (τa n) s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by rw [h.sp]; exact hfit, by rw [h.wr, h.sp]; exact hwr⟩,
    fun _ h => (List.not_mem_nil h).elim⟩

/-- Two runs of field arithmetic agree on what code reading the arguments
needs public, if their entry states agree on the arguments. -/
theorem FE.agreeA {bs : State → Addr} {σ₁ σ₂ s₁ s₂ : State} (h₁ : FE bs σ₁ s₁) (h₂ : FE bs σ₂ s₂)
    (hb : bs σ₁ = bs σ₂) (hs : σ₁.gpr .esp = σ₂.gpr .esp) {n : Nat}
    (hfit₁ : (σ₁.gpr .esp).toNat + n ≤ 2 ^ 32) (hfit₂ : (σ₂.gpr .esp).toNat + n ≤ 2 ^ 32)
    (hwr₁ : ∀ r ∈ σ₁.wr, Region.Disjoint ⟨(σ₁.gpr .esp).setWidth 64, n⟩ r)
    (hwr₂ : ∀ r ∈ σ₂.wr, Region.Disjoint ⟨(σ₂.gpr .esp).setWidth 64, n⟩ r)
    (hd₁ : ∀ r ∈ σ₁.wr ++ [below (σ₁.gpr .esp) 20], (⟨argAddr σ₁ 0, n - 4⟩ : Region).Disjoint r)
    (hd₂ : ∀ r ∈ σ₂.wr ++ [below (σ₂.gpr .esp) 20], (⟨argAddr σ₂ 0, n - 4⟩ : Region).Disjoint r)
    (hm : ∀ k, 4 ≤ k → k < n →
      σ₁.mem (VG.X86.Taint.argByte σ₁ k) = σ₂.mem (VG.X86.Taint.argByte σ₂ k)) :
    VG.X86.Taint.Agree (τa n) s₁ s₂ := by
  have esp : s₁.gpr .esp = s₂.gpr .esp := h₁.sp.trans (hs.trans h₂.sp.symm)
  have edi : s₁.gpr .edi = s₂.gpr .edi := edi_eq h₁.fin.scr (hb ▸ h₂.fin.scr)
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, h₁.wfA hfit₁ hwr₁,
    h₂.wfA hfit₂ hwr₂, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => esp, fun k h4 hk => ?_⟩
  · simp only [τa, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · simp only [τa, VG.X86.Taint.depth, Nat.zero_add] at hk ⊢
    rw [h₁.argByte (by omega) hd₁ h4 (by omega), h₂.argByte (by omega) hd₂ h4 (by omega)]
    exact hm k h4 hk

end VG.Proof.X448.X86
