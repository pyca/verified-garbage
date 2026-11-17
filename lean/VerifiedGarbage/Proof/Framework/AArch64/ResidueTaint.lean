module

public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# What a function leaves in its registers (AArch64)

`rtaint` is the vector taint analysis (`VectorTaint.taint`) extended to the
rest of what `Outside` compares: the condition flags (public or not), how
many low bits of `x0`, the result, may differ, and what no instruction makes
secret (the regions, PSTATE.DIT, `unknowns`, and the memory outside the
regions, which a store, writing only inside a writable region, leaves as it
was). It knows `movi0`, which zeroes a vector register, as public.

`noResidue_of_check`: code whose analysis from everything public (`init`, as
`Outside 0` has it) ends with every register public, the flags public, and at
most the low `r` bits of `x0` secret (`done r`) returns without secret residue
(`AArch64.NoResidue`) with an `r`-bit result, whatever its contract. Code
that leaves a secret in a register clears it before it returns (a `movz` or a
`movi0`), which the analysis then sees.

The analysis has no calls or frames (its `call`, `push` and `pop` fail).
-/

@[expose] public section

namespace VG.AArch64.RTaint

open VG.AArch64

/-- The public registers and vector registers (`VectorTaint.T`), whether the
flags are public, and how many low bits of `x0` may be secret. -/
abbrev T := VectorTaint.T × Bool × Nat

/-- The condition flags agree. -/
def Flags (s₁ s₂ : State) : Prop := s₁.c = s₂.c ∧ s₁.nf = s₂.nf ∧ s₁.zf = s₂.zf ∧ s₁.vf = s₂.vf

/-- What no instruction of the analysis makes secret. -/
def Rest (s₁ s₂ : State) : Prop :=
  s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ s₁.dit = s₂.dit ∧ s₁.unknowns = s₂.unknowns ∧
    Residue.MemOff (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

def Agree (τ : T) (s₁ s₂ : State) : Prop :=
  VectorTaint.Agree τ.1 s₁ s₂ ∧ (τ.2.1 = true → Flags s₁ s₂) ∧
    s₁.gpr .x0 >>> τ.2.2 = s₂.gpr .x0 >>> τ.2.2 ∧ Rest s₁ s₂

/-- `VectorTaint.step`, with `movi0` giving a public vector register, `mov` a copy of its
source's, and every other operation it does not know making secret only the register it writes
(`VOp.dst`), not every one. -/
def vopStep (τ : VectorTaint.T) : VOp → Option VectorTaint.T
  | .movi0 d => some (τ.1, τ.2.insert d)
  | .mov d n => some (τ.1, VectorTaint.setV τ.2 d (τ.2.mem n))
  | .dup a d n => VectorTaint.step τ (.vop (.dup a d n))
  | .add a d n m => VectorTaint.step τ (.vop (.add a d n m))
  | .sub a d n m => VectorTaint.step τ (.vop (.sub a d n m))
  | op => some (τ.1, τ.2.erase op.dst)

def vstep (τ : VectorTaint.T) : Instr → Option VectorTaint.T
  | .vop op => vopStep τ op
  | .ldrq t n off => (Taint.step τ.1 (.ldrq t n off)).map fun g => (g, τ.2.erase t)
  | i => VectorTaint.step τ i

/-- The instructions that write the flags. -/
def setsFlags : Instr → Bool
  | .adds .. | .adcs .. | .subs .. | .sbcs .. | .tst .. | .ccmp .. => true
  | _ => false

/-- Whether the flags are public after `i`, from the public registers `g`
before it and whether the flags were. -/
def fstep (g : Taint.T) (f : Bool) : Instr → Bool
  | .adds _ _ n m | .subs _ _ n m | .tst _ n m => Taint.pub g n && Taint.pub g m
  | i => !setsFlags i && f

/-- How many low bits of `x0` may be secret after `i`, from the public
registers `g'` after it and the bits `h` before. -/
def hstep (g' : Taint.T) (h : Nat) (i : Instr) : Nat :=
  if Taint.pub g' .x0 then 0
  else if !clobbers i .x0 then h
  else match i with
    | .lsr .x .x0 _ sh => 64 - sh
    | .movz .w .x0 _ _ | .lsr .w .x0 _ _ | .logic _ .w .x0 _ _ | .add .w .x0 _ _
    | .sub .w .x0 _ _ | .addImm .w .x0 _ _ | .subImm .w .x0 _ _ => 32
    | _ => 64

def step (τ : T) (i : Instr) : Option T :=
  (vstep τ.1 i).map fun v => (v, fstep τ.1.1 τ.2.1 i, hstep v.1 τ.2.2 i)

/-! ## Soundness -/

/-- An instruction that writes no flag leaves them as they were. -/
theorem exec_flags {i : Instr} {s s' : State} (hi : setsFlags i = false) (he : exec i s = some s') :
    s'.c = s.c ∧ s'.nf = s.nf ∧ s'.zf = s.zf ∧ s'.vf = s.vf := by
  cases i <;> simp only [setsFlags, Bool.true_eq_false] at hi
  case ldp => obtain ⟨_, _, rfl⟩ := exec_ldp_eq he; exact ⟨rfl, rfl, rfl, rfl⟩
  case stp => obtain ⟨_, rfl⟩ := exec_stp_eq he; exact ⟨rfl, rfl, rfl, rfl⟩
  all_goals
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
  all_goals
    repeat' first
      | split at he
      | simp only [Option.map_eq_some_iff] at he
      | rcases he with ⟨_, _, he⟩
  all_goals
    try simp_all only [State.store]
  all_goals
    repeat' first | split at he | cases he
  all_goals first
    | exact ⟨rfl, rfl, rfl, rfl⟩
    | simp_all only [RegUpd.c_write, RegUpd.nf_write, RegUpd.zf_write, RegUpd.vf_write, and_self]

/-- No instruction changes `unknowns`, and only `msr DIT` PSTATE.DIT, to a
value of its own. -/
theorem exec_ud {i : Instr} {s s' : State} (he : exec i s = some s') :
    s'.unknowns = s.unknowns ∧ (s'.dit = s.dit ∨ ∃ on, i = .msrDitImm on ∧ s'.dit = on) := by
  cases i
  case ldp => obtain ⟨_, _, rfl⟩ := exec_ldp_eq he; exact ⟨rfl, .inl rfl⟩
  case stp => obtain ⟨_, rfl⟩ := exec_stp_eq he; exact ⟨rfl, .inl rfl⟩
  case msrDitImm on =>
    simp only [reduceExec, Option.some.injEq] at he
    subst he; exact ⟨rfl, .inr ⟨on, rfl, rfl⟩⟩
  case mrsDit t =>
    simp only [reduceExec] at he
    split at he <;> (cases he; exact ⟨rfl, .inl rfl⟩)
  all_goals
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
  all_goals
    repeat' first
      | split at he
      | simp only [Option.map_eq_some_iff] at he
      | rcases he with ⟨_, _, he⟩
  all_goals
    try simp_all only [State.store]
  all_goals
    repeat' first | split at he | cases he
  all_goals first
    | exact ⟨rfl, .inl rfl⟩
    | exact ⟨rfl, trivial⟩
    | simp_all only [true_or, and_self]

theorem dit_step {i : Instr} {s₁ s₂ s₁' s₂' : State} (h : s₁.dit = s₂.dit)
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') : s₁'.dit = s₂'.dit := by
  by_cases hi : ∃ on, i = .msrDitImm on
  · obtain ⟨on, rfl⟩ := hi
    simp only [reduceExec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂; rfl
  · have g : ∀ {s s' : State}, exec i s = some s' → s'.dit = s.dit := fun e =>
      (exec_ud e).2.resolve_right fun ⟨on, h₁, _⟩ => hi ⟨on, h₁⟩
    rw [g e₁, g e₂, h]

theorem rest_step {i : Instr} {s₁ s₂ s₁' s₂' : State} (h : Rest s₁ s₂)
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') : Rest s₁' s₂' := by
  obtain ⟨hrd, hwr, hd, hu, hm⟩ := h
  obtain ⟨r₁, w₁, -, f₁⟩ := exec_regions e₁
  obtain ⟨r₂, w₂, -, f₂⟩ := exec_regions e₂
  have u₁ := (exec_ud e₁).1
  have u₂ := (exec_ud e₂).1
  refine ⟨by rw [r₁, r₂, hrd], by rw [w₁, w₂, hwr], dit_step hd e₁ e₂, by rw [u₁, u₂, hu], ?_⟩
  · intro x hx
    rw [r₁, w₁] at hx
    have hw : ∀ r ∈ s₁.wr, ¬ r.Contains x 1 := fun r hr => hx r (List.mem_append_right _ hr)
    have hw₂ : ∀ r ∈ s₂.wr, ¬ r.Contains x 1 := by rw [← hwr]; exact hw
    rw [f₁ x hw, f₂ x hw₂]
    exact hm x hx

theorem flags_step {τ : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    fstep τ.1.1 τ.2.1 i = true → Flags s₁' s₂' := by
  intro hf
  have hg := ha.1.1
  cases i
  case adds sz d n m | subs sz d n m =>
    simp only [fstep, Bool.and_eq_true] at hf
    simp only [reduceExec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    simp only [State.read, hg.reg hf.1, hg.reg hf.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  case tst sz n m =>
    simp only [fstep, Bool.and_eq_true] at hf
    simp only [reduceExec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    simp only [State.read, hg.reg hf.1, hg.reg hf.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  all_goals
    simp only [fstep, setsFlags, Bool.not_true, Bool.false_and, Bool.not_false, Bool.true_and,
      Bool.false_eq_true] at hf
  all_goals
    obtain ⟨c₁, n₁, z₁, v₁⟩ := exec_flags rfl e₁
    obtain ⟨c₂, n₂, z₂, v₂⟩ := exec_flags rfl e₂
    obtain ⟨hc, hn, hz, hv⟩ := ha.2.1 hf
    exact ⟨by rw [c₁, c₂, hc], by rw [n₁, n₂, hn], by rw [z₁, z₂, hz], by rw [v₁, v₂, hv]⟩

theorem shr_shr (x : BitVec 64) (a b : Nat) : x >>> a >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

/-- Two values that agree above bit `a` agree above any bit `b ≥ a`. -/
theorem shr_mono {x y : BitVec 64} {a b : Nat} (h : x >>> a = y >>> a) (hab : a ≤ b) :
    x >>> b = y >>> b := by
  rw [show b = a + (b - a) by omega, ← shr_shr, ← shr_shr, h]

theorem w_shift (v : BitVec 32) : v.setWidth 64 >>> 32 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]
  have := v.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt this]
  rfl

theorem shift64 (x : BitVec 64) : x >>> 64 = 0 := BitVec.ushiftRight_eq_zero (Nat.le_refl _)

theorem x0_step {τ : T} {i : Instr} {v : VectorTaint.T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hv : VectorTaint.Agree v s₁' s₂')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    s₁'.gpr .x0 >>> hstep v.1 τ.2.2 i = s₂'.gpr .x0 >>> hstep v.1 τ.2.2 i := by
  unfold hstep
  cases hp : Taint.pub v.1 .x0
  case true => simp only [↓reduceIte, hv.1.reg hp]
  cases hk : clobbers i .x0
  case false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, exec_gpr hk e₁, exec_gpr hk e₂]
    exact ha.2.2.1
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  split
  · rename_i n sh
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hsh
    simp only [hsh, ↓reduceIte] at e₂
    cases e₁; cases e₂
    simp only [RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq] at hsh ⊢
    rw [shr_shr, shr_shr, BitVec.ushiftRight_eq_zero (by omega), BitVec.ushiftRight_eq_zero (by omega)]
  all_goals first
    | (rw [shift64, shift64])
    | (simp only [reduceExec] at e₁ e₂
       (try split at e₁ <;> [skip; cases e₁])
       (try simp only [*, ↓reduceIte] at e₂)
       cases e₁; cases e₂
       simp only [RegUpd.gpr_write_self, w_shift])

/-- A vector operation writes only `op.dst`: every other vector register that
was public stays so. -/
theorem vop_erase {τ : VectorTaint.T} {op : VOp} {s₁ s₂ s₁' s₂' : State}
    (ha : VectorTaint.Agree τ s₁ s₂) (e₁ : exec (.vop op) s₁ = some s₁')
    (e₂ : exec (.vop op) s₂ = some s₂') :
    addrs (.vop op) s₁ = addrs (.vop op) s₂ ∧ VectorTaint.Agree (τ.1, τ.2.erase op.dst) s₁' s₂' := by
  simp only [reduceExec] at e₁ e₂
  obtain ⟨⟨d₁, x₁⟩, hp₁, rfl⟩ := Option.map_eq_some_iff.mp e₁
  obtain ⟨⟨d₂, x₂⟩, hp₂, rfl⟩ := Option.map_eq_some_iff.mp e₂
  refine ⟨rfl, ⟨ha.1.1, ha.1.2⟩, fun w hw => ?_⟩
  rw [RegSet.mem_erase] at hw
  have h₁ : w ≠ d₁ := VOp.eval_dst hp₁ ▸ hw.1
  have h₂ : w ≠ d₂ := VOp.eval_dst hp₂ ▸ hw.1
  rw [RegUpd.v_setV_of_ne _ _ h₁, RegUpd.v_setV_of_ne _ _ h₂]
  exact ha.2 w hw.2

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hvs : addrs i s₁ = addrs i s₂ ∧ VectorTaint.Agree v s₁' s₂' := by
    cases i
    case vop op =>
      simp only [vstep] at hv
      cases op
      case movi0 d =>
        simp only [vopStep, Option.some.injEq] at hv
        subst hv
        simp only [reduceExec, reduceVOpEval, Option.map_some, Option.some.injEq] at e₁ e₂
        subst e₁ e₂
        refine ⟨rfl, ⟨ha.1.1.1, ha.1.1.2⟩, fun w hw => ?_⟩
        rw [RegSet.mem_insert] at hw
        by_cases hd : w = d
        · subst hd; simp only [RegUpd.v_setV_self]
        · rw [RegUpd.v_setV_of_ne _ _ hd, RegUpd.v_setV_of_ne _ _ hd]
          exact ha.1.2 w (hw.resolve_left hd)
      case mov d n =>
        simp only [vopStep, Option.some.injEq] at hv
        subst hv
        simp only [reduceExec, reduceVOpEval, Option.map_some, Option.some.injEq] at e₁ e₂
        subst e₁ e₂
        refine ⟨rfl, ⟨ha.1.1.1, ha.1.1.2⟩, fun w hw => ?_⟩
        unfold VectorTaint.setV at hw
        by_cases hd : w = d
        · subst hd
          simp only [RegUpd.v_setV_self]
          split at hw
          · exact ha.1.2 n (by assumption)
          · simp at hw
        · rw [RegUpd.v_setV_of_ne _ _ hd, RegUpd.v_setV_of_ne _ _ hd]
          split at hw
          · exact ha.1.2 w ((RegSet.mem_insert.mp hw).resolve_left hd)
          · exact ha.1.2 w (RegSet.mem_erase.mp hw).2
      case dup | add | sub => exact VectorTaint.step_sound ha.1 hv e₁ e₂
      all_goals
        simp only [vopStep, Option.some.injEq] at hv
        subst hv
        exact vop_erase ha.1 e₁ e₂
    case ldrq t n off =>
      simp only [vstep] at hv
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hv
      have ht := Taint.step_sound ha.1.1 hg e₁ e₂
      refine ⟨ht.1, ht.2, fun w hw => ?_⟩
      rw [RegSet.mem_erase] at hw
      simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨_, -, _, -, rfl⟩ := e₁
      obtain ⟨_, -, _, -, rfl⟩ := e₂
      rw [RegUpd.v_setV_of_ne _ _ hw.1, RegUpd.v_setV_of_ne _ _ hw.1]
      exact ha.1.2 w hw.2
    all_goals exact VectorTaint.step_sound ha.1 hv e₁ e₂
  exact ⟨hvs.1, hvs.2, flags_step ha e₁ e₂, x0_step ha hvs.2 e₁ e₂, rest_step ha.2.2.2 e₁ e₂⟩

end VG.AArch64.RTaint

namespace VG.AArch64

open RTaint in
/-- The residue analysis of AArch64 (see `RTaint`). -/
def rtaint : VG.Taint isa where
  T := RTaint.T
  Agree := RTaint.Agree
  step := RTaint.step
  step_sound := RTaint.step_sound
  condPub τ := Taint.condPub τ.1.1
  cond_sound h hc := Taint.cond_sound h.1.1 hc
  meet (τ σ : RTaint.T) := ((τ.1.1.inter σ.1.1, τ.1.2.inter σ.1.2), τ.2.1 && σ.2.1, max τ.2.2 σ.2.2)
  meet_left h := ⟨⟨⟨h.1.1.1, fun r hr => h.1.1.2 r (RegSet.mem_inter.mp hr).1⟩,
      fun v hv => h.1.2 v (RegSet.mem_inter.mp hv).1⟩,
    fun hf => h.2.1 (Bool.and_eq_true _ _ ▸ hf).1, shr_mono h.2.2.1 (Nat.le_max_left _ _), h.2.2.2⟩
  meet_right h := ⟨⟨⟨h.1.1.1, fun r hr => h.1.1.2 r (RegSet.mem_inter.mp hr).2⟩,
      fun v hv => h.1.2 v (RegSet.mem_inter.mp hv).2⟩,
    fun hf => h.2.1 (Bool.and_eq_true _ _ ▸ hf).2, shr_mono h.2.2.1 (Nat.le_max_right _ _), h.2.2.2⟩
  le (τ σ : RTaint.T) := τ.1.1.subset σ.1.1 && τ.1.2.subset σ.1.2 && (!τ.2.1 || σ.2.1) && Nat.ble σ.2.2 τ.2.2
  le_sound hl h := by
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hl
    obtain ⟨⟨⟨hg, hv⟩, hf⟩, hh⟩ := hl
    refine ⟨⟨⟨h.1.1.1, fun r hr => h.1.1.2 r (RegSet.mem_of_subset hg hr)⟩,
      fun v hr => h.1.2 v (RegSet.mem_of_subset hv hr)⟩, fun ht => ?_, ?_, h.2.2.2⟩
    · rcases hf with hf | hf
      · rw [hf] at ht; cases ht
      · exact h.2.1 hf
    · exact shr_mono h.2.2.1 (Nat.le_of_ble_eq_true hh)
  call _ := none
  call_sound _ hs := nomatch hs
  ret _ := none
  ret_sound _ hs := nomatch hs
  push _ _ := none
  push_sound _ hs := nomatch hs
  pop _ _ := none
  pop_sound _ hs := nomatch hs

namespace RTaint

/-- Every register. -/
def allRegs : RegSet Reg := RegSet.ofList
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
   .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

/-- Every vector register. -/
def allVRegs : RegSet VReg := RegSet.ofList
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15,
   .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

/-- Everything public, as `Outside 0` has it. -/
def init : T := ((allRegs, allVRegs), true, 0)

/-- Every register but `x0` and every vector register public, the flags
public, and at most the low `r` bits of `x0` secret. -/
def done (r : Nat) (τ : T) : Bool :=
  (allRegs.erase .x0).subset τ.1.1 && allVRegs.subset τ.1.2 && τ.2.1 && Nat.ble τ.2.2 r

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by
  rw [allRegs, RegSet.mem_ofList]; cases r <;> simp

theorem mem_allVRegs (v : VReg) : v ∈ allVRegs := by
  rw [allVRegs, RegSet.mem_ofList]; cases v <;> simp

theorem agree_init {s₁ s₂ : State} (h : Outside 0 s₁ s₂) (hu : s₁.unknowns = s₂.unknowns) :
    rtaint.Agree init s₁ s₂ := by
  obtain ⟨hrd, hwr, hg, hx0, hsp, hc, hn, hz, hvf, hd, hv, hm⟩ := h
  refine ⟨⟨⟨hsp, fun r _ => ?_⟩, fun v _ => by rw [hv]⟩, fun _ => ⟨hc, hn, hz, hvf⟩, hx0,
    hrd, hwr, hd, hu, hm⟩
  by_cases hr : r = .x0
  · subst hr; simpa using hx0
  · exact hg r hr

theorem outside_of_done {τ : T} {r : Nat} {s₁ s₂ : State} (h : rtaint.Agree τ s₁ s₂)
    (hd : done r τ = true) : Outside r s₁ s₂ := by
  simp only [done, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hg, hv⟩, hf⟩, hr⟩ := hd
  obtain ⟨⟨⟨hsp, hgr⟩, hvr⟩, hfl, hx0, hrd, hwr, hdit, -, hm⟩ := h
  obtain ⟨hc, hn, hz, hvf⟩ := hfl hf
  refine ⟨hrd, hwr, fun q hq => hgr q (RegSet.mem_of_subset hg (RegSet.mem_erase.mpr
    ⟨hq, mem_allRegs q⟩)), ?_, hsp, hc, hn, hz, hvf, hdit,
    funext fun v => hvr v (RegSet.mem_of_subset hv (mem_allVRegs v)), hm⟩
  exact shr_mono hx0 (Nat.le_of_ble_eq_true hr)

/-- Code whose residue analysis from everything public ends in `done r`
returns without secret residue, with an `r`-bit result, whatever its
contract. -/
theorem noResidue_of_check {c : Prog isa} {r : Nat}
    (h : ∃ hc, (rtaint.check init c hc).any (done r) = true) (k : Contract isa) :
    NoResidue c k r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ _ ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : rtaint.check init c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
    rw [hτ] at h
    exact outside_of_done (VG.Taint.check_sound hτ (agree_init ho hu) e₁ e₂).2 h

end RTaint

end VG.AArch64
