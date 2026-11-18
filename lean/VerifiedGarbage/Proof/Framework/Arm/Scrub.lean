module

public import VerifiedGarbage.TCB.Arm.Residue
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.CallWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-!
# Returning without secret residue (ARMv7)

`NoResidue` (`TCB/Arm/Residue.lean`) asks that two runs of a function that
agree on its public data and on everything outside its buffers end agreeing
on everything outside the buffers but the result: the registers, the
condition flags, and the memory outside the buffers.

Code without frames (`Code.noFrames`) writes memory only within the regions
its state permits (`Exec.regions`), which are the function's buffers, and the
calling convention restores `r4`–`r11`, `lr` and `sp` (`abiPreserved`). What
is left are the registers a callee may change, `r0`–`r3` and `r12`, and the
flags. `scrub rb c` is `c` followed by instructions that set them to
constants (`tail`): `r2`, `r3` and `r12` to zero, the flags to those of
comparing zero with itself, and of the result `r1 ++ r0` what is above its
`rb` bits to zero (`r1` for a result of 32 bits, both for no result; ARM's
results are of 0, 32 or 64 bits, `retBits_cases`). They read no memory and
leak nothing, so `scrub rb c` meets `c`'s contract (`Verified.scrub`), and
every run of it ends with the same values there: it returns without secret
residue.

`scrubReg` is a registration with its code scrubbed, which proves it;
`scrubRegF` is the same for code with frames (see "Code with frames" below).
-/

@[expose] public section

namespace VG.Arm

/-! ### Runs with the same trace use the same unknowns
The trace of a run records each branch it takes, and each instruction
leaks a number of addresses fixed by the instruction, so two runs of code
without indirect calls that leak the same trace take the same path: they
make the same calls and release the same frames, and so use the same
number of the state's unknowns (`Exec.path`). Two runs that start with the
same unknowns therefore end with the same unknowns, which a proof that a
function returns without secret residue needs when what a release leaves
in a frame depends on them.
-/

/-- `c`, and the functions it calls, make no indirect call. -/
def noIcall : Prog isa → Bool
  | .block _ => true
  | .seq a b => noIcall a && noIcall b
  | .ite _ t e => noIcall t && noIcall e
  | .loop b _ => noIcall b
  | .call _ b => noIcall b
  | .frame _ b _ => noIcall b
  | .icall .. => false

theorem exec_unknowns {i : Instr} {s s' : State} (h : exec i s = some s') : s'.unknowns = s.unknowns := by
  cases i <;> simp only [reduceExec, State.load32, State.load8, State.store32, State.store8,
      Option.map_eq_some_iff, reduceCtorEq] at h <;> (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Option.map_some, Option.map_none] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, rfl⟩ := h; rfl)
    | cases h

/-- How many addresses an instruction leaks depends on the instruction alone. -/
theorem addrs_length (i : Instr) (s s' : State) : (addrs i s).length = (addrs i s').length := by
  cases i <;> simp [addrs, words]

theorem push_unknowns {i : Instr} {s s' : State} (h : push i s = some s') : s'.unknowns = s.unknowns := by
  cases i <;> simp only [push, reduceCtorEq] at h <;> (repeat' split at h) <;>
    first | (cases h; rfl) | cases h

/-- Two releases of a frame by the same instruction, from states with the same
unknowns, leave the same unknowns. -/
theorem pop_unknowns {j : Instr} {a₁ b₁ c₁ a₂ b₂ c₂ : State} (h₁ : isa.pop j a₁ b₁ = some c₁)
    (h₂ : isa.pop j a₂ b₂ = some c₂) (hu : b₁.unknowns = b₂.unknowns) : c₁.unknowns = c₂.unknowns := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h₁ h₂ <;> split at h₁ <;> split at h₂ <;>
    simp only [Option.some.injEq, reduceCtorEq] at h₁ h₂ <;> subst h₁ h₂ <;> (dsimp only; rw [hu])

/-- Two releases of a frame by the same instruction leave the same byte at
`x` if it was the same before them, in states with the same stack pointer
and unknowns. -/
theorem pop_mem_congr {j : Instr} {a₁ b₁ c₁ a₂ b₂ c₂ : State} (h₁ : isa.pop j a₁ b₁ = some c₁)
    (h₂ : isa.pop j a₂ b₂ = some c₂) (hsp : b₁.sp = b₂.sp) (hu : b₁.unknowns = b₂.unknowns) {x : Addr}
    (hx : b₁.mem x = b₂.mem x) : c₁.mem x = c₂.mem x := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h₁ h₂ <;> split at h₁ <;> split at h₂ <;>
    simp only [Option.some.injEq, reduceCtorEq] at h₁ h₂ <;> subst h₁ h₂ <;>
    (dsimp only; simp only [lose, hsp, hu, hx])

theorem execBlock_path : ∀ {is : List Instr} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) →
    t₁.length = t₂.length ∧ (s₁.unknowns = s₂.unknowns → s₁'.unknowns = s₂'.unknowns)
  | [], _, _, _, _, _, _, h₁, h₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, id⟩
  | i :: is, s₁, s₂, s₁', s₂', t₁, t₂, h₁, h₂ => by
    simp only [execBlock] at h₁ h₂
    split at h₁
    · cases h₁
    · rename_i u₁ e₁
      split at h₂
      · cases h₂
      · rename_i u₂ e₂
        obtain ⟨⟨v₁, r₁⟩, k₁, q₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨⟨v₂, r₂⟩, k₂, q₂⟩ := Option.map_eq_some_iff.mp h₂
        cases q₁; cases q₂
        obtain ⟨hl, hu⟩ := execBlock_path k₁ k₂
        refine ⟨?_, fun h => hu ?_⟩
        · simp only [List.length_append, List.length_map, hl, addrs_length i s₁ s₂]
        · rw [exec_unknowns e₁, exec_unknowns e₂, h]

/-- Two runs of code without indirect calls from states with the same
unknowns, whose traces agree up to what follows them, have the same trace
and end with the same unknowns. -/
theorem Exec.path {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    noIcall c = true → ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak}, Exec isa c s₂ t₂ s₂' →
      t₁ ++ r₁ = t₂ ++ r₂ → s₁.unknowns = s₂.unknowns → t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns := by
  induction e₁ with
  | block h =>
    intro _ s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    cases e₂ with
    | block h' =>
      obtain ⟨hl, hk⟩ := execBlock_path h h'
      exact ⟨(List.append_inj ht hl).1, hk hu⟩
  | seq _ _ ih₁ ih₂ =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | seq a b =>
      simp only [List.append_assoc] at ht
      obtain ⟨rfl, hm⟩ := ih₁ hc.1 a ht hu
      obtain ⟨rfl, he⟩ := ih₂ hc.2 b (List.append_cancel_left ht) hm
      exact ⟨rfl, he⟩
  | iteT _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ b =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih hc.1 b ht hu
      exact ⟨rfl, he⟩
    | iteF _ b => simp at ht
  | iteF _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ b => simp at ht
    | iteF _ b =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih hc.2 b ht hu
      exact ⟨rfl, he⟩
  | loopExit _ _ ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | loopExit b _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨rfl, he⟩ := ih hc b ht hu
      exact ⟨rfl, he⟩
    | loopNext b _ _ =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, -⟩ := ih hc b ht hu
      simp at ht
  | loopNext _ _ _ ih₁ ih₂ =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    cases e₂ with
    | loopExit b _ =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, -⟩ := ih₁ hc b ht hu
      simp at ht
    | loopNext b _ l =>
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨rfl, hm⟩ := ih₁ hc b ht hu
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, he⟩ := ih₂ hc l ht hm
      exact ⟨rfl, he⟩
  | call k _ q ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | call k' b q' =>
      simp only [isa, call, Option.some.injEq] at k k'
      simp only [isa, ret] at q q'
      split at q <;> [cases q; cases q]
      split at q' <;> [cases q'; cases q']
      subst k k'
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht ⊢
      exact ih hc b ht (by simp only [hu])
  | frame p _ q ih =>
    intro hc s₂ s₂' t₂ r₁ r₂ e₂ ht hu
    simp only [noIcall] at hc
    cases e₂ with
    | frame p' b q' =>
      simp only [List.append_assoc] at ht
      obtain ⟨ha, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact addrs_length _ _ _)
      obtain ⟨rfl, hm⟩ := ih hc b ht (by
        rw [show isa.push = push from rfl] at p p'
        rw [push_unknowns p, push_unknowns p', hu])
      have ht' := List.append_cancel_left ht
      obtain ⟨hb, -⟩ := List.append_inj ht' (by simp only [List.length_map]; exact addrs_length _ _ _)
      rw [ha, hb]
      exact ⟨rfl, pop_unknowns q q' hm⟩
  | icall => intro hc; simp [noIcall] at hc
  | icallNext => intro hc; simp [noIcall] at hc

end VG.Arm

namespace VG.Arm.Scrub

/-- Zero what of the result `r1 ++ r0` is above its `rb` bits. -/
def retFix (rb : Nat) : List Instr :=
  if rb = 0 then [.mov .r0 (.imm 0), .mov .r1 (.imm 0)]
  else if rb ≤ 32 then [.mov .r1 (.imm 0)] else []

/-- Set the registers a callee may change, but the result, and the flags to
constants. -/
def tail (rb : Nat) : List Instr :=
  retFix rb ++ [.mov .r2 (.imm 0), .mov .r3 (.imm 0), .mov .r12 (.imm 0), .cmp .r2 (.reg .r2)]

/-- `c`, then `tail rb`. -/
def scrub (rb : Nat) (c : Prog isa) : Prog isa := .seq c (.block (tail rb))

/-- A result on ARM is of 0, 32 or 64 bits. -/
theorem retBits_cases (sig : Sig) : sig.retBits 32 = 0 ∨ sig.retBits 32 = 32 ∨ sig.retBits 32 = 64 := by
  unfold Sig.retBits
  cases sig.ret with
  | none => exact .inl rfl
  | some ty => cases ty <;> simp [IntTy.bits]

theorem append_shr32 (a : BitVec 32) : (0#32 ++ a) >>> 32 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.zero_shiftLeft, Nat.zero_or, Nat.shiftRight_eq_div_pow]
  omega

theorem append_low32 (a b : BitVec 32) : BitVec.setWidth 32 (0#32 ++ a) = BitVec.setWidth 32 (b ++ a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp only [hi, decide_true, Bool.true_and, ↓reduceIte]

theorem shr64 (x : BitVec 64) : x >>> 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod, Nat.shiftRight_eq_div_pow]
  omega

/-- What `tail rb` leaves: it leaks nothing, keeps the memory, the regions,
the stack pointer, the registers the calling convention preserves and the
`rb` bits of the result, and leaves constants in the others and the flags. -/
theorem tail_run {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (u : State) :
    ∃ u', execBlock isa (tail rb) u = some (u', []) ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      u'.sp = u.sp ∧ (∀ r ∈ preserved, u'.gpr r = u.gpr r) ∧
      u'.gpr .r2 = 0 ∧ u'.gpr .r3 = 0 ∧ u'.gpr .r12 = 0 ∧
      u'.n = false ∧ u'.z = true ∧ u'.c = true ∧ u'.v = false ∧
      (u'.gpr .r1 ++ u'.gpr .r0) >>> rb = 0 ∧
      (u'.gpr .r1 ++ u'.gpr .r0).setWidth rb = (u.gpr .r1 ++ u.gpr .r0).setWidth rb := by
  rcases hrb with rfl | rfl | rfl
  · refine ⟨_, by simp [tail, retFix, execBlock, isa, exec, Op2.eval, addrs]; rfl, ?_⟩
    simp only [subFlags, preserved, State.setReg]
    simp
    exact (BitVec.eq_nil _).trans (BitVec.eq_nil _).symm
  · refine ⟨_, by simp [tail, retFix, execBlock, isa, exec, Op2.eval, addrs]; rfl, ?_⟩
    simp only [subFlags, preserved, State.setReg]
    simp
    exact ⟨append_shr32 _, append_low32 _ _⟩
  · refine ⟨_, by simp [tail, retFix, execBlock, isa, exec, Op2.eval, addrs]; rfl, ?_⟩
    simp only [subFlags, preserved, State.setReg]
    simp
    exact shr64 _

/-- What `Verified.scrub` and `Verified.scrubF` need of the calling convention
a contract is for: `abi`'s, possibly with tables of constants
(`Abi.withConsts`), which add readable regions apart from the stack the
function uses, and with tables of functions (`Abi.withTables`). -/
structure ScrubAbi (A : Abi isa) : Prop where
  ptrBits : A.ptrBits = 32
  mem : ∀ s, A.mem s = s.mem
  ret : ∀ s, A.ret s = s.gpr .r1 ++ s.gpr .r0
  reserved : A.reserved = abi.reserved
  wr : ∀ s, A.wr s = s.wr
  wf : ∀ ws n s, A.wf ws n s → (n = 0 ∨ n ≤ s.sp.toNat) ∧
    ∀ r ∈ s.rd, r ∉ A.rd s → ∀ q ∈ abi.reserved n s, q.Disjoint r
  pub : ∀ s₁ s₂, A.pub s₁ s₂ → s₁.sp = s₂.sp
  rdSub : ∀ s r, r ∈ A.rd s → r ∈ s.rd
  argsLen : ∀ ws f, A.args ws = some f → ∀ s, (f s).length = ws.length

theorem abi_args_len (ws : List Nat) (f : State → List (BitVec 64)) (h : abi.args ws = some f) (s : State) :
    (f s).length = ws.length := by
  simp only [abi] at h
  split at h <;> cases h
  simp only [List.length_map, classify_length]

theorem abi_wf_stack {ws : List Nat} {n : Nat} {s : State} (h : abi.wf ws n s) :
    n = 0 ∨ n ≤ s.sp.toNat := by
  cases n with
  | zero => exact .inl rfl
  | succ n => exact .inr h.1

theorem ScrubAbi.plain : ScrubAbi abi :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl,
    fun _ _ _ h => ⟨abi_wf_stack h, fun _ hr hn => absurd hr hn⟩, fun _ _ h => h, fun _ _ h => h, abi_args_len⟩

theorem ScrubAbi.consts (cs : List (String × List (BitVec 64))) : ScrubAbi (abi.withConsts cs) := by
  cases cs with
  | nil => exact ScrubAbi.plain
  | cons c cs =>
    refine ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun ws n s h => ?_, fun _ _ h => h.1,
      fun _ _ h => List.mem_of_mem_take h, abi_args_len⟩
    obtain ⟨hw, hdrop, -, hdis, -⟩ := h
    refine ⟨abi_wf_stack hw, fun r hr hn q hq => ?_⟩
    have hr' : r ∈ (abi.rd s).drop ((abi.rd s).length - (c :: cs).length) := by
      change r ∈ abi.rd s at hr
      rw [← List.take_append_drop ((abi.rd s).length - (c :: cs).length) (abi.rd s)] at hr
      rcases List.mem_append.mp hr with h | h
      · exact absurd h hn
      · exact h
    rw [hdrop] at hr'
    exact ((hdis r hr').2.2 q hq).symm

theorem ScrubAbi.tables {A : Abi isa} (hA : ScrubAbi A) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi (A.withTables sig ts) := by
  cases ts with
  | nil => exact hA
  | cons t ts =>
    exact ⟨hA.ptrBits, hA.mem, hA.ret, hA.reserved, hA.wr, fun ws n s h => hA.wf ws n s h.1,
      fun s₁ s₂ h => hA.pub s₁ s₂ h.1, hA.rdSub, hA.argsLen⟩

/-- The calling convention of every ARM artifact (`Api.artifact`). -/
theorem ScrubAbi.of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi ((abi.withConsts cs).withTables sig ts) :=
  (ScrubAbi.consts cs).tables sig ts

/-- A postcondition of `Sig.contract` reads of the state on return its
memory and the bits of its result. -/
theorem contract_post_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s u u' : State}
    (h : (sig.contract A pre post wa stack leak).post s u) (hm : u'.mem = u.mem)
    (hr : (u'.gpr .r1 ++ u'.gpr .r0).setWidth (sig.retBits A.ptrBits) =
      (u.gpr .r1 ++ u.gpr .r0).setWidth (sig.retBits A.ptrBits)) :
    (sig.contract A pre post wa stack leak).post s u' := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · rename_i vals hv
    simp only [hA.mem, hA.ret] at h ⊢
    rw [hm, hr]
    exact h

/-- Running `scrub rb c` is running `c`, then `tail rb`. -/
theorem exec_scrub {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) {c : Prog isa} {s u' : State}
    {t : List Leak} (h : Exec isa (scrub rb c) s t u') :
    ∃ u, Exec isa c s t u ∧ execBlock isa (tail rb) u = some (u', []) := by
  cases h with
  | seq a b =>
    cases b with
    | block hb =>
      rename_i u t₁ t₂
      obtain ⟨w, hw, -⟩ := tail_run hrb u
      rw [hw, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨u, by simpa using a, hw⟩

/-- The registers the tail zeroes: all but the result's and those the calling
convention preserves. -/
private theorem tail_zeroed (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) (hr : r ∉ preserved) :
    r = .r2 ∨ r = .r3 ∨ r = .r12 := by
  revert h0 h1 hr; cases r <;> decide

/-- `scrub rb c` meets the contract of `c`, code without frames, and returns
without secret residue. -/
theorem Verified.scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract A pre post wa stack leak)) (hn : c.noFrames = true)
    {rb : Nat} (e : rb = sig.retBits A.ptrBits) :
    Verified target (scrub rb c) (sig.contract A pre post wa stack leak) ∧
      NoResidue (scrub rb c) (sig.contract A pre post wa stack leak) rb := by
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [e, hA.ptrBits]; exact retBits_cases sig
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩, ?_⟩
  · obtain ⟨t, u, he, habi, hpost⟩ := hv.1 s hs
    obtain ⟨u', hb, hm, -, -, hsp, hpres, -, -, -, -, -, -, -, -, hret⟩ := tail_run hrb u
    refine ⟨t ++ [], u', .seq he (.block hb), ⟨fun r hr => (hpres r hr).trans (habi.1 r hr),
      hsp.trans habi.2⟩, contract_post_scrub hA hpost hm (e ▸ hret)⟩
  · obtain ⟨w₁, a₁, -⟩ := exec_scrub hrb e₁
    obtain ⟨w₂, a₂, -⟩ := exec_scrub hrb e₂
    exact hv.2.1 s₁ s₂ t₁ t₂ w₁ w₂ p₁ p₂ hp a₁ a₂
  · intro s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ _ ho _ e₁ e₂
    obtain ⟨w₁, a₁, b₁⟩ := exec_scrub hrb e₁
    obtain ⟨w₂, a₂, b₂⟩ := exec_scrub hrb e₂
    -- Each run keeps what the calling convention preserves, and the memory outside its buffers.
    have keep : ∀ {s w u : State} {t : List Leak}, (sig.contract A pre post wa stack leak).pre s →
        Exec isa c s t w → execBlock isa (tail rb) w = some (u, []) →
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧
          Frame s.wr s.mem u.mem ∧ u.gpr .r2 = 0 ∧ u.gpr .r3 = 0 ∧ u.gpr .r12 = 0 ∧
          u.n = false ∧ u.z = true ∧ u.c = true ∧ u.v = false ∧ (u.gpr .r1 ++ u.gpr .r0) >>> rb = 0 := by
      intro s w u t hs a b
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s hs
      obtain ⟨-, rfl⟩ := Exec.det a a'
      obtain ⟨hrd, hwr, hsp, hf⟩ := Exec.regions a hn
      obtain ⟨u', hb, hm, hrd', hwr', hsp', hpres, h2, h3, h12, fn, fz, fc, fv, hsh, -⟩ := tail_run hrb w
      rw [hb, Option.some.injEq, Prod.mk.injEq] at b
      obtain ⟨rfl, -⟩ := b
      exact ⟨hrd'.trans hrd, hwr'.trans hwr, hsp'.trans hsp, fun r hr => (hpres r hr).trans (habi.1 r hr),
        hm ▸ hf, h2, h3, h12, fn, fz, fc, fv, hsh⟩
    obtain ⟨rd₁, wr₁, sp₁, pr₁, f₁, x2, x3, x12, n₁, z₁, c₁, v₁, r₁⟩ := keep p₁ a₁ b₁
    obtain ⟨rd₂, wr₂, sp₂, pr₂, f₂, y2, y3, y12, n₂, z₂, c₂, v₂, r₂⟩ := keep p₂ a₂ b₂
    obtain ⟨ord, owr, oreg, -, osp, -, -, -, -, omem⟩ := ho
    refine ⟨rd₁.trans (ord.trans rd₂.symm), wr₁.trans (owr.trans wr₂.symm), fun r h0 h1 => ?_,
      r₁.trans r₂.symm, sp₁.trans (osp.trans sp₂.symm), n₁.trans n₂.symm, z₁.trans z₂.symm,
      c₁.trans c₂.symm, v₁.trans v₂.symm, fun x hx => ?_⟩
    · by_cases hr : r ∈ preserved
      · rw [pr₁ r hr, pr₂ r hr]; exact oreg r h0 h1
      · obtain rfl | rfl | rfl := tail_zeroed r h0 h1 hr
        · exact x2.trans y2.symm
        · exact x3.trans y3.symm
        · exact x12.trans y12.symm
    · rw [rd₁, wr₁] at hx
      rw [f₁ x fun r hr => hx r (List.mem_append_right _ hr),
        f₂ x fun r hr => hx r (List.mem_append_right _ (owr ▸ hr))]
      exact omem x hx

/-! ## Code with frames

Code with frames also writes the stack below the stack pointer: at most
`armStack c` bytes of it (`Exec.frameSp`), which hold what its frames held.
`scrubF rb n c` is `c`, then a frame of the `n` bytes below the stack pointer
whose every word is zeroed (`wipeBelow`), then `tail rb`: so those bytes are
zero when that frame is released, and every other byte outside the buffers
is what it was. The frame is apart from the buffers (the contract reserves
it), so a postcondition that reads the memory on return only within the
buffers (`PostOut`) still holds.

The frame's size is one the model accepts (`FrameOk`: a multiple of 8
bytes). Code whose contract reserves another number of bytes meets it with
more (`Verified.stack_le`), and is registered with the next such size.

What the release then leaves in those bytes is the model's (`pop`), which a
proof may not read back: two releases leave the same bytes where they held
the same bytes, at the same stack pointer and with the same unknowns
(`pop_mem_congr`). Two runs of `c` without indirect calls (`noIcall`) whose
traces agree, as constant time makes them, end with the same unknowns
(`Exec.path`), so two runs of `scrubF rb n c` agree on those bytes on
return. -/

open VG.Impl.StackScratch.Arm VG.Arm.FrameStack

/-- What `Sig.contract` gives of the stack it reserves: there is that much,
apart from every region the code may read or write. -/
theorem contract_pre_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) (hn : stack ≠ 0) :
    stack ≤ s.sp.toNat ∧ ∀ r ∈ s.rd ++ s.wr, (belowA s.sp stack).Disjoint r := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals _
  obtain ⟨hwf, hrd, hwr, -, hres, -⟩ := h
  obtain ⟨hst, hcon⟩ := hA.wf _ _ _ hwf
  have hsp : stack ≤ s.sp.toNat := hst.resolve_left hn
  have hres' : ∀ r ∈ abi.reserved stack s, ∀ a ∈ (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
      (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)), r.Disjoint a.1 := by
    rw [← hA.reserved]; exact hres
  have hb : belowA s.sp stack ∈ abi.reserved stack s := by
    cases stack with
    | zero => exact absurd rfl hn
    | succ n => simp [abi, stackBelow, belowA, addr_sub' hsp]
  refine ⟨hsp, fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · by_cases hn' : r ∈ A.rd s
    · rw [hrd] at hn'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn'
      exact hres' _ hb a (List.mem_filter.mp ha).1
    · exact hcon r hr hn' _ hb
  · rw [← hA.wr, hwr] at hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact hres' _ hb a (List.mem_filter.mp ha).1

/-- Two runs that agree on what is public have the same stack pointer. -/
theorem contract_pub_sp {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : s₁.sp = s₂.sp := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact hA.pub _ _ h.1
    | some f => exact hA.pub _ _ h.1.1

/-- `Sig.contract`'s precondition with `n'` bytes of stack gives it with
fewer: the stack it reserves is then within the `n'` bytes. -/
theorem contract_pre_stack_le {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {n n' : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State} (hn : n ≤ n')
    (h : (sig.contract abi pre post wa n' leak).pre s) : (sig.contract abi pre post wa n leak).pre s := by
  simp only [Sig.contract] at h ⊢
  revert h
  cases abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => exact id
  | some vals =>
    intro h
    simp only at h ⊢
    obtain ⟨hwf, hrd, hwr, hpw, hres, rest⟩ := h
    cases n with
    | zero =>
      refine ⟨?_, hrd, hwr, hpw, fun r hr => absurd hr List.not_mem_nil, rest⟩
      cases n' with
      | zero => exact hwf
      | succ m => exact hwf.2
    | succ k =>
      obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
      obtain ⟨hsp, hfit⟩ : m + 1 ≤ s.sp.toNat ∧ _ := hwf
      refine ⟨⟨Nat.le_trans hn hsp, hfit⟩, hrd, hwr, hpw, fun r hr a ha => ?_, rest⟩
      obtain rfl : r = ⟨State.addr s.sp - BitVec.ofNat 64 (k + 1), k + 1⟩ := by
        simpa [abi, stackBelow] using hr
      have hsub := belowA_sub hn hsp
      rw [belowA, belowA, addr_sub' (Nat.le_trans hn hsp), addr_sub' hsp] at hsub
      exact (hres _ (by simp [abi, stackBelow]) a ha).sub_left hsub

/-- `Sig.contract`'s precondition is satisfiable with `n` bytes of stack if
it is with more. -/
theorem sat_stack_le {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {n n' : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} (hn : n ≤ n')
    (h : ∃ s, (sig.contract abi pre post wa n' leak).pre s) : ∃ s, (sig.contract abi pre post wa n leak).pre s :=
  h.imp fun _ => contract_pre_stack_le hn

/-- Code that meets a contract `Sig.contract` with `n` bytes of stack meets
it with more, `n'`, if its precondition is then still satisfiable: so a
function whose frames use a number of bytes that is no frame size of the
model (`FrameOk`) is registered with the next one, and `scrubRegF` wipes
that. -/
theorem Verified.stack_le {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {n n' : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} (hn : n ≤ n')
    (hv : Verified target c (sig.contract abi pre post wa n leak))
    (hsat : ∃ s, (sig.contract abi pre post wa n' leak).pre s) :
    Verified target c (sig.contract abi pre post wa n' leak) :=
  ⟨fun s hs => hv.1 s (contract_pre_stack_le hn hs),
    fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ =>
      hv.2.1 s₁ s₂ t₁ t₂ u₁ u₂ (contract_pre_stack_le hn p₁) (contract_pre_stack_le hn p₂) hp e₁ e₂, hsat⟩

/-- A postcondition that reads the memory on return only within the
buffers, and of the result only its `rb` bits (`Verified.scrubF`'s `hpost`). -/
def PostOut (k : Contract isa) (rb : Nat) : Prop :=
  ∀ s u u', k.pre s → k.post s u →
    (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
    (u'.gpr .r1 ++ u'.gpr .r0).setWidth rb = (u.gpr .r1 ++ u.gpr .r0).setWidth rb → k.post s u'

/-- `PostOut` of a contract `Sig.contract` derives, from its postcondition's
reading the memory on return only within the buffers. -/
theorem postOut_of_local {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -⟩ := hs
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- A frame size the model accepts. -/
abbrev FrameOk (n : Nat) : Prop :=
  0 < n ∧ n < 4096 ∧ n % 8 = 0 ∧ encodable (BitVec.ofNat 32 n) = true

/-- Zero the `n` bytes below the stack pointer, in a frame of them. -/
def wipeBelow (n : Nat) : Prog isa := .frame (.alloc n) (.block (wipe (n / 4))) (.free n)

/-- `c`, then the `n` bytes below the stack pointer zeroed, then `tail rb`. -/
def scrubF (rb n : Nat) (c : Prog isa) : Prog isa := .seq c (.seq (wipeBelow n) (.block (tail rb)))

/-- The trace of `wipeStores words` from a state whose `r12` is `p`. -/
def wipeTr (p : BitVec 32) (words : Nat) : List Leak :=
  (List.range words).map fun k => .addr (State.addr (p + BitVec.ofNat 32 (4 * k)))

theorem wipeStores_succ (w : Nat) :
    wipeStores (w + 1) = wipeStores w ++ ([.str .r2 .r12 (4 * w)] : List Instr) := by
  simp only [wipeStores, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The stores of `wipeStores`, of a zero in `r2`, change memory only in the
region `R`, which holds each of them and which `u` may write, and leave the
words they store zero. -/
theorem wipeStores_zero (R : Region) (u : State) (hR : R ∈ u.wr) (h2 : u.gpr .r2 = 0) :
    ∀ words, 4 * words ≤ 4096 → (u.gpr .r12).toNat + 4 * words ≤ 2 ^ 32 →
    (∀ k < words, R.Contains (State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 * k))) 4) →
    ∃ m', execBlock isa (wipeStores words) u =
        some ({ u with mem := m' }, wipeTr (u.gpr .r12) words) ∧ Frame [R] u.mem m' ∧
      ∀ x, (x - State.addr (u.gpr .r12)).toNat < 4 * words → m' x = 0
  | 0, _, _, _ => ⟨u.mem, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | w + 1, hwb, hnw, hc => by
    obtain ⟨m', he, hf, hz⟩ := wipeStores_zero R u hR h2 w (by omega) (by omega) fun k hk => hc k (by omega)
    have hin : InRegions u.wr (State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 * w))) 4 :=
      ⟨R, hR, hc w (by omega)⟩
    have hoff : 4 * w < 4096 := by omega
    refine ⟨m'.writeW (State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 * w))) (u.gpr .r2), ?_,
      hf.writeW (List.mem_singleton_self _) _ (hc w (by omega)), fun x hx => ?_⟩
    · rw [wipeStores_succ, execBlock_append, he]
      simp only [Option.bind_some, execBlock, isa, exec, hoff, ↓reduceIte, State.store32, hin,
        Option.map_some, addrs, List.map_cons, List.map_nil, List.append_nil, wipeTr,
        List.range_succ, List.map_append]
    · rw [h2, addr_add (by omega)]
      simp only [Mem.writeW, Mem.write]
      split
      · simp
      · rename_i hx'
        refine hz x ?_
        have hx'' : ¬ (x - (State.addr (u.gpr .r12) + BitVec.ofNat 64 (4 * w))).toNat < 4 := by
          simpa using hx'
        have : ¬ (4 * w ≤ (x - State.addr (u.gpr .r12)).toNat ∧
            (x - State.addr (u.gpr .r12)).toNat < 4 * w + 4) :=
          fun h => hx'' ((Offset.lt_iff x (State.addr (u.gpr .r12)) (d := 4 * w) (n := 4) (by omega)).mpr h)
        omega

/-- `wipeBelow n` zeroes the `n` bytes below the stack pointer, in a frame
it then releases (`v`, the state before the release), and changes no other
byte, with a trace of their addresses alone; it keeps the regions, the stack
pointer and every register but `r2` and `r12`. -/
theorem wipeBelow_run {n : Nat} (hn : FrameOk n) (w : State) (hsp : n ≤ w.sp.toNat) :
    ∃ u v, Exec isa (wipeBelow n) w (wipeTr (w.sp - BitVec.ofNat 32 n) (n / 4)) u ∧
      u.rd = w.rd ∧ u.wr = w.wr ∧ u.sp = w.sp ∧
      (∀ r, r ≠ .r12 → r ≠ .r2 → u.gpr r = w.gpr r) ∧
      Frame [belowA w.sp n] w.mem u.mem ∧
      isa.pop (.free n) (allocated n w) v = some u ∧ v.sp = w.sp - BitVec.ofNat 32 n ∧
      v.unknowns = w.unknowns ∧ ∀ x, (belowA w.sp n).Contains x 1 → v.mem x = 0 := by
  obtain ⟨h0, h1, h8, henc⟩ := hn
  have h4 : 4 * (n / 4) = n := by omega
  have hsub : (w.sp - BitVec.ofNat 32 n).toNat = w.sp.toNat - n := sub_toNat' hsp
  have hlt := w.sp.isLt
  let a := allocated n w
  let v := (a.setReg .r12 (a.sp + BitVec.ofNat 32 0)).setReg .r2 0
  have h12 : v.gpr .r12 = w.sp - BitVec.ofNat 32 n := by
    simp [v, a, allocated, State.setReg]
  obtain ⟨m', he, hf, hz⟩ := wipeStores_zero (belowA w.sp n) v (by simp [v, a, allocated, State.setReg, belowA])
    (by simp [v, State.setReg]) (n / 4) (by omega) (by rw [h12, hsub]; omega) (fun k hk => by
      rw [h12, addr_add (by rw [hsub]; omega)]
      exact Offset.contains_base _ (by omega) (by omega))
  have hblk : execBlock isa (wipe (n / 4)) a = some ({ v with mem := m' }, wipeTr (w.sp - BitVec.ofNat 32 n) (n / 4)) := by
    simp only [wipe, execBlock, isa, exec, show (0 : Nat) < 256 by decide, ↓reduceIte, Op2.eval,
      show encodable (0 : BitVec 32) = true by decide, Option.map_some]
    rw [show ((a.setReg .r12 (a.sp + BitVec.ofNat 32 0)).setReg .r2 0) = v from rfl, he, h12]
    simp [addrs]
  have ha : isa.push (.alloc n) w = some a := by
    simp only [isa, push, h0, h1, h8, henc, hsp, and_self, ite_true]
    rfl
  have hfr : isa.pop (.free n) a { v with mem := m' } = some { freed n { v with mem := m' } with
      mem := lose m' (State.addr v.sp) n v.unknowns, unknowns := fun k => v.unknowns (k + n / 2) } := by
    simp only [freed, isa, pop, h0, h1, h8, henc, v, a, allocated, State.setReg,
      List.head?_cons, and_self, ite_true]
  refine ⟨{ freed n { v with mem := m' } with
      mem := lose m' (State.addr v.sp) n v.unknowns, unknowns := fun k => v.unknowns (k + n / 2) },
    { v with mem := m' },
    by simpa [addrs, wipeBelow] using Exec.frame ha (Exec.block hblk) hfr,
    rfl, rfl, ?_, fun r hr12 hr2 => ?_, ?_, hfr, rfl, rfl, fun x hx => ?_⟩
  · simp [freed, v, a, allocated, State.setReg, BitVec.sub_add_cancel]
  · simp [freed, v, a, allocated, State.setReg, hr12, hr2]
  · have hf' : Frame [belowA w.sp n] w.mem m' := by simpa [v, a, allocated, State.setReg] using hf
    exact hf'.trans (lose_frame _ _ _ _)
  · refine hz x ?_
    rw [h12, h4]
    simp only [Region.Contains] at hx
    omega

/-- A run of `scrubF rb n c` from `s`, after `c`'s run to `w`: what it leaks
after `c`'s trace are the addresses of the wiped words, and it leaves what
`tail rb` leaves, the `n` bytes below the stack pointer what the release of
a frame of them, all zero, leaves (`v`, the state before the release, with
`w`'s unknowns), and every other byte as `c` left it. -/
theorem scrubF_run {rb n : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (hn : FrameOk n) {c : Prog isa}
    (hd : armStack c ≤ n) {s w : State} {t : List Leak} (hsp : n ≤ s.sp.toNat) (he : Exec isa c s t w) :
    ∃ u, Exec isa (scrubF rb n c) s (t ++ (wipeTr (s.sp - BitVec.ofNat 32 n) (n / 4) ++ [])) u ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ r ∈ preserved, u.gpr r = w.gpr r) ∧
      u.gpr .r2 = 0 ∧ u.gpr .r3 = 0 ∧ u.gpr .r12 = 0 ∧
      u.n = false ∧ u.z = true ∧ u.c = true ∧ u.v = false ∧
      (u.gpr .r1 ++ u.gpr .r0) >>> rb = 0 ∧
      (u.gpr .r1 ++ u.gpr .r0).setWidth rb = (w.gpr .r1 ++ w.gpr .r0).setWidth rb ∧
      (∃ v a u', v.sp = s.sp - BitVec.ofNat 32 n ∧ v.unknowns = w.unknowns ∧
        (∀ x, (belowA s.sp n).Contains x 1 → v.mem x = 0) ∧
        isa.pop (.free n) a v = some u' ∧ u.mem = u'.mem) ∧
      (∀ x, ¬ (belowA s.sp n).Contains x 1 → u.mem x = w.mem x) ∧
      Frame (s.wr ++ [belowA s.sp n]) s.mem w.mem := by
  obtain ⟨hrd, hwr, hp⟩ := Exec.rdwr he
  have hfs := Frame.belowA_mono (Exec.frameSp he (Nat.le_trans hd hsp)) hd hsp
  obtain ⟨v, v₀, hv, vrd, vwr, vsp, vreg, vf, vpop, v₀sp, v₀u, vz⟩ := wipeBelow_run hn w (hp ▸ hsp)
  obtain ⟨u, hb, hm, urd, uwr, usp, upres, h2, h3, h12, fn, fz, fc, fv, hsh, hret⟩ := tail_run hrb v
  rw [hp] at hv vf vz v₀sp
  refine ⟨u, .seq he (.seq hv (.block hb)), urd.trans (vrd.trans hrd), uwr.trans (vwr.trans hwr),
    usp.trans (vsp.trans hp), fun r hr => ?_, h2, h3, h12, fn, fz, fc, fv, hsh, ?_, ?_,
    fun x hx => ?_, hfs⟩
  · rw [upres r hr]
    exact vreg r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
  · rw [hret, vreg .r1 (by decide) (by decide), vreg .r0 (by decide) (by decide)]
  · exact ⟨v₀, _, v, v₀sp, v₀u, vz, vpop, hm⟩
  · rw [hm]; exact vf x fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx

/-- `scrubF rb stack c` meets the contract of `c`, whose frames use at most
the `stack` bytes the contract reserves, which makes no indirect call, and
whose postcondition reads the memory on return only within the buffers, and
returns without secret residue. -/
theorem Verified.scrubF {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hv : Verified target c (sig.contract A pre post wa stack leak)) (hd : armStack c ≤ stack)
    (hni : noIcall c = true) (hn : FrameOk stack) {rb : Nat} (e : rb = sig.retBits A.ptrBits)
    (hpost : PostOut (sig.contract A pre post wa stack leak) rb) :
    Verified target (scrubF rb stack c) (sig.contract A pre post wa stack leak) ∧
      NoResidue (scrubF rb stack c) (sig.contract A pre post wa stack leak) rb := by
  have hrb : rb = 0 ∨ rb = 32 ∨ rb = 64 := by rw [e, hA.ptrBits]; exact retBits_cases sig
  have h0 : stack ≠ 0 := by have := hn.1; omega
  -- Every run is `c`'s run, then the wipe and the tail.
  have run : ∀ {s u : State} {T : List Leak}, (sig.contract A pre post wa stack leak).pre s →
      Exec isa (Scrub.scrubF rb stack c) s T u → ∃ t w, Exec isa c s t w ∧
        T = t ++ (wipeTr (s.sp - BitVec.ofNat 32 stack) (stack / 4) ++ []) ∧
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ r ∈ preserved, u.gpr r = w.gpr r) ∧
        u.gpr .r2 = 0 ∧ u.gpr .r3 = 0 ∧ u.gpr .r12 = 0 ∧
        u.n = false ∧ u.z = true ∧ u.c = true ∧ u.v = false ∧
        (u.gpr .r1 ++ u.gpr .r0) >>> rb = 0 ∧
        (u.gpr .r1 ++ u.gpr .r0).setWidth rb = (w.gpr .r1 ++ w.gpr .r0).setWidth rb ∧
        (∃ v a u', v.sp = s.sp - BitVec.ofNat 32 stack ∧ v.unknowns = w.unknowns ∧
          (∀ x, (belowA s.sp stack).Contains x 1 → v.mem x = 0) ∧
          isa.pop (.free stack) a v = some u' ∧ u.mem = u'.mem) ∧
        (∀ x, ¬ (belowA s.sp stack).Contains x 1 → u.mem x = w.mem x) ∧
        Frame (s.wr ++ [belowA s.sp stack]) s.mem w.mem := by
    intro s u T hs h
    cases h with
    | seq a b =>
      rename_i w t₁ t₂
      obtain ⟨u', hu', facts⟩ := scrubF_run hrb hn hd (contract_pre_scrub hA hs h0).1 a
      obtain ⟨hT, rfl⟩ := Exec.det (Exec.seq a b) hu'
      exact ⟨t₁, w, a, hT, facts⟩
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp e₁ e₂ => ?_, hv.2.2⟩, ?_⟩
  · obtain ⟨t, w, he, habi, hq⟩ := hv.1 s hs
    obtain ⟨hsp, hdis⟩ := contract_pre_scrub hA hs h0
    obtain ⟨u, hu, -, -, usp, upres, -, -, -, -, -, -, -, -, hret, -, hkeep, -⟩ := scrubF_run hrb hn hd hsp he
    refine ⟨_, u, hu, ⟨fun r hr => (upres r hr).trans (habi.1 r hr), usp⟩,
      hpost s w u hs hq (fun x ⟨r, hr, hx⟩ => hkeep x fun hb => hdis r hr x hb hx) hret⟩
  · obtain ⟨a₁, w₁, x₁, rfl, -⟩ := run p₁ e₁
    obtain ⟨a₂, w₂, x₂, rfl, -⟩ := run p₂ e₂
    rw [hv.2.1 s₁ s₂ a₁ a₂ w₁ w₂ p₁ p₂ hp x₁ x₂, contract_pub_sp hA hp]
  · intro s₁ s₂ t₁ t₂ u₁ u₂ p₁ p₂ hp ho hu e₁ e₂
    obtain ⟨a₁, w₁, x₁, -, rd₁, wr₁, sp₁, pr₁, x2, x3, x12, n₁, z₁, c₁, v₁, r₁, -, zero₁, keep₁, f₁⟩ := run p₁ e₁
    obtain ⟨a₂, w₂, x₂, -, rd₂, wr₂, sp₂, pr₂, y2, y3, y12, n₂, z₂, c₂, v₂, r₂, -, zero₂, keep₂, f₂⟩ := run p₂ e₂
    obtain ⟨ord, owr, oreg, -, osp, -, -, -, -, omem⟩ := ho
    -- The two runs of `c` leak the same trace, so end with the same unknowns.
    have hw : w₁.unknowns = w₂.unknowns :=
      (Exec.path x₁ hni (r₁ := []) (r₂ := []) x₂
        (by rw [hv.2.1 s₁ s₂ a₁ a₂ w₁ w₂ p₁ p₂ hp x₁ x₂]) hu).2
    -- Each run keeps what the calling convention preserves.
    have abi₁ : ∀ r ∈ preserved, w₁.gpr r = s₁.gpr r := by
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s₁ p₁
      obtain ⟨-, rfl⟩ := Exec.det x₁ a'
      exact habi.1
    have abi₂ : ∀ r ∈ preserved, w₂.gpr r = s₂.gpr r := by
      obtain ⟨t', w', a', habi, -⟩ := hv.1 s₂ p₂
      obtain ⟨-, rfl⟩ := Exec.det x₂ a'
      exact habi.1
    refine ⟨rd₁.trans (ord.trans rd₂.symm), wr₁.trans (owr.trans wr₂.symm), fun r h0 h1 => ?_,
      r₁.trans r₂.symm, sp₁.trans (osp.trans sp₂.symm), n₁.trans n₂.symm, z₁.trans z₂.symm,
      c₁.trans c₂.symm, v₁.trans v₂.symm, fun x hx => ?_⟩
    · by_cases hr : r ∈ preserved
      · rw [pr₁ r hr, pr₂ r hr, abi₁ r hr, abi₂ r hr]; exact oreg r h0 h1
      · obtain rfl | rfl | rfl := tail_zeroed r h0 h1 hr
        · exact x2.trans y2.symm
        · exact x3.trans y3.symm
        · exact x12.trans y12.symm
    · rw [rd₁, wr₁] at hx
      by_cases hb : (belowA s₁.sp stack).Contains x 1
      · obtain ⟨v₁, _, u₁', vsp₁, vu₁, vz₁, vp₁, vm₁⟩ := zero₁
        obtain ⟨v₂, _, u₂', vsp₂, vu₂, vz₂, vp₂, vm₂⟩ := zero₂
        rw [vm₁, vm₂]
        exact pop_mem_congr vp₁ vp₂ (by rw [vsp₁, vsp₂, osp]) (by rw [vu₁, vu₂, hw])
          ((vz₁ x hb).trans (vz₂ x (osp ▸ hb)).symm)
      · rw [keep₁ x hb, keep₂ x (osp ▸ hb),
          f₁ x fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact hx r (List.mem_append_right _ hr)
            · simp only [List.mem_singleton] at hr; subst hr; exact hb,
          f₂ x fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact hx r (List.mem_append_right _ (owr ▸ hr))
            · simp only [List.mem_singleton] at hr; subst hr; exact osp ▸ hb]
        exact omem x hx

/-- No ARM instruction writes the stack pointer, other than a frame's. -/
theorem spSafe_any (c : Prog isa) : c.all (fun i => !target.isa.writesSp i) = true := by
  induction c <;> simp_all [Code.all, List.all_eq_true]

/-- A function that writes at most the first bytes of some of its buffers
still does when the state on return is replaced by one with its memory. -/
theorem writtenWithin_mem {sig : Sig} {written : List (String × Nat)} {s u u' : State}
    (h : Sig.writtenWithin abi sig written s u) (hm : u'.mem = u.mem) :
    Sig.writtenWithin abi sig written s u' := by
  cases written with
  | nil => exact True.intro
  | cons w ws =>
    simp only [Sig.writtenWithin] at h ⊢
    split
    · exact True.intro
    · rename_i vals hv
      rw [hv] at h
      intro w hw b hb hbw i hi hl
      have := h w hw b hb hbw i hi hl
      simp only [abi] at this ⊢
      rw [hm]; exact this

/-- `r`, a registration of code without frames, scrubbed: its code followed
by `tail`, which returns without secret residue. -/
def scrubReg {api : Api} (r : Registration api target) (hn : r.code.noFrames = true) :
    Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    rw [e] at hv ⊢
    exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv hn
      rfl).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := spSafe_any _
  written := r.written
  writtenOk := by
    intro s t u' hs he
    have hrb := retBits_cases api.sig
    obtain ⟨u, a, b⟩ := exec_scrub (rb := api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (by rw [(ScrubAbi.tables (ScrubAbi.consts r.consts) api.sig r.tables).ptrBits]; exact hrb) he
    obtain ⟨w, hw, hm, -⟩ := tail_run (rb := api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (by rw [(ScrubAbi.tables (ScrubAbi.consts r.consts) api.sig r.tables).ptrBits]; exact hrb) u
    rw [hw, Option.some.injEq, Prod.mk.injEq] at b
    obtain ⟨rfl, -⟩ := b
    exact writtenWithin_mem (r.writtenOk s t u hs a) hm
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    rw [e] at hv ⊢
    exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv hn
      rfl).2⟩

/-- `r`, a registration of code whose frames use at most the `stack` bytes
its contract reserves and which makes no indirect call, scrubbed: its code,
then those bytes zeroed, then `tail`, which returns without secret residue,
if its postcondition reads the memory on return only within the buffers. -/
def scrubRegF {api : Api} (r : Registration api target) (hd : armStack r.code ≤ r.stack)
    (hni : noIcall r.code = true) (hn : FrameOk r.stack)
    (hpost : PostOut r.contract
      (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hw : r.written = []) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrubF (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    r.stack r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    rw [e] at hv hp ⊢
    exact (Verified.scrubF (ScrubAbi.of r.consts api.sig r.tables) hv hd hni hn
      rfl hp).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := spSafe_any _
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    rw [e] at hv hp ⊢
    exact (Verified.scrubF (ScrubAbi.of r.consts api.sig r.tables) hv hd hni hn
      rfl hp).2⟩

end VG.Arm.Scrub
