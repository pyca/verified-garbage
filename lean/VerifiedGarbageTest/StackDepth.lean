module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbageTest.RenderOnly
meta import VerifiedGarbageTest.RenderOnly
import VerifiedGarbage.TCB.AArch64.Print
meta import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Arm.Print
meta import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.TCB.PPC64LE.Print
meta import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.TCB.RISCV64.Print
meta import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.TCB.X86.Print
meta import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.TCB.X86_64.Print
meta import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# The stack a function's calls and frames take (`Rust.checkStack`, #6397)

A contract is for an implementation whose calls and frames take at most some
bytes of stack (`Sig.contract`'s `stack`): no buffer overlaps those bytes, and
the documentation says so. The proof does not see that they do: an x86-64
function that calls another and is proven for no stack at all (`verified`) may
store the return address over one of its buffers. The emitter refuses it.
-/

namespace VG.Test.StackDepth
open VG

/-! ## What a push takes: how far it moves the stack pointer down -/

theorem x86_64_push {i : X86_64.Instr} {s s' : X86_64.State} (h : X86_64.push i s = some s') :
    s'.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (X86_64.emitter.frameBytes i) := by
  have regs : ∀ (rs : List X86_64.Reg) (s : X86_64.State),
      (X86_64.pushRegs s rs).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length) := by
    intro rs
    induction rs with
    | nil => intro s; simp [X86_64.pushRegs]
    | cons r rs ih =>
      intro s
      rw [X86_64.pushRegs, ih, List.length_cons, Nat.mul_succ, Nat.add_comm, BitVec.ofNat_add,
        ← BitVec.sub_sub]
      rfl
  cases i <;> simp only [X86_64.push, reduceCtorEq] at h
  all_goals
    split at h <;> cases h
  · exact regs _ _
  · rfl

theorem x86_push {i : X86.Instr} {s s' : X86.State} (h : X86.push i s = some s') :
    s'.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (X86.emitter.frameBytes i) := by
  have regs : ∀ (rs : List X86.Reg) (s : X86.State),
      (X86.pushRegs s rs).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) := by
    intro rs
    induction rs with
    | nil => intro s; simp [X86.pushRegs]
    | cons r rs ih =>
      intro s
      rw [X86.pushRegs, ih, List.length_cons, Nat.mul_succ, Nat.add_comm, BitVec.ofNat_add,
        ← BitVec.sub_sub]
      rfl
  cases i <;> simp only [X86.push, reduceCtorEq] at h
  all_goals
    split at h <;> cases h
  all_goals first
    | exact regs _ _
    | rfl
    | exact (BitVec.sub_zero _).symm
    | (rename_i hd; exact ite_eq_right (Ne.symm hd.1))

theorem aarch64_push {i : AArch64.Instr} {s s' : AArch64.State} (h : AArch64.push i s = some s') :
    s'.sp = s.sp - BitVec.ofNat 64 (AArch64.emitter.frameBytes i) := by
  cases i <;> simp only [AArch64.push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals rfl

theorem arm_push {i : Arm.Instr} {s s' : Arm.State} (h : Arm.push i s = some s') :
    s'.sp = s.sp - BitVec.ofNat 32 (Arm.emitter.frameBytes i) := by
  cases i <;> simp only [Arm.push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals rfl

theorem riscv64_push {i : RISCV64.Instr} {s s' : RISCV64.State} (h : RISCV64.push i s = some s') :
    s'.sp = s.sp - BitVec.ofNat 64 (RISCV64.emitter.frameBytes i) := by
  cases i <;> simp only [RISCV64.push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals rfl

theorem ppc64le_push {i : PPC64LE.Instr} {s s' : PPC64LE.State} (h : PPC64LE.push i s = some s') :
    s'.sp = s.sp - BitVec.ofNat 64 (PPC64LE.emitter.frameBytes i) := by
  cases i <;> simp only [PPC64LE.push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals rfl

/-! ## What a call takes: how far it moves the stack pointer down -/

theorem x86_64_call {s s' : X86_64.State} (h : X86_64.call s = some s') :
    s'.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 X86_64.emitter.callBytes := by cases h; rfl

theorem x86_call {s s' : X86.State} (h : X86.call s = some s') :
    s'.gpr .esp = s.gpr .esp - BitVec.ofNat 32 X86.emitter.callBytes := by cases h; rfl

theorem aarch64_call {s s' : AArch64.State} (h : AArch64.call s = some s') :
    s'.sp = s.sp - BitVec.ofNat 64 AArch64.emitter.callBytes := by
  cases h; exact (BitVec.sub_zero _).symm

theorem arm_call {s s' : Arm.State} (h : Arm.call s = some s') :
    s'.sp = s.sp - BitVec.ofNat 32 Arm.emitter.callBytes := by
  cases h; exact (BitVec.sub_zero _).symm

theorem riscv64_call {s s' : RISCV64.State} (h : RISCV64.call s = some s') :
    s'.sp = s.sp - BitVec.ofNat 64 RISCV64.emitter.callBytes := by
  cases h; exact (BitVec.sub_zero _).symm

theorem ppc64le_call {s s' : PPC64LE.State} (h : PPC64LE.call s = some s') :
    s'.sp = s.sp - BitVec.ofNat 64 PPC64LE.emitter.callBytes := by
  cases h; exact (BitVec.sub_zero _).symm

/-! ## The depth of code -/

def x64 : EmitTarget := .of X86_64.target X86_64.emitter
def a64 : EmitTarget := .of AArch64.target AArch64.emitter

/-- A function with a frame of 24 bytes. -/
def f24 : Prog X86_64.isa := .frame (.push [.rbx, .rbp, .r12]) (.block []) (.pop .rbx 3)

-- Straight-line code takes none, a frame its bytes, a call its return address and what its
-- function takes, of a sequence or a choice the most of either.
#guard Rust.stackSeen x64 (.block []) [] == (0, [])
#guard Rust.stackSeen x64 f24 [] == (24, [])
#guard Rust.stackSeen x64 (.frame (.alloc 40) f24 (.free 40)) [] == (64, [])
#guard Rust.stackSeen x64 (.call "f" f24) [] == (32, [("f", 24)])
#guard Rust.stackSeen x64 (.seq (.call "f" f24) (.loop (.call "g" (.call "f" f24)) .e)) [] ==
  (40, [("g", 32), ("f", 24)])
#guard (Rust.stackSeen x64 (.ite .e (.block []) (.frame (.alloc 8) (.call "f" f24) (.free 8))) []).1 == 40
#guard (Rust.stackSeen x64 (.ite .e (.frame (.alloc 8) (.call "f" f24) (.free 8)) (.block [])) []).1 == 40
-- An indirect call takes what the function of its candidates that takes the most does.
#guard (Rust.stackSeen x64 (.icall (.callr .r11) "e" (.block []) (.icall (.callr .r11) "f" f24 (.block []))) []) ==
  (32, [("f", 24), ("e", 0)])
#guard (Rust.stackSeen x64 (.icall (.callr .r11) "f" f24 (.icall (.callr .r11) "e" (.block []) (.block []))) []).1 ==
  32
-- A call that leaves its return address in a register takes what its function does.
#guard (Rust.stackSeen a64 (.call "f" (.frame (.push .x30) (.block []) (.pop .x30))) []).1 == 16
#guard (Rust.stackSeen a64 (.frame (.push .x30) (.call "f" (.frame (.alloc 64) (.block []) (.free 64)))
  (.pop .x30)) []).1 == 80

/-! ## A function that takes more stack than its contract is for -/

def sig : Sig := { params := [("buf", .array false .u8 8)] }

/-- The postcondition, which says nothing. -/
def Nothing (_ : Addr) : Prop := True

/-- The contract, for an implementation that takes `n` bytes of stack. -/
def contract (n : Nat) : Contract X86_64.isa :=
  sig.contract X86_64.abi (post := fun buf _ _ _ => Nothing buf) (stack := n)

/-- A call of a function that does nothing, which stores a return address. -/
def code : Prog X86_64.isa := .call "vg_test_nothing" (.block [])

/-- A state satisfying the precondition: `buf` at `0x1000`. -/
def sat : X86_64.State where
  gpr r := if r = .rdi then 0x1000 else if r = .rsp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 8⟩]
  wr := []

/-- It runs from any state, storing the return address below `rsp`. -/
theorem runs (s : X86_64.State) : ∃ t s', Exec X86_64.isa code s t s' ∧
    s'.mem = s.mem.writeW (s.gpr .rsp - 8) (s.unknowns 0) :=
  ⟨_, _, .call rfl (.block rfl) (ite_eq_left ⟨rfl, rfl⟩), rfl⟩

/-- The proof is for any `n`: it does not see what the call takes. -/
theorem verified (n : Nat) (hsat : ∃ s, (contract n).pre s) : Verified X86_64.target code (contract n) := by
  refine ⟨fun s _ => ⟨_, _, .call rfl (.block rfl) (ite_eq_left ⟨rfl, rfl⟩), ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_, rfl⟩
    · by_cases h : r = .rsp
      · subst h
        show s.gpr .rsp - 8 + 8 = _
        exact BitVec.sub_add_cancel ..
      · show (if r = .rsp then _ else if r = .rsp then _ else s.gpr r) = _
        rw [ite_eq_right h, ite_eq_right h]
    · exact Mem.readW_writeW_sep (by
        simp only [Mem.Sep]
        bv_omega) (by decide)
  · sig_post [contract, sig, X86_64.abi, X86_64.argRegs]
    exact True.intro
  · exact .of_leakage (fun s => [.addr (s.gpr .rsp - 8), .addr (s.gpr .rsp - 8)]) (fun s t s' _ e => by
        cases e with | call h₁ e h₂ => cases h₁; cases e with | block e => cases e; rfl)
      (fun _ _ _ _ h => by
        have : X86_64.abi.pub _ _ := h.1
        rw [this.1])
  · exact hsat

theorem sat0 : ∃ s, (contract 0).pre s := by
  refine ⟨sat, ?_⟩
  sig_pre [contract, sig, X86_64.abi, X86_64.argRegs, stackBelow, sat]
  exact ⟨Region.disjoint_of_sep (by decide), by decide⟩

theorem sat8 : ∃ s, (contract 8).pre s := by
  refine ⟨sat, ?_⟩
  sig_pre [contract, sig, X86_64.abi, X86_64.argRegs, stackBelow, sat]
  exact ⟨by decide, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide⟩

def artifact (n : Nat) (h : ∃ s, (contract n).pre s) : EmitArtifact where
  target := .of (renderOnly X86_64.target) X86_64.emitter
  api := { module := "test", name := "vg_test_stack", sig := sig, safety := ["None."], summary := "Nothing." }
  code := code
  contract := contract n
  verified := renderOnly_verified (verified n h)
  stack := n

def understated : EmitArtifact := artifact 0 sat0
def stated : EmitArtifact := artifact 8 sat8

#guard match Rust.checkStack [understated] with
  | .error e => e == "x86_64: the calls and frames of vg_test_stack take 8 bytes of stack, but its contract is for 0"
  | .ok _ => false
#guard (Rust.checkStack [stated]) matches .ok _
-- Whatever the artifacts before it.
#guard !(Rust.checkStack [stated, understated]) matches .ok _

/-- What the contract for no stack lets the call do: the return address it
stores is over a buffer that the function may only read. -/
def overlapping : X86_64.State :=
  { sat with gpr := fun r => if r = .rdi then 0x1000 else if r = .rsp then 0x1008 else 0
             unknowns := fun _ => 1 }

example : (contract 0).pre overlapping ∧ overlapping.mem 0x1000 = 0 ∧
    ∃ t s', Exec X86_64.isa code overlapping t s' ∧ s'.mem 0x1000 = 1 := by
  obtain ⟨t, s', e, hm⟩ := runs overlapping
  refine ⟨?_, rfl, t, s', e, ?_⟩
  · sig_pre [contract, sig, X86_64.abi, X86_64.argRegs, stackBelow, overlapping, sat]
    exact ⟨Region.disjoint_of_sep (by decide), by decide⟩
  · rw [hm]; decide

-- The contract for the bytes it takes does not.
example : ¬ (contract 8).pre overlapping := by
  sig_pre [contract, sig, X86_64.abi, X86_64.argRegs, stackBelow, overlapping, sat]
  intro h
  exact h.2.2.1 0x1000 (by decide) (by decide)

end VG.Test.StackDepth
