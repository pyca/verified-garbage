module

public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Framework.X86.TaintErase
public import VerifiedGarbage.Impl.Mont.X86.Dynamic
public import VerifiedGarbage.Impl.Mont.X86.Exponent
public import VerifiedGarbage.Impl.Mont.X86.Power
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Taint checks for runtime-modulus Montgomery arithmetic on x86

The loops over words address `edi`, `ebp` and `ecx` plus offsets, so the
analysis of a loop's code without its offsets and immediates
(`Code.erase`) is the analysis of the code itself (`check_erase`). That
code is the same for every modulus and layout: each check below rewrites
it to one instance and evaluates the analysis there. `counter` makes `esi`
public too, for a loop around the arithmetic that counts in it.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86

/-- The analysis of two programs whose code agrees but for offsets and immediates. -/
theorem check_of_erase_eq (c c' : Prog isa) (τ : VG.X86.Taint.T) (h : VG.Taint.Hint VG.X86.Taint.T)
    (e : Code.erase c = Code.erase c') (hn : VG.X86.Taint.noBases τ = true)
    (hh : VG.X86.Taint.hintNoBases h = true) :
    VG.Taint.check taint τ c h = VG.Taint.check taint τ c' h := by
  rw [← VG.X86.Taint.check_erase c τ h hn hh, e, VG.X86.Taint.check_erase c' τ h hn hh]

/-- Only the workspace pointer is public on entry. -/
def workspaceTaint (counter : Bool) : VG.X86.Taint.T :=
  { regs := .ofList ([.edi] ++ if counter then [.esi] else []), flags := false }

/-- The workspace pointer and a zero in `eax`. -/
def zeroTaint (counter : Bool) : VG.X86.Taint.T :=
  { regs := .ofList ([.edi, .eax] ++ if counter then [.esi] else []), flags := false }

/-- After a loop over words: its pointer and bound, and the flags of its comparison. -/
def rowTaint (counter : Bool) : VG.X86.Taint.T :=
  { regs := .ofList ([.edi, .ebp, .edx] ++ if counter then [.esi] else []), flags := true }

/-- After a zeroing loop, which also keeps its zero in `eax`. -/
def zerosTaint (counter : Bool) : VG.X86.Taint.T :=
  { regs := .ofList ([.edi, .ebp, .edx, .eax] ++ if counter then [.esi] else []), flags := true }

/-- A modulus whose code stands for every modulus's, once erased. -/
def eraseMod : VG.Impl.Mont.Mod := { n := 1, mo := 0, tmp := 0, minv := 0 }

def mulHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (Dynamic.mul eraseMod 0 0 0 0 0))

def addHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (Dynamic.addW eraseMod 0 0 0 0))

def zerosHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (Dynamic.zerosW 0 1))

def oneHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (Dynamic.one 1 0))

def selectHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (Dynamic.selectProduct eraseMod 0 0 0))

/-- The multiplication's addresses and branches are public, for every
public width and workspace layout. -/
theorem mul_check (counter : Bool) (M : VG.Impl.Mont.Mod) (inv acc out a b : Nat) :
    VG.Taint.check taint (workspaceTaint counter) (Dynamic.mul M inv acc out a b) (mulHint counter) =
      some (rowTaint counter) := by
  exact (check_of_erase_eq (Dynamic.mul M inv acc out a b) (Dynamic.mul eraseMod 0 0 0 0 0) (workspaceTaint counter) (mulHint counter) rfl
    (by cases counter <;> rfl) (by cases counter <;> kernel_rfl)).trans (by cases counter <;> kernel_rfl)

theorem add_check (counter : Bool) (M : VG.Impl.Mont.Mod) (acc out a b : Nat) :
    VG.Taint.check taint (workspaceTaint counter) (Dynamic.addW M acc out a b) (addHint counter) =
      some (rowTaint counter) := by
  exact (check_of_erase_eq (Dynamic.addW M acc out a b) (Dynamic.addW eraseMod 0 0 0 0) (workspaceTaint counter) (addHint counter) rfl
    (by cases counter <;> rfl) (by cases counter <;> kernel_rfl)).trans (by cases counter <;> kernel_rfl)

theorem zeros_check (counter : Bool) (o k : Nat) :
    VG.Taint.check taint (workspaceTaint counter) (Dynamic.zerosW o k) (zerosHint counter) =
      some (zerosTaint counter) := by
  exact (check_of_erase_eq (Dynamic.zerosW o k) (Dynamic.zerosW 0 1) (workspaceTaint counter) (zerosHint counter) rfl
    (by cases counter <;> rfl) (by cases counter <;> kernel_rfl)).trans (by cases counter <;> kernel_rfl)

theorem one_check (counter : Bool) (n out : Nat) :
    VG.Taint.check taint (workspaceTaint counter) (Dynamic.one n out) (oneHint counter) =
      some (zerosTaint counter) := by
  exact (check_of_erase_eq (Dynamic.one n out) (Dynamic.one 1 0) (workspaceTaint counter) (oneHint counter) rfl
    (by cases counter <;> rfl) (by cases counter <;> kernel_rfl)).trans (by cases counter <;> kernel_rfl)

theorem selectProduct_check (M : VG.Impl.Mont.Mod) (out product mask : Nat) :
    VG.Taint.check taint (workspaceTaint true) (Dynamic.selectProduct M out product mask) selectHint =
      some (rowTaint true) := by
  exact (check_of_erase_eq (Dynamic.selectProduct M out product mask) (Dynamic.selectProduct eraseMod 0 0 0)
    (workspaceTaint true) selectHint rfl rfl (by kernel_rfl)).trans (by kernel_rfl)

theorem check_append {M : ISA} (A : VG.Taint M) (τ : A.T) (a b : List M.Instr) :
    A.checkBlock τ (a ++ b) = (A.checkBlock τ a).bind (A.checkBlock · b) := by
  induction a generalizing τ with
  | nil => rfl
  | cons i is ih =>
    change (A.step τ i).bind (fun t => A.checkBlock t (is ++ b)) =
      ((A.step τ i).bind (fun t => A.checkBlock t is)).bind (A.checkBlock · b)
    rw [Option.bind_assoc]
    simp only [ih]

theorem check_append_of {M : ISA} (A : VG.Taint M) (τ : A.T)
    {a b : List M.Instr} (ha : A.checkBlock τ a = some τ) (hb : A.checkBlock τ b = some τ) :
    A.checkBlock τ (a ++ b) = some τ := by
  rw [check_append A τ, ha, Option.bind_some]
  exact hb

/-- Newton iteration preserves the only public register, the workspace pointer. -/
theorem newton_taint (counter : Bool) :
    taint.checkBlock (workspaceTaint counter) Dynamic.newton = some (workspaceTaint counter) := by
  cases counter <;> rfl

theorem inverse_taint (counter : Bool) :
    taint.checkBlock (workspaceTaint counter) Dynamic.inverse = some (workspaceTaint counter) := by
  have cp : taint.checkBlock (workspaceTaint counter) [.mov .ecx (.reg .ebx)] = some (workspaceTaint counter) := by
    cases counter <;> rfl
  have neg : taint.checkBlock (workspaceTaint counter) [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx)] =
      some (workspaceTaint counter) := by cases counter <;> rfl
  have N := newton_taint counter
  exact check_append_of taint _ (check_append_of taint _ (check_append_of taint _ (check_append_of taint _
    (check_append_of taint _ cp N) N) N) N) neg

/-- Inverse initialization never publishes the loaded modulus word. -/
theorem setupInverse_taint (counter : Bool) (mo inv : Nat) :
    taint.checkBlock (workspaceTaint counter) (Dynamic.setupInverse mo inv) =
      some (workspaceTaint counter) := by
  have ld : taint.checkBlock (workspaceTaint counter) [.mov .ebx (.mem (sc mo))] = some (workspaceTaint counter) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (by cases counter <;> rfl)]
    change taint.checkBlock (workspaceTaint counter) [.mov .ebx (.mem (sc 0))] = _
    cases counter <;> rfl
  have st : taint.checkBlock (workspaceTaint counter) [.store (sc inv) .eax] = some (workspaceTaint counter) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (by cases counter <;> rfl)]
    change taint.checkBlock (workspaceTaint counter) [.store (sc 0) .eax] = _
    cases counter <;> rfl
  exact check_append_of taint _ (check_append_of taint _ ld (inverse_taint counter)) st

/-- The full multiplication has secret-independent branches and addresses,
including its initialization and final conditional subtraction. -/
theorem mul_constantTime (M : VG.Impl.Mont.Mod) (inv acc out a b : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint false))
      (Dynamic.mul M inv acc out a b) := by
  refine VG.Taint.constantTime (A := taint) (workspaceTaint false) (fun _ _ _ _ h => h)
    (hc := mulHint false) ?_
  rw [mul_check]
  rfl

end VG.Proof.Mont.X86.Dynamic
