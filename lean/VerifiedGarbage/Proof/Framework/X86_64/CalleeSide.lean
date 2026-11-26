module

public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# What the cleanup of a caller needs of an implementation it calls (x86-64)

`calleeSide c k n` is what the cleanup of a function generic over the
implementations it calls (`Proof/Framework/X86_64/ScrubCall.lean`) needs of
each implementation's code `c`, which the implementation proves where it is
defined. It is in a module of its own so that the structures of variants
that state it import only this.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64

/-! ## Tests of an instruction, as the kernel evaluates them

Each is one match on the instruction, its cases closed (`inline_match%`):
what the checks below state of the instructions of code is equal to it. -/

/-- `decide (i.vecLevelR ≤ k) && !loadsMxcsr i`, in one match. -/
def lvOkFn : Instr → Nat → Bool
  | .ldmxcsr _ => fun _ => false
  | i => fun k => Nat.ble i.vecLevel k

/-- `lvOkFn`, with its cases closed. -/
def lvOkK : Instr → Nat → Bool := inline_match% VG.X86_64.Scrub.lvOkFn VG.X86_64.Instr.vecLevel

theorem lvOkK_eq (i : Instr) (k : Nat) : lvOkK i k = (decide (i.vecLevelR ≤ k) && !loadsMxcsr i) := by
  have h : lvOkK i = lvOkFn i := by cases i <;> rfl
  have hb : ∀ n, Nat.ble n k = decide (n ≤ k) := fun n => by
    by_cases hn : n ≤ k
    · rw [Nat.ble_eq_true_of_le hn, decide_eq_true hn]
    · rw [decide_eq_false hn]; exact Bool.eq_false_iff.mpr fun e => hn (Nat.le_of_ble_eq_true e)
  rw [h]
  cases i <;> first
    | exact (Bool.and_false _).symm
    | exact (hb _).trans (Bool.and_true _).symm

/-- What the cleanup needs of an instruction at the level `k`. -/
def lvOk (k : Nat) (i : Instr) : Bool := lvOkK i k

/-- `lvOk k` of every instruction of `c`. Only the kernel evaluates it. -/
noncomputable def lvAll (k : Nat) (c : Prog isa) : Bool := c.allInstrs (lvOk k)

theorem lvAll_eq (k : Nat) (c : Prog isa) :
    lvAll k c = c.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) :=
  congrArg (Code.allInstrs · c) (funext fun i => lvOkK_eq i k)

/-- What the cleanup of a function that calls `c` needs of it: at most `n`
bytes of stack, vector instructions of at most the level `k`, no load of
MXCSR, and no indirect call. Only the kernel evaluates it. -/
noncomputable def calleeSide (c : Prog isa) (k n : Nat) : Bool :=
  decide (c.x86_64Depth ≤ n) && lvAll k c &&
    (UpperLock.inames c).isEmpty

/-- `calleeSide` at the level of EVEX, which every instruction is within: of code whose depth is
known and which is known to load no MXCSR, without asking its instructions. -/
theorem calleeSide_evex {c : Prog isa} {n : Nat} (hd : c.x86_64Depth ≤ n)
    (hm : c.allInstrs (fun i => !loadsMxcsr i) = true) (hn : (UpperLock.inames c).isEmpty = true) :
    calleeSide c 2 n = true := by
  have hl : lvAll 2 c = true := by
    rw [lvAll_eq]
    rw [Code.allInstrs_eq] at hm ⊢
    refine List.all_eq_true.mpr fun i hi => ?_
    rw [List.all_eq_true.mp hm i hi, Bool.and_true, decide_eq_true_eq]
    unfold Instr.vecLevelR Instr.vecLevel
    split
    · decide
    · split <;> decide
  rw [calleeSide, hl, hn, decide_eq_true hd]; rfl

/-- `Code.x86_64Depth` of code with a stub for the implementations it calls,
each call `.call f (.block [])` of one (`Fill.hole`) taking `n f` bytes: the
stack of the code with implementations that need at most that much
(`Fill.depth_leH`). -/
def depthH (n : String → Nat) : Prog isa → Nat
  | .block _ => 0
  | .call f (.block []) => n f + 8
  | .seq a b => max (depthH n a) (depthH n b)
  | .ite _ t e => max (depthH n t) (depthH n e)
  | .loop b _ => depthH n b
  | .call _ b => depthH n b + 8
  | .frame i b _ => depthH n b + i.frameBytes
  | .icall _ _ b x => max (depthH n b + 8) (depthH n x)

/-- What `calleeSide` needs of code `a` with a stub for the implementations
it calls, which need at most `n f` bytes of stack: its stack with theirs at
most `m`, vector instructions of at most the level `k`, no load of MXCSR,
and no indirect call. -/
noncomputable def stubCallee (a : Prog isa) (k : Nat) (n : String → Nat) (m : Nat) : Bool :=
  decide (depthH n a ≤ m) && lvAll k a &&
    (UpperLock.inames a).isEmpty

end VG.X86_64.Scrub
