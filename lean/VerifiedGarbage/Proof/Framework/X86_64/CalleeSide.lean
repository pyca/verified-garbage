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

/-- What the cleanup of a function that calls `c` needs of it: at most `n`
bytes of stack, vector instructions of at most the level `k`, no load of
MXCSR, and no indirect call. Only the kernel evaluates it. -/
noncomputable def calleeSide (c : Prog isa) (k n : Nat) : Bool :=
  decide (c.x86_64Depth ≤ n) && c.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) &&
    (UpperLock.inames c).isEmpty

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
  decide (depthH n a ≤ m) && a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) &&
    (UpperLock.inames a).isEmpty

end VG.X86_64.Scrub
