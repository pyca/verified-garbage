module

public import VerifiedGarbage.Impl.Ffdh.AArch64.KeyGeneration.Search
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate

/-! The cached controller consumes p_len bytes per attempt and retains the existing
budgets, statuses and zeroing convention. The immutable context is reloaded from the caller's public stack arguments;
only the existing link-register frame and the attempt arguments need stack space. -/
@[expose] public section
namespace VG.Impl.Ffdh.AArch64.Cached.Search
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search

/-- The context arguments remain in the original caller's argument area. -/
def cachedArguments : List Instr := [.ldrSp .x12 104,.ldrSp .x13 112] ++ arguments ++
 [st .x12 .x11 24,st .x13 .x11 32]

def attemptRun (attempt : Prog isa) : Prog isa :=
 .frame (.alloc 48) (.seq (.block cachedArguments) attempt) (.free 48)

def attemptOrRequest (attempt : Prog isa) : Prog isa := .seq (.block room)
 (.ite (.zero .x .x12) request (.seq (attemptRun attempt) classify))

def branch (attempt : Prog isa) : Prog isa :=
 .ite (.zero .x .x9) exhausted (.seq (.block [ldf .x9 1])
  (.ite (.zero .x .x9) exhausted (attemptOrRequest attempt)))

def iteration (attempt : Prog isa) : Prog isa :=
 .seq (.block [ldf .x9 0]) (.seq (branch attempt) (.block [ldf .x9 14,.subImm .x .x9 .x9 4]))

def search (attempt : Prog isa) : Prog isa :=
 .frame (.push .x30) (.loop (iteration attempt) (.zero .x .x9)) (.pop .x30)

def code (attempt : Prog isa) : Prog isa :=
 .seq (.block entry) (.seq (search attempt) (.block finish))

end VG.Impl.Ffdh.AArch64.Cached.Search
