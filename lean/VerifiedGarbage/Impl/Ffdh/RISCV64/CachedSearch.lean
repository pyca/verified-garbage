module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.KeyGeneration.Search

/-! # The cached FFDH key-generation controller on RISC-V

`vg_ffdh_generate_key_search_cached` repeats an attempt of
`vg_ffdh_generate_key_cached` on successive `p_len` octets of the random tape
until it gives a key, a budget runs out, or the tape does, with the blocks of
`KeyGeneration/Search.lean`. The loop runs in a frame of 16 bytes saving
`ra`, which the calls change; each attempt in a frame of 48 bytes holding its
five stack arguments, the last two the controller's context, copied from its
own stack arguments.

`vg_ffdh_generate_key_search_cached(x = a0, x_len = a1, y = a2, y_len = a3,
used = a4, domain = a5, domain_len = a6, p_len = a7, rand = [sp],
rand_len = [sp + 8], scratch = [sp + 16], scratch_len = [sp + 24],
state = [sp + 32], ctx = [sp + 40], ctx_len = [sp + 48])`.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.Cached.Search

open VG VG.RISCV64 VG.Impl.Ffdh.RISCV64.KeyGeneration.Search

/-- The context's two arguments (the controller's sixth and seventh stack
arguments, above its frames of 16 and 48 bytes) loaded, the attempt's
arguments, and the context's stored as its fourth and fifth stack arguments,
at offsets 24 and 32 of its frame. -/
def cachedArguments : List Instr :=
  [.addSp .t3 104, .load .d .t4 .t3 0, .load .d .t5 .t3 8] ++ arguments ++
    [.store .d .t4 .t2 24, .store .d .t5 .t2 32]

variable (attempt : Prog isa)

/-- The attempt in a frame of its five stack arguments. -/
def attemptRun : Prog isa := .frame (.alloc 48) (.seq (.block cachedArguments) attempt) (.free 48)

def attemptOrRequest : Prog isa := .seq (.block room)
  (.ite (.ltu .t0 .t1) request (.seq (attemptRun attempt) classify))

def branch : Prog isa :=
  .ite (.zero .t0) exhausted (.seq (.block [ldf .t0 1])
    (.ite (.zero .t0) exhausted (attemptOrRequest attempt)))

/-- The loop goes on while the status is 4, a rejection: `t0 := status − 4`. -/
def iteration : Prog isa :=
  .seq (.block [ldf .t0 0]) (.seq (branch attempt) (.block [ldf .t0 14, .addi .t0 .t0 (-4)]))

def search : Prog isa := .frame (.push .ra) (.loop (iteration attempt) (.zero .t0)) (.pop .ra)

def code : Prog isa := .seq (.block entry) (.seq (search attempt) (.block finish))

end VG.Impl.Ffdh.RISCV64.Cached.Search
