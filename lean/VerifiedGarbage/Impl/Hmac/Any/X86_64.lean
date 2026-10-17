module

public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
public import VerifiedGarbage.Impl.Dispatch.X86_64

/-!
# HMAC and streaming `update` with the hash function as an argument: x86-64 implementation

`vg_hmac_init_scratch(inner = rdi, outer = rsi, key = rdx, key_len = rcx,
scratch = r8, hash = r9)`, `vg_hash_update_scratch(state = rdi, count = rsi,
data = rdx, len = rcx, scratch = r8, hash = r9)` and
`vg_hmac_finalize_scratch(inner = rdi, outer = rsi, count = rdx, out = rcx,
scratch = r8, hash = r9)` (`Spec/Hmac/Any.lean`): each moves `hash` into
`rax` and calls, through `Dispatch.X86_64.chain`, the function of the hash
function it names, of the hash functions `hs` (by their numbers): its HMAC
`init` or `finalize`, or its streaming `update`. The arguments are already
where that function takes them, so each case is its call alone.
-/

@[expose] public section

namespace VG.Impl.Hmac.Any.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (hs : List (Nat × Hash))

/-- `hash` (`r9`) into `rax`, for the dispatch. -/
def ldSel : List Instr := [.mov .rax (.reg .r9)]

/-- `vg_hmac_init_scratch`: HMAC's `init` of the hash function `hash` names. -/
def init : Prog isa :=
  .seq (.block ldSel) (Dispatch.X86_64.chain (hs.map fun p => (p.1, .call p.2.hmacInitN p.2.hmacInit)))

/-- `vg_hash_update_scratch`: the streaming `update` of the hash function
`hash` names. -/
def update : Prog isa :=
  .seq (.block ldSel) (Dispatch.X86_64.chain (hs.map fun p => (p.1, .call p.2.updN p.2.updC)))

/-- `vg_hmac_finalize_scratch`: HMAC's `finalize` of the hash function
`hash` names. -/
def finalize : Prog isa :=
  .seq (.block ldSel) (Dispatch.X86_64.chain (hs.map fun p => (p.1, .call p.2.hmacFinN p.2.hmacFin)))

end VG.Impl.Hmac.Any.X86_64
