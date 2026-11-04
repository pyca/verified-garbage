module

public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 public-key derivation on x86-64

`publicKeyExpanded bs fs (out = rdi, digest = rsi, scratch = rdx)` copies the
seed's SHA-512 digest to `scratch + 1568`, prunes its first half (RFC 8032
§5.1.5) and encodes `[s]B` with `vg_ed25519_scalar_base` (`bs`, named with
the suffix `fs`).

Everything runs in one stack frame of seven words, pushed from `rdi`, `rsi`,
`rdx` and four copies of `rax`: from `rsp`, the pruned scalar (32 bytes),
then `scratch`, `digest` and `out`, which the calls cannot change. The
pruned scalar must lie outside `scratch` and `out`, which
`vg_ed25519_scalar_base` writes; it is cleared before the frame
is popped. Signing and verification use `scrPtr` and `callWith` too, with the
SHA-512 streaming state (192 bytes) and the working space of `update` and
`finalize` (1376 bytes) at the start of `scratch`.
-/

@[expose] public section

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- `[rsp + d]`, in the frame. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- Where in the frame `scratch`, `seed` and `out` are. -/
def fScratch : Nat := 32
def fSeed : Nat := 40
def fOut : Nat := 48

/-- Where in `scratch` the SHA-512 working space and the digest are. -/
def shaScratch : Nat := 192
def digestAt : Nat := 1568

/-- `d ← scratch + o`. -/
def scrPtr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.mem (stk fScratch)), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-- `scalar_base(out, scalar = rsp, scratch)`. -/
def pkBaseArgs : List Instr :=
  [.mov .rdi (.mem (stk fOut)), .mov .rsi (.reg .rsp), .mov .rdx (.mem (stk fScratch))]

/-- `[rdx + 1568 + 8 k]`: word `k` of the digest, with `scratch` in `rdx`. -/
def digestWord (k : Nat) : MemOp := { base := .rdx, disp := ((digestAt + 8 * k : Nat) : Int) }

/-- The first half of the digest at `rdx + 1568`, pruned (`Spec.Ed25519.prune`),
in `r8`–`r11`: bits 0–2 and 255 cleared, bit 254 set. -/
def pkPruneRegs : List Instr :=
  [.mov .r8 (.mem (digestWord 0)), .mov .r9 (.mem (digestWord 1)),
    .mov .r10 (.mem (digestWord 2)), .mov .r11 (.mem (digestWord 3)),
    .alu .and .r8 (.imm (BitVec.ofInt 32 (-8))),
    .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 62 - 1)), .alu .and .r11 (.reg .rcx),
    .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 62)), .alu .or .r11 (.reg .rcx)]

/-- `r8`–`r11` into the frame. -/
def pkPruneStores : List Instr :=
  [.store (stk 0) .r8, .store (stk 8) .r9, .store (stk 16) .r10, .store (stk 24) .r11]

/-- The pruned first half of the digest, into the frame. -/
def pkPrune : List Instr := pkPruneRegs ++ pkPruneStores

/-- `r8`–`r11` cleared. -/
def pkZero : List Instr :=
  [.alu32 .xor .r8 (.reg .r8), .alu32 .xor .r9 (.reg .r9), .alu32 .xor .r10 (.reg .r10),
    .alu32 .xor .r11 (.reg .r11)]

/-- The scalar in the frame, cleared. -/
def pkWipe : List Instr := pkZero ++ pkPruneStores

/-- The moves of a call's arguments, and the call. -/
def callWith (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

/-- The name of the base-point multiplication called, with its suffix `fs` (`_adx`,
`_ifma`, or none). -/
def scalarBaseName (fs : String) : String := "vg_ed25519_scalar_base" ++ fs

/-- The frame's body after `hash`, which leaves the seed's SHA-512 digest at
`scratch + 1568`, calling the base-point multiplication `bs`. -/
def pkBodyFrom (hash : Prog isa) (bs : Prog isa) (fs : String) : Prog isa :=
  .seq hash
    (.seq (.block pkBaseArgs) (.seq (.block pkPrune)
    (.seq (.call (scalarBaseName fs) bs) (.block pkWipe))))

/-- The pointers of `vg_ed25519_public_key_expanded`'s copy: the digest (its second
argument, saved at `fSeed`) in `rax`, `scratch` in `rcx`. -/
def pkCopyPtrs : List Instr := [.mov .rax (.mem (stk fSeed)), .mov .rcx (.mem (stk fScratch))]

/-- The eight words at `rax` copied to `rcx + 1568`, where `pkBodyFrom` reads the digest. -/
def pkCopyWords : List Instr :=
  (List.range 8).flatMap fun i =>
    [.mov .rdx (.mem { base := .rax, disp := ((8 * i : Nat) : Int) }),
      .store { base := .rcx, disp := ((digestAt + 8 * i : Nat) : Int) } .rdx]

/-- The seed's cached digest copied to `scratch + 1568`. -/
def pkCopyExpanded : Prog isa := .seq (.block pkCopyPtrs) (.block pkCopyWords)

/-- `vg_ed25519_public_key_expanded`: the public key from the seed's SHA-512 digest
(`publicKeyExpandedContract`), calling the base-point multiplication `bs`,
`vg_ed25519_scalar_base` with the suffix `fs`. -/
def publicKeyExpanded (bs : Prog isa) (fs : String) : Prog isa :=
  .frame (.push [.rdi, .rsi, .rdx, .rax, .rax, .rax, .rax]) (pkBodyFrom pkCopyExpanded bs fs) (.pop .rax 7)

end VG.Impl.Ed25519.X86_64
