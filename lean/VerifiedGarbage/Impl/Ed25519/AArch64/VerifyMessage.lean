module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Setup
public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry
public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Wipe
public import VerifiedGarbage.Impl.Sha512.AArch64.Stream
public import VerifiedGarbage.Spec.Sha512.Contract

/-! Whole-message verification with every SHA-512 backend. -/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64.VerifyMessage
open VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def initArgs : List Instr := setup [(.x0, .caller 4 0)]
def prefixArgs (source count : Nat) : List Instr :=
  setup [(.x0, .caller 4 0), (.x1, .const count), (.x2, .caller source 0),
    (.x3, .const 32), (.x4, .caller 4 192)]
def messageArgs : List Instr :=
  setup [(.x0, .caller 4 0), (.x1, .const 64), (.x2, .caller 1 0),
    (.x3, .caller 2 0), (.x4, .caller 4 192)]
def finalizeArgs : List Instr :=
  setup [(.x0, .caller 4 0), (.x1, .caller 2 64), (.x2, .frame 192), (.x3, .caller 4 192)]

def init : Prog isa := callWith initArgs Spec.Sha512.init512Api.name
  (Sha512.AArch64.Stream.init Spec.Sha512.H0_512)
def update (compress : Prog isa) (suffix : String) (args : List Instr) : Prog isa :=
  callWith args ("vg_sha512_update_scratch" ++ suffix) (Sha512.AArch64.Stream.updateWith suffix compress)
def finalize (compress : Prog isa) (suffix : String) : Prog isa :=
  callWith finalizeArgs ("vg_sha512_finalize_scratch" ++ suffix) (Sha512.AArch64.Stream.finalizeWith suffix compress)
def hash (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq init (.seq (update compress suffix (prefixArgs 3 0))
    (.seq (update compress suffix (prefixArgs 0 32))
      (.seq (update compress suffix messageArgs) (finalize compress suffix))))
def reduceArgs : List Instr :=
  setup [(.x0, .frame 128), (.x1, .frame 192), (.x2, .caller 4 0)]
def extendChallenge : List Instr := zeroWords 20 4
def equationArgs : List Instr :=
  setup [(.x0, .caller 0 0), (.x1, .caller 3 0), (.x2, .frame 128), (.x3, .caller 4 0)]
def body (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq (hash compress suffix)
    (.seq (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce)
      (.seq (.block extendChallenge)
        (callWith equationArgs "vg_ed25519_verify_equation" verifyEquation)))
def code (compress : Prog isa) (suffix : String) : Prog isa := wrap (body compress suffix)

/-! ## The function, as emitted -/

namespace Fn

open VG.Impl.Scrub.AArch64 (Clear scrubAll)

/-- The registers `vg_ed25519_verify`'s own instructions write. -/
def verifyOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v7, .v16, .v17, .v18, .v31], []⟩

/-- `vg_ed25519_verify` over an implementation of SHA-512's compression
function: `code`, then its cleanup (`Impl.Scrub.AArch64.scrubAll`), which
clears the registers its own instructions and the compression function write
that the calling convention does not preserve, but its 32-bit result, and
zeroes its 352 bytes of stack, so that it returns without secret residue. -/
def verify (c : Sha512.AArch64.Stream.Compress) : Prog isa :=
  scrubAll 352 32 (verifyOwn.union c.clear) (code c.code c.suffix)

end Fn

end VG.Impl.Ed25519.AArch64.VerifyMessage
