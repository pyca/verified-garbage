module

public import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
public import VerifiedGarbage.Impl.Ed25519.AArch64.SignCached.Prefix
public import VerifiedGarbage.Impl.Ed25519.AArch64.MulAdd
public import VerifiedGarbage.Impl.Sha512.AArch64.Stream
public import VerifiedGarbage.Spec.Sha512.Contract

/-! Complete signing from the seed's cached SHA-512 digest. SHA-512 is generic over its compression
implementation. The local frame holds scalar32, prefix64, nonce96,
challenge128 and digest192; the original six arguments are saved at256.
SHA-512 state and working memory use scratch[0..880). All secret local
buffers are wiped before returning. -/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64.SignCached
open VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def initArgs : List Instr := setup [(.x0, .caller 5 0)]
def inputArgs (source count : Nat) : List Instr :=
  setup [(.x0, .caller 5 0), (.x1, .const count), (.x2, .caller source 0),
    (.x3, .const 32), (.x4, .caller 5 192)]
def prefixArgs : List Instr :=
  setup [(.x0, .caller 5 0), (.x1, .const 0), (.x2, .frame 64),
    (.x3, .const 32), (.x4, .caller 5 192)]
def messageArgs (count : Nat) : List Instr :=
  setup [(.x0, .caller 5 0), (.x1, .const count), (.x2, .caller 3 0),
    (.x3, .caller 4 0), (.x4, .caller 5 192)]
def finalizeArgs (prefixLen : Nat) (withMessage : Bool) : List Instr :=
  setup [(.x0, .caller 5 0), (.x1, if withMessage then .caller 4 prefixLen else .const prefixLen),
    (.x2, .frame 192), (.x3, .caller 5 192)]

def init : Prog isa := callWith initArgs Spec.Sha512.init512Api.name
  (Sha512.AArch64.Stream.init Spec.Sha512.H0_512)
def update (compress : Prog isa) (suffix : String) (args : List Instr) : Prog isa :=
  callWith args ("vg_sha512_update_scratch" ++ suffix) (Sha512.AArch64.Stream.updateWith suffix compress)
def finalize (compress : Prog isa) (suffix : String) (n : Nat) (b : Bool) : Prog isa :=
  callWith (finalizeArgs n b) ("vg_sha512_finalize_scratch" ++ suffix)
    (Sha512.AArch64.Stream.finalizeWith suffix compress)

def saveSecret : List Instr := PublicKey.prune ++ copyPrefix

def hashNonce (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq init (.seq (update compress suffix prefixArgs)
    (.seq (update compress suffix (messageArgs 32)) (finalize compress suffix 32 true)))
def reduceArgs (out : Nat) : List Instr :=
  setup [(.x0, .frame out), (.x1, .frame 192), (.x2, .caller 5 0)]
def reduce (out : Nat) : Prog isa :=
  callWith (reduceArgs out) "vg_ed25519_scalar_reduce" scalarReduce
def baseArgs : List Instr := setup [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]
def hashChallenge (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq init (.seq (update compress suffix (inputArgs 0 0))
    (.seq (update compress suffix (inputArgs 2 32))
      (.seq (update compress suffix (messageArgs 64)) (finalize compress suffix 64 true))))
def mulAddArgs : List Instr :=
  setup [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128),
    (.x3, .frame 32), (.x4, .caller 5 0)]
def wipe : List Instr := zeroWords 4 28

def nonceCode (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq (hashNonce compress suffix) (.seq (reduce 96)
    (callWith baseArgs "vg_ed25519_scalar_base" scalarBase))
def challengeCode (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq (hashChallenge compress suffix) (.seq (reduce 128)
    (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd))
/-- Signing after `secret`, which leaves the seed's SHA-512 digest at `frame 192`. -/
def bodyFrom (secret : Prog isa) (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq (.seq secret (.block saveSecret)) (.seq (nonceCode compress suffix)
    (.seq (challengeCode compress suffix) (.block wipe)))
/-- `vg_ed25519_sign_expanded`: signing with the seed's cached SHA-512 digest
(`signExpandedContract`), copied to `frame 192` by `PublicKey.copyExpanded`. -/
def codeExpanded (compress : Prog isa) (suffix : String) : Prog isa :=
  wrap (bodyFrom PublicKey.copyExpanded compress suffix)

/-! ## The function, as emitted -/

namespace Fn

open VG.Impl.Scrub.AArch64 (Clear scrubAll)

/-- The registers `vg_ed25519_sign_expanded`'s own instructions write. -/
def signExpandedOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [], []⟩

/-- `vg_ed25519_sign_expanded` over an implementation of SHA-512's compression
function: `codeExpanded`, then its cleanup (`Impl.Scrub.AArch64.scrubAll`),
which clears the registers its own instructions and the compression function
write that the calling convention does not preserve, and zeroes its 352
bytes of stack, so that it returns without secret residue. -/
def signExpanded (c : Sha512.AArch64.Stream.Compress) : Prog isa :=
  scrubAll 352 0 (signExpandedOwn.union c.clear) (codeExpanded c.code c.suffix)

end Fn

end VG.Impl.Ed25519.AArch64.SignCached
