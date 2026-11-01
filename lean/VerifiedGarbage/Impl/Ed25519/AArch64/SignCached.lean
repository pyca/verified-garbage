module

public import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
public import VerifiedGarbage.Impl.Ed25519.AArch64.SignCached.Prefix
public import VerifiedGarbage.Impl.Ed25519.AArch64.MulAdd

/-! Complete cached-key signing. SHA-512 is generic over its compression
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

def hashSeed (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq init (.seq (update compress suffix (inputArgs 1 0)) (finalize compress suffix 32 false))
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

def secretCode (compress : Prog isa) (suffix : String) : Prog isa :=
  .seq (hashSeed compress suffix) (.block saveSecret)
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
def body (compress : Prog isa) (suffix : String) : Prog isa :=
  bodyFrom (hashSeed compress suffix) compress suffix
def code (compress : Prog isa) (suffix : String) : Prog isa := wrap (body compress suffix)

/-- Signing with the seed's cached SHA-512 digest (`signExpandedContract`): `code`, with the
digest copied (`PublicKey.copyExpanded`) rather than computed. -/
def codeExpanded (compress : Prog isa) (suffix : String) : Prog isa :=
  wrap (bodyFrom PublicKey.copyExpanded compress suffix)

end VG.Impl.Ed25519.AArch64.SignCached
