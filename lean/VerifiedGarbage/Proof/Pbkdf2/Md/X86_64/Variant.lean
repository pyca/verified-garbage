import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.Proof.Sha512.X86_64.Variant
import VerifiedGarbage.Proof.Sha256.X86_64.Variant
import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.RsaPss.X86_64.Checks

/-!
# Merkle–Damgård hash functions on x86-64, as variants

An `MdHash` is one Merkle–Damgård hash function with one implementation of
its compression function: each is a variant of the interface `MdHash` on
x86-64 (`Variants/MdHash/X86_64/`), and each function built on the hash
function (in `Generic/MdHash/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`): its streaming `update` and `finalize` (when they are not
shared by several variants, `stream`), HMAC's `init` and `finalize`, and
PBKDF2's `iterate` and `pbkdf2`, all named with the variant's `suffix`.

`MdHash.of` builds one from what the proofs need of the hash function's
code (`HashOK`), what the kernel checks of the code HMAC and PBKDF2 add to
it (`CoreOK`, once for each hash function) and of the functions they call
(`Callees`, once for each implementation), and the satisfiability of the
shared contracts, which the kernel checks for each instance.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- `Code.allInstrs p` from `Code.all p`. -/
theorem allInstrs_of_all {I C : Type} {p : I → Bool} {c : Code I C} (h : c.all p = true) :
    c.allInstrs p = true := by
  induction c with
  | block is => induction is <;> simp_all [Code.all, Code.allInstrs]
  | _ => simp_all [Code.all, Code.allInstrs]

/-- One of the streaming functions made with an implementation of a hash
function's compression function, which `Generic/MdHash/X86_64/Stream.lean`
emits, naming it with the variant's suffix: its `Api` (in `Spec/`), and its
code, verified against the contract the `Api` gives it (`ofApi`, as
`Artifact.ofApi`) with `stack` bytes of stack. -/
structure StreamFn where
  api : Api
  code : Prog X86_64.target.isa
  contract : Contract X86_64.target.isa
  stack : Nat := 0
  verified : Verified X86_64.target code contract
  ofSig : ∃ pre post leak,
      contract = api.sig.contract X86_64.target.abi pre post api.writeArgs stack leak := by
    exact ⟨_, _, _, rfl⟩
  ofApi : api.contracts.elim True fun f => contract = f X86_64.target.abi stack := by
    first | exact True.intro | exact rfl
  spSafe : code.all (fun i => !X86_64.target.isa.writesSp i) = true

/-- The bytes of the frame in which HMAC's `init` and `finalize` (of
instance `I`) keep their working space, for their `_scratch` forms. -/
def hmacFrame (I : Spec.Hmac.Instance) : Nat := 8 + 8 * I.scratch

/-- The bytes of the frame in which PBKDF2's `pbkdf2` (of instance `I`) keeps
its working space, for its `_scratch` form: a quadword standing for the
return address, a copy of `out_len` and the buffer's address (its stack
arguments), then the buffer. -/
def pbkdf2Frame (I : Spec.Hmac.Instance) : Nat := 24 + 8 * I.pbkdf2Scratch

/-- A Merkle–Damgård hash function on x86-64, with one implementation of its
compression function: its functions, verified against the contracts of its
instance `I` (`Spec/Hmac/Generic.lean`, `Spec/Pbkdf2/Generic.lean`). -/
structure MdHash where
  /-- The hash function's code and the names of its functions. -/
  H : Hash
  /-- The instance of the shared contracts. -/
  I : Spec.Hmac.Instance
  /-- What the proofs know of the hash function's code, and of the functions
  it calls (for the callers that work at the level of its compression
  function: RSASSA-PSS's, `Generic/MdHash/RsaPrivateCrt/X86_64/RsaPss.lean`). -/
  ok : HashOK H
  K : Callees H
  /-- The hash function as RSA's padding takes it. -/
  mgf : MgfLink H ok
  /-- RSASSA-PSS's taint checks of the pieces of its code that depend on the
  hash function, once for each hash function. -/
  pss : Proof.RsaPss.X86_64.PssChecks H.P H.D
  hmacInit : Verified X86_64.target H.hmacInit (I.initScratchContract X86_64.abi 16)
  hmacFin : Verified X86_64.target H.hmacFin (I.finalizeScratchContract X86_64.abi 16)
  iterate : Verified X86_64.target H.iterate (I.iterateContract X86_64.abi 8)
  pbkdf2 : Verified X86_64.target H.pbkdf2 (I.pbkdf2ScratchContract X86_64.abi 24)
  hmacInitSp : H.hmacInit.all (fun i => !isa.writesSp i) = true
  hmacFinSp : H.hmacFin.all (fun i => !isa.writesSp i) = true
  iterateSp : H.iterate.all (fun i => !isa.writesSp i) = true
  pbkdf2Sp : H.pbkdf2.all (fun i => !isa.writesSp i) = true
  /-- HMAC's `init` and `finalize` with their working space in a frame of
  their own (`hmacInit` and `hmacFin` are their `_scratch` forms). -/
  hmacInitF : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit)
    (I.initContract X86_64.abi (16 + hmacFrame I))
  hmacFinF : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacFin)
    (I.finalizeContract X86_64.abi (16 + hmacFrame I))
  /-- PBKDF2's `pbkdf2` with its working space in a frame of its own
  (`pbkdf2` is its `_scratch` form). -/
  pbkdf2F : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame I) 1 H.pbkdf2)
    (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame I))
  /-- What the names of the functions emitted for it end with (e.g.
  `_shani`; nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String
  /-- The streaming `update` and `finalize` made with this implementation of
  the compression function, when no other variant shares them (otherwise
  they are in the hash function's registration file). -/
  stream : List StreamFn
  /-- For SHA-512's variants, the implementation of the compression
  function, from which the functions built on SHA-512 alone (Ed25519's) are
  made (`Generic/MdHash/X86_64/Ed25519.lean`); `none` for the other hash
  functions. -/
  sha512 : Option Proof.Sha512.X86_64.Compress := none
  /-- For SHA-256's variants, the implementation of the compression
  function, from which the functions built on SHA-256 alone (scrypt's) are
  made (`Generic/MdHash/X86_64/Scrypt.lean`); `none` for the other hash
  functions. -/
  sha256 : Option Proof.Sha256.X86_64.Compress := none
  /-- For SHA-384's variants, the implementation of the compression
  function, from which the functions built on SHA-384 alone (deterministic
  ECDSA's) are made (`Generic/MdHash/P256/X86_64/EcdsaP256Sha384.lean`); `none`
  for the other hash functions. -/
  sha384 : Option Proof.Sha512.X86_64.Compress := none

namespace MdHash

variable {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
  (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
include hH C K hSH hW

theorem hmacInit_of (hs : ∃ s, (I.initScratchContract X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (I.initScratchContract X86_64.abi 16) := by
  simp only [Spec.Hmac.Instance.initScratchContract, ← hSH, ← hW] at hs ⊢
  exact hmacInit_verified hH C K hs

theorem hmacFin_of (hs : ∃ s, (I.finalizeScratchContract X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (I.finalizeScratchContract X86_64.abi 16) := by
  simp only [Spec.Hmac.Instance.finalizeScratchContract, ← hSH, ← hW] at hs ⊢
  exact hmacFin_verified hH C K hs

theorem iterate_of (hs : ∃ s, (I.iterateContract X86_64.abi 8).pre s) :
    Verified X86_64.target H.iterate (I.iterateContract X86_64.abi 8) := by
  simp only [Spec.Hmac.Instance.iterateContract, ← hSH, ← hW] at hs ⊢
  exact iterate_verified hH C K hs

theorem pbkdf2_of (hsI : ∃ s, (I.initScratchContract X86_64.abi 16).pre s)
    (hsF : ∃ s, (I.finalizeScratchContract X86_64.abi 16).pre s)
    (hsT : ∃ s, (I.iterateContract X86_64.abi 8).pre s)
    (hs : ∃ s, (I.pbkdf2ScratchContract X86_64.abi 24).pre s) :
    Verified X86_64.target H.pbkdf2 (I.pbkdf2ScratchContract X86_64.abi 24) := by
  simp only [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.Instance.finalizeScratchContract,
    Spec.Hmac.Instance.iterateContract, Spec.Hmac.Instance.pbkdf2ScratchContract,
    Spec.Hmac.Instance.pbkdf2Scratch, ← hSH, ← hW, hH.hS] at hsI hsF hsT hs ⊢
  exact pbkdf2_verified hH C K hsI hsF hsT hs

theorem hmacInitF_of (hsI : ∃ s, (I.initScratchContract X86_64.abi 16).pre s) (hs : I.scratch < 511)
    (hsat : ∃ s, (I.initContract X86_64.abi (16 + hmacFrame I)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit)
      (I.initContract X86_64.abi (16 + hmacFrame I)) :=
  X86_64.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (pre := Spec.Hmac.initPre I.S X86_64.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame I) (hmacInit_of hH C K hSH hW hsI) (by exact (by decide : 4 < 6))
    (by simp only [hmacFrame, Elem.size]; omega) (by simp only [hmacFrame]; omega) (hmacInit_sp C K)
    (Callees.hmacInitXD K C) hsat rfl

theorem hmacFinF_of (hsF : ∃ s, (I.finalizeScratchContract X86_64.abi 16).pre s) (hs : I.scratch < 511)
    (hsat : ∃ s, (I.finalizeContract X86_64.abi (16 + hmacFrame I)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacFin)
      (I.finalizeContract X86_64.abi (16 + hmacFrame I)) :=
  X86_64.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (post := Spec.Hmac.finalizePost I.S X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame I) (hmacFin_of hH C K hSH hW hsF) (by exact (by decide : 4 < 6))
    (by simp only [hmacFrame, Elem.size]; omega) (by simp only [hmacFrame]; omega) (hmacFin_sp C K)
    (Callees.hmacFinXD K C) hsat rfl

theorem pbkdf2F_of (hsI : ∃ s, (I.initScratchContract X86_64.abi 16).pre s)
    (hsF : ∃ s, (I.finalizeScratchContract X86_64.abi 16).pre s)
    (hsT : ∃ s, (I.iterateContract X86_64.abi 8).pre s)
    (hsP : ∃ s, (I.pbkdf2ScratchContract X86_64.abi 24).pre s) (hp : I.pbkdf2Scratch < 509)
    (hsat : ∃ s, (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame I)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame I) 1 H.pbkdf2)
      (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame I)) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Pbkdf2.pbkdf2Sig) (nm := "scratch") (e := .u64)
    (n := I.pbkdf2Scratch) (pre := Spec.Pbkdf2.pbkdf2Pre I.S X86_64.abi.ptrBits)
    (post := Spec.Pbkdf2.pbkdf2Post I.S X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := pbkdf2Frame I) (pbkdf2_of hH C K hSH hW hsI hsF hsT hsP) (by decide)
    (by
      have : X86_64.nStack Spec.Pbkdf2.pbkdf2Sig = 1 := rfl
      simp only [pbkdf2Frame, Elem.size]; omega)
    (by simp only [pbkdf2Frame]; omega) (pbkdf2_sp C K) (Callees.pbkdf2XD K C)
    (pbkdf2Pre_local I.S _) (pbkdf2Post_local I.S _) hsat

end MdHash

/-- The variant of hash function `H`, of instance `I`, from what the proofs
need of it and the satisfiability of the shared contracts. -/
def MdHash.of {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
    (mgf : MgfLink H hH) (pss : Proof.RsaPss.X86_64.PssChecks H.P H.D) (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
    (hsI : ∃ s, (I.initScratchContract X86_64.abi 16).pre s)
    (hsF : ∃ s, (I.finalizeScratchContract X86_64.abi 16).pre s)
    (hsT : ∃ s, (I.iterateContract X86_64.abi 8).pre s)
    (hsP : ∃ s, (I.pbkdf2ScratchContract X86_64.abi 24).pre s)
    (hs : I.scratch < 511)
    (hsIF : ∃ s, (I.initContract X86_64.abi (16 + hmacFrame I)).pre s)
    (hsFF : ∃ s, (I.finalizeContract X86_64.abi (16 + hmacFrame I)).pre s)
    (hp : I.pbkdf2Scratch < 509)
    (hsPF : ∃ s, (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame I)).pre s)
    (suffix : String) (features : List String) (stream : List StreamFn) : MdHash where
  H := H
  I := I
  ok := hH
  K := K
  mgf := mgf
  pss := pss
  hmacInit := MdHash.hmacInit_of hH C K hSH hW hsI
  hmacFin := MdHash.hmacFin_of hH C K hSH hW hsF
  iterate := MdHash.iterate_of hH C K hSH hW hsT
  pbkdf2 := MdHash.pbkdf2_of hH C K hSH hW hsI hsF hsT hsP
  hmacInitSp := hmacInit_sp C K
  hmacFinSp := hmacFin_sp C K
  iterateSp := iterate_sp C K
  pbkdf2Sp := pbkdf2_sp C K
  hmacInitF := MdHash.hmacInitF_of hH C K hSH hW hsI hs hsIF
  hmacFinF := MdHash.hmacFinF_of hH C K hSH hW hsF hs hsFF
  pbkdf2F := MdHash.pbkdf2F_of hH C K hSH hW hsI hsF hsT hsP hp hsPF
  suffix := suffix
  features := features
  stream := stream

end VG.Proof.Pbkdf2.Md.X86_64
