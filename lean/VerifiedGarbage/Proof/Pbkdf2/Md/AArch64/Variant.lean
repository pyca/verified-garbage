module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKeyCT
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKeyEntry
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Sha512.AArch64.Variant
public import VerifiedGarbage.Proof.Sha256.AArch64.Variant
public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Hmac.Scratch

/-!
# Merkle–Damgård hash functions on AArch64, as variants

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Variant.lean`): an `MdHash` is one
Merkle–Damgård hash function with one implementation of its compression
function, a variant of the interface `MdHash` on AArch64
(`Variants/MdHash/AArch64/`), and each function built on the hash function (in
`Generic/MdHash/AArch64/`) is emitted once for each of them: HMAC's `init` and
`finalize`, and PBKDF2's `iterate` and `pbkdf2`, named with the variant's
`suffix`.

`MdHash.of` builds one from what the proofs need of the hash function's
code (`HashOK`), what the kernel checks of the code HMAC and PBKDF2 add to
it (`CoreOK`, once for each hash function), and the satisfiability of the
shared contracts, which the kernel checks for each instance.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- One of the streaming functions made with an implementation of a hash
function's compression function, which `Generic/MdHash/AArch64/Stream.lean`
emits, naming it with the variant's suffix: its `Api` (in `Spec/`), and its
code, verified against the contract the `Api` gives it (`ofApi`, as
`Artifact.ofApi`) with `stack` bytes of stack. -/
structure StreamFn where
  api : Api
  code : Prog AArch64.target.isa
  contract : Contract AArch64.target.isa
  stack : Nat := 0
  verified : Verified AArch64.target code contract
  ofSig : ∃ pre post leak,
      contract = api.sig.contract AArch64.target.abi pre post api.writeArgs stack leak := by
    exact ⟨_, _, _, rfl⟩
  ofApi : contract = api.contract AArch64.target.abi stack := by exact rfl
  spSafe : code.all (fun i => !AArch64.target.isa.writesSp i) = true

/-- `f` as a registration of its `Api` (`Api.artifact`). -/
def StreamFn.reg (f : StreamFn) : Registration f.api AArch64.target where
  consts := []
  code := f.code
  contract := f.contract
  stack := f.stack
  verified := f.verified
  ofApi := f.ofApi
  ofSig := f.ofSig
  spSafe := f.spSafe

/-- The bytes of the frame in which HMAC's `init` and `finalize` (of
instance `I`) keep their working space, for their `_scratch` forms. -/
def hmacFrame (I : Spec.Hmac.Instance) : Nat := 8 * I.scratch

/-- The bytes of the frame in which HMAC's `init` for a key of any length (of
instance `I`) keeps its working space (`VG.Spec.Hmac.Instance.initAnyKeyScratch`
words), which it wipes before returning. -/
def anyFrame (I : Spec.Hmac.Instance) : Nat := 8 * I.initAnyKeyScratch

/-- HMAC's `init` for a key of any length, `vg_hmac_<hash>_init`: for a key
of at most a block, `init_scratch` (`Hash.hmacInit`) in a frame holding its
working space; for a longer key (cold), `Hash.hmacInitAny`, in a frame
holding its larger working space, which it wipes. -/
def initCode (H : Hash) (I : Spec.Hmac.Instance) : Prog isa :=
  Impl.Pbkdf2.Md.AArch64.initEntry I.S.H.blockSize
    (Impl.StackScratch.AArch64.withStackScratch (hmacFrame I) .x4 H.hmacInit)
    (Impl.StackScratch.AArch64.withStackScratchWiped (anyFrame I) .x4 I.initAnyKeyScratch H.hmacInitAny)

/-- The bytes of the frame in which PBKDF2's `pbkdf2` (of instance `I`) keeps
its working space, for its `_scratch` form. -/
def pbkdf2Frame (I : Spec.Hmac.Instance) : Nat := 8 * I.pbkdf2Scratch

/-- A Merkle–Damgård hash function on AArch64, with one implementation of
its compression function: its functions, verified against the contracts of
its instance `I` (`Spec/Hmac/Generic.lean`, `Spec/Pbkdf2/Generic.lean`). -/
structure MdHash where
  /-- The hash function's code and the names of its functions. -/
  H : Hash
  /-- The instance of the shared contracts. -/
  I : Spec.Hmac.Instance
  /-- What the proofs know of the hash function's code (for the callers that
  work at the level of its compression function: RSASSA-PSS's,
  `Generic/MdHash/RsaPrivateCrt/AArch64/RsaPss.lean`). -/
  ok : HashOK H
  /-- The hash function as RSA's padding takes it. -/
  mgf : MgfLink H ok
  /-- RSASSA-PSS's taint checks of the pieces of its code that depend on the
  hash function, once for each hash function. -/
  pss : Proof.RsaPss.AArch64.PssChecks H.P H.D
  hmacInit : Verified AArch64.target H.hmacInit (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16)
  hmacFin : Verified AArch64.target H.hmacFin (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16)
  iterate : Verified AArch64.target H.iterate (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi)
  pbkdf2 : Verified AArch64.target H.pbkdf2 (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16)
  /-- HMAC's `init` for a key of any length (`initEntry`): for a key of at
  most a block, `init_scratch` with its working space in a frame of its own;
  for a longer key, `hmacInitAny` with its working space in a frame of its
  own, wiped before returning; and `finalize` with its working space in a
  frame of its own (`hmacFin` is its `_scratch` form). -/
  hmacInitF : Verified AArch64.target (initCode H I) (I.initAnyKeyContract AArch64.abi (16 + anyFrame I))
  hmacFinF : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch (hmacFrame I) .x4 H.hmacFin)
    (I.finalizeContract AArch64.abi (16 + hmacFrame I))
  /-- PBKDF2's `pbkdf2` with its working space in a frame of its own
  (`pbkdf2` is its `_scratch` form). -/
  pbkdf2F : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch (pbkdf2Frame I) .x7 H.pbkdf2)
    (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I))
  /-- What the names of the functions emitted for it end with (nothing for
  the baseline implementation). -/
  suffix : String
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String
  /-- The streaming `update` and `finalize` made with this implementation of
  the compression function, when no other variant shares them (otherwise
  they are in the hash function's registration file). -/
  stream : List StreamFn := []
  /-- SHA-512 compression backend for constructions that require this hash. -/
  sha512 : Option Proof.Sha512.AArch64.Compress := none
  /-- For SHA-256's variants, the implementation of the compression
  function, from which the functions built on SHA-256 alone (scrypt's) are
  made (`Generic/MdHash/AArch64/Scrypt.lean`); `none` for the other hash
  functions. -/
  sha256 : Option Proof.Sha256.AArch64.Compress := none
  /-- For SHA-384's variants, the implementation of SHA-512's compression
  function, from which the functions built on SHA-384 alone (deterministic
  ECDSA's) are made (`Generic/MdHash/P256/AArch64/EcdsaP256Sha384.lean`); `none`
  for the other hash functions. -/
  sha384 : Option Proof.Sha512.AArch64.Compress := none
  /-- For SHA-224's variants, the implementation of SHA-256's compression
  function, from which the functions built on SHA-224 alone (deterministic
  ECDSA's) are made (`Generic/MdHash/P224/AArch64/EcdsaP224Sha224.lean`); `none`
  for the other hash functions. -/
  sha224 : Option Proof.Sha256.AArch64.Compress := none

namespace MdHash

variable {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H))
  (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
include hH C hSH hW

theorem hmacInit_of (hs : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16) := by
  simp only [Proof.Hmac.Instance.initScratchContract, ← hSH, ← hW] at hs ⊢
  exact hmacInit_verified hH C hs

theorem hmacFin_of (hs : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16) := by
  simp only [Proof.Hmac.Instance.finalizeScratchContract, ← hSH, ← hW] at hs ⊢
  exact hmacFin_verified hH C hs

theorem iterate_of (hs : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi) := by
  simp only [Proof.Pbkdf2.Instance.iterateContract, ← hSH, ← hW] at hs ⊢
  exact iterate_verified hH C hs

theorem pbkdf2_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi).pre s)
    (hs : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16).pre s) :
    Verified AArch64.target H.pbkdf2 (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16) := by
  simp only [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.Instance.finalizeScratchContract,
    Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.Instance.pbkdf2ScratchContract,
    Spec.Hmac.Instance.pbkdf2Scratch, ← hSH, ← hW, hH.hS] at hsI hsF hsT hs ⊢
  exact pbkdf2_verified hH C hsI hsF hsT hs

theorem hmacInitAny_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hs : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s) :
    Verified AArch64.target H.hmacInitAny (Any.anyScratchContract I.S I.initAnyKeyScratch) := by
  simp only [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, ← hSH, ← hW,
    hH.hS] at hsI hs ⊢
  exact Any.hmacInitAny_verified hH C A hsI hs

theorem hmacInitAnyF_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hs : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s)
    (ha : 0 < I.initAnyKeyScratch ∧ I.initAnyKeyScratch < 512 ∧ I.initAnyKeyScratch % 2 = 0)
    (hR : Proof.Hmac.ReprLocal I.S)
    (hsat : ∃ s, (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)).pre s) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped (anyFrame I) .x4 I.initAnyKeyScratch H.hmacInitAny)
      (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.initAnyKeyScratch) (post := Spec.Hmac.initPost I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := anyFrame I) (words := I.initAnyKeyScratch) (hmacInitAny_of hH C hSH hW A hsI hs)
    (by exact (by decide : 4 < 8)) (by simp only [anyFrame, Elem.size]; omega_arith) (by simp only [Elem.size]; omega_arith)
    (Proof.Hmac.initPostOut_local I.S _ hR (by
      rw [← hSH, hH.hS]; have := hH.N_le; have := hH.B_le
      omega_arith)) hsat

theorem hmacShortF_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hs : 0 < I.scratch ∧ I.scratch < 512 ∧ I.scratch % 2 = 0)
    (hsat : ∃ s, (I.initContract AArch64.abi (16 + hmacFrame I)).pre s) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch (hmacFrame I) .x4 H.hmacInit)
      (I.initContract AArch64.abi (16 + hmacFrame I)) :=
  AArch64.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (pre := Spec.Hmac.initPre I.S AArch64.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame I) (hmacInit_of hH C hSH hW hsI) (by exact (by decide : 4 < 8))
    (by simp only [hmacFrame, Elem.size]; omega_arith) hsat

theorem hmacInitF_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hs : 0 < I.scratch ∧ I.scratch < 512 ∧ I.scratch % 2 = 0)
    (hsIF : ∃ s, (I.initContract AArch64.abi (16 + hmacFrame I)).pre s)
    (hsA : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s)
    (ha : 0 < I.initAnyKeyScratch ∧ I.initAnyKeyScratch < 512 ∧ I.initAnyKeyScratch % 2 = 0)
    (hR : Proof.Hmac.ReprLocal I.S) (hB : I.S.H.blockSize < 2 ^ 16)
    (hsat : ∃ s, (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)).pre s) :
    Verified AArch64.target (initCode H I) (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)) :=
  initEntry_verified (hmacShortF_of hH C hSH hW hsI hs hsIF) (hmacInitAnyF_of hH C hSH hW A hsI hsA ha hR hsat)
    (by omega_arith) (by simp only [hmacFrame, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch]; omega_arith) hB hsat

theorem hmacFinF_of (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s)
    (hs : 0 < I.scratch ∧ I.scratch < 512 ∧ I.scratch % 2 = 0)
    (hsat : ∃ s, (I.finalizeContract AArch64.abi (16 + hmacFrame I)).pre s) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch (hmacFrame I) .x4 H.hmacFin)
      (I.finalizeContract AArch64.abi (16 + hmacFrame I)) :=
  AArch64.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (post := Spec.Hmac.finalizePost I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame I) (hmacFin_of hH C hSH hW hsF) (by exact (by decide : 4 < 8))
    (by simp only [hmacFrame, Elem.size]; omega_arith) hsat

theorem pbkdf2F_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi).pre s)
    (hsP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16).pre s)
    (hp : 0 < I.pbkdf2Scratch ∧ I.pbkdf2Scratch < 512 ∧ I.pbkdf2Scratch % 2 = 0)
    (hsat : ∃ s, (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I)).pre s) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch (pbkdf2Frame I) .x7 H.pbkdf2)
      (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I)) :=
  AArch64.Verified.stackScratch (sig := Spec.Pbkdf2.pbkdf2Sig) (nm := "scratch") (e := .u64)
    (n := I.pbkdf2Scratch) (pre := Spec.Pbkdf2.pbkdf2Pre I.S AArch64.abi.ptrBits)
    (post := Spec.Pbkdf2.pbkdf2Post I.S AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := pbkdf2Frame I) (pbkdf2_of hH C hSH hW hsI hsF hsT hsP) (by exact (by decide : 7 < 8))
    (by simp only [pbkdf2Frame, Elem.size]; omega_arith) hsat

end MdHash

/-- The variant of hash function `H`, of instance `I`, from what the proofs
need of it and the satisfiability of the shared contracts. -/
def MdHash.of {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (lk : MgfLink H hH)
    (pss : Proof.RsaPss.AArch64.PssChecks H.P H.D)
    (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
    (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I AArch64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I AArch64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I AArch64.abi).pre s)
    (hsP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I AArch64.abi 16).pre s)
    (hs : 0 < I.scratch ∧ I.scratch < 512 ∧ I.scratch % 2 = 0)
    (A : Any.AnyOK (core H)) (hsA : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s)
    (ha : 0 < I.initAnyKeyScratch ∧ I.initAnyKeyScratch < 512 ∧ I.initAnyKeyScratch % 2 = 0)
    (hR : Proof.Hmac.ReprLocal I.S)
    (hsAF : ∃ s, (I.initAnyKeyContract AArch64.abi (16 + anyFrame I)).pre s)
    (hsIF : ∃ s, (I.initContract AArch64.abi (16 + hmacFrame I)).pre s) (hB : I.S.H.blockSize < 2 ^ 16)
    (hsFF : ∃ s, (I.finalizeContract AArch64.abi (16 + hmacFrame I)).pre s)
    (hp : 0 < I.pbkdf2Scratch ∧ I.pbkdf2Scratch < 512 ∧ I.pbkdf2Scratch % 2 = 0)
    (hsPF : ∃ s, (I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame I)).pre s)
    (suffix : String) (features : List String) (stream : List StreamFn := []) : MdHash where
  H := H
  I := I
  ok := hH
  mgf := lk
  pss := pss
  hmacInit := MdHash.hmacInit_of hH C hSH hW hsI
  hmacFin := MdHash.hmacFin_of hH C hSH hW hsF
  iterate := MdHash.iterate_of hH C hSH hW hsT
  pbkdf2 := MdHash.pbkdf2_of hH C hSH hW hsI hsF hsT hsP
  hmacInitF := MdHash.hmacInitF_of hH C hSH hW A hsI hs hsIF hsA ha hR hB hsAF
  hmacFinF := MdHash.hmacFinF_of hH C hSH hW hsF hs hsFF
  pbkdf2F := MdHash.pbkdf2F_of hH C hSH hW hsI hsF hsT hsP hp hsPF
  suffix := suffix
  features := features
  stream := stream

end VG.Proof.Pbkdf2.Md.AArch64
