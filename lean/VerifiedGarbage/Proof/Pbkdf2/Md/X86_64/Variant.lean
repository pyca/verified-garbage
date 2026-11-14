module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyCT
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Sha512.X86_64.Variant
public import VerifiedGarbage.Proof.Sha256.X86_64.Variant
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Pbkdf2.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

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
it (`CoreOK`, once for each hash function and amount of working space) and
of the functions they call (`Callees`, once for each implementation), and the
satisfiability of the shared contracts, which the kernel checks for each
instance. Each variant's functions give its compression function the scratch
space it uses and take the working space they use (`Hash.wOf`), the functions
other algorithms call by name (`update_scratch`, HMAC's and PBKDF2's
`_scratch` functions) too: those callers' proofs take the working space of the
variant's code, at most that of the hash function's slowest implementation.
-/

@[expose] public section

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
      contract = api.sig.contract (X86_64.target.abi.withMode api.pubMode) pre post api.writeArgs stack leak := by
    exact ⟨_, _, _, rfl⟩
  ofApi : contract = api.contract X86_64.target.abi stack := by exact rfl
  spSafe : code.all (fun i => !X86_64.target.isa.writesSp i) = true
  /-- `Artifact.residue`. -/
  residue : Option (PLift (X86_64.NoResidue code contract (api.sig.retBits 64))) := none

/-- `f` as a registration of its `Api` (`Api.artifact`). -/
def StreamFn.reg (f : StreamFn) : Registration f.api X86_64.target where
  consts := []
  tables := []
  code := f.code
  contract := f.contract
  stack := f.stack
  verified := f.verified
  ofApi := f.ofApi
  ofSig := f.ofSig
  spSafe := f.spSafe
  residue := f.residue

/-- The bytes of the frame in which HMAC's `finalize` keeps the working space
of its `_scratch` form (`H.W` words, the hash function's functions' with the
variant's compression function): a quadword standing for the return address,
then the buffer. -/
def hmacFrame (H : Hash) : Nat := 8 + 8 * H.W

/-- The words of working space HMAC's `init` for a key of any length uses:
those of the HMAC functions (`H.W`), then a word for each byte of the
streaming state (as `VG.Spec.Hmac.Instance.initAnyKeyScratch` with the
instance's `scratch`). -/
def anyWords (H : Hash) : Nat := H.W + H.S

/-- The bytes of the frame in which HMAC's `init` for a key of any length
keeps its working space, which it wipes before returning: a quadword
standing for the return address, then the buffer (`anyWords` words). -/
def anyFrame (H : Hash) : Nat := 8 + 8 * anyWords H

/-- The words of working space HMAC's `init` for a key of at most a block
(`Hash.hmacInit`) uses, of the `H.W` it is given as `init_scratch`: the
streaming functions' (`so + 48` bytes, of which the compression function it
calls uses `so`), then our caller's registers. -/
def initWords (H : Hash) : Nat := H.stream.W + 6

theorem initWords_eq (H : Hash) : initWords H = (H.P.so + 48) / 8 + 6 := rfl

/-- The bytes of the frame in which HMAC's `init` for a key of at most a
block keeps its working space: a quadword standing for the return address,
then `initWords` words. -/
def initFrame (H : Hash) : Nat := 8 + 8 * initWords H

/-- HMAC's `init` for a key of any length, `vg_hmac_<hash>_init`: for a key
of at most a block, `H.hmacInit` (`init_scratch`'s code) in a frame holding
the working space it uses; for a longer key (cold), `H.hmacInitAny`, in a
frame holding its larger working space, which it wipes. -/
def initCode (H : Hash) (I : Spec.Hmac.Instance) : Prog isa :=
  Impl.Pbkdf2.Md.X86_64.initEntry I.S.H.blockSize
    (Impl.StackScratch.X86_64.withStackScratch (initFrame H) .r8 H.hmacInit)
    (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame H) .r8 (anyWords H) H.hmacInitAny)

/-- The bytes of the frame in which PBKDF2's `pbkdf2` keeps its working
space, for its `_scratch` form: a quadword standing for the return address,
a copy of `out_len` and the buffer's address (its stack arguments), then the
buffer (`H.W + H.S` words, as `VG.Spec.Hmac.Instance.pbkdf2Scratch` with the
instance's `scratch`). -/
def pbkdf2Frame (H : Hash) : Nat := 24 + 8 * (H.W + H.S)

/-- A Merkle–Damgård hash function on x86-64, with one implementation of its
compression function: its functions, verified against the contracts of its
instance `I` (`Spec/Hmac/Generic.lean`, `Spec/Pbkdf2/Generic.lean`), with
the working space they use (`H.W` words for the HMAC functions, `H.W + H.S`
for PBKDF2's). -/
structure MdHash where
  /-- The hash function's code and the names of its functions, made with the
  working space its compression function uses (`H.P.so`): the functions
  other functions call by name (`update_scratch`, `finalize_scratch`, HMAC's
  and PBKDF2's `_scratch` functions) give it that much, and get the working
  space they use (`H.W`). -/
  H : Hash
  /-- The instance of the shared contracts. -/
  I : Spec.Hmac.Instance
  /-- What the proofs know of the hash function's code, and of the functions
  it calls. -/
  ok : HashOK H
  K : Callees H
  /-- The hash function as RSA's padding takes it. -/
  mgf : MgfLink H ok
  /-- The working space of the compression function of the hash function's
  slowest implementation, `soU` bytes, which RSASSA-PSS's code
  (`Generic/MdHash/RsaPrivateCrt/X86_64/RsaPss.lean`), which calls the
  compression function through a table, gives every implementation: what
  its proofs know of the hash function's code made with that much. -/
  soU : Nat
  okU : HashOK (H.withWs soU (Hash.wOf { H.P with so := soU }))
  hSU : okU.SH = I.S
  hmacInit : Verified X86_64.target H.hmacInit (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16)
  hmacFin : Verified X86_64.target H.hmacFin (Proof.Hmac.finalizeScratchContract I.S H.W X86_64.abi 16)
  iterate : Verified X86_64.target H.iterate (Proof.Pbkdf2.iterateContract I.S H.W X86_64.abi 8)
  pbkdf2 : Verified X86_64.target H.pbkdf2 (Proof.Pbkdf2.pbkdf2ScratchContract I.S (H.W + H.S) X86_64.abi 24)
  hmacInitSp : H.hmacInit.all (fun i => !isa.writesSp i) = true
  hmacFinSp : H.hmacFin.all (fun i => !isa.writesSp i) = true
  iterateSp : H.iterate.all (fun i => !isa.writesSp i) = true
  pbkdf2Sp : H.pbkdf2.all (fun i => !isa.writesSp i) = true
  /-- HMAC's `init` for a key of any length (`initEntry`): for a key of at
  most a block, `init_scratch` with its working space in a frame of its own;
  for a longer key, `hmacInitAny` with its working space in a frame of its
  own, wiped before returning; and `finalize` with its working space in a
  frame of its own (`hmacFin` is its `_scratch` form). -/
  hmacInitF : Verified X86_64.target (initCode H I) (I.initAnyKeyContract X86_64.abi (24 + anyFrame H))
  hmacInitFSp : (initCode H I).all (fun i => !isa.writesSp i) = true
  /-- The two branches of `initCode`, each verified against its contract:
  what `hmacInitF` is made of, for `MdHash.initScrubbed`, which clears after
  each. -/
  hmacShortF : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch (initFrame H) .r8 H.hmacInit)
    (I.initContract X86_64.abi (16 + initFrame H))
  hmacShortFSp : (Impl.StackScratch.X86_64.withStackScratch (initFrame H) .r8 H.hmacInit).all
    (fun i => !isa.writesSp i) = true
  hmacAnyF : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame H) .r8 (anyWords H) H.hmacInitAny)
    (I.initAnyKeyContract X86_64.abi (24 + anyFrame H))
  hmacAnyFSp : (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame H) .r8 (anyWords H)
    H.hmacInitAny).all (fun i => !isa.writesSp i) = true
  /-- The streaming states represent a message by their bytes alone, and a
  block's size is small. -/
  reprLocal : Proof.Hmac.ReprLocal I.S
  hBlock : I.S.H.blockSize + 1 < 2 ^ 31
  hmacFinF : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame H) .r8 H.hmacFin)
    (I.finalizeContract X86_64.abi (16 + hmacFrame H))
  /-- PBKDF2's `pbkdf2` with its working space in a frame of its own
  (`pbkdf2` is its `_scratch` form). -/
  pbkdf2F : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame H) 1 H.pbkdf2)
    (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame H))
  /-- What the kernel checked of the code HMAC and PBKDF2 add to the hash
  function's (`CoreOK`), and that the instance's streaming hash function is
  the code's: what a function generic over the variant that calls HMAC's
  `_scratch` functions needs (deterministic ECDSA's, through a table of
  `Hmac`, `Proof/HmacTable/X86_64.lean`). -/
  C : CoreOK (core H)
  hSH : ok.SH = I.S
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
  /-- The residue analysis of HMAC's `finalize` (`hmacFinF`), if the analysis
  handles it: that function then returns without secret residue
  (`MdHash.hmacFinReg`). -/
  hmacFinRes : Option (RScrub.Analysed I.finalizeApi.sig (16 + hmacFrame H) []
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame H) .r8 H.hmacFin)) := none

/-- The hash function's code made with the working space of its slowest
implementation's compression function (`MdHash.soU`). -/
abbrev MdHash.U (v : MdHash) : Hash := v.H.withWs v.soU (Hash.wOf { v.H.P with so := v.soU })

/-- `MdHash.K` for `MdHash.U`. -/
theorem MdHash.KU (v : MdHash) : Callees v.U := v.K.withWs _ _

/-- `MdHash.mgf` for `MdHash.U`. -/
def MdHash.mgfU (v : MdHash) : MgfLink v.U v.okU :=
  ⟨v.mgf.G, v.mgf.mem, fun x => (v.mgf.hash x).trans (by rw [v.hSH, v.hSU]), v.mgf.len⟩

namespace MdHash

variable {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
  (hSH : hH.SH = I.S)
include hH C K hSH

theorem hmacInit_of (hs : ∃ s, (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16) := by
  rw [← hSH] at hs ⊢
  exact hmacInit_verified hH C K hs

/-- `hmacInit_of`, with the working space `init` uses (`initWords`). -/
theorem hmacInitW_of (hs : ∃ s, (Proof.Hmac.initScratchContract I.S (initWords H) X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (Proof.Hmac.initScratchContract I.S (initWords H) X86_64.abi 16) := by
  rw [← hSH] at hs ⊢
  refine hmacInit_verifiedW hH C K ?_ hs
  show 8 * ((H.P.so + 48) / 8) + 48 ≤ 8 * ((H.P.so + 48) / 8 + 6)
  omega_using []

theorem hmacFin_of (hs : ∃ s, (Proof.Hmac.finalizeScratchContract I.S H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (Proof.Hmac.finalizeScratchContract I.S H.W X86_64.abi 16) := by
  rw [← hSH] at hs ⊢
  exact hmacFin_verified hH C K hs

theorem iterate_of (hs : ∃ s, (Proof.Pbkdf2.iterateContract I.S H.W X86_64.abi 8).pre s) :
    Verified X86_64.target H.iterate (Proof.Pbkdf2.iterateContract I.S H.W X86_64.abi 8) := by
  rw [← hSH] at hs ⊢
  exact iterate_verified hH C K hs

theorem pbkdf2_of (hsI : ∃ s, (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.finalizeScratchContract I.S H.W X86_64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.iterateContract I.S H.W X86_64.abi 8).pre s)
    (hs : ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract I.S (H.W + H.S) X86_64.abi 24).pre s) :
    Verified X86_64.target H.pbkdf2 (Proof.Pbkdf2.pbkdf2ScratchContract I.S (H.W + H.S) X86_64.abi 24) := by
  rw [← hSH] at hsI hsF hsT hs ⊢
  exact pbkdf2_verified hH C K hsI hsF hsT hs

theorem hmacInitAny_of (A : Any.AnyOK (core H))
    (hsI : ∃ s, (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16).pre s)
    (hs : ∃ s, (Any.anyScratchContract I.S (anyWords H)).pre s) :
    Verified X86_64.target H.hmacInitAny (Any.anyScratchContract I.S (anyWords H)) := by
  rw [← hSH] at hsI hs ⊢
  exact Any.hmacInitAny_verified hH C A K hsI hs

omit hH C hSH in
theorem hmacInitAnySp_of (A : Any.AnyOK (core H)) :
    (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame H) .r8 (anyWords H)
      H.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe (by decide)
    (by simp only [Code.all, Any.hmacInitAny_sp A K, X86_64.wipe_spSafe, Bool.and_self])

theorem hmacInitAnyF_of (A : Any.AnyOK (core H))
    (hsI : ∃ s, (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16).pre s)
    (hs : ∃ s, (Any.anyScratchContract I.S (anyWords H)).pre s) (ha : anyWords H < 511)
    (hR : Proof.Hmac.ReprLocal I.S)
    (hsat : ∃ s, (I.initAnyKeyContract X86_64.abi (24 + anyFrame H)).pre s) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame H) .r8 (anyWords H) H.hmacInitAny)
      (I.initAnyKeyContract X86_64.abi (24 + anyFrame H)) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := anyWords H) (post := Spec.Hmac.initPost I.S X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := anyFrame H) (words := anyWords H) (hmacInitAny_of hH C K hSH A hsI hs)
    (by exact (by decide : 4 < 6)) (by simp only [anyFrame, Elem.size]; omega_arith) (by simp only [anyFrame]; omega_arith)
    (Any.hmacInitAny_sp A K) (Any.hmacInitAny_xd A K)
    (by simp only [Elem.size]; omega_arith)
    (Proof.Hmac.initPostOut_local I.S _ hR (by
      rw [← hSH, hH.hS]; have := hH.N_le; have := hH.B_le
      show H.P.N + H.P.B < 2 ^ 64; omega_arith)) hsat rfl

theorem hmacShortF_of (hsI : ∃ s, (Proof.Hmac.initScratchContract I.S (initWords H) X86_64.abi 16).pre s)
    (hsat : ∃ s, (I.initContract X86_64.abi (16 + initFrame H)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch (initFrame H) .r8 H.hmacInit)
      (I.initContract X86_64.abi (16 + initFrame H)) :=
  have : initWords H < 263 := by rw [initWords_eq]; have := hH.hso; omega_using [this]
  X86_64.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := initWords H) (pre := Spec.Hmac.initPre I.S X86_64.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := initFrame H) (hmacInitW_of hH C K hSH hsI) (by exact (by decide : 4 < 6))
    (by simp only [initFrame, Elem.size]; omega_arith) (by simp only [initFrame]; omega_arith) (hmacInit_sp C K)
    (Callees.hmacInitXD K C) hsat rfl

theorem hmacInitF_of (A : Any.AnyOK (core H))
    (hsI : ∃ s, (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16).pre s)
    (hsW : ∃ s, (Proof.Hmac.initScratchContract I.S (initWords H) X86_64.abi 16).pre s)
    (hsIF : ∃ s, (I.initContract X86_64.abi (16 + initFrame H)).pre s)
    (hsA : ∃ s, (Any.anyScratchContract I.S (anyWords H)).pre s) (ha : anyWords H < 511)
    (hR : Proof.Hmac.ReprLocal I.S) (hB : I.S.H.blockSize + 1 < 2 ^ 31)
    (hsat : ∃ s, (I.initAnyKeyContract X86_64.abi (24 + anyFrame H)).pre s) :
    Verified X86_64.target (initCode H I) (I.initAnyKeyContract X86_64.abi (24 + anyFrame H)) :=
  have : initWords H ≤ H.W := by
    have h := C.fitI
    change 8 * ((H.P.so + 48) / 8) + 48 ≤ 8 * H.W at h
    rw [initWords_eq]; omega_using [h]
  initEntry_verified (hmacShortF_of hH C K hSH hsW hsIF)
    (hmacInitAnyF_of hH C K hSH A hsI hsA ha hR hsat) (by omega_arith)
    (by simp only [initFrame, anyFrame, anyWords]; omega_arith) hB hsat

omit hH hSH in
theorem hmacShortFSp_of :
    (Impl.StackScratch.X86_64.withStackScratch (initFrame H) .r8 H.hmacInit).all
      (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe_of (r := .r8) (hmacInit_sp C K)

omit hH hSH in
theorem hmacInitFSp_of (A : Any.AnyOK (core H)) :
    (initCode H I).all (fun i => !isa.writesSp i) = true := by
  simp only [initCode, Impl.Pbkdf2.Md.X86_64.initEntry, Code.iteCold, Code.all, hmacInitAnySp_of K A,
    hmacShortFSp_of C K, Bool.and_true]
  rfl

theorem hmacFinF_of (hsF : ∃ s, (Proof.Hmac.finalizeScratchContract I.S H.W X86_64.abi 16).pre s)
    (hs : H.W < 511) (hsat : ∃ s, (I.finalizeContract X86_64.abi (16 + hmacFrame H)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch (hmacFrame H) .r8 H.hmacFin)
      (I.finalizeContract X86_64.abi (16 + hmacFrame H)) :=
  X86_64.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := H.W) (post := Spec.Hmac.finalizePost I.S X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame H) (hmacFin_of hH C K hSH hsF) (by exact (by decide : 4 < 6))
    (by simp only [hmacFrame, Elem.size]; omega_arith) (by simp only [hmacFrame]; omega_arith) (hmacFin_sp C K)
    (Callees.hmacFinXD K C) hsat rfl

theorem pbkdf2F_of (hsI : ∃ s, (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.finalizeScratchContract I.S H.W X86_64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.iterateContract I.S H.W X86_64.abi 8).pre s)
    (hsP : ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract I.S (H.W + H.S) X86_64.abi 24).pre s)
    (hp : H.W + H.S < 509)
    (hsat : ∃ s, (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame H)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame H) 1 H.pbkdf2)
      (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame H)) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Pbkdf2.pbkdf2Sig) (nm := "scratch") (e := .u64)
    (n := H.W + H.S) (pre := Spec.Pbkdf2.pbkdf2Pre I.S X86_64.abi.ptrBits)
    (post := Spec.Pbkdf2.pbkdf2Post I.S X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := pbkdf2Frame H) (pbkdf2_of hH C K hSH hsI hsF hsT hsP) (by decide)
    (by
      have : X86_64.nStack Spec.Pbkdf2.pbkdf2Sig = 1 := rfl
      simp only [pbkdf2Frame, Elem.size]; omega_arith)
    (by simp only [pbkdf2Frame]; omega_arith) (pbkdf2_sp C K) (Callees.pbkdf2XD K C)
    (pbkdf2Pre_local I.S _) (pbkdf2Post_local I.S _) hsat

end MdHash

/-- The variant of hash function `H`, of instance `I`, from what the proofs
need of it (with the working space its compression function uses, and with
its slowest implementation's, `okU`) and the satisfiability of the shared
contracts. -/
def MdHash.of {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
    (mgf : MgfLink H hH) (hSH : hH.SH = I.S)
    (soU : Nat) (okU : HashOK (H.withWs soU (Hash.wOf { H.P with so := soU }))) (hSU : okU.SH = I.S)
    (hsI : ∃ s, (Proof.Hmac.initScratchContract I.S H.W X86_64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.finalizeScratchContract I.S H.W X86_64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.iterateContract I.S H.W X86_64.abi 8).pre s)
    (hsP : ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract I.S (H.W + H.S) X86_64.abi 24).pre s)
    (hs : H.W < 511)
    (A : Any.AnyOK (core H)) (hsA : ∃ s, (Any.anyScratchContract I.S (anyWords H)).pre s)
    (ha : anyWords H < 511) (hR : Proof.Hmac.ReprLocal I.S)
    (hsAF : ∃ s, (I.initAnyKeyContract X86_64.abi (24 + anyFrame H)).pre s)
    (hsW : ∃ s, (Proof.Hmac.initScratchContract I.S (initWords H) X86_64.abi 16).pre s)
    (hsIF : ∃ s, (I.initContract X86_64.abi (16 + initFrame H)).pre s)
    (hB : I.S.H.blockSize + 1 < 2 ^ 31)
    (hsFF : ∃ s, (I.finalizeContract X86_64.abi (16 + hmacFrame H)).pre s)
    (hp : H.W + H.S < 509)
    (hsPF : ∃ s, (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame H)).pre s)
    (suffix : String) (features : List String) (stream : List StreamFn) : MdHash where
  H := H
  I := I
  ok := hH
  K := K
  mgf := mgf
  soU := soU
  okU := okU
  hSU := hSU
  hmacInit := MdHash.hmacInit_of hH C K hSH hsI
  hmacFin := MdHash.hmacFin_of hH C K hSH hsF
  iterate := MdHash.iterate_of hH C K hSH hsT
  pbkdf2 := MdHash.pbkdf2_of hH C K hSH hsI hsF hsT hsP
  hmacInitSp := hmacInit_sp C K
  hmacFinSp := hmacFin_sp C K
  iterateSp := iterate_sp C K
  pbkdf2Sp := pbkdf2_sp C K
  hmacInitF := MdHash.hmacInitF_of hH C K hSH A hsI hsW hsIF hsA ha hR hB hsAF
  hmacInitFSp := MdHash.hmacInitFSp_of C K A
  hmacShortF := MdHash.hmacShortF_of hH C K hSH hsW hsIF
  hmacShortFSp := MdHash.hmacShortFSp_of C K
  hmacAnyF := MdHash.hmacInitAnyF_of hH C K hSH A hsI hsA ha hR hsAF
  hmacAnyFSp := MdHash.hmacInitAnySp_of K A
  reprLocal := hR
  hBlock := hB
  hmacFinF := MdHash.hmacFinF_of hH C K hSH hsF hs hsFF
  pbkdf2F := MdHash.pbkdf2F_of hH C K hSH hsI hsF hsT hsP hp hsPF
  C := C
  hSH := hSH
  suffix := suffix
  features := features
  stream := stream

end VG.Proof.Pbkdf2.Md.X86_64
