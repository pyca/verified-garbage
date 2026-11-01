module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.TCB.Registration

/-!
# SHA-1 backends on x86

A backend is one implementation of SHA-1's compression function on x86: a
variant of the interface `Sha1` on x86 (`Variants/Sha1/X86/`). Each function
built on it (in `Generic/Sha1/X86/`) is emitted once for each backend, named
with its suffix (see `TCB/Emit.lean`): its own functions, the streaming
ones made with it (`functions`; its compression function and the streaming
functions with their working space passed in `scratch` are internal
functions, emitted from their callers' code), and HMAC's `init`
and `finalize`, PBKDF2's `iterate` and the whole of PBKDF2, the
implementations for every hash function (`Impl/Pbkdf2/Md/X86.lean`,
`Impl/Pbkdf2/Whole/X86.lean`) at SHA-1 made with the backend (`Code.lean`).
HMAC's `init` calls SHA-1's streaming `init` and the backend's compression
function; HMAC's `finalize` the backend's streaming `finalize` (`stream`) and
its compression function; PBKDF2's iteration its compression function. They
are proven once for every backend, against the contracts of `Spec.Hmac.sha1I`
(`Proof/Pbkdf2/Md/X86/Sha1.lean`, `Proof/Pbkdf2/Whole/X86/Sha1.lean`), from
what the backend proves of its compression function and streaming functions.
So adding an implementation of the compression function also emits the
SHA-1, HMAC and PBKDF2 functions that call it. What the kernel checks of each
backend's code (that it keeps `esp`, and the stack it uses) is evaluated on
its literals.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86.Variants

open VG.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha1Stream)
open VG.Proof.Pbkdf2.Md.X86 (sha1M)

structure StreamFn where
  api : Api
  code : Prog isa
  contract : Contract isa
  stack : Nat := 0
  verified : Verified X86.target code contract
  ofSig : ∃ pre post leak,
    contract = api.sig.contract X86.abi pre post api.writeArgs stack leak
  ofApi : contract = api.contract X86.abi stack
  spSafe : code.all (fun i => !isa.writesSp i) = true

/-- `f` as a registration of its `Api` (`Api.artifact`). -/
def StreamFn.reg (f : StreamFn) : Registration f.api X86.target where
  consts := []
  code := f.code
  contract := f.contract
  stack := f.stack
  verified := f.verified
  ofApi := f.ofApi
  ofSig := f.ofSig
  spSafe := f.spSafe

/-- The functions the whole of PBKDF2 calls, with the compression function
`cmpN`/`cmpC` and the streaming functions `s`. -/
abbrev pbkdf2Fns (s : Sha1Stream) (cmpN : String) (cmpC : Prog isa) : Impl.Pbkdf2.Whole.X86.Fns :=
  fns s.suffix cmpN cmpC s.upd s.fin

structure Backend where
  /-- The compression function, verified: it keeps `esp`, and calls nothing
  that uses the stack. -/
  cmpN : String
  cmpC : Prog isa
  cmp : Verified X86.target cmpC Proof.Sha1.compressX86
  cmpSp : NoSp cmpC
  cmpStack : stackUse cmpC = 0
  /-- SHA-1's streaming `update` and `finalize` made with it, verified, and
  the suffix of the names of the functions emitted for it (e.g. `_shani`;
  nothing for the baseline implementation). -/
  stream : Sha1Stream
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String
  /-- Its own functions: the streaming functions made with it. -/
  functions : List StreamFn
  /-- No instruction of the functions built on it writes `esp` (the
  artifacts' `spSafe`). -/
  initSp : (sha1M stream cmpN cmpC).hmacInit.all (fun i => !isa.writesSp i) = true
  finSp : (sha1M stream cmpN cmpC).hmacFin.all (fun i => !isa.writesSp i) = true
  iterSp : (sha1M stream cmpN cmpC).iterate.all (fun i => !isa.writesSp i) = true
  pbkdf2Sp : (pbkdf2Fns stream cmpN cmpC).pbkdf2.all (fun i => !isa.writesSp i) = true
  /-- What the whole of PBKDF2 needs of the functions it calls: they keep
  `esp`, and use at most 48 bytes of stack. -/
  initNoSp : NoSp (sha1M stream cmpN cmpC).hmacInit
  initStack : stackUse (sha1M stream cmpN cmpC).hmacInit ≤ 48
  finalizeNoSp : NoSp (sha1M stream cmpN cmpC).hmacFin
  finalizeStack : stackUse (sha1M stream cmpN cmpC).hmacFin ≤ 48
  iterNoSp : NoSp (sha1M stream cmpN cmpC).iterate
  iterStack : stackUse (sha1M stream cmpN cmpC).iterate ≤ 48

namespace Backend

variable (v : Backend)

/-- What the names of the functions emitted for it end with. -/
abbrev suffix : String := v.stream.suffix

/-- SHA-1 as a Merkle–Damgård hash function, as HMAC's `init` and
`finalize` and PBKDF2's iteration call it. -/
abbrev M : Impl.Pbkdf2.Md.X86.Hash := sha1M v.stream v.cmpN v.cmpC

/-- The functions the whole of PBKDF2 calls. -/
abbrev F : Impl.Pbkdf2.Whole.X86.Fns := pbkdf2Fns v.stream v.cmpN v.cmpC

/-- The compression function, as HMAC's `finalize` and PBKDF2's iteration
call it. -/
theorem comp : Proof.Pbkdf2.Md.X86.CompOk Proof.Sha1.md 112 v.cmpC := ⟨v.cmp, v.cmpSp, v.cmpStack⟩

theorem hmacInit : Verified X86.target v.M.hmacInit (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha1I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha1_init v.stream v.cmpN v.comp

theorem hmacFin : Verified X86.target v.M.hmacFin (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha1I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha1_finalize v.stream v.cmpN v.comp

theorem iterate : Verified X86.target v.M.iterate (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha1I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha1_iterate v.stream v.cmpN v.comp

end Backend

end VG.Proof.Sha1.X86.Variants
