module

public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.X86.ScrubSide
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Sha1.PostOut
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.Scrub.X86
meta import VerifiedGarbage.Proof.Sha1.PostOut
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha1
public import VerifiedGarbage.Proof.Sha1.X86.Stream.Md
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha1
meta import VerifiedGarbage.Proof.Sha1.X86.Stream.Md
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit

/-! ### `Pbkdf2.Md.X86.Sha1`, which this module and modules that import it used -/

section

/-!
# HMAC-SHA-1 and PBKDF2-HMAC-SHA-1 over the compression function on x86 (32-bit), for every backend

SHA-1 as a `Hash` of `Impl/Pbkdf2/Md/X86.lean` with a backend's compression
function and streaming functions (`Proof.Sha1.X86.Variants.mdHash`), what the
proofs know of it (`sha1Ok`): SHA-1's `Md` (`Proof/Sha1/Md.lean`) from `H0`,
the digest its streaming code writes (`Proof.Sha1.X86.Stream.shape`), and the
backend's verified compression function, whose contract is `cmpK`; and the
generic proofs of HMAC's `init` and `finalize` and PBKDF2's iteration
(`HmacInitCT.lean`, `HmacFinCT.lean`, `IterateCT.lean`) at it, moved to the
shared contracts of `Spec.Hmac.sha1I`. Their taint checks depend only on the
sizes, so they are evaluated once, for every backend (`sha1Shape`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 (Sha1Stream sha1OK)
open VG.Proof.Sha1.X86.Variants (mdHash)

/-- SHA-1 with the compression function `cmpN`/`cmpC` and the streaming
functions `v` calling it. -/
abbrev sha1M (v : Sha1Stream) (cmpN : String) (cmpC : Prog isa) : Hash :=
  mdHash v.suffix cmpN cmpC v.upd v.fin

/-- `MdOk` for SHA-1, for any backend: its streaming functions `v` and its
verified compression function `cmpC`. -/
def sha1Ok (v : Sha1Stream) (cmpN : String) {cmpC : Prog isa} (hc : CompOk Proof.Sha1.md 112 cmpC) :
    MdOk (sha1M v cmpN cmpC) where
  hH := sha1OK v
  md := Proof.Sha1.md
  iv := Spec.Sha1.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm,
    show 20 ≤ 20 by decide, show 20 + 8 < 64 by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega_using [hj])
  tail := sha1_tail
  out := outOk_of_shape Proof.Sha1.X86.Stream.shape
  comp := hc
  sizes := sha1_sizes
where
  sha1_tail : Proof.Sha1.md.tailPad 20 = (sha1M v cmpN cmpC).tailB := by
    show Proof.Sha1.md.tailPad 20 = Impl.Pbkdf2.Md.X86.tail 64 20 8 true
    decide
  sha1_sizes : Sizes (sha1M v cmpN cmpC) :=
    ⟨show 64 = 64 ∨ 64 = 128 by decide, show 0 < 20 ∧ 20 ≤ 64 ∧ 20 % 4 = 0 by decide,
      show 0 < 20 ∧ 20 ≤ 20 ∧ 20 % 4 = 0 by decide, show 20 + 8 + 4 ≤ 64 by decide,
      show 84 = 20 + 64 from rfl, show 112 ≤ 8 * 20 by decide, show 20 ≤ 64 by decide,
      show 20 ≤ 20 ∧ 20 ≤ 64 by decide⟩

/-- SHA-1's sizes and digest code, without the functions: `shapeOf` of every
backend's `sha1M`, written out, so that the kernel reduces each side to it
field by field rather than comparing the backends' functions. -/
def sha1Shape : Hash :=
  ⟨⟨64, 84, 20, 20, 20, "", .block [], "", .block [], "", .block []⟩, 20, 8, true, 112, "", .block [],
    Impl.Sha1.X86.Stream.params.out⟩

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 (Sha1Stream initW initG finW finG iterW iterG countF)

theorem sha1Shape_iterChecks : Iterate.Checks sha1Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha1Shape_initChecks : HmacInit.Checks sha1Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha1Shape_finChecks : HmacFin.Checks sha1Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha1_iterChecks (v : Sha1Stream) (cmpN : String) (cmpC : Prog isa) :
    Iterate.Checks (sha1M v cmpN cmpC) :=
  iterChecks_of_shape (H := sha1M v cmpN cmpC) sha1Shape_iterChecks

theorem sha1_initChecks (v : Sha1Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacInit.Checks (sha1M v cmpN cmpC) :=
  initChecks_of_shape (H := sha1M v cmpN cmpC) sha1Shape_initChecks

theorem sha1_finChecks (v : Sha1Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacFin.Checks (sha1M v cmpN cmpC) :=
  finChecks_of_shape (H := sha1M v cmpN cmpC) sha1Shape_finChecks

theorem sha1_iterImp : (iterW Spec.Hmac.sha1S 56).Implies (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha1I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 84 20 56
  sig_implies [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 84 20 56

theorem sha1_finImp : (finW Spec.Hmac.sha1S 56).Implies (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha1I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 84 20 56
  sig_implies [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 84 20 56

theorem sha1_initImp : (initW Spec.Hmac.sha1S 56).Implies (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha1I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 84 56
  sig_implies [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract,
    Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 84 56

/-- PBKDF2's iteration for SHA-1 with any backend. -/
theorem sha1_iterate (v : Sha1Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha1.md 112 cmpC) :
    Verified X86.target (sha1M v cmpN cmpC).iterate (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha1I X86.abi 48) :=
  (Iterate.verifiedW (sha1Ok v cmpN hc) (sha1_iterChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 20 + 64 ≤ 8 * 56 by decide)
    sha1_iterImp.sat_left).of_implies sha1_iterImp

/-- HMAC's `finalize` for SHA-1 with any backend. -/
theorem sha1_finalize (v : Sha1Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha1.md 112 cmpC) :
    Verified X86.target (sha1M v cmpN cmpC).hmacFin (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha1I X86.abi 48) :=
  (HmacFin.verifiedW (sha1Ok v cmpN hc) (sha1_finChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 20 ≤ 8 * 56 by decide)
    sha1_finImp.sat_left).of_implies sha1_finImp

/-- HMAC's `init` for SHA-1 with any backend. -/
theorem sha1_init (v : Sha1Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha1.md 112 cmpC) :
    Verified X86.target (sha1M v cmpN cmpC).hmacInit (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha1I X86.abi 48) :=
  (HmacInit.verifiedW (sha1Ok v cmpN hc) (sha1_initChecks v cmpN cmpC)
    (show 8 * 20 + 16 ≤ 8 * 56 by decide)
    sha1_initImp.sat_left).of_implies sha1_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances

end

end

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
(`Proof/Sha1/X86/Variants/Interface.lean`, `Proof/Pbkdf2/Whole/X86/Sha1.lean`), from
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
    contract = api.sig.contract (X86.abi) pre post api.writeArgs stack leak
  ofApi : contract = api.contract X86.abi stack
  spSafe : code.all (fun i => !isa.writesSp i) = true
  /-- Its postcondition reads the memory on return only within the buffers. -/
  post : X86.Scrub.PostOut contract (api.sig.retBits 32)
  /-- What the cleanup needs of its code over its stack
  (`X86.Scrub.scrubFSide`, for `verifiedScrubbedAll`): from the
  variant's facts of the code it wraps (`update_scrub`, …), not evaluated
  again. -/
  scrub : X86.Scrub.scrubFSide code [] stack = true

/-- `f`'s code as emitted, `f.code` and then its cleanup: the zeroing of its
stack and the clearing of the registers a callee may change but the result's
bits (`Impl.Scrub.X86.scrubAll`), meets `f`'s contract in constant time and
returns without secret residue (`X86.Scrub.verifiedScrubbedAll`). -/
theorem StreamFn.scrubbed (f : StreamFn) :
    VerifiedScrubbed X86.target (Impl.Scrub.X86.scrubAll (f.api.sig.retBits 32) f.stack f.code) f.contract
      (f.api.sig.retBits 32) :=
  X86.Scrub.verifiedScrubbedAll (api := f.api)
    { consts := []
      tables := []
      code := f.code
      contract := f.contract
      stack := f.stack
      verified := f.verified
      ofApi := f.ofApi
      ofSig := f.ofSig
      spSafe := f.spSafe }
    f.post f.scrub

/-- `f` as a registration of its `Api` (`Api.artifact`): its code as emitted,
with its cleanup, and the theorem about that code (`StreamFn.scrubbed`). -/
def StreamFn.reg (f : StreamFn) : Registration f.api X86.target where
  consts := []
  tables := []
  code := Impl.Scrub.X86.scrubAll (f.api.sig.retBits 32) f.stack f.code
  contract := f.contract
  stack := f.stack
  verified := .scrubbed f.scrubbed
  ofApi := f.ofApi
  ofSig := f.ofSig
  spSafe := X86.Scrub.scrubAll_spSafe f.spSafe

/-! ## What the cleanup of the streaming functions needs

Their postconditions read the memory on return only within the buffers
(`updateOut`, …). `update` and `finalize` are the code of the variant's
streaming functions in a frame of working space: what the cleanup needs
of them (`scrubFSide`: `update_scrub`, …) follows from that frame with an
empty body, evaluated once here, and the variant's `calleeOk` and stack of
the code (`Fill`, `Proof/Framework/X86/ScrubCall.lean`). -/

theorem updateOut (stack : Nat) :
    X86.Scrub.PostOut (Spec.Sha1.updateContract X86.abi stack) (Spec.Sha1.updateSig.retBits 32) :=
  X86.Scrub.postOut_of_local X86.Scrub.ScrubAbi.plain (Proof.Sha1.updatePost_out 32)

theorem finalizeOut (stack : Nat) :
    X86.Scrub.PostOut (Spec.Sha1.finalizeContract X86.abi stack) (Spec.Sha1.finalizeSig.retBits 32) :=
  X86.Scrub.postOut_of_local X86.Scrub.ScrubAbi.plain (Proof.Sha1.finalizePost_out 32)

theorem update_side :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 188 5 (.block [])) [] 188 = true := by
  lit_decide

/-- What the cleanup needs of `update`'s code with the streaming `update` `c`, in its
frame of 188 bytes, from `c`'s `calleeOk` and stack. -/
theorem update_scrub (c : Prog isa) (hc : calleeOk c = true) (hs : stackUse c ≤ 20) :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 188 5 c) [] (20 + 188) = true := by
  have h := X86.Scrub.calleeSide_of_le (n := 20) hs hc
  exact X86.Scrub.scrubFSide_of_fill (n := 20) (by fill_calls) update_side

theorem finalize_side :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 184 4 (.block [])) [] 184 = true := by
  lit_decide

/-- What the cleanup needs of `finalize`'s code with the streaming `finalize` `c`, in its
frame of 184 bytes, from `c`'s `calleeOk` and stack. -/
theorem finalize_scrub (c : Prog isa) (hc : calleeOk c = true) (hs : stackUse c ≤ 20) :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 184 4 c) [] (20 + 184) = true := by
  have h := X86.Scrub.calleeSide_of_le (n := 20) hs hc
  exact X86.Scrub.scrubFSide_of_fill (n := 20) (by fill_calls) finalize_side

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
  /-- The compression function and the streaming functions it makes, the
  code the functions built on it call, have no MMX instruction and make no
  indirect call (`calleeOk`): what the cleanup of every function that calls
  them needs of them, with their stack (`X86.Scrub.calleeSide`), so that each
  proves only its own code, whatever the implementation
  (`Proof/Framework/X86/ScrubCall.lean`). -/
  cmpScrub : calleeOk cmpC = true
  updScrub : calleeOk stream.upd = true
  finScrub : calleeOk stream.fin = true
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
