import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha224
import VerifiedGarbage.Proof.Sha1.X86.Stream.Variant
import VerifiedGarbage.Proof.Framework.TaintBatch

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

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 (Sha1Stream sha1OK)
open VG.Proof.Sha1.X86.Variants (mdHash)

/-- SHA-1 with the compression function `cmpN`/`cmpC` and the streaming
functions `v` calling it. -/
abbrev sha1M (v : Sha1Stream) (cmpN : String) (cmpC : Prog isa) : Hash :=
  VG.Proof.Sha1.X86.Variants.mdHash v.suffix cmpN cmpC v.upd v.fin

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
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega)
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

theorem sha1_iterImp : (iterW Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 84 20 56
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 84 20 56

theorem sha1_finImp : (finW Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.finalizeScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 84 20 56
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 84 20 56

theorem sha1_initImp : (initW Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.initScratchContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 84 56
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract,
    Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using VG.Proof.Pbkdf2.Md.X86.Instances.initSat 84 56

/-- PBKDF2's iteration for SHA-1 with any backend. -/
theorem sha1_iterate (v : Sha1Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha1.md 112 cmpC) :
    Verified X86.target (sha1M v cmpN cmpC).iterate (Spec.Hmac.sha1I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW (sha1Ok v cmpN hc) (sha1_iterChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 20 + 64 ≤ 8 * 56 by decide)
    sha1_iterImp.sat_left).of_implies sha1_iterImp

/-- HMAC's `finalize` for SHA-1 with any backend. -/
theorem sha1_finalize (v : Sha1Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha1.md 112 cmpC) :
    Verified X86.target (sha1M v cmpN cmpC).hmacFin (Spec.Hmac.sha1I.finalizeScratchContract X86.abi 48) :=
  (HmacFin.verifiedW (sha1Ok v cmpN hc) (sha1_finChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 20 ≤ 8 * 56 by decide)
    sha1_finImp.sat_left).of_implies sha1_finImp

/-- HMAC's `init` for SHA-1 with any backend. -/
theorem sha1_init (v : Sha1Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha1.md 112 cmpC) :
    Verified X86.target (sha1M v cmpN cmpC).hmacInit (Spec.Hmac.sha1I.initScratchContract X86.abi 48) :=
  (HmacInit.verifiedW (sha1Ok v cmpN hc) (sha1_initChecks v cmpN cmpC)
    (show 8 * 20 + 16 ≤ 8 * 56 by decide)
    sha1_initImp.sat_left).of_implies sha1_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
