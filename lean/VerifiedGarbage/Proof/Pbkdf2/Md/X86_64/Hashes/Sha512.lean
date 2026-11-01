module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha512.X86_64.OneShot
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
meta import VerifiedGarbage.Proof.Sha512.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
meta import VerifiedGarbage.Proof.Sha512.X86_64.OneShot
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Sha512.X86_64.Shared
public import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init

/-!
# The SHA-512 family on x86-64, as Merkle–Damgård hash functions

SHA-384, SHA-512, SHA-512/224 and SHA-512/256, each with an implementation `v`
of their compression function (`Proof/Sha512/X86_64/Variant.lean`), as
variants of `MdHash` (`sha384 v`, …), from which HMAC and PBKDF2 are emitted
(`Generic/MdHash/X86_64/`): their streaming code is the generic Merkle–Damgård
code (`Stream.params`), shared by the four, which differ in their initial hash
value `iv` and the size `D` of their digest, the first `D` bytes of the final
hash value. The facts about the code HMAC and PBKDF2 add, which do not depend
on `v`, are checked once for each member (`coreOK`).

`stream v` are the streaming `update` and `finalize` made with `v`, which
the four share: SHA-512's variant (`sha512 v`) carries them, and
`Generic/MdHash/X86_64/Stream.lean` emits them from their `Api`s, named
with its suffix. SHA-384's, SHA-512/256's and SHA-512/224's own `finalize`,
which writes their digest (`stream384 v`, …), is carried by their
variants.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha512

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha512.X86_64 (Compress)
open Spec.Sha512 (H0_384 H0_512 H0_512_224 H0_512_256)

/-- The member of the SHA-512 family of instance `I`, with a `D`-byte digest,
initial hash value `iv` and streaming `init` named `initN`, calling the
implementation `v` of the compression function, named with its suffix. -/
def hash (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) (v : Compress) :
    Hash where
  P := Impl.Sha512.X86_64.Stream.params
  D := D
  W := I.scratch
  compN := v.callee.name
  compC := v.callee.code
  initN := initN
  initC := Impl.Sha512.X86_64.Stream.init iv
  updN := Spec.Sha512.updateScratchApi.name ++ v.suffix
  finN := Spec.Sha512.finalizeScratchApi.name ++ v.suffix
  hmacInitN := s!"vg_hmac_{I.rust}_init_scratch" ++ v.suffix
  hmacFinN := s!"vg_hmac_{I.rust}_finalize_scratch" ++ v.suffix
  iterN := s!"vg_pbkdf2_hmac_{I.rust}_iterate" ++ v.suffix

/-- A member of the family without the functions it calls, the same for
every `v`. -/
def coreH (D : Nat) : Hash :=
  ⟨Impl.Sha512.X86_64.Stream.params, D, 234, "", .block [], "", .block [], "", "", "", "", ""⟩

theorem coreOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : CoreOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> refine {
      pbk := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      iter := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      hinit := {
        pro := ⟨?_, ?_⟩
        argI := List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩
        keys := ⟨?_, ?_⟩
        mid := ⟨?_, ?_⟩
        restore := ⟨?_, ?_⟩ }
      hfin := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      pbkMx := ?_
      pbkSp := ?_
      hinitMx := ?_
      hinitSp := ?_
      hinitNs := ?_
      hinitD := ?_
      hfinMx := ?_
      hfinSp := ?_
      hfinNs := ?_
      hfinD := ?_
      hinitXD := ?_
      hfinXD := ?_
      pbkXD := ?_
      iterMx := ?_
      iterSp := ?_
      iterNs := ?_
      iterD := ?_
      updMx := ?_
      updNs := ?_
      updD := ?_
      finMx := ?_
      finNs := ?_
      finD := ?_
      fitI := ?_
      fitF := ?_
  }
  taint_decide_all

theorem anyOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : Any.AnyOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  taint_decide_all

/-- The initial hash values of the family. -/
abbrev IVs (iv : Spec.Sha512.HashValue) : Prop := iv = H0_384 ∨ iv = H0_512 ∨ iv = H0_512_224 ∨ iv = H0_512_256

theorem callees {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} (hiv : IVs iv)
    (v : Compress) : Callees (hash I D initN iv v) where
  cMx := v.mxcsr
  cSp := allInstrs_of_all v.spSafe
  cNs := by
    show v.callee.code.allInstrs _ = true
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi]
  cD := v.ok.depth
  iMx := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iSp := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iNs := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iD := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  cXD := v.noStack
  iXD := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} {v : Compress}
    (C : CoreOK (core (hash I D initN iv v))) (K : Callees (hash I D initN iv v))
    (hR : I.S.Repr = Spec.Sha512.Repr iv) (hh : ∀ m, I.S.H.hash m = (Proof.Sha512.md.hash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hW : I.scratch = 234) : HashOK (hash I D initN iv v) where
  md := Proof.Sha512.md
  dims := Proof.Sha512.X86_64.Stream.dims
  shape := Proof.Sha512.X86_64.Stream.shape
  taints := Proof.Sha512.X86_64.Stream.taints
  comp := v.ok
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  lenOk _ h := h
  SH := I.S
  iv := iv
  repr _ _ _ := by rw [hR]; exact Proof.Sha512.repr_iff
  hash := hh
  hB := hB
  hS := hS
  hD := hDs
  hD0 := by show 0 < D; omega
  hDN := by show D ≤ 64; omega
  hD4 := by show D % 4 = 0; omega
  hN4 := by simp only [hash] <;> decide
  hDL := by show D + 16 + 4 ≤ 128; omega
  hL4 := by simp only [hash] <;> decide
  hNL := by simp only [hash] <;> decide
  hPad := by show 16 * (D / 16 + 1) + 16 ≤ 128; omega
  hso := by simp only [hash] <;> decide
  fits := by show 1328 + 48 + 64 + 128 ≤ 8 * I.scratch; omega
  hW := by show I.scratch ≤ 256; omega
  init := hR ▸ Proof.Sha512.X86_64.Stream.init_verified iv
  initDepth := by rw [K.iD]; decide
  initSp := nosp_of K.iNs
  updMx := Callees.updMx K C
  finMx := Callees.finMx K C
  updSp := Callees.updSp K C
  finSp := Callees.finSp K C
  updDepth := Callees.updD K C
  finDepth := Callees.finD K C

/-- The streaming `update` and `finalize` made with `v`, which the family
shares and which keep their working space in a frame of their own, and
`update_scratch` and `finalize_scratch`, which HMAC's, PBKDF2's and
Ed25519's code calls with theirs. -/
def stream (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .r8 (Impl.Sha512.X86_64.Stream.update v.callee)
    contract := Spec.Sha512.updateContract X86_64.abi (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.update v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe) },
  { api := Spec.Sha512.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx (Impl.Sha512.X86_64.Stream.finalize v.callee)
    contract := Spec.Sha512.finalizeContract X86_64.abi (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalize v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe) },
  { api := Spec.Sha512.updateScratchApi
    code := Impl.Sha512.X86_64.Stream.update v.callee
    contract := Spec.Sha512.updateScratchContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha512.X86_64.Shared.updateScratch v.ok v.mxcsr
    spSafe := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe },
  { api := Spec.Sha512.finalizeScratchApi
    code := Impl.Sha512.X86_64.Stream.finalize v.callee
    contract := Spec.Sha512.finalizeScratchContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha512.X86_64.Shared.finalizeScratch v.ok v.mxcsr
    spSafe := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe },
  { api := Spec.Sha512.digest512Api
    code := Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 8) H0_512 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 64 Spec.Sha512.sha512 (8 + Proof.Sha512.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frame
    verified := Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code512
      (fun m => List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code512 H0_512 v.spSafe }]

/-- SHA-384's `finalize` made with `v`, which writes its digest (`finalizeDigest`). -/
def stream384 (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.finalize384Api
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest Impl.Sha512.X86_64.Stream.params384 v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_384 48 Spec.Sha512.sha384 (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStack Proof.Sha512.X86_64.Shared.digest384
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.digest384.spSafe v.callee v.spSafe) },
  { api := Spec.Sha512.digest384Api
    code := Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 6) H0_384 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 48 Spec.Sha512.sha384 (8 + Proof.Sha512.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frame
    verified := Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code384
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code384 H0_384 v.spSafe }]

/-- SHA-512/256's `finalize` made with `v`, which writes its digest (`finalizeDigest`). -/
def stream512_256 (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.finalize512_256Api
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest Impl.Sha512.X86_64.Stream.params512_256 v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_512_256 32 Spec.Sha512.sha512_256 (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStack Proof.Sha512.X86_64.Shared.digest512_256
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.digest512_256.spSafe v.callee v.spSafe) },
  { api := Spec.Sha512.digest512_256Api
    code := Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 4) H0_512_256 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 32 Spec.Sha512.sha512_256 (8 + Proof.Sha512.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frame
    verified := Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code512_256
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code512_256 H0_512_256 v.spSafe }]

/-- SHA-512/224's `finalize` made with `v`, which writes its digest (`finalizeDigest`). -/
def stream512_224 (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.finalize512_224Api
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest Impl.Sha512.X86_64.Stream.params512_224 v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_512_224 28 Spec.Sha512.sha512_224 (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStack Proof.Sha512.X86_64.Shared.digest512_224
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.digest512_224.spSafe v.callee v.spSafe) },
  { api := Spec.Sha512.digest512_224Api
    code := Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 3 ++ Impl.Sha512.X86_64.Stream.outHi 3) H0_512_224 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 28 Spec.Sha512.sha512_224 (8 + Proof.Sha512.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frame
    verified := Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code512_224
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code512_224 H0_512_224 v.spSafe }]

/-! ## SHA-384 -/

theorem sha384_satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha384I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha384I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha384_satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha384I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha384I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using finSat 192 48 234

theorem sha384_satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha384I X86_64.abi 8).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha384I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 48 234

theorem sha384_satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha384I.S Spec.Hmac.sha384I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha384I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using initSat 192 426

theorem sha384_satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha384I X86_64.abi 24).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha384_satPF :
    ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha384I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha384_coreOK : CoreOK (coreH 48) := coreOK 48 (Or.inr (Or.inr (Or.inl rfl)))

theorem sha384_anyOK : Any.AnyOK (coreH 48) := anyOK 48 (Or.inr (Or.inr (Or.inl rfl)))

/-- SHA-384's functions, with the implementation `v` of the compression function. -/
abbrev sha384H (v : Compress) : Hash := hash Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384 v

theorem sha384K (v : Compress) : Callees (sha384H v) := callees (Or.inl rfl) v

/-- What the proofs know of SHA-384's functions. -/
def sha384OK (v : Compress) : HashOK (sha384H v) :=
  ok sha384_coreOK (sha384K v) rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function, for the
four members at once: one kernel evaluation shares the pieces that do not depend
on the digest's size. -/
theorem pss_all :
    Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 48 ∧
    Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 64 ∧
    Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 28 ∧
    Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  taint_decide_all

theorem pss_sha384 : Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 48 := pss_all.1
theorem pss_sha512 : Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 64 := pss_all.2.1
theorem pss_sha512_224 : Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 28 := pss_all.2.2.1
theorem pss_sha512_256 : Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 32 := pss_all.2.2.2


/-- SHA-384 with the implementation `v` of the compression function, which it
carries for the functions built on SHA-384 alone (`MdHash.sha384`). -/
def sha384 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  { MdHash.of (sha384OK v) sha384_coreOK (sha384K v) ⟨Spec.Mgf1.sha384, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha384 rfl rfl
      sha384_satI sha384_satF sha384_satT sha384_satP (by decide)
      sha384_anyOK sha384_satA (by decide) Proof.Hmac.sha384_local
      (by
        unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
        exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
      (by
        unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
        exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
      (by decide)
      (by
        unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
        exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel)
          (by rw [Curry.apply_const]; trivial))
      (by decide) sha384_satPF
      v.suffix v.features stream with
    sha384 := some v }

/-! ## SHA-512 -/

theorem sha512_satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha512I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using finSat 192 64 234

theorem sha512_satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512I X86_64.abi 8).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha512I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 64 234

theorem sha512_satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha512I.S Spec.Hmac.sha512I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using initSat 192 426

theorem sha512_satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha512I X86_64.abi 24).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_satPF :
    ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha512I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_coreOK : CoreOK (coreH 64) := coreOK 64 (Or.inr (Or.inr (Or.inr rfl)))

theorem sha512_anyOK : Any.AnyOK (coreH 64) := anyOK 64 (Or.inr (Or.inr (Or.inr rfl)))

/-- SHA-512's functions, with the implementation `v` of the compression function. -/
abbrev sha512H (v : Compress) : Hash := hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512 v

theorem sha512K (v : Compress) : Callees (sha512H v) := callees (Or.inr (Or.inl rfl)) v

/-- What the proofs know of SHA-512's functions. -/
def sha512OK (v : Compress) : HashOK (sha512H v) :=
  ok sha512_coreOK (sha512K v) rfl
    (fun _ => (List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))).symm) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr rfl))) rfl

/-- SHA-512 with the implementation `v` of the compression function, which it
carries for the functions built on SHA-512 alone (`MdHash.sha512`). -/
def sha512 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  { MdHash.of (sha512OK v) sha512_coreOK (sha512K v) ⟨Spec.Mgf1.sha512, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512 rfl rfl
      sha512_satI sha512_satF sha512_satT sha512_satP (by decide)
    sha512_anyOK sha512_satA (by decide) Proof.Hmac.sha512_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_satPF
    v.suffix v.features stream with
    sha512 := some v }

/-! ## SHA-512/224 -/

theorem sha512_224_satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512_224I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_224_satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512_224I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512_224I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using finSat 192 28 234

theorem sha512_224_satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512_224I X86_64.abi 8).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha512_224I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 28 234

theorem sha512_224_satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha512_224I.S Spec.Hmac.sha512_224I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using initSat 192 426

theorem sha512_224_satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha512_224I X86_64.abi 24).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_224_satPF :
    ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha512_224I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_224_coreOK : CoreOK (coreH 28) := coreOK 28 (Or.inl rfl)

theorem sha512_224_anyOK : Any.AnyOK (coreH 28) := anyOK 28 (Or.inl rfl)

/-- SHA-512/224 with the implementation `v` of the compression function. -/
def sha512_224 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224 v)) := sha512_224_coreOK
  have K : Callees (hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224 v) := callees (Or.inr (Or.inr (Or.inl rfl))) v
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl) rfl) C K ⟨Spec.Mgf1.sha512_224, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512_224 rfl rfl
    sha512_224_satI sha512_224_satF sha512_224_satT sha512_224_satP (by decide)
    sha512_224_anyOK sha512_224_satA (by decide) Proof.Hmac.sha512_224_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_224_satPF
    v.suffix v.features stream

/-! ## SHA-512/256 -/

theorem sha512_256_satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512_256I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_256_satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512_256I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512_256I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using finSat 192 32 234

theorem sha512_256_satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512_256I X86_64.abi 8).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha512_256I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 32 234

theorem sha512_256_satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha512_256I.S Spec.Hmac.sha512_256I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using initSat 192 426

theorem sha512_256_satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha512_256I X86_64.abi 24).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_256_satPF :
    ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha512_256I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_256_coreOK : CoreOK (coreH 32) := coreOK 32 (Or.inr (Or.inl rfl))

theorem sha512_256_anyOK : Any.AnyOK (coreH 32) := anyOK 32 (Or.inr (Or.inl rfl))

/-- SHA-512/256 with the implementation `v` of the compression function. -/
def sha512_256 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256 v)) := sha512_256_coreOK
  have K : Callees (hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256 v) := callees (Or.inr (Or.inr (Or.inr rfl))) v
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl)) rfl) C K ⟨Spec.Mgf1.sha512_256, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512_256 rfl rfl
    sha512_256_satI sha512_256_satF sha512_256_satT sha512_256_satP (by decide)
    sha512_256_anyOK sha512_256_satA (by decide) Proof.Hmac.sha512_256_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_256_satPF
    v.suffix v.features stream

end VG.Proof.Pbkdf2.Md.X86_64.Sha512
