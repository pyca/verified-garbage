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
hash value. The facts about the code HMAC and PBKDF2 add, which depend on `v`
only through the scratch space it uses, are checked once for each member and
amount (`coreOKS`).

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
implementation `v` of the compression function, named with its suffix
(HMAC's `init`'s alone, for an implementation that is another one with a
function compressing two blocks at once: the rest are that one's). Its
instances call `init`'s code as the internal `vg_<alg>_init_core`: the
function exported as `vg_<alg>_init` also clears what it leaves
(`Proof.Sha512.X86_64.init512Reg`), which its callers, which clear their own,
do not need. -/
def hash (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) (v : Compress) :
    Hash where
  P := Proof.Sha512.X86_64.Stream.paramsS v.callee.so
  D := D
  W := Hash.wOf (Proof.Sha512.X86_64.Stream.paramsS v.callee.so)
  compN := v.callee.name
  compC := v.callee.code
  initN := initN
  initC := Impl.Sha512.X86_64.Stream.init iv
  updN := "vg_sha512_update_scratch" ++ v.baseSuffix
  finN := "vg_sha512_finalize_scratch" ++ v.baseSuffix
  hmacInitN := s!"vg_hmac_{I.rust}_init_scratch" ++ v.suffix
  hmacFinN := s!"vg_hmac_{I.rust}_finalize_scratch" ++ v.baseSuffix
  iterN := s!"vg_pbkdf2_hmac_{I.rust}_iterate" ++ v.baseSuffix
  compBoth := match v.pair with
    | none => Impl.Pbkdf2.Md.X86_64.compTwice Impl.Sha512.X86_64.Stream.params.N v.callee.name v.callee.code
    | some p => Impl.Pbkdf2.Md.X86_64.compPair Impl.Sha512.X86_64.Stream.params.N p.name p.code

/-- A member of the family without the functions it calls, for an
implementation that uses `so` bytes of scratch space. -/
def coreHS (so D : Nat) : Hash :=
  ⟨Proof.Sha512.X86_64.Stream.paramsS so, D, Hash.wOf (Proof.Sha512.X86_64.Stream.paramsS so), "", .block [], "",
    .block [], "", "", "", "", "", Proof.Pbkdf2.Md.X86_64.coreBoth⟩

/-- The scratch space the implementations use. -/
abbrev SoOk (so : Nat) : Prop := so = 0 ∨ so = 192 ∨ so = 1328

/-- The digest lengths of the family. -/
abbrev DOk (D : Nat) : Prop := D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64

theorem coreOKS (so : Nat) (hso : SoOk so) (D : Nat) (hD : DOk D) : CoreOK (coreHS so D) := by
  rcases hso with rfl | rfl | rfl <;> rcases hD with rfl | rfl | rfl | rfl <;> refine {
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

theorem anyOKS (so : Nat) (hso : SoOk so) (D : Nat) (hD : DOk D) : Any.AnyOK (coreHS so D) := by
  rcases hso with rfl | rfl | rfl <;> rcases hD with rfl | rfl | rfl | rfl <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  taint_decide_all

/-- The initial hash values of the family. -/
abbrev IVs (iv : Spec.Sha512.HashValue) : Prop := iv = H0_384 ∨ iv = H0_512 ∨ iv = H0_512_224 ∨ iv = H0_512_256

/-- The arguments of a function that compresses two blocks at once are set
up from registers that hold nothing secret. -/
theorem pairArgs_taint : ∃ hc, (Taint.check taint (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r15, .rsp])
    (.block (Impl.Pbkdf2.Md.X86_64.pairArgs Impl.Sha512.X86_64.Stream.params.N)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem callees {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} (hiv : IVs iv)
    (v : Compress) : Callees (hash I D initN iv v) := by
  have cMx := v.mxcsr
  have cSp := allInstrs_of_all v.spSafe
  have cNs : v.callee.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi]
  have b : BothFacts (hash I D initN iv v) := by
    cases hv : v.pair with
    | none => exact .twice (by simp only [hash, hv]) cMx cSp cNs v.ok.depth v.noStack
    | some p =>
      exact .pair (name := p.name) (code := p.code) (by simp only [hash, hv]) p.mxcsr p.spSafe p.noSp
        p.ok.depth p.noStack
  refine ⟨cMx, cSp, cNs, v.ok.depth, ?_, ?_, ?_, ?_, v.noStack, ?_, b⟩ <;>
    (simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- The words of working space of a member's functions with `v`. -/
theorem hashW {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} (v : Compress) :
    (hash I D initN iv v).W = 30 ∨ (hash I D initN iv v).W = 54 ∨ (hash I D initN iv v).W = 196 := by
  rcases v.hso with h | h | h <;> simp only [hash, Hash.wOf, Proof.Sha512.X86_64.Stream.paramsS, h] <;> decide

/-- The words of working space of a member's HMAC `init` for a key of at
most a block with `v`. -/
theorem hashIW {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} (v : Compress) :
    initWords (hash I D initN iv v) = 12 ∨ initWords (hash I D initN iv v) = 36 ∨
      initWords (hash I D initN iv v) = 178 := by
  rcases v.hso with h | h | h <;> simp only [initWords_eq, hash, Proof.Sha512.X86_64.Stream.paramsS, h] <;> decide

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} {v : Compress}
    (C : CoreOK (core (hash I D initN iv v))) (K : Callees (hash I D initN iv v))
    (hR : I.S.Repr = Spec.Sha512.Repr iv) (hh : ∀ m, I.S.H.hash m = (Proof.Sha512.md.hash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : DOk D) : HashOK (hash I D initN iv v) where
  md := Proof.Sha512.md
  dims := Proof.Sha512.X86_64.Stream.dimsS _ (by rcases v.hso with h | h | h <;> omega_using [h])
  shape := Proof.Sha512.X86_64.Stream.shapeS _
  taints := Proof.Sha512.X86_64.Stream.taintsS3 _ v.hso
  comp := v.okS
  both := by
    cases hv : v.pair with
    | none => exact .inl (by simp only [hash, hv])
    | some p => exact .inr ⟨p.name, p.code, by simp only [hash, hv], v.pairOk p hv, pairArgs_taint⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
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
  hso := by
    show v.callee.so % 8 = 0 ∧ v.callee.so + 48 ≤ 8 * 256
    rcases v.hso with h | h | h <;> rw [h] <;> decide
  fits := by
    show v.callee.so + 48 + 64 + 128 ≤ 8 * ((v.callee.so + 48 + 64 + 128 + 7) / 8)
    omega_using []
  hW := by rcases hashW v with h | h | h <;> rw [h] <;> decide
  init := hR ▸ Proof.Sha512.X86_64.Stream.init_verified iv
  initDepth := by rw [K.iD]; decide
  initSp := nosp_of K.iNs
  updMx := Callees.updMx K C
  finMx := Callees.finMx K C
  updSp := Callees.updSp K C
  finSp := Callees.finSp K C
  updDepth := Callees.updD K C
  finDepth := Callees.finD K C

/-- The streaming `update` made with `v`, which keeps its working space in a frame of its own. -/
def updFn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .r8 (Impl.Sha512.X86_64.Stream.update v.callee)
    contract := Spec.Sha512.updateContract X86_64.abi (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.update v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe) }

/-- The streaming `finalize` made with `v`, likewise. -/
def finFn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx (Impl.Sha512.X86_64.Stream.finalize v.callee)
    contract := Spec.Sha512.finalizeContract X86_64.abi (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalize v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe) }

/-- SHA-512's one-shot `digest` made with `v`. -/
def digFn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.digest512Api
    code := Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 8) H0_512 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 64 Spec.Sha512.sha512 (8 + Proof.Sha512.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frame
    verified := Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code512
      (fun m => List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code512 H0_512 v.spSafe }

/-- The streaming `update` and `finalize` made with `v`, and SHA-512's one-shot `digest`. -/
def stream (v : Compress) : List StreamFn := [updFn v, finFn v, digFn v]

/-- SHA-384's `finalize` made with `v`, which writes its digest (`finalizeDigest`). -/
def fin384Fn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.finalize384Api
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest Impl.Sha512.X86_64.Stream.params384 v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_384 48 Spec.Sha512.sha384 (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStack Proof.Sha512.X86_64.Shared.digest384
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.digest384.spSafe v.callee v.spSafe) }

/-- SHA-384's one-shot `digest` made with `v`. -/
def dig384Fn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.digest384Api
    code := Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 6) H0_384 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 48 Spec.Sha512.sha384 (8 + Proof.Sha512.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frame
    verified := Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code384
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code384 H0_384 v.spSafe }

/-- SHA-384's `finalize` and one-shot `digest` made with `v`. -/
def stream384 (v : Compress) : List StreamFn := [fin384Fn v, dig384Fn v]

/-- SHA-512/256's `finalize` made with `v`, which writes its digest (`finalizeDigest`). -/
def fin512_256Fn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.finalize512_256Api
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest Impl.Sha512.X86_64.Stream.params512_256 v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_512_256 32 Spec.Sha512.sha512_256 (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStack Proof.Sha512.X86_64.Shared.digest512_256
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.digest512_256.spSafe v.callee v.spSafe) }

/-- SHA-512/256's one-shot `digest` made with `v`. -/
def dig512_256Fn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.digest512_256Api
    code := Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 4) H0_512_256 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 32 Spec.Sha512.sha512_256 (8 + Proof.Sha512.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frame
    verified := Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code512_256
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code512_256 H0_512_256 v.spSafe }

/-- SHA-512/256's `finalize` and one-shot `digest` made with `v`. -/
def stream512_256 (v : Compress) : List StreamFn := [fin512_256Fn v, dig512_256Fn v]

/-- SHA-512/224's `finalize` made with `v`, which writes its digest (`finalizeDigest`). -/
def fin512_224Fn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.finalize512_224Api
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest Impl.Sha512.X86_64.Stream.params512_224 v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_512_224 28 Spec.Sha512.sha512_224 (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStack Proof.Sha512.X86_64.Shared.digest512_224
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.digest512_224.spSafe v.callee v.spSafe) }

/-- SHA-512/224's one-shot `digest` made with `v`. -/
def dig512_224Fn (v : Compress) : StreamFn :=
  { api := Spec.Sha512.digest512_224Api
    code := Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 3 ++ Impl.Sha512.X86_64.Stream.outHi 3) H0_512_224 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 28 Spec.Sha512.sha512_224 (8 + Proof.Sha512.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frame
    verified := Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code512_224
      (fun _ => rfl) v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code512_224 H0_512_224 v.spSafe }

/-- SHA-512/224's `finalize` and one-shot `digest` made with `v`. -/
def stream512_224 (v : Compress) : List StreamFn := [fin512_224Fn v, dig512_224Fn v]

/-! ### With the working space the compression function uses

The same functions made for an implementation `v` of the compression
function verified with `so` bytes of scratch space (`hv`), which give it
only that much (`Stream.paramsS`): their frames shrink with it. -/

section S

variable (v : Compress) {so : Nat} (h : so = 0 ∨ so = 192)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha512.compressWideX86_64S so))

/-- The streaming `update` made with `v`, in a frame of `so + 56` bytes. -/
def updFnS : StreamFn :=
  { api := Spec.Sha512.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch (so + 56) .r8
      (Impl.MdStream.X86_64.update (Proof.Sha512.X86_64.Stream.paramsS so) v.callee.name v.callee.code)
    contract := Spec.Sha512.updateContract X86_64.abi (8 + (so + 56))
    stack := 8 + (so + 56)
    verified := Proof.Sha512.X86_64.Shared.updateS h v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by rcases h with rfl | rfl <;> decide)
      (Proof.Sha512.X86_64.Shared.updateS_spSafe h v.spSafe) }

/-- The streaming `finalize` made with `v`, likewise. -/
def finFnS : StreamFn :=
  { api := Spec.Sha512.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx
      (Impl.MdStream.X86_64.finalize (Proof.Sha512.X86_64.Stream.paramsS so) v.callee.name v.callee.code)
    contract := Spec.Sha512.finalizeContract X86_64.abi (8 + (so + 56))
    stack := 8 + (so + 56)
    verified := Proof.Sha512.X86_64.Shared.finalizeS h v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by rcases h with rfl | rfl <;> decide)
      (Proof.Sha512.X86_64.Shared.finalizeS_spSafe h v.spSafe) }

/-- `digFn`, in a frame holding a buffer of `Proof.Sha512.X86_64.OneShot.wordsS so` words. -/
def digFnS : StreamFn :=
  { api := Spec.Sha512.digest512Api
    code := Proof.Sha512.X86_64.OneShot.digestS so (Impl.MdStream.X86_64.out64 8) H0_512 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 64 Spec.Sha512.sha512 (8 + Proof.Sha512.X86_64.OneShot.frameS so)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frameS so
    verified := Proof.Sha512.X86_64.OneShot.verifiedS (Proof.Sha512.X86_64.OneShot.code512S h)
      (fun m => List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))) v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafeS (Proof.Sha512.X86_64.OneShot.code512S h) H0_512 v.spSafe }

/-- `fin384Fn`, in a frame of `so + 56` bytes. -/
def fin384FnS : StreamFn :=
  { api := Spec.Sha512.finalize384Api
    code := Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest { Proof.Sha512.X86_64.Stream.paramsS so with out := Impl.MdStream.X86_64.out64 6 } v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_384 48 Spec.Sha512.sha384 (8 + (so + 56))
    stack := 8 + (so + 56)
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStackS (Proof.Sha512.X86_64.Shared.digest384S h)
      (fun _ => rfl) v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by rcases h with rfl | rfl <;> decide)
      ((Proof.Sha512.X86_64.Shared.digest384S h).spSafe v.callee v.spSafe) }

/-- `dig384Fn`, in a frame holding a buffer of `Proof.Sha512.X86_64.OneShot.wordsS so` words. -/
def dig384FnS : StreamFn :=
  { api := Spec.Sha512.digest384Api
    code := Proof.Sha512.X86_64.OneShot.digestS so (Impl.MdStream.X86_64.out64 6) H0_384 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 48 Spec.Sha512.sha384 (8 + Proof.Sha512.X86_64.OneShot.frameS so)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frameS so
    verified := Proof.Sha512.X86_64.OneShot.verifiedS (Proof.Sha512.X86_64.OneShot.code384S h)
      (fun _ => rfl) v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafeS (Proof.Sha512.X86_64.OneShot.code384S h) H0_384 v.spSafe }

/-- `fin512_256Fn`, in a frame of `so + 56` bytes. -/
def fin512_256FnS : StreamFn :=
  { api := Spec.Sha512.finalize512_256Api
    code := Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest { Proof.Sha512.X86_64.Stream.paramsS so with out := Impl.MdStream.X86_64.out64 4 } v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_512_256 32 Spec.Sha512.sha512_256 (8 + (so + 56))
    stack := 8 + (so + 56)
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStackS (Proof.Sha512.X86_64.Shared.digest512_256S h)
      (fun _ => rfl) v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by rcases h with rfl | rfl <;> decide)
      ((Proof.Sha512.X86_64.Shared.digest512_256S h).spSafe v.callee v.spSafe) }

/-- `dig512_256Fn`, in a frame holding a buffer of `Proof.Sha512.X86_64.OneShot.wordsS so` words. -/
def dig512_256FnS : StreamFn :=
  { api := Spec.Sha512.digest512_256Api
    code := Proof.Sha512.X86_64.OneShot.digestS so (Impl.MdStream.X86_64.out64 4) H0_512_256 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 32 Spec.Sha512.sha512_256 (8 + Proof.Sha512.X86_64.OneShot.frameS so)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frameS so
    verified := Proof.Sha512.X86_64.OneShot.verifiedS (Proof.Sha512.X86_64.OneShot.code512_256S h)
      (fun _ => rfl) v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafeS (Proof.Sha512.X86_64.OneShot.code512_256S h) H0_512_256 v.spSafe }

/-- `fin512_224Fn`, in a frame of `so + 56` bytes. -/
def fin512_224FnS : StreamFn :=
  { api := Spec.Sha512.finalize512_224Api
    code := Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx
      (Impl.Sha512.X86_64.Stream.finalizeDigest { Proof.Sha512.X86_64.Stream.paramsS so with out := Impl.MdStream.X86_64.out64 3 ++ Impl.Sha512.X86_64.Stream.outHi 3 } v.callee)
    contract := Spec.Sha512.finalizeDigestContract X86_64.abi H0_512_224 28 Spec.Sha512.sha512_224 (8 + (so + 56))
    stack := 8 + (so + 56)
    verified := Proof.Sha512.X86_64.Shared.finalizeDigestStackS (Proof.Sha512.X86_64.Shared.digest512_224S h)
      (fun _ => rfl) v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by rcases h with rfl | rfl <;> decide)
      ((Proof.Sha512.X86_64.Shared.digest512_224S h).spSafe v.callee v.spSafe) }

/-- `dig512_224Fn`, in a frame holding a buffer of `Proof.Sha512.X86_64.OneShot.wordsS so` words. -/
def dig512_224FnS : StreamFn :=
  { api := Spec.Sha512.digest512_224Api
    code := Proof.Sha512.X86_64.OneShot.digestS so (Impl.MdStream.X86_64.out64 3 ++ Impl.Sha512.X86_64.Stream.outHi 3) H0_512_224 v.callee
    contract := Spec.Sha512.digestContract X86_64.abi 28 Spec.Sha512.sha512_224 (8 + Proof.Sha512.X86_64.OneShot.frameS so)
    stack := 8 + Proof.Sha512.X86_64.OneShot.frameS so
    verified := Proof.Sha512.X86_64.OneShot.verifiedS (Proof.Sha512.X86_64.OneShot.code512_224S h)
      (fun _ => rfl) v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha512.X86_64.OneShot.spSafeS (Proof.Sha512.X86_64.OneShot.code512_224S h) H0_512_224 v.spSafe }

end S

/-! ## SHA-384 -/

section
variable {w : Nat}

theorem sha384_satI (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha384I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 192 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha384I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha384I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha384_satW (hw : w = 12 ∨ w = 36 ∨ w = 178) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha384I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 192 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha384I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha384I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha384_satF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Hmac.finalizeScratchContract Spec.Hmac.sha384I.S w X86_64.abi 16).pre s := by
  refine ⟨finSat 192 48 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha384I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha384I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha384_satT (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Pbkdf2.iterateContract Spec.Hmac.sha384I.S w X86_64.abi 8).pre s := by
  refine ⟨Pbkdf2.X86_64.iterSat 192 48 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha384I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha384S,
    Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha384I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha384S,
    Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha384_satA (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Any.anyScratchContract Spec.Hmac.sha384I.S (w + 192)).pre s := by
  refine ⟨initSat 192 (w + 192), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Any.anyScratchContract, Spec.Hmac.sha384I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Any.anyScratchContract, Spec.Hmac.sha384I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha384_satP (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract Spec.Hmac.sha384I.S (w + 192) X86_64.abi 24).pre s := by
  refine ⟨pbkSat (w + 192), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha384I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi,
    X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha384I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi,
    X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha384_satPF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract X86_64.abi (24 + (24 + 8 * (w + 192)))).pre s := by
  refine ⟨pbkFrameSat, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
    | (sig_pre [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha384_satIF (hw : w = 12 ∨ w = 36 ∨ w = 178) :
    ∃ s, (Spec.Hmac.sha384I.initContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl)

theorem sha384_satAF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha384I.initAnyKeyContract X86_64.abi (24 + (8 + 8 * (w + 192)))).pre s := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

theorem sha384_satFF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha384I.finalizeContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

end

/-- SHA-384's functions, with the implementation `v` of the compression function. -/
abbrev sha384H (v : Compress) : Hash := hash Spec.Hmac.sha384I 48 "vg_sha384_init_core" H0_384 v

theorem sha384K (v : Compress) : Callees (sha384H v) := callees (Or.inl rfl) v

theorem sha384W (v : Compress) : (sha384H v).W = 30 ∨ (sha384H v).W = 54 ∨ (sha384H v).W = 196 := hashW v

theorem sha384C (v : Compress) : CoreOK (core (sha384H v)) := coreOKS v.callee.so v.hso 48 (Or.inr (Or.inr (Or.inl rfl)))

theorem sha384A (v : Compress) : Any.AnyOK (core (sha384H v)) := anyOKS v.callee.so v.hso 48 (Or.inr (Or.inr (Or.inl rfl)))

/-- What the proofs know of SHA-384's functions. -/
def sha384OK (v : Compress) : HashOK (sha384H v) :=
  ok (sha384C v) (sha384K v) rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl)))

/-- SHA-384 with the implementation `v` of the compression function. -/
def sha384 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  MdHash.of (I := Spec.Hmac.sha384I) (sha384OK v) (sha384C v) (sha384K v)
    ⟨Spec.Mgf1.sha384, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl
    1328 (sha384OK v.uniform) rfl
    (sha384_satI (hashW v)) (sha384_satF (hashW v)) (sha384_satT (hashW v)) (sha384_satP (hashW v))
    (by rcases sha384W v with h | h | h <;> omega_using [h])
    (sha384A v) (sha384_satA (hashW v))
    (by
      show (sha384H v).W + 192 < 511
      rcases sha384W v with h | h | h <;> omega_using [h])
    Proof.Hmac.sha384_local (sha384_satAF (hashW v)) (sha384_satW (hashIW v)) (sha384_satIF (hashIW v))
    (by decide) (sha384_satFF (hashW v))
    (by
      show (sha384H v).W + 192 < 509
      rcases sha384W v with h | h | h <;> omega_using [h])
    (sha384_satPF (hashW v))
    v.suffix v.features stream

/-! ## SHA-512 -/

section
variable {w : Nat}

theorem sha512_satI (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha512I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 192 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_satW (hw : w = 12 ∨ w = 36 ∨ w = 178) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha512I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 192 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_satF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Hmac.finalizeScratchContract Spec.Hmac.sha512I.S w X86_64.abi 16).pre s := by
  refine ⟨finSat 192 64 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_satT (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Pbkdf2.iterateContract Spec.Hmac.sha512I.S w X86_64.abi 8).pre s := by
  refine ⟨Pbkdf2.X86_64.iterSat 192 64 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512S,
    Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512S,
    Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_satA (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Any.anyScratchContract Spec.Hmac.sha512I.S (w + 192)).pre s := by
  refine ⟨initSat 192 (w + 192), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Any.anyScratchContract, Spec.Hmac.sha512I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Any.anyScratchContract, Spec.Hmac.sha512I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_satP (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract Spec.Hmac.sha512I.S (w + 192) X86_64.abi 24).pre s := by
  refine ⟨pbkSat (w + 192), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi,
    X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi,
    X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_satPF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract X86_64.abi (24 + (24 + 8 * (w + 192)))).pre s := by
  refine ⟨pbkFrameSat, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
    | (sig_pre [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_satIF (hw : w = 12 ∨ w = 36 ∨ w = 178) :
    ∃ s, (Spec.Hmac.sha512I.initContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl)

theorem sha512_satAF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512I.initAnyKeyContract X86_64.abi (24 + (8 + 8 * (w + 192)))).pre s := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

theorem sha512_satFF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512I.finalizeContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

end

/-- SHA-512's functions, with the implementation `v` of the compression function. -/
abbrev sha512H (v : Compress) : Hash := hash Spec.Hmac.sha512I 64 "vg_sha512_init_core" H0_512 v

theorem sha512K (v : Compress) : Callees (sha512H v) := callees (Or.inr (Or.inl rfl)) v

theorem sha512W (v : Compress) : (sha512H v).W = 30 ∨ (sha512H v).W = 54 ∨ (sha512H v).W = 196 := hashW v

theorem sha512C (v : Compress) : CoreOK (core (sha512H v)) := coreOKS v.callee.so v.hso 64 (Or.inr (Or.inr (Or.inr rfl)))

theorem sha512A (v : Compress) : Any.AnyOK (core (sha512H v)) := anyOKS v.callee.so v.hso 64 (Or.inr (Or.inr (Or.inr rfl)))

/-- What the proofs know of SHA-512's functions. -/
def sha512OK (v : Compress) : HashOK (sha512H v) :=
  ok (sha512C v) (sha512K v) rfl (fun _ => (List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))).symm) rfl rfl rfl (Or.inr (Or.inr (Or.inr rfl)))

/-- SHA-512 with the implementation `v` of the compression function. -/
def sha512 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  MdHash.of (I := Spec.Hmac.sha512I) (sha512OK v) (sha512C v) (sha512K v)
    ⟨Spec.Mgf1.sha512, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl
    1328 (sha512OK v.uniform) rfl
    (sha512_satI (hashW v)) (sha512_satF (hashW v)) (sha512_satT (hashW v)) (sha512_satP (hashW v))
    (by rcases sha512W v with h | h | h <;> omega_using [h])
    (sha512A v) (sha512_satA (hashW v))
    (by
      show (sha512H v).W + 192 < 511
      rcases sha512W v with h | h | h <;> omega_using [h])
    Proof.Hmac.sha512_local (sha512_satAF (hashW v)) (sha512_satW (hashIW v)) (sha512_satIF (hashIW v))
    (by decide) (sha512_satFF (hashW v))
    (by
      show (sha512H v).W + 192 < 509
      rcases sha512W v with h | h | h <;> omega_using [h])
    (sha512_satPF (hashW v))
    v.suffix v.features stream

/-! ## SHA-512/224 -/

section
variable {w : Nat}

theorem sha512_224_satI (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha512_224I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 192 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_224_satW (hw : w = 12 ∨ w = 36 ∨ w = 178) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha512_224I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 192 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_224_satF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Hmac.finalizeScratchContract Spec.Hmac.sha512_224I.S w X86_64.abi 16).pre s := by
  refine ⟨finSat 192 28 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_224I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_224I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_224_satT (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Pbkdf2.iterateContract Spec.Hmac.sha512_224I.S w X86_64.abi 8).pre s := by
  refine ⟨Pbkdf2.X86_64.iterSat 192 28 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_224I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S,
    Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_224I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S,
    Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_224_satA (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Any.anyScratchContract Spec.Hmac.sha512_224I.S (w + 192)).pre s := by
  refine ⟨initSat 192 (w + 192), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Any.anyScratchContract, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Any.anyScratchContract, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_224_satP (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract Spec.Hmac.sha512_224I.S (w + 192) X86_64.abi 24).pre s := by
  refine ⟨pbkSat (w + 192), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_224I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi,
    X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_224I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi,
    X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_224_satPF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract X86_64.abi (24 + (24 + 8 * (w + 192)))).pre s := by
  refine ⟨pbkFrameSat, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
    | (sig_pre [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_224_satIF (hw : w = 12 ∨ w = 36 ∨ w = 178) :
    ∃ s, (Spec.Hmac.sha512_224I.initContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl)

theorem sha512_224_satAF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512_224I.initAnyKeyContract X86_64.abi (24 + (8 + 8 * (w + 192)))).pre s := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

theorem sha512_224_satFF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512_224I.finalizeContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

end

/-- SHA-512/224's functions, with the implementation `v` of the compression function. -/
abbrev sha512_224H (v : Compress) : Hash := hash Spec.Hmac.sha512_224I 28 "vg_sha512_224_init_core" H0_512_224 v

theorem sha512_224K (v : Compress) : Callees (sha512_224H v) := callees (Or.inr (Or.inr (Or.inl rfl))) v

theorem sha512_224W (v : Compress) : (sha512_224H v).W = 30 ∨ (sha512_224H v).W = 54 ∨ (sha512_224H v).W = 196 := hashW v

theorem sha512_224C (v : Compress) : CoreOK (core (sha512_224H v)) := coreOKS v.callee.so v.hso 28 (Or.inl rfl)

theorem sha512_224A (v : Compress) : Any.AnyOK (core (sha512_224H v)) := anyOKS v.callee.so v.hso 28 (Or.inl rfl)

/-- What the proofs know of SHA-512/224's functions. -/
def sha512_224OK (v : Compress) : HashOK (sha512_224H v) :=
  ok (sha512_224C v) (sha512_224K v) rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl)

/-- SHA-512/224 with the implementation `v` of the compression function. -/
def sha512_224 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  MdHash.of (I := Spec.Hmac.sha512_224I) (sha512_224OK v) (sha512_224C v) (sha512_224K v)
    ⟨Spec.Mgf1.sha512_224, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl
    1328 (sha512_224OK v.uniform) rfl
    (sha512_224_satI (hashW v)) (sha512_224_satF (hashW v)) (sha512_224_satT (hashW v)) (sha512_224_satP (hashW v))
    (by rcases sha512_224W v with h | h | h <;> omega_using [h])
    (sha512_224A v) (sha512_224_satA (hashW v))
    (by
      show (sha512_224H v).W + 192 < 511
      rcases sha512_224W v with h | h | h <;> omega_using [h])
    Proof.Hmac.sha512_224_local (sha512_224_satAF (hashW v)) (sha512_224_satW (hashIW v)) (sha512_224_satIF (hashIW v))
    (by decide) (sha512_224_satFF (hashW v))
    (by
      show (sha512_224H v).W + 192 < 509
      rcases sha512_224W v with h | h | h <;> omega_using [h])
    (sha512_224_satPF (hashW v))
    v.suffix v.features stream

/-! ## SHA-512/256 -/

section
variable {w : Nat}

theorem sha512_256_satI (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha512_256I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 192 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_256_satW (hw : w = 12 ∨ w = 36 ∨ w = 178) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha512_256I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 192 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_256_satF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Hmac.finalizeScratchContract Spec.Hmac.sha512_256I.S w X86_64.abi 16).pre s := by
  refine ⟨finSat 192 32 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_256I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_256I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_256_satT (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Pbkdf2.iterateContract Spec.Hmac.sha512_256I.S w X86_64.abi 8).pre s := by
  refine ⟨Pbkdf2.X86_64.iterSat 192 32 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_256I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S,
    Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_256I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S,
    Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_256_satA (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Any.anyScratchContract Spec.Hmac.sha512_256I.S (w + 192)).pre s := by
  refine ⟨initSat 192 (w + 192), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Any.anyScratchContract, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Any.anyScratchContract, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_256_satP (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract Spec.Hmac.sha512_256I.S (w + 192) X86_64.abi 24).pre s := by
  refine ⟨pbkSat (w + 192), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha512_256I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi,
    X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha512_256I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi,
    X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_256_satPF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract X86_64.abi (24 + (24 + 8 * (w + 192)))).pre s := by
  refine ⟨pbkFrameSat, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
    | (sig_pre [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem sha512_256_satIF (hw : w = 12 ∨ w = 36 ∨ w = 178) :
    ∃ s, (Spec.Hmac.sha512_256I.initContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl)

theorem sha512_256_satAF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512_256I.initAnyKeyContract X86_64.abi (24 + (8 + 8 * (w + 192)))).pre s := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

theorem sha512_256_satFF (hw : w = 30 ∨ w = 54 ∨ w = 196) :
    ∃ s, (Spec.Hmac.sha512_256I.finalizeContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

end

/-- SHA-512/256's functions, with the implementation `v` of the compression function. -/
abbrev sha512_256H (v : Compress) : Hash := hash Spec.Hmac.sha512_256I 32 "vg_sha512_256_init_core" H0_512_256 v

theorem sha512_256K (v : Compress) : Callees (sha512_256H v) := callees (Or.inr (Or.inr (Or.inr rfl))) v

theorem sha512_256W (v : Compress) : (sha512_256H v).W = 30 ∨ (sha512_256H v).W = 54 ∨ (sha512_256H v).W = 196 := hashW v

theorem sha512_256C (v : Compress) : CoreOK (core (sha512_256H v)) := coreOKS v.callee.so v.hso 32 (Or.inr (Or.inl rfl))

theorem sha512_256A (v : Compress) : Any.AnyOK (core (sha512_256H v)) := anyOKS v.callee.so v.hso 32 (Or.inr (Or.inl rfl))

/-- What the proofs know of SHA-512/256's functions. -/
def sha512_256OK (v : Compress) : HashOK (sha512_256H v) :=
  ok (sha512_256C v) (sha512_256K v) rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl))

/-- SHA-512/256 with the implementation `v` of the compression function. -/
def sha512_256 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  MdHash.of (I := Spec.Hmac.sha512_256I) (sha512_256OK v) (sha512_256C v) (sha512_256K v)
    ⟨Spec.Mgf1.sha512_256, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl
    1328 (sha512_256OK v.uniform) rfl
    (sha512_256_satI (hashW v)) (sha512_256_satF (hashW v)) (sha512_256_satT (hashW v)) (sha512_256_satP (hashW v))
    (by rcases sha512_256W v with h | h | h <;> omega_using [h])
    (sha512_256A v) (sha512_256_satA (hashW v))
    (by
      show (sha512_256H v).W + 192 < 511
      rcases sha512_256W v with h | h | h <;> omega_using [h])
    Proof.Hmac.sha512_256_local (sha512_256_satAF (hashW v)) (sha512_256_satW (hashIW v)) (sha512_256_satIF (hashIW v))
    (by decide) (sha512_256_satFF (hashW v))
    (by
      show (sha512_256H v).W + 192 < 509
      rcases sha512_256W v with h | h | h <;> omega_using [h])
    (sha512_256_satPF (hashW v))
    v.suffix v.features stream

end VG.Proof.Pbkdf2.Md.X86_64.Sha512
