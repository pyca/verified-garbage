module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha256.X86_64.Shared
public import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
public import VerifiedGarbage.Proof.Sha256.X86_64.OneShot
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
meta import VerifiedGarbage.Proof.Sha256.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
meta import VerifiedGarbage.Proof.Sha256.X86_64.OneShot
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# SHA-224 on x86-64, as a Merkle–Damgård hash function

SHA-224 with an implementation `v` of SHA-256's compression function
(`Proof/Sha256/X86_64/Variant.lean`), as a variant of `MdHash` (`variant v`),
from which HMAC and PBKDF2 are emitted (`Generic/MdHash/X86_64/`): its
streaming code is SHA-256's, the generic Merkle–Damgård code (`Stream.params`)
from SHA-224's initial hash value (`vg_sha224_init`), its specification
`Spec.Hmac.sha224S`, with the digest the first 28 bytes of the final hash
value. The facts about the code HMAC and PBKDF2 add, which depend on `v`
only through the scratch space it uses, are checked once for each
(`coreOKS`).

Its streaming `update` is SHA-256's, which SHA-256's variants carry
(`Proof/Pbkdf2/Md/X86_64/Hashes/Sha256.lean`); SHA-224's carry its own
`finalize`, which writes its digest (`stream v`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha224

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.X86_64 (Compress)

/-- SHA-224's functions, calling the implementation `v` of the compression
function, named with its suffix, giving it the scratch space it uses
(`Callee.so`) and taking the working space they use (`Hash.wOf`). They call
`vg_sha224_init`'s code as the internal `vg_sha224_init_core`: the function
exported as `vg_sha224_init` also clears what it leaves
(`Proof.Sha256.X86_64.init224Reg`), which its callers, which clear their own,
do not need. -/
def hash (v : Compress) : Hash where
  P := Proof.Sha256.X86_64.Stream.paramsS v.callee.so
  D := 28
  W := Hash.wOf (Proof.Sha256.X86_64.Stream.paramsS v.callee.so)
  compN := v.callee.name
  compC := v.callee.code
  initN := "vg_sha224_init_core"
  initC := Impl.Sha256.X86_64.Stream.init224
  updN := "vg_sha256_update_scratch" ++ v.suffix
  finN := "vg_sha256_finalize_scratch" ++ v.suffix
  hmacInitN := "vg_hmac_sha224_init_scratch" ++ v.suffix
  hmacFinN := "vg_hmac_sha224_finalize_scratch" ++ v.suffix
  iterN := "vg_pbkdf2_hmac_sha224_iterate" ++ v.suffix

/-- `hash v` without the functions it calls, for an implementation that uses
`so` bytes of scratch space. -/
def coreHS (so : Nat) : Hash :=
  ⟨Proof.Sha256.X86_64.Stream.paramsS so, 28, Hash.wOf (Proof.Sha256.X86_64.Stream.paramsS so), "", .block [],
    "", .block [], "", "", "", "", "", Proof.Pbkdf2.Md.X86_64.coreBoth⟩

/-- The scratch space the implementations use. -/
abbrev SoOk (so : Nat) : Prop := so = 0 ∨ so = 112 ∨ so = 560

theorem coreOKS (so : Nat) (h : SoOk so) : CoreOK (coreHS so) := by
  rcases h with rfl | rfl | rfl <;>
  refine {
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
    fitF := ?_ }
  taint_decide_all

theorem anyOKS (so : Nat) (h : SoOk so) : Any.AnyOK (coreHS so) := by
  rcases h with rfl | rfl | rfl <;> refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  taint_decide_all

variable (v : Compress)

theorem coreOK : CoreOK (core (hash v)) := coreOKS v.callee.so v.hso

theorem anyOK : Any.AnyOK (core (hash v)) := anyOKS v.callee.so v.hso

theorem callees : Callees (hash v) :=
  .ofTwice rfl
    (cMx := v.mxcsr)
    (cSp := allInstrs_of_all v.spSafe)
    (cNs := by
      show v.callee.code.allInstrs _ = true
      rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi])
    (cD := v.ok.depth)
    (iMx := by simp only [hash] <;> decide +kernel)
    (iSp := by simp only [hash] <;> decide +kernel)
    (iNs := by simp only [hash] <;> decide +kernel)
    (iD := by simp only [hash] <;> decide +kernel)
    (cXD := v.noStack)
    (iXD := by simp only [hash] <;> decide +kernel)

/-- The words of working space of `hash v`'s functions. -/
theorem hashW : (hash v).W = 18 ∨ (hash v).W = 32 ∨ (hash v).W = 88 := by
  rcases v.hso with h | h | h <;> simp only [hash, Hash.wOf, Proof.Sha256.X86_64.Stream.paramsS, h] <;> decide

/-- The words of working space of `hash v`'s HMAC `init` for a key of at
most a block. -/
theorem hashIW : initWords (hash v) = 12 ∨ initWords (hash v) = 26 ∨ initWords (hash v) = 82 := by
  rcases v.hso with h | h | h <;> simp only [initWords_eq, hash, Proof.Sha256.X86_64.Stream.paramsS, h] <;> decide

def ok : HashOK (hash v) where
  md := Proof.Sha256.md
  dims := Proof.Sha256.X86_64.Stream.dimsS _ (by rcases v.hso with h | h | h <;> omega)
  shape := Proof.Sha256.X86_64.Stream.shapeS _
  taints := Proof.Sha256.X86_64.Stream.taintsS3 _ v.hso
  comp := v.okS
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  lenOk _ _ := trivial
  SH := Spec.Hmac.sha224S
  iv := Spec.Sha256.H0_224
  repr _ _ _ := Iff.rfl
  hash _ := rfl
  hB := rfl
  hS := rfl
  hD := rfl
  hD0 := by simp only [hash] <;> decide
  hDN := by simp only [hash] <;> decide
  hD4 := by simp only [hash] <;> decide
  hN4 := by simp only [hash] <;> decide
  hDL := by simp only [hash] <;> decide
  hL4 := by simp only [hash] <;> decide
  hNL := by simp only [hash] <;> decide
  hPad := by simp only [hash] <;> decide
  hso := by
    show v.callee.so % 8 = 0 ∧ v.callee.so + 48 ≤ 8 * 256
    rcases v.hso with h | h | h <;> rw [h] <;> decide
  fits := by
    show v.callee.so + 48 + 32 + 64 ≤ 8 * ((v.callee.so + 48 + 32 + 64 + 7) / 8)
    omega
  hW := by rcases hashW v with h | h | h <;> rw [h] <;> decide
  init := Proof.Sha256.X86_64.Stream.init224_verified
  initDepth := by simp only [hash] <;> decide +kernel
  initSp := nosp_of (callees v).iNs
  updMx := Callees.updMx (callees v) (coreOK v)
  finMx := Callees.finMx (callees v) (coreOK v)
  updSp := Callees.updSp (callees v) (coreOK v)
  finSp := Callees.finSp (callees v) (coreOK v)
  updDepth := Callees.updD (callees v) (coreOK v)
  finDepth := Callees.finD (callees v) (coreOK v)

/-- `hash v` made with the working space of the slowest implementation,
AVX2's (`MdHash.okU`). -/
def okU : HashOK ((hash v).withWs 560 (Hash.wOf { (hash v).P with so := 560 })) :=
  (ok v).withWs 560 _ (by decide) Proof.Sha256.X86_64.Stream.taints (Proof.Sha256.X86_64.Stream.callee v.ok)
    (by show 560 + 48 + 32 + 64 ≤ 8 * ((560 + 48 + 32 + 64 + 7) / 8); decide)
    (by show (560 + 48 + 32 + 64 + 7) / 8 ≤ 256; decide) rfl (callees v) (coreOKS 560 (.inr (.inr rfl)))

/-! ### The shared contracts are satisfiable

With each implementation's working space (`hashW`, `hashIW`). -/

variable {w : Nat}

theorem satI (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha224I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 96 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satW (hw : w = 12 ∨ w = 26 ∨ w = 82) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha224I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 96 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satF (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Proof.Hmac.finalizeScratchContract Spec.Hmac.sha224I.S w X86_64.abi 16).pre s := by
  refine ⟨finSat 96 28 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha224I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha224I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satT (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Proof.Pbkdf2.iterateContract Spec.Hmac.sha224I.S w X86_64.abi 8).pre s := by
  refine ⟨Pbkdf2.X86_64.iterSat 96 28 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha224I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha224S,
    Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha224I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha224S,
    Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satA (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Any.anyScratchContract Spec.Hmac.sha224I.S (w + 96)).pre s := by
  refine ⟨initSat 96 (w + 96), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Any.anyScratchContract, Spec.Hmac.sha224I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Any.anyScratchContract, Spec.Hmac.sha224I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satP (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract Spec.Hmac.sha224I.S (w + 96) X86_64.abi 24).pre s := by
  refine ⟨pbkSat (w + 96), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha224I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi,
    X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha224I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi,
    X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satPF (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract X86_64.abi (24 + (24 + 8 * (w + 96)))).pre s := by
  refine ⟨pbkFrameSat, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
    | (sig_pre [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satIF (hw : w = 12 ∨ w = 26 ∨ w = 82) :
    ∃ s, (Spec.Hmac.sha224I.initContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl)

theorem satAF (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Spec.Hmac.sha224I.initAnyKeyContract X86_64.abi (24 + (8 + 8 * (w + 96)))).pre s := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

theorem satFF (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Spec.Hmac.sha224I.finalizeContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

/-- SHA-224's `finalize` made with `v`, which writes its digest (`finalize224`). -/
def finFn : StreamFn :=
  { api := Spec.Sha256.finalize224Api
    code := Impl.StackScratch.X86_64.withStackScratch 616 .rcx (Impl.Sha256.X86_64.Stream.finalize224 v.callee)
    contract := Spec.Sha256.finalize224Contract X86_64.abi (8 + 616)
    stack := 8 + 616
    verified := Proof.Sha256.X86_64.Shared.finalize224Stack v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha256.X86_64.Shared.finalize224_spSafe v.spSafe) }

/-- SHA-224's one-shot `digest` made with `v`. -/
def digFn : StreamFn :=
  { api := Spec.Sha256.digest224Api
    code := Proof.Sha256.X86_64.OneShot.digest (Impl.MdStream.X86_64.out32 7 true) Spec.Sha256.H0_224 v.callee
    contract := Spec.Sha256.digestContract X86_64.abi 28 Spec.Sha256.sha224 (8 + Proof.Sha256.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha256.X86_64.OneShot.frame
    verified := Proof.Sha256.X86_64.OneShot.verified Proof.Sha256.X86_64.OneShot.code224
      Proof.Sha256.X86_64.OneShot.init_check224 Proof.Sha256.X86_64.OneShot.sha224_take v.ok v.mxcsr v.spSafe
      v.noStack
    spSafe := Proof.Sha256.X86_64.OneShot.spSafe Proof.Sha256.X86_64.OneShot.code224 Spec.Sha256.H0_224 v.spSafe }

/-- SHA-224's `finalize` and one-shot `digest` made with `v`. -/
def stream : List StreamFn := [finFn v, digFn v]

/-! ### With the working space the compression function uses

As `Sha256.updFnS`: for an implementation `v` verified with `so` bytes of
scratch space (`hv`). -/

section S

variable {so : Nat} (h : so = 0 ∨ so = 112)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha256.compressX86_64S so))

/-- SHA-224's `finalize` made with `v`, in a frame of `so + 56` bytes. -/
def finFnS : StreamFn :=
  { api := Spec.Sha256.finalize224Api
    code := Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx
      (Impl.MdStream.X86_64.finalize (Proof.Sha256.X86_64.Stream.params224S so) v.callee.name v.callee.code)
    contract := Spec.Sha256.finalize224Contract X86_64.abi (8 + (so + 56))
    stack := 8 + (so + 56)
    verified := Proof.Sha256.X86_64.Shared.finalize224S h v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by rcases h with rfl | rfl <;> decide)
      (Proof.Sha256.X86_64.Shared.finalize224S_spSafe h v.spSafe) }

/-- SHA-224's one-shot `digest` made with `v`, likewise. -/
def digFnS : StreamFn :=
  { api := Spec.Sha256.digest224Api
    code := Proof.Sha256.X86_64.OneShot.digestS so (Impl.MdStream.X86_64.out32 7 true) Spec.Sha256.H0_224 v.callee
    contract := Spec.Sha256.digestContract X86_64.abi 28 Spec.Sha256.sha224 (8 + Proof.Sha256.X86_64.OneShot.frameS so)
    stack := 8 + Proof.Sha256.X86_64.OneShot.frameS so
    verified := Proof.Sha256.X86_64.OneShot.verifiedS (Proof.Sha256.X86_64.OneShot.code224S h)
      Proof.Sha256.X86_64.OneShot.init_check224 Proof.Sha256.X86_64.OneShot.sha224_take v.ok hv v.mxcsr v.spSafe
      v.noStack
    spSafe := Proof.Sha256.X86_64.OneShot.spSafeS (Proof.Sha256.X86_64.OneShot.code224S h) Spec.Sha256.H0_224
      v.spSafe }

/-- `stream`, made for `so` bytes of scratch space. -/
def streamS : List StreamFn := [finFnS v h hv, digFnS v h hv]

end S

/-- SHA-224 with the implementation `v` of SHA-256's compression function.
Its streaming `update` is SHA-256's, which SHA-256's variant with `v`
carries, and its `finalize` its own (`stream v`). -/
def variant (stream : List StreamFn := stream v) : MdHash :=
  MdHash.of (I := Spec.Hmac.sha224I) (ok v) (coreOK v) (callees v)
    ⟨Spec.Mgf1.sha224, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl 560 (okU v) rfl
    (satI (hashW v)) (satF (hashW v)) (satT (hashW v)) (satP (hashW v))
    (by rcases hashW v with h | h | h <;> omega)
    (anyOK v) (satA (hashW v)) (by show (hash v).W + 96 < 511; rcases hashW v with h | h | h <;> omega)
    Proof.Hmac.sha224_local (satAF (hashW v)) (satW (hashIW v)) (satIF (hashIW v))
    (by decide) (satFF (hashW v))
    (by show (hash v).W + 96 < 509; rcases hashW v with h | h | h <;> omega) (satPF (hashW v))
    v.suffix v.features stream

end VG.Proof.Pbkdf2.Md.X86_64.Sha224
