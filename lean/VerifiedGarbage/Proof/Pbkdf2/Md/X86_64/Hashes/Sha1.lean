module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha1.X86_64.Variant
public import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Init
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
meta import VerifiedGarbage.Proof.Sha1.X86_64.Variant
meta import VerifiedGarbage.Proof.Sha1.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha1.X86_64.OneShot
meta import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Init
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Sha1.X86_64.Shared
public import VerifiedGarbage.Proof.Sha1.X86_64.OneShot

/-!
# SHA-1 on x86-64, as a Merkle–Damgård hash function

SHA-1 with an implementation `v` of its compression function
(`Proof/Sha1/X86_64/Variant.lean`), as a variant of `MdHash` (`variant v`), from
which HMAC and PBKDF2 are emitted (`Generic/MdHash/X86_64/`): its streaming code
is the generic Merkle–Damgård code (`Stream.params`), its specification
`Spec.Hmac.sha1S`. The facts about the code HMAC and PBKDF2 add, which depend on
`v` only through the scratch space it uses, are checked once for each
(`coreOKS`).

`stream v` are the streaming `update` and `finalize` made with `v` (and
their `_scratch` forms, which HMAC and PBKDF2 call) and the one-shot `digest`
(`Proof/Sha1/X86_64/OneShot.lean`), which
`Generic/MdHash/X86_64/Stream.lean` emits from their `Api`s, named with
its suffix.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha1

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha1.X86_64 (Compress)

/-- SHA-1's functions, calling the implementation `v` of the compression
function, named with its suffix, giving it the scratch space it uses
(`Callee.so`) and taking the working space they use (`Hash.wOf`). They call
`vg_sha1_init`'s code as the internal `vg_sha1_init_core`: the function
exported as `vg_sha1_init` also clears what it leaves
(`Proof.Sha1.X86_64.initReg`), which its callers, which clear their own, do
not need. -/
def hash (v : Compress) : Hash where
  P := { Impl.Sha1.X86_64.Stream.params with so := v.callee.so }
  D := 20
  W := Hash.wOf { Impl.Sha1.X86_64.Stream.params with so := v.callee.so }
  compN := v.callee.name
  compC := v.callee.code
  initN := "vg_sha1_init_core"
  initC := Impl.Sha1.X86_64.Stream.init
  updN := "vg_sha1_update_scratch" ++ v.suffix
  finN := "vg_sha1_finalize_scratch" ++ v.suffix
  hmacInitN := "vg_hmac_sha1_init_scratch" ++ v.suffix
  hmacFinN := "vg_hmac_sha1_finalize_scratch" ++ v.suffix
  iterN := "vg_pbkdf2_hmac_sha1_iterate" ++ v.suffix

/-- `hash v` without the functions it calls, for an implementation that uses
`so` bytes of scratch space. -/
def coreHS (so : Nat) : Hash :=
  ⟨{ Impl.Sha1.X86_64.Stream.params with so := so }, 20, Hash.wOf { Impl.Sha1.X86_64.Stream.params with so := so },
    "", .block [], "", .block [], "", "", "", "", "", Proof.Pbkdf2.Md.X86_64.coreBoth⟩

theorem coreOKS (so : Nat) (h : so = 0 ∨ so = 112) : CoreOK (coreHS so) := by
  rcases h with rfl | rfl <;>
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

theorem anyOKS (so : Nat) (h : so = 0 ∨ so = 112) : Any.AnyOK (coreHS so) := by
  rcases h with rfl | rfl <;> refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  taint_decide_all

variable (v : Compress)

theorem coreOK : CoreOK (core (hash v)) := coreOKS v.callee.so v.hso

theorem anyOK : Any.AnyOK (core (hash v)) := anyOKS v.callee.so v.hso

theorem callees : Callees (hash v) :=
  .ofTwice rfl
    (cMx := v.mxcsr)
    (cSp := allInstrs_of_all v.spSafe)
    (cNs := v.callee_nosp)
    (cD := v.ok.depth)
    (iMx := by simp only [hash] <;> decide +kernel)
    (iSp := by simp only [hash] <;> decide +kernel)
    (iNs := by simp only [hash] <;> decide +kernel)
    (iD := by simp only [hash] <;> decide +kernel)
    (cXD := v.noStack)
    (iXD := by simp only [hash] <;> decide +kernel)

/-- The words of working space of `hash v`'s functions. -/
theorem hashW : (hash v).W = 17 ∨ (hash v).W = 31 := by
  rcases v.hso with h | h <;> simp only [hash, Hash.wOf, h] <;> decide

/-- The words of working space of `hash v`'s HMAC `init` for a key of at
most a block. -/
theorem hashIW : initWords (hash v) = 12 ∨ initWords (hash v) = 26 := by
  rcases v.hso with h | h <;> simp only [initWords_eq, hash, h] <;> decide

def ok : HashOK (hash v) where
  md := Proof.Sha1.md
  dims := ⟨Proof.Sha1.X86_64.Stream.dims.B, Proof.Sha1.X86_64.Stream.dims.N, Proof.Sha1.X86_64.Stream.dims.L,
    show v.callee.so ≤ 2048 by rcases v.hso with h | h <;> omega_using [h]⟩
  shape := ⟨Proof.Sha1.X86_64.Stream.shape.len, Proof.Sha1.X86_64.Stream.shape.lenV,
    Proof.Sha1.X86_64.Stream.shape.out⟩
  taints := by
    show MdStream.X86_64.Taints { Impl.Sha1.X86_64.Stream.params with so := v.callee.so }
    rcases v.hso with h | h <;> rw [h]
    · exact Proof.Sha1.X86_64.Stream.taints0
    · exact Proof.Sha1.X86_64.Stream.taints
  comp := v.okS
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega_using [hj])
  lenOk _ _ := trivial
  SH := Spec.Hmac.sha1S
  iv := Spec.Sha1.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm
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
    rcases v.hso with h | h <;> rw [h] <;> decide
  fits := by
    show v.callee.so + 48 + 20 + 64 ≤ 8 * ((v.callee.so + 48 + 20 + 64 + 7) / 8)
    omega_using []
  hW := by rcases hashW v with h | h <;> rw [h] <;> decide
  init := Proof.Sha1.X86_64.Stream.init_verified
  initDepth := by simp only [hash] <;> decide +kernel
  initSp := nosp_of (callees v).iNs
  updMx := Callees.updMx (callees v) (coreOK v)
  finMx := Callees.finMx (callees v) (coreOK v)
  updSp := Callees.updSp (callees v) (coreOK v)
  finSp := Callees.finSp (callees v) (coreOK v)
  updDepth := Callees.updD (callees v) (coreOK v)
  finDepth := Callees.finD (callees v) (coreOK v)

/-- `hash v` made with the working space of the slowest implementations
(`MdHash.okU`). -/
def okU : HashOK ((hash v).withWs 112 (Hash.wOf { (hash v).P with so := 112 })) :=
  (ok v).withWs 112 _ (by decide) Proof.Sha1.X86_64.Stream.taints v.ok
    (by show 112 + 48 + 20 + 64 ≤ 8 * ((112 + 48 + 20 + 64 + 7) / 8); decide)
    (by show (112 + 48 + 20 + 64 + 7) / 8 ≤ 256; decide) rfl (callees v)
    (coreOKS 112 (.inr rfl))

/-! ### The shared contracts are satisfiable

With each implementation's working space (`hashW`, `hashIW`). -/

variable {w : Nat}

theorem satI (hw : w = 17 ∨ w = 31) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha1I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 84 w, ?_⟩
  rcases hw with rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha1I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha1I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satW (hw : w = 12 ∨ w = 26) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha1I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 84 w, ?_⟩
  rcases hw with rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha1I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha1I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satF (hw : w = 17 ∨ w = 31) :
    ∃ s, (Proof.Hmac.finalizeScratchContract Spec.Hmac.sha1I.S w X86_64.abi 16).pre s := by
  refine ⟨finSat 84 20 w, ?_⟩
  rcases hw with rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha1I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha1I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satT (hw : w = 17 ∨ w = 31) :
    ∃ s, (Proof.Pbkdf2.iterateContract Spec.Hmac.sha1I.S w X86_64.abi 8).pre s := by
  refine ⟨Pbkdf2.X86_64.iterSat 84 20 w, ?_⟩
  rcases hw with rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha1I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha1S,
    Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha1I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha1S,
    Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satA (hw : w = 17 ∨ w = 31) :
    ∃ s, (Any.anyScratchContract Spec.Hmac.sha1I.S (w + 84)).pre s := by
  refine ⟨initSat 84 (w + 84), ?_⟩
  rcases hw with rfl | rfl <;>
  first
    | sig_sat_check [Any.anyScratchContract, Spec.Hmac.sha1I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Any.anyScratchContract, Spec.Hmac.sha1I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satP (hw : w = 17 ∨ w = 31) :
    ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract Spec.Hmac.sha1I.S (w + 84) X86_64.abi 24).pre s := by
  refine ⟨pbkSat (w + 84), ?_⟩
  rcases hw with rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha1I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi,
    X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha1I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi,
    X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satPF (hw : w = 17 ∨ w = 31) :
    ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract X86_64.abi (24 + (24 + 8 * (w + 84)))).pre s := by
  refine ⟨pbkFrameSat, ?_⟩
  rcases hw with rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha1I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
    | (sig_pre [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha1I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha1S, Spec.Hmac.sha1, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satIF (hw : w = 12 ∨ w = 26) :
    ∃ s, (Spec.Hmac.sha1I.initContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  rcases hw with rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl)

theorem satAF (hw : w = 17 ∨ w = 31) :
    ∃ s, (Spec.Hmac.sha1I.initAnyKeyContract X86_64.abi (24 + (8 + 8 * (w + 84)))).pre s := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  rcases hw with rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

theorem satFF (hw : w = 17 ∨ w = 31) :
    ∃ s, (Spec.Hmac.sha1I.finalizeContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  rcases hw with rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

/-- The streaming `update` made with `v`, which keeps its working space in a
frame of its own. -/
def updFn : StreamFn :=
  { api := Spec.Sha1.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch 168 .r8 (Impl.Sha1.X86_64.Stream.update v.callee)
    contract := Spec.Sha1.updateContract X86_64.abi (8 + 168)
    stack := 8 + 168
    verified := Proof.Sha1.X86_64.Shared.update v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha1.X86_64.Shared.update_spSafe v.spSafe) }

/-- The streaming `finalize` made with `v`, likewise. -/
def finFn : StreamFn :=
  { api := Spec.Sha1.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch 168 .rcx (Impl.Sha1.X86_64.Stream.finalize v.callee)
    contract := Spec.Sha1.finalizeContract X86_64.abi (8 + 168)
    stack := 8 + 168
    verified := Proof.Sha1.X86_64.Shared.finalize v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha1.X86_64.Shared.finalize_spSafe v.spSafe) }

/-- The one-shot `digest` made with `v`. -/
def digFn : StreamFn :=
  { api := Spec.Sha1.digestApi
    code := Proof.Sha1.X86_64.OneShot.digest v.callee
    contract := Spec.Sha1.digestContract X86_64.abi (8 + Proof.Sha1.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha1.X86_64.OneShot.frame
    verified := Proof.Sha1.X86_64.OneShot.verified v.ok v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha1.X86_64.OneShot.spSafe v.spSafe }

/-- The streaming `update` and `finalize` made with `v`, and the one-shot
`digest`. -/
def stream : List StreamFn := [updFn v, finFn v, digFn v]

/-! ### With no working space for the compression function

The same functions made for an implementation `v` that uses none (`hc`, such
as `vg_sha1_compress_shani`), which give it none (`Stream.params0`): their
frames shrink with it. -/

section Zero

variable (hc : MdStream.X86_64.CalleeOk (P := Proof.Sha1.X86_64.Stream.params0) Proof.Sha1.md v.callee.code)

/-- The streaming `update` made with `v`, in a frame of 56 bytes. -/
def updFn0 : StreamFn :=
  { api := Spec.Sha1.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch 56 .r8
      (Impl.MdStream.X86_64.update Proof.Sha1.X86_64.Stream.params0 v.callee.name v.callee.code)
    contract := Spec.Sha1.updateContract X86_64.abi (8 + 56)
    stack := 8 + 56
    verified := Proof.Sha1.X86_64.Shared.update0 hc v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide) (Proof.Sha1.X86_64.Shared.update0_spSafe v.spSafe) }

/-- The streaming `finalize` made with `v`, likewise. -/
def finFn0 : StreamFn :=
  { api := Spec.Sha1.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch 56 .rcx
      (Impl.MdStream.X86_64.finalize Proof.Sha1.X86_64.Stream.params0 v.callee.name v.callee.code)
    contract := Spec.Sha1.finalizeContract X86_64.abi (8 + 56)
    stack := 8 + 56
    verified := Proof.Sha1.X86_64.Shared.finalize0 hc v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide) (Proof.Sha1.X86_64.Shared.finalize0_spSafe v.spSafe) }

/-- The one-shot `digest` made with `v`, likewise. -/
def digFn0 : StreamFn :=
  { api := Spec.Sha1.digestApi
    code := Proof.Sha1.X86_64.OneShot.digest0 v.callee
    contract := Spec.Sha1.digestContract X86_64.abi (8 + Proof.Sha1.X86_64.OneShot.frame0)
    stack := 8 + Proof.Sha1.X86_64.OneShot.frame0
    verified := Proof.Sha1.X86_64.OneShot.verified0 hc v.mxcsr v.spSafe v.noStack
    spSafe := Proof.Sha1.X86_64.OneShot.spSafe0 v.spSafe }

end Zero

/-- SHA-1 with the implementation `v` of its compression function. -/
def variant (stream : List StreamFn := stream v) : MdHash :=
  MdHash.of (I := Spec.Hmac.sha1I) (ok v) (coreOK v) (callees v)
    ⟨Spec.Mgf1.sha1, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl 112 (okU v) rfl
    (satI (hashW v)) (satF (hashW v)) (satT (hashW v)) (satP (hashW v))
    (by rcases hashW v with h | h <;> omega_using [h])
    (anyOK v) (satA (hashW v)) (by show (hash v).W + 84 < 511; rcases hashW v with h | h <;> omega_using [h])
    Proof.Hmac.sha1_local (satAF (hashW v)) (satW (hashIW v)) (satIF (hashIW v))
    (by decide) (satFF (hashW v))
    (by show (hash v).W + 84 < 509; rcases hashW v with h | h <;> omega_using [h]) (satPF (hashW v))
    v.suffix v.features stream

end VG.Proof.Pbkdf2.Md.X86_64.Sha1
