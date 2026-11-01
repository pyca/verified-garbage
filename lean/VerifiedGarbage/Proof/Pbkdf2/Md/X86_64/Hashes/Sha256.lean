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
# SHA-256 on x86-64, as a Merkle–Damgård hash function

SHA-256 with an implementation `v` of its compression function
(`Proof/Sha256/X86_64/Variant.lean`), as a variant of `MdHash` (`variant v`),
from which HMAC and PBKDF2 are emitted (`Generic/MdHash/X86_64/`): its streaming
code is the generic Merkle–Damgård code (`Stream.params`), its specification
`Spec.Hmac.sha256S`. The facts about the code HMAC and PBKDF2 add, which do not
depend on `v`, are checked once (`coreOK`).

`stream v` are the streaming `update` and `finalize` made with `v`, and the
one-shot `digest` (`Proof/Sha256/X86_64/OneShot.lean`), which
`Generic/MdHash/X86_64/Stream.lean` emits from their `Api`s, named with
its suffix.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha256

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.X86_64 (Compress)

/-- SHA-256's functions, calling the implementation `v` of the compression
function, named with its suffix. -/
def hash (v : Compress) : Hash where
  P := Impl.Sha256.X86_64.Stream.params
  D := 32
  W := Spec.Hmac.sha256I.scratch
  compN := v.callee.name
  compC := v.callee.code
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.X86_64.Stream.init
  updN := Spec.Sha256.updateScratchApi.name ++ v.suffix
  finN := Spec.Sha256.finalizeScratchApi.name ++ v.suffix
  hmacInitN := "vg_hmac_sha256_init_scratch" ++ v.suffix
  hmacFinN := "vg_hmac_sha256_finalize_scratch" ++ v.suffix
  iterN := "vg_pbkdf2_hmac_sha256_iterate" ++ v.suffix

/-- `hash v` without the functions it calls, the same for every `v`. -/
def coreH : Hash := ⟨Impl.Sha256.X86_64.Stream.params, 32, 104, "", .block [], "", .block [], "", "", "", "",
  ""⟩

theorem coreOK : CoreOK coreH := by
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

theorem anyOK : Any.AnyOK coreH := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  taint_decide_all

variable (v : Compress)

theorem callees : Callees (hash v) where
  cMx := v.mxcsr
  cSp := allInstrs_of_all v.spSafe
  cNs := by
    show v.callee.code.allInstrs _ = true
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi]
  cD := v.ok.depth
  iMx := by simp only [hash] <;> decide +kernel
  iSp := by simp only [hash] <;> decide +kernel
  iNs := by simp only [hash] <;> decide +kernel
  iD := by simp only [hash] <;> decide +kernel
  cXD := v.noStack
  iXD := by simp only [hash] <;> decide +kernel

def ok : HashOK (hash v) where
  md := Proof.Sha256.md
  dims := Proof.Sha256.X86_64.Stream.dims
  shape := Proof.Sha256.X86_64.Stream.shape
  taints := Proof.Sha256.X86_64.Stream.taints
  comp := Proof.Sha256.X86_64.Stream.callee v.ok
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  lenOk _ _ := trivial
  SH := Spec.Hmac.sha256S
  iv := Spec.Sha256.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm
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
  hso := by simp only [hash] <;> decide
  fits := by simp only [hash] <;> decide
  hW := by simp only [hash] <;> decide
  init := Proof.Sha256.X86_64.Stream.init_verified
  initDepth := by simp only [hash] <;> decide +kernel
  initSp := nosp_of (callees v).iNs
  updMx := Callees.updMx (callees v) coreOK
  finMx := Callees.finMx (callees v) coreOK
  updSp := Callees.updSp (callees v) coreOK
  finSp := Callees.finSp (callees v) coreOK
  updDepth := Callees.updD (callees v) coreOK
  finDepth := Callees.finD (callees v) coreOK

theorem satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha256I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs] using initSat 96 104

theorem satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha256I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha256I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs] using finSat 96 32 104

theorem satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha256I X86_64.abi 8).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha256I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs] using Pbkdf2.X86_64.iterSat 96 32 104

theorem satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha256I.S Spec.Hmac.sha256I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha256I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs] using initSat 96 200

theorem satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I X86_64.abi 24).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi,
    X86_64.argRegs] using pbkSat 200

theorem satPF :
    ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha256I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- The streaming `update` and `finalize` made with `v`, which keep their
working space in a frame of their own, and `update_scratch` and
`finalize_scratch`, which HMAC's, PBKDF2's and ECDSA's code calls with
theirs. -/
def stream : List StreamFn := [
  { api := Spec.Sha256.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch 616 .r8 (Impl.Sha256.X86_64.Stream.update v.callee)
    contract := Spec.Sha256.updateContract X86_64.abi (8 + 616)
    stack := 8 + 616
    verified := Proof.Sha256.X86_64.Shared.update v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha256.X86_64.Shared.update_spSafe v.spSafe) },
  { api := Spec.Sha256.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch 616 .rcx (Impl.Sha256.X86_64.Stream.finalize v.callee)
    contract := Spec.Sha256.finalizeContract X86_64.abi (8 + 616)
    stack := 8 + 616
    verified := Proof.Sha256.X86_64.Shared.finalize v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha256.X86_64.Shared.finalize_spSafe v.spSafe) },
  { api := Spec.Sha256.updateScratchApi
    code := Impl.Sha256.X86_64.Stream.update v.callee
    contract := Spec.Sha256.updateScratchContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha256.X86_64.Shared.updateScratch v.ok v.mxcsr
    spSafe := Proof.Sha256.X86_64.Shared.update_spSafe v.spSafe },
  { api := Spec.Sha256.finalizeScratchApi
    code := Impl.Sha256.X86_64.Stream.finalize v.callee
    contract := Spec.Sha256.finalizeScratchContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha256.X86_64.Shared.finalizeScratch v.ok v.mxcsr
    spSafe := Proof.Sha256.X86_64.Shared.finalize_spSafe v.spSafe },
  { api := Spec.Sha256.digest256Api
    code := Proof.Sha256.X86_64.OneShot.digest (Impl.MdStream.X86_64.out32 8 true) Spec.Sha256.H0 v.callee
    contract := Spec.Sha256.digestContract X86_64.abi 32 Spec.Sha256.hash (8 + Proof.Sha256.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha256.X86_64.OneShot.frame
    verified := Proof.Sha256.X86_64.OneShot.verified Proof.Sha256.X86_64.OneShot.code256
      Proof.Sha256.X86_64.OneShot.init_check256 Proof.Sha256.X86_64.OneShot.hash_take v.ok v.mxcsr v.spSafe
      v.noStack
    spSafe := Proof.Sha256.X86_64.OneShot.spSafe Proof.Sha256.X86_64.OneShot.code256 Spec.Sha256.H0 v.spSafe }]

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha256 : Proof.RsaPss.X86_64.PssChecks Impl.Sha256.X86_64.Stream.params 32 := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  taint_decide_all


/-- SHA-256 with the implementation `v` of its compression function, which it
carries for the functions built on SHA-256 alone (`MdHash.sha256`). -/
def variant : MdHash :=
  { MdHash.of (ok v) coreOK (callees v) ⟨Spec.Mgf1.sha256, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha256 rfl rfl satI satF satT satP (by decide)
    anyOK satA (by decide) Proof.Hmac.sha256_local
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
    (by decide) satPF
    v.suffix v.features (stream v) with
    sha256 := some v }

end VG.Proof.Pbkdf2.Md.X86_64.Sha256
