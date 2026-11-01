module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Md5.X86_64.Stream.Md
public import VerifiedGarbage.Proof.Md5.X86_64.Stream.Init
public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Md5.X86_64.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
meta import VerifiedGarbage.Proof.Md5.X86_64.Stream.Md
meta import VerifiedGarbage.Proof.Md5.X86_64.Stream.Init
meta import VerifiedGarbage.Spec.Md5.Contract
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Md5.X86_64.Lit

/-!
# MD5 on x86-64, as a Merkle–Damgård hash function

MD5, with its one implementation of the compression function, as a variant of
`MdHash` (`variant`), from which HMAC and PBKDF2 are emitted
(`Generic/MdHash/X86_64/`): its streaming code is the generic Merkle–Damgård
code (`Stream.params`), its specification `Spec.Hmac.md5S`. Its streaming
`update` and `finalize` are in its registration file
(`Artifacts/Md5/X86_64.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Md5

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- MD5's functions. -/
def hash : Hash where
  P := Impl.Md5.X86_64.Stream.params
  D := 16
  W := Spec.Hmac.md5I.scratch
  compN := "vg_md5_compress"
  compC := Impl.Md5.X86_64.compress
  initN := Spec.Md5.initApi.name
  initC := Impl.Md5.X86_64.Stream.init
  updN := "vg_md5_update_scratch"
  finN := "vg_md5_finalize_scratch"
  hmacInitN := "vg_hmac_md5_init_scratch"
  hmacFinN := "vg_hmac_md5_finalize_scratch"
  iterN := "vg_pbkdf2_hmac_md5_iterate"

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Md5.X86_64.Stream.params, 16, 48, "", .block [], "", .block [], "", "", "", "",
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

theorem callees : Callees hash where
  cMx := by simp only [hash]; lit_decide
  cSp := by simp only [hash]; lit_decide
  cNs := by simp only [hash]; lit_decide
  cD := Proof.Md5.X86_64.Stream.callee.depth
  iMx := by simp only [hash] <;> decide +kernel
  iSp := by simp only [hash] <;> decide +kernel
  iNs := by simp only [hash] <;> decide +kernel
  iD := by simp only [hash] <;> decide +kernel
  cXD := by simp only [hash]; lit_decide
  iXD := by simp only [hash] <;> decide +kernel

def ok : HashOK hash where
  md := Proof.Md5.md
  dims := Proof.Md5.X86_64.Stream.dims
  shape := Proof.Md5.X86_64.Stream.shape
  taints := Proof.Md5.X86_64.Stream.taints
  comp := Proof.Md5.X86_64.Stream.callee
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  lenOk _ _ := trivial
  SH := Spec.Hmac.md5S
  iv := Spec.Md5.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm
  hB := rfl
  hS := rfl
  hD := rfl
  hD0 := by decide
  hDN := by decide
  hD4 := by decide
  hN4 := by decide
  hDL := by decide
  hL4 := by decide
  hNL := by decide
  hPad := by decide
  hso := by decide
  fits := by decide
  hW := by decide
  init := Proof.Md5.X86_64.Stream.init_verified
  initDepth := by simp only [hash] <;> decide +kernel
  initSp := nosp_of callees.iNs
  updMx := Callees.updMx callees coreOK
  finMx := Callees.finMx callees coreOK
  updSp := Callees.updSp callees coreOK
  finSp := Callees.finSp callees coreOK
  updDepth := Callees.updD callees coreOK
  finDepth := Callees.finD callees coreOK

theorem satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.md5I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.md5I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi, X86_64.argRegs] using initSat 80 48

theorem satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.md5I X86_64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.md5I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi, X86_64.argRegs] using finSat 80 16 48

theorem satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.md5I X86_64.abi 8).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.md5I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi, X86_64.argRegs] using Pbkdf2.X86_64.iterSat 80 16 48

theorem satA : ∃ s, (Any.anyScratchContract Spec.Hmac.md5I.S Spec.Hmac.md5I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.md5I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi, X86_64.argRegs] using initSat 80 128

theorem satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.md5I X86_64.abi 24).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi,
    X86_64.argRegs] using pbkSat 128

theorem satPF :
    ∃ s, (Spec.Hmac.md5I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.md5I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_md5 : Proof.RsaPss.X86_64.PssChecks Impl.Md5.X86_64.Stream.params 16 := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  taint_decide_all


/-- MD5, as a variant of `MdHash`. -/
def variant : MdHash :=
  MdHash.of ok coreOK callees ⟨Spec.Mgf1.md5, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_md5 rfl rfl satI satF satT satP (by decide)
    anyOK satA (by decide) Proof.Hmac.md5_local
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
    "" [] []

end VG.Proof.Pbkdf2.Md.X86_64.Md5
