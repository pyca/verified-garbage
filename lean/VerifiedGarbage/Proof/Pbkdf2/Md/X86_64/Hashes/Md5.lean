import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Md5.X86_64.Stream.Md
import VerifiedGarbage.Proof.Md5.X86_64.Stream.Init
import VerifiedGarbage.Proof.Md5.X86_64.Lit
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# MD5 on x86-64, as a Merkle–Damgård hash function

MD5, with its one implementation of the compression function, as a variant of
`MdHash` (`variant`), from which HMAC and PBKDF2 are emitted
(`Generic/MdHash/X86_64/`): its streaming code is the generic Merkle–Damgård
code (`Stream.params`), its specification `Spec.Hmac.md5S`. Its streaming
`update` and `finalize` are in its registration file
(`Artifacts/Md5/X86_64.lean`).
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Md5

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- MD5's functions. -/
def hash : Hash where
  P := Impl.Md5.X86_64.Stream.params
  D := 16
  W := Spec.Hmac.md5I.scratch
  compN := Spec.Md5.compressApi.name
  compC := Impl.Md5.X86_64.compress
  initN := Spec.Md5.initApi.name
  initC := Impl.Md5.X86_64.Stream.init
  updN := Spec.Md5.updateScratchApi.name
  finN := Spec.Md5.finalizeScratchApi.name
  hmacInitN := Spec.Hmac.md5I.initScratchApi.name
  hmacFinN := Spec.Hmac.md5I.finalizeScratchApi.name
  iterN := Spec.Hmac.md5I.iterateApi.name

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

theorem satI : ∃ s, (Spec.Hmac.md5I.initScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.md5I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi, X86_64.argRegs] using initSat 80 48

theorem satF : ∃ s, (Spec.Hmac.md5I.finalizeScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.md5I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi, X86_64.argRegs] using finSat 80 16 48

theorem satT : ∃ s, (Spec.Hmac.md5I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.md5I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi, X86_64.argRegs] using Pbkdf2.X86_64.iterSat 80 16 48

theorem satP : ∃ s, (Spec.Hmac.md5I.pbkdf2ScratchContract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi,
    X86_64.argRegs] using pbkSat 128

theorem satPF :
    ∃ s, (Spec.Hmac.md5I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.md5I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5S, Spec.Hmac.md5, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- MD5, as a variant of `MdHash`. -/
def variant : MdHash :=
  MdHash.of ok coreOK callees rfl rfl satI satF satT satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) satPF
    "" [] []

end VG.Proof.Pbkdf2.Md.X86_64.Md5
