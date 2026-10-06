import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Sha256.X86_64.Variant
import VerifiedGarbage.Proof.Sha256.X86_64.Shared
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# SHA-224 on x86-64, as a Merkle–Damgård hash function

SHA-224 with an implementation `v` of SHA-256's compression function
(`Proof/Sha256/X86_64/Variant.lean`), as a variant of `MdHash` (`variant v`),
from which HMAC and PBKDF2 are emitted (`Generic/MdHash/X86_64/`): its
streaming code is SHA-256's, the generic Merkle–Damgård code (`Stream.params`)
from SHA-224's initial hash value (`vg_sha224_init`), its specification
`Spec.Hmac.sha224S`, with the digest the first 28 bytes of the final hash
value. The facts about the code HMAC and PBKDF2 add, which do not depend on
`v`, are checked once (`coreOK`).

Its streaming `update` and `finalize` are SHA-256's, which SHA-256's
variants carry (`Proof/Pbkdf2/Md/X86_64/Hashes/Sha256.lean`): SHA-224's
carry none.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha224

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.X86_64 (Compress)

/-- SHA-224's functions, calling the implementation `v` of the compression
function, named with its suffix. -/
def hash (v : Compress) : Hash where
  P := Impl.Sha256.X86_64.Stream.params
  D := 28
  W := Spec.Hmac.sha224I.scratch
  compN := v.callee.name
  compC := v.callee.code
  initN := Spec.Sha256.init224Api.name
  initC := Impl.Sha256.X86_64.Stream.init224
  updN := Spec.Sha256.updateScratchApi.name ++ v.suffix
  finN := Spec.Sha256.finalizeScratchApi.name ++ v.suffix
  hmacInitN := Spec.Hmac.sha224I.initScratchApi.name ++ v.suffix
  hmacFinN := Spec.Hmac.sha224I.finalizeScratchApi.name ++ v.suffix
  iterN := Spec.Hmac.sha224I.iterateApi.name ++ v.suffix

/-- `hash v` without the functions it calls, the same for every `v`. -/
def coreH : Hash := ⟨Impl.Sha256.X86_64.Stream.params, 28, 104, "", .block [], "", .block [], "", "", "", "",
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
  hso := by simp only [hash] <;> decide
  fits := by simp only [hash] <;> decide
  hW := by simp only [hash] <;> decide
  init := Proof.Sha256.X86_64.Stream.init224_verified
  initDepth := by simp only [hash] <;> decide +kernel
  initSp := nosp_of (callees v).iNs
  updMx := Callees.updMx (callees v) coreOK
  finMx := Callees.finMx (callees v) coreOK
  updSp := Callees.updSp (callees v) coreOK
  finSp := Callees.finSp (callees v) coreOK
  updDepth := Callees.updD (callees v) coreOK
  finDepth := Callees.finD (callees v) coreOK

theorem satI : ∃ s, (Spec.Hmac.sha224I.initScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha224I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs] using initSat 96 104

theorem satF : ∃ s, (Spec.Hmac.sha224I.finalizeScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha224I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs] using finSat 96 28 104

theorem satT : ∃ s, (Spec.Hmac.sha224I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha224I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 96 28 104

theorem satP : ∃ s, (Spec.Hmac.sha224I.pbkdf2ScratchContract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi,
    X86_64.argRegs] using pbkSat 200

theorem satPF :
    ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha224I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha224 : Proof.RsaPss.X86_64.PssChecks Impl.Sha256.X86_64.Stream.params 28 := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  taint_decide_all


/-- SHA-224 with the implementation `v` of SHA-256's compression function.
Its streaming `update` and `finalize` are SHA-256's, which SHA-256's variant
with `v` carries; `v` itself, for the functions built on SHA-224 alone
(`MdHash.sha224`). -/
def variant : MdHash :=
  { MdHash.of (ok v) coreOK (callees v) ⟨Spec.Mgf1.sha224, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha224 rfl rfl satI satF satT satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) satPF
    v.suffix v.features [] with
    sha224 := some v }

end VG.Proof.Pbkdf2.Md.X86_64.Sha224
