module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Md5.AArch64.Stream.Md
public import VerifiedGarbage.Proof.Md5.AArch64.Stream.Init
public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Md5.AArch64.Stream.Md
meta import VerifiedGarbage.Proof.Md5.AArch64.Stream.Init
meta import VerifiedGarbage.Spec.Md5.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# MD5 on AArch64, as a Merkle–Damgård hash function

MD5 with its compression function, as a variant of `MdHash` (`variant`), from
which HMAC and PBKDF2 are emitted (`Generic/MdHash/AArch64/`): its streaming
code is the generic Merkle–Damgård code (`Stream.params`), its specification
`Spec.Hmac.md5S`. The facts about the code HMAC and PBKDF2 add, which do not
depend on the functions they call, are checked once (`coreOK`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Md5

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- MD5's functions. -/
def hash : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Md5.AArch64.Stream.params
  D := 16
  W := Spec.Hmac.md5I.scratch
  compN := Spec.Md5.compressApi.name
  compC := Impl.Md5.AArch64.compress
  initN := Spec.Md5.initApi.name
  initC := Impl.Md5.AArch64.Stream.init
  updN := Spec.Md5.updateScratchApi.name
  updC := Impl.Md5.AArch64.Stream.update
  finN := Spec.Md5.finalizeScratchApi.name
  finC := Impl.Md5.AArch64.Stream.finalize
  hmacInitN := "vg_hmac_md5_init_scratch"
  hmacFinN := "vg_hmac_md5_finalize_scratch"
  iterN := "vg_pbkdf2_hmac_md5_iterate"

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Md5.AArch64.Stream.params, 16, 48, "", .block [], "",
  .block [], "", .block [], "", .block [], "", "", ""⟩

theorem coreOK : CoreOK coreH := by
  refine {
    pbk := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    iter := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    hinit := {
      pro := ⟨?_, ?_⟩
      argI := List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩
      keys := ⟨?_, ?_⟩
      mid := ⟨?_, ?_⟩
      restore := ⟨?_, ?_⟩ }
    hfin := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    fitI := ?_
    fitF := ?_ }
  taint_decide_all

theorem anyOK : Any.AnyOK coreH := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

/-- The streaming functions, verified against the contracts HMAC's proofs
call them with. -/
def streamOK : Calls.StreamOK hash.stream where
  SH := Spec.Hmac.md5S
  Wb := 112
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by decide
  hF := by decide
  hD0 := by decide
  hS0 := by decide
  hSB := by decide
  hB0 := by decide
  hBB := by decide
  hWb := by decide
  hW := by decide
  repr := Hmac.Generic.Common.md5_repr
  init := Proof.Md5.AArch64.Stream.init_verified
  upd := Proof.Md5.AArch64.Stream.Update.update_verified
  fin := Proof.Md5.AArch64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
        rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Md5.AArch64.Stream.Finalize.finalize_verified.2.2 }
  initDepth := by decide +kernel
  updDepth := by decide +kernel
  finDepth := by decide +kernel

def ok : HashOK hash where
  initKeepsV := by decide +kernel
  updKeepsV := by lit_decide
  finKeepsV := by lit_decide
  md := Proof.Md5.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Md5.AArch64.Stream.shape
  comp := ⟨Proof.Md5.AArch64.Stream.callee.verified, Proof.Md5.AArch64.compress_verified.2.1,
    Proof.Md5.AArch64.Stream.callee.noFrames, Proof.Md5.AArch64.Stream.callee.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  lenOk _ _ := trivial
  stream := streamOK
  iv := Spec.Md5.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm
  sizes := ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  L := by decide
  W := by decide
  hPad := by decide
  L816 := by decide

theorem satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.md5I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.md5I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using initSat 80 48

theorem satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.md5I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.md5I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using finSat 80 16 48

theorem satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.md5I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.md5I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 80 16 48

theorem satA : ∃ s, (Any.anyScratchContract Spec.Hmac.md5I.S Spec.Hmac.md5I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.md5I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using initSat 80 128

theorem satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.md5I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi,
    AArch64.argRegs] using pbkSat 128

theorem satPF :
    ∃ s, (Spec.Hmac.md5I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.md5I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_md5 : Proof.RsaPss.AArch64.PssChecks coreH.P 16 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

/-- MD5 with its compression function. -/
def variant : MdHash := MdHash.of ok coreOK ⟨Spec.Mgf1.md5, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_md5 rfl rfl satI satF satT satP (by decide)
    anyOK satA (by decide) Proof.Hmac.md5_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) satPF
    "" []

end VG.Proof.Pbkdf2.Md.AArch64.Md5
