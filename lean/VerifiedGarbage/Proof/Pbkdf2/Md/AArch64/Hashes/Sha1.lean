module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha1.AArch64.Variant
public import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Init
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha1.AArch64.Shared
meta import VerifiedGarbage.Proof.Sha1.AArch64.OneShot
meta import VerifiedGarbage.Proof.Sha1.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Init
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Sha1.AArch64.Shared
public import VerifiedGarbage.Proof.Sha1.AArch64.OneShot

/-!
# SHA-1 on AArch64, as a Merkle–Damgård hash function

SHA-1 with its compression function, as a variant of `MdHash` (`variant`),
from which HMAC and PBKDF2 are emitted (`Generic/MdHash/AArch64/`): its
streaming code is the generic Merkle–Damgård code (`Stream.params`), its
specification `Spec.Hmac.sha1S`. The facts about the code HMAC and PBKDF2 add,
which do not depend on the functions they call, are checked once (`coreOK`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha1

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Sha1.AArch64 (Compress)

/-- SHA-1's functions. -/
def hash (v : Compress) : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Sha1.AArch64.Stream.params
  D := 20
  W := Spec.Hmac.sha1I.scratch
  compN := v.name
  compC := v.code
  initN := Spec.Sha1.initApi.name
  initC := Impl.Sha1.AArch64.Stream.init
  updN := Spec.Sha1.updateScratchApi.name ++ v.suffix
  updC := v.update
  finN := Spec.Sha1.finalizeScratchApi.name ++ v.suffix
  finC := v.finalize
  hmacInitN := "vg_hmac_sha1_init_scratch" ++ v.suffix
  hmacFinN := "vg_hmac_sha1_finalize_scratch" ++ v.suffix
  iterN := "vg_pbkdf2_hmac_sha1_iterate" ++ v.suffix

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha1.AArch64.Stream.params, 20, 56, "", .block [], "",
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

variable (v : Compress)

/-- The streaming functions, verified against the contracts HMAC's proofs
call them with. -/
def streamOK : Calls.StreamOK (hash v).stream where
  SH := Spec.Hmac.sha1S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by simp only [hash, Hash.stream] <;> decide
  hF := by simp only [hash, Hash.stream] <;> decide
  hD0 := by simp only [hash, Hash.stream] <;> decide
  hS0 := by simp only [hash, Hash.stream, Hash.S] <;> decide
  hSB := by simp only [hash, Hash.stream, Hash.S] <;> decide
  hB0 := by simp only [hash, Hash.stream] <;> decide
  hBB := by simp only [hash, Hash.stream] <;> decide
  hWb := by simp only [hash, Hash.stream] <;> decide
  hW := by simp only [hash, Hash.stream] <;> decide
  repr := Hmac.Generic.Common.sha1_repr
  init := Proof.Sha1.AArch64.Stream.init_verified
  upd := v.update_verified
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finalize_verified.2.2 }
  initDepth := by simp only [hash, Hash.stream] <;> decide +kernel
  updDepth := by
    show (Impl.MdStream.AArch64.update _ v.name v.code).aarch64Depth ≤ 1
    simp only [Impl.MdStream.AArch64.update, Code.aarch64Depth, v.updateDepth]; decide
  finDepth := by
    show (Impl.MdStream.AArch64.finalize _ v.name v.code).aarch64Depth ≤ 1
    simp only [Impl.MdStream.AArch64.finalize, Code.aarch64Depth, v.finalizeDepth]; decide

def ok : HashOK (hash v) where
  initKeepsV := by rfl
  updKeepsV := MdStream.AArch64.update_keepsV v.keepsV
  finKeepsV := MdStream.AArch64.finalize_keepsV Proof.Sha1.AArch64.Stream.shape v.keepsV
  md := Proof.Sha1.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Sha1.AArch64.Stream.shape
  comp := ⟨v.callee.verified, v.verified.2.1, v.noFrames, v.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega)
  lenOk _ _ := trivial
  stream := streamOK v
  iv := Spec.Sha1.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm
  sizes := ⟨⟨by simp only [hash] <;> decide, by simp only [hash] <;> decide, by simp only [hash] <;> decide,
      by simp only [hash] <;> decide⟩,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide⟩
  L := by simp only [hash] <;> decide
  W := by simp only [hash] <;> decide
  hPad := by simp only [hash] <;> decide
  L816 := by simp only [hash] <;> decide

theorem satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha1I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha1I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using initSat 84 56

theorem satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha1I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha1I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using finSat 84 20 56

theorem satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha1I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha1I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 84 20 56

theorem satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha1I.S Spec.Hmac.sha1I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha1I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using initSat 84 140

theorem satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha1I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi,
    AArch64.argRegs] using pbkSat 140

theorem satPF :
    ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha1I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- The streaming `update` and `finalize` made with `v`, which keep their
working space in a frame of their own, `update_scratch` and
`finalize_scratch`, which HMAC's and PBKDF2's code calls with theirs, and the
one-shot `digest` (`Proof/Sha1/AArch64/OneShot.lean`), which
`Generic/MdHash/AArch64/Stream.lean` emits. -/
def stream : List StreamFn := [
  { api := Spec.Sha1.updateApi
    code := Impl.StackScratch.AArch64.withStackScratch 160 .x4 v.update
    contract := Spec.Sha1.updateContract AArch64.abi (16 + 160)
    stack := 16 + 160
    verified := Proof.Sha1.AArch64.Shared.update_of v.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha1.finalizeApi
    code := Impl.StackScratch.AArch64.withStackScratch 160 .x3 v.finalize
    contract := Spec.Sha1.finalizeContract AArch64.abi (16 + 160)
    stack := 16 + 160
    verified := Proof.Sha1.AArch64.Shared.finalize_of v.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha1.updateScratchApi
    code := v.update
    contract := Spec.Sha1.updateScratchContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha1.AArch64.Shared.updateScratch_of v.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha1.finalizeScratchApi
    code := v.finalize
    contract := Spec.Sha1.finalizeScratchContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha1.AArch64.Shared.finalizeScratch_of v.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha1.digestApi
    code := Proof.Sha1.AArch64.oneShotWith v.name v.code
    contract := Spec.Sha1.digestContract AArch64.abi Proof.Sha1.AArch64.OneShot.stack
    stack := Proof.Sha1.AArch64.OneShot.stack
    verified := v.oneShot_verified.of_implies Proof.Sha1.AArch64.OneShot.implies
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha1 : Proof.RsaPss.AArch64.PssChecks coreH.P 20 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

/-- Every construction follows the registered compression backend. -/
def variant : MdHash :=
  MdHash.of (ok v) coreOK ⟨Spec.Mgf1.sha1, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha1 rfl rfl satI satF satT satP (by decide)
    anyOK satA (by decide) Proof.Hmac.sha1_local
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
    v.suffix v.features (stream v)

end VG.Proof.Pbkdf2.Md.AArch64.Sha1
