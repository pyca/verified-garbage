module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha256.AArch64.OneShot
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha256.AArch64.Shared
meta import VerifiedGarbage.Proof.Sha256.AArch64.OneShot
meta import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Sha256.AArch64.Shared
meta import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Md
meta import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Md

/-!
# SHA-224 on AArch64, as a Merkle–Damgård hash function

SHA-224 with an implementation of SHA-256's compression function, as a variant
of `MdHash` (`variant`), from which HMAC and PBKDF2 are emitted
(`Generic/MdHash/AArch64/`): its streaming code is SHA-256's, the generic
Merkle–Damgård code (`Stream.params`) from SHA-224's initial hash value
(`vg_sha224_init`), its specification `Spec.Hmac.sha224S`, with the digest the
first 28 bytes of the final hash value. The facts about the code HMAC and
PBKDF2 add, which do not depend on the functions they call, are checked once
(`coreOK`).

Its streaming `update` is SHA-256's, which SHA-256's variants carry
(`Proof/Pbkdf2/Md/AArch64/Hashes/Sha256.lean`); SHA-224's carry its own
`finalize`, which writes its digest (`stream v`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha224

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Impl.MdStream.AArch64 (out32)

/-- SHA-224's functions, calling the implementation `v` of SHA-256's
compression function and SHA-256's streaming functions made with it, named
with its suffix. -/
def hash (v : Compress) : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Sha256.AArch64.Stream.params
  D := 28
  W := Spec.Hmac.sha224I.scratch
  compN := v.name
  compC := v.code
  initN := Spec.Sha256.init224Api.name
  initC := Impl.Sha256.AArch64.Stream.init224
  updN := Spec.Sha256.updateScratchApi.name ++ v.suffix
  updC := v.update
  finN := Spec.Sha256.finalizeScratchApi.name ++ v.suffix
  finC := v.finalize
  hmacInitN := "vg_hmac_sha224_init_scratch" ++ v.suffix
  hmacFinN := "vg_hmac_sha224_finalize_scratch" ++ v.suffix
  iterN := "vg_pbkdf2_hmac_sha224_iterate" ++ v.suffix

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha256.AArch64.Stream.params, 28, 104, "", .block [], "",
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

/-- The representation moves with the state's bytes. -/
theorem sha224_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m p msg) :
    Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc h (by omega)
  · rw [← hr.2]
    exact Hmac.Generic.Common.bytesAt_reloc h (o := 32) (k := msg.length % 64) (by omega)

variable (v : Compress)

/-- The streaming functions, verified against the contracts HMAC's proofs
call them with. -/
def streamOK : Calls.StreamOK (hash v).stream where
  SH := Spec.Hmac.sha224S
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
  repr := sha224_repr
  init := Proof.Sha256.AArch64.Stream.init224_verified
  upd := v.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0_224 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.update_verified.2.2 }
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 28 (Spec.Sha256.bytesAt s'.mem _ 32) = Spec.Sha256.sha224 m
        rw [h Spec.Sha256.H0_224 m hr hc]
        rfl
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
  finKeepsV := MdStream.AArch64.finalize_keepsV Proof.Sha256.AArch64.Stream.shape v.keepsV
  md := Proof.Sha256.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Sha256.AArch64.Stream.shape
  comp := ⟨v.callee.verified, v.verified.2.1, v.noFrames, v.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  lenOk _ _ := trivial
  stream := streamOK v
  iv := Spec.Sha256.H0_224
  repr _ _ _ := Iff.rfl
  hash _ := rfl
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

theorem satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs] using initSat 96 104

theorem satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha224I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs] using finSat 96 28 104

theorem satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha224I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha224I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 96 28 104

theorem satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha224I.S Spec.Hmac.sha224I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha224I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs] using initSat 96 200

theorem satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi,
    AArch64.argRegs] using pbkSat 200

theorem satPF :
    ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha224I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha224 : Proof.RsaPss.AArch64.PssChecks coreH.P 28 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

/-- SHA-224's `finalize` made with `v`, which writes its digest
(`Compress.finalize224`). -/
def stream : List StreamFn := [
  { api := Spec.Sha256.finalize224Api
    code := Impl.StackScratch.AArch64.withStackScratch 608 .x3 v.finalize224
    contract := Spec.Sha256.finalize224Contract AArch64.abi (16 + 608)
    stack := 16 + 608
    verified := Proof.Sha256.AArch64.Shared.finalize224_of v.finalize224_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha256.digest224Api
    code := Proof.Sha256.AArch64.oneShotWith (out32 7 true) Spec.Sha256.H0_224 v.name
      v.code
    contract := Spec.Sha256.digestContract AArch64.abi 28 Spec.Sha256.sha224 Proof.Sha256.AArch64.OneShot.stack
    stack := Proof.Sha256.AArch64.OneShot.stack
    verified := (v.oneShot_verified (by decide) Proof.Sha256.AArch64.Stream.shape224 v.oneShot224).of_implies
        (Proof.Sha256.AArch64.OneShot.implies (by decide) Proof.Sha256.AArch64.OneShot.sha224_take)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-- SHA-224 with the implementation `v` of SHA-256's compression function.
Its streaming `update` is SHA-256's, which SHA-256's variant with `v`
carries, and its `finalize` its own (`stream v`); it carries `v` for
deterministic ECDSA's functions (`MdHash.sha224`). -/
def variant : MdHash :=
  { MdHash.of (ok v) coreOK ⟨Spec.Mgf1.sha224, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha224 rfl rfl satI satF satT satP (by decide)
    anyOK satA (by decide) Proof.Hmac.sha224_local
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
    v.suffix v.features (stream v) with
    sha224 := some v }

end VG.Proof.Pbkdf2.Md.AArch64.Sha224
