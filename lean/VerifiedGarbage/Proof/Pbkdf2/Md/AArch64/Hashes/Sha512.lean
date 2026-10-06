import VerifiedGarbage.Proof.Sha512.AArch64.Variant
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Sha512.AArch64.Shared
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# The SHA-512 family on AArch64, as Merkle–Damgård hash functions

SHA-384, SHA-512, SHA-512/224 and SHA-512/256, with their compression
function, as variants of `MdHash` (`sha384`, …), from which HMAC and PBKDF2
are emitted (`Generic/MdHash/AArch64/`). Their streaming code is the generic
Merkle–Damgård code (`Stream.params`), shared by the four, which differ in
their initial hash value `iv` and the size `D` of their digest, the first `D`
bytes of the final hash value. The facts about the code HMAC and PBKDF2 add,
which do not depend on the functions they call, are checked once for each
member (`coreOK`).
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha512

open VG.AArch64
open VG.Proof.Sha512.AArch64 (Compress)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open Spec.Sha512 (H0_384 H0_512 H0_512_224 H0_512_256)

/-- The member of the SHA-512 family of instance `I`, with a `D`-byte digest,
initial hash value `iv` and streaming `init` named `initN`. -/
def hash (v : Compress) (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Sha512.AArch64.Stream.params
  D := D
  W := I.scratch
  compN := v.name
  compC := v.code
  initN := initN
  initC := Impl.Sha512.AArch64.Stream.init iv
  updN := Spec.Sha512.updateScratchApi.name ++ v.suffix
  updC := v.update
  finN := Spec.Sha512.finalizeScratchApi.name ++ v.suffix
  finC := v.finalize
  hmacInitN := I.initScratchApi.name ++ v.suffix
  hmacFinN := I.finalizeScratchApi.name ++ v.suffix
  iterN := I.iterateApi.name ++ v.suffix

/-- A member of the family without the functions it calls. -/
def coreH (D : Nat) : Hash :=
  ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha512.AArch64.Stream.params, D, 234, "", .block [], "", .block [], "", .block [], "", .block [], "", "", ""⟩

theorem coreOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : CoreOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> refine {
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
      fitF := ?_
  }
  taint_decide_all

/-- The initial hash values of the family. -/
abbrev IVs (iv : Spec.Sha512.HashValue) : Prop := iv = H0_384 ∨ iv = H0_512 ∨ iv = H0_512_224 ∨ iv = H0_512_256

section
variable (v : Compress)
variable {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}

/-- The streaming functions of the member of instance `I`, verified against
the contracts HMAC's proofs call them with. -/
def streamOK (hR : I.S.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, I.S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hiv : IVs iv) :
    Calls.StreamOK (hash v I D initN iv).stream where
  SH := I.S
  Wb := Impl.Sha512.AArch64.scratchBytes + 48
  hS := hS
  hD := hDs
  hB := hB
  hDF := by show D ≤ 64; omega
  hF := Nat.le_refl 64
  hD0 := by show 0 < D; omega
  hS0 := show 0 < 192 by decide
  hSB := show 192 ≤ 256 by decide
  hB0 := show 0 < 128 by decide
  hBB := Nat.le_refl 128
  hWb := by show Impl.Sha512.AArch64.scratchBytes + 48 ≤ 8 * ((Impl.Sha512.AArch64.Stream.params.so + 48) / 8); decide
  hW := by show (Impl.Sha512.AArch64.Stream.params.so + 48) / 8 ≤ 134; decide
  repr := hR ▸ Hmac.Generic.Common.sha512_repr iv
  init := hR ▸ Proof.Sha512.AArch64.Stream.init_verified iv
  upd := hR ▸ v.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.update_verified.2.2 }
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := v.finalize_verified.2.2 }
  initDepth := by
    show (Impl.Sha512.AArch64.Stream.init iv).aarch64Depth ≤ 1
    rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  updDepth := by show v.update.aarch64Depth ≤ 1; rw [v.update_depth]
  finDepth := by show v.finalize.aarch64Depth ≤ 1; rw [v.finalize_depth]

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok (hR : I.S.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, I.S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hW : I.scratch = 234) (hiv : IVs iv) :
    HashOK (hash v I D initN iv) where
  initKeepsV := by rfl
  updKeepsV := v.update_keepsV
  finKeepsV := v.finalize_keepsV
  md := Proof.Sha512.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Sha512.AArch64.Stream.shape
  comp := ⟨v.verified.1, v.verified.2.1, v.noFrames, v.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  lenOk _ h := h
  stream := streamOK v hR hh hB hS hDs hD hiv
  iv := iv
  repr _ _ _ := by show I.S.Repr _ _ _ ↔ _; rw [hR]; exact Proof.Sha512.repr_iff
  hash := hh
  sizes := by
    show Pbkdf2.AArch64.Sizes (Impl.Pbkdf2.AArch64.ofMd Impl.Sha512.AArch64.Stream.params) D I.scratch
    rw [hW]
    rcases hD with rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩
  L := by show 0 < Impl.Sha512.AArch64.Stream.params.L ∧ Impl.Sha512.AArch64.Stream.params.L ≤ 16; decide
  W := by show I.scratch ≤ 256; omega

end

/-- Streaming wrappers shared by all four digest sizes. The SHA-512 member
emits them once per backend through `MdHash`; the other members call them:
`update` and `finalize`, which keep their working space in a frame of their
own, and `update_scratch` and `finalize_scratch`, which HMAC's, PBKDF2's and
Ed25519's code calls with theirs. -/
def stream (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.updateApi
    code := Impl.StackScratch.AArch64.withStackScratch 1376 .x4 v.update
    contract := Spec.Sha512.updateContract AArch64.abi (16 + 1376)
    stack := 16 + 1376
    verified := Proof.Sha512.AArch64.Shared.update_of v.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.finalizeApi
    code := Impl.StackScratch.AArch64.withStackScratch 1376 .x3 v.finalize
    contract := Spec.Sha512.finalizeContract AArch64.abi (16 + 1376)
    stack := 16 + 1376
    verified := Proof.Sha512.AArch64.Shared.finalize_of v.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.updateScratchApi
    code := v.update
    contract := Spec.Sha512.updateScratchContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha512.AArch64.Shared.updateScratch_of v.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.finalizeScratchApi
    code := v.finalize
    contract := Spec.Sha512.finalizeScratchContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha512.AArch64.Shared.finalizeScratch_of v.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-! ## SHA-384 -/

theorem sha384_satI : ∃ s, (Spec.Hmac.sha384I.initScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha384I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha384_satF : ∃ s, (Spec.Hmac.sha384I.finalizeScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha384I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using finSat 192 48 234

theorem sha384_satT : ∃ s, (Spec.Hmac.sha384I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha384I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 48 234

theorem sha384_satP : ∃ s, (Spec.Hmac.sha384I.pbkdf2ScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha384_satPF :
    ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha384I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha384 : Proof.RsaPss.AArch64.PssChecks (coreH 48).P 48 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha384_coreOK : CoreOK (coreH 48) := coreOK 48 (Or.inr (Or.inr (Or.inl rfl)))

/-- SHA-384 with its compression function, which it carries for the
functions built on SHA-384 alone (`MdHash.sha384`). -/
def sha384 (v : Compress) : MdHash :=
  { MdHash.of (H := hash v Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl (Or.inl rfl)) sha384_coreOK ⟨Spec.Mgf1.sha384, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha384 rfl rfl
    sha384_satI sha384_satF sha384_satT sha384_satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha384_satPF
    v.suffix v.features with
    sha384 := some v }

/-! ## SHA-512 -/

theorem sha512_satI : ∃ s, (Spec.Hmac.sha512I.initScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha512I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_satF : ∃ s, (Spec.Hmac.sha512I.finalizeScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using finSat 192 64 234

theorem sha512_satT : ∃ s, (Spec.Hmac.sha512I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 64 234

theorem sha512_satP : ∃ s, (Spec.Hmac.sha512I.pbkdf2ScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_satPF :
    ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha512I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha512 : Proof.RsaPss.AArch64.PssChecks (coreH 64).P 64 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_coreOK : CoreOK (coreH 64) := coreOK 64 (Or.inr (Or.inr (Or.inr rfl)))

/-- SHA-512 with its compression function. -/
def sha512 (v : Compress) : MdHash :=
  { MdHash.of (H := hash v Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512)
    (ok v rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm) rfl rfl rfl (Or.inr (Or.inr (Or.inr rfl))) rfl (Or.inr (Or.inl rfl))) sha512_coreOK ⟨Spec.Mgf1.sha512, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512 rfl rfl
    sha512_satI sha512_satF sha512_satT sha512_satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_satPF
    v.suffix v.features (stream v) with
    sha512 := some v }

/-! ## SHA-512/224 -/

theorem sha512_224_satI : ∃ s, (Spec.Hmac.sha512_224I.initScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha512_224I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_224_satF : ∃ s, (Spec.Hmac.sha512_224I.finalizeScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512_224I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using finSat 192 28 234

theorem sha512_224_satT : ∃ s, (Spec.Hmac.sha512_224I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_224I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 28 234

theorem sha512_224_satP : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2ScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_224_satPF :
    ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha512_224I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha512_224 : Proof.RsaPss.AArch64.PssChecks (coreH 28).P 28 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_224_coreOK : CoreOK (coreH 28) := coreOK 28 (Or.inl rfl)

/-- SHA-512/224 with its compression function. -/
def sha512_224 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl) rfl (Or.inr (Or.inr (Or.inl rfl)))) sha512_224_coreOK ⟨Spec.Mgf1.sha512_224, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512_224 rfl rfl
    sha512_224_satI sha512_224_satF sha512_224_satT sha512_224_satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_224_satPF
    v.suffix v.features

/-! ## SHA-512/256 -/

theorem sha512_256_satI : ∃ s, (Spec.Hmac.sha512_256I.initScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha512_256I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_256_satF : ∃ s, (Spec.Hmac.sha512_256I.finalizeScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512_256I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using finSat 192 32 234

theorem sha512_256_satT : ∃ s, (Spec.Hmac.sha512_256I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_256I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 32 234

theorem sha512_256_satP : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2ScratchContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_256_satPF :
    ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha512_256I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha512_256 : Proof.RsaPss.AArch64.PssChecks (coreH 32).P 32 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_256_coreOK : CoreOK (coreH 32) := coreOK 32 (Or.inr (Or.inl rfl))

/-- SHA-512/256 with its compression function. -/
def sha512_256 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl)) rfl (Or.inr (Or.inr (Or.inr rfl)))) sha512_256_coreOK ⟨Spec.Mgf1.sha512_256, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512_256 rfl rfl
    sha512_256_satI sha512_256_satF sha512_256_satT sha512_256_satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_256_satPF
    v.suffix v.features

end VG.Proof.Pbkdf2.Md.AArch64.Sha512
