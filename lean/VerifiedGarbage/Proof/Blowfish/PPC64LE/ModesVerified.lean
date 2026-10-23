module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Proof.Blowfish.CbcScratch
public import VerifiedGarbage.Proof.Blowfish.FbScratch
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModeCore
import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit

/-!
# Blowfish's modes on PPC64LE meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/PPC64LE/` over Blowfish's core (`Mode.dirCoreSpec`), with the
working space as the fifth argument (`modeContract`), meet the contracts
with a scratch buffer of 12 words (`Proof.Blowfish.cbcEncChainedScratchContract`,
`fbScratchContract`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE.Modes

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S)
open VG.Proof.Blowfish.PPC64LE.Mode (dirCoreSpec KeyArgs layout)

/-- Blowfish under the schedule at `r3`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .r3))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Blowfish.invCipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .r3))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .r4) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Blowfish.cbcBlocksAt m (s.gpr .r5) (s.gpr .r6).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (s.gpr .r6).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- A mode's function on PPC64LE with its working space as the fifth
argument, and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 4168⟩
    let iv : Region := ⟨s.gpr .r4, 8⟩
    let data : Region := ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 8 * 12⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r4).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 8 * 12 ≤ 2 ^ 64
  post := post
  pub := modePub

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (up : Bool) (hstep : M.step = 8) {s : State}
    (h : (modeContract post).pre s) : SeqPre (dirCore up) M s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h
  have e8 : 4 * (dirCore up).bw = 8 := rfl
  have eS : scrRegion (dirCore up) (S s) = ⟨s.gpr .r7, 8 * 12⟩ := rfl
  have eV : ivR s (dirCore up) = ⟨s.gpr .r4, 8⟩ := rfl
  refine ⟨⟨by rw [hwr]; simp [dirCore], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [e8]; exact fV, by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dDS,
    by rw [eV, eS]; exact dVS, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega, by rw [e8]; omega⟩, layout up⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (up : Bool) (hstep : M.step = 8) {s : State}
    (h : (modeContract post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 (dirCore up) M s) (Spec.Blowfish.scheduleAt s.mem (s.gpr .r3)) := by
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, -, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .r3) 4168).Disjoint ⟨s.gpr .r5, M.step * (s.gpr .r6).toNat⟩
    rw [hstep]; exact dKD
  · exact dKS

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Blowfish.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n :=
  Proof.Blowfish.cbcBlocksAt_eq m p n

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcEncChained_wp (dirCoreSpec true)
    (seqPre_of true (M := Mode.cbcEncChained 2) rfl hs) (keyArgs_of true (M := Mode.cbcEncChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcDecChained_wp (dirCoreSpec false)
    (seqPre_of false (M := Mode.cbcDecChained 2) rfl hs) (keyArgs_of false (M := Mode.cbcDecChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem ofb_correct (s : State) (hs : (modeContract ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract ofbPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.ofb_wp (dirCoreSpec true)
    (seqPre_of true (M := Mode.ofb 2) rfl hs) (keyArgs_of true (M := Mode.ofb 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbEnc_wp (dirCoreSpec true)
    (seqPre_of true (M := Mode.cfbEnc 2) rfl hs) (keyArgs_of true (M := Mode.cfbEnc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbDec_wp (dirCoreSpec true)
    (seqPre_of true (M := Mode.cfbDec 2) rfl hs) (keyArgs_of true (M := Mode.cfbDec 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
the IV at `0x3000`, no data at `0x4000`, and the scratch buffer at `0x5000`. -/
def modeSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 0x4000 | .r7 => 0x5000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 0⟩, ⟨0x5000, 96⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified target cbcEncryptChained (Proof.Blowfish.cbcEncChainedScratchContract abi 12) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  sig_implies [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig,
    Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, abi, argRegs, modeContract, cbcEncPost,
    modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified target cbcDecryptChained (Proof.Blowfish.cbcDecChainedScratchContract abi 12) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  sig_implies [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig,
    Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, abi, argRegs, modeContract, cbcDecPost,
    modePub_iff] [modeSat] using modeSat

theorem ofb_verified :
    Verified target ofb (Proof.Blowfish.fbScratchContract abi 12 Proof.Blowfish.ofbPost) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
    Proof.Blowfish.ofbPost, abi, argRegs, modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified target cfbEncrypt (Proof.Blowfish.fbScratchContract abi 12 Proof.Blowfish.cfbEncPost) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
    Proof.Blowfish.cfbEncPost, abi, argRegs, modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified target cfbDecrypt (Proof.Blowfish.fbScratchContract abi 12 Proof.Blowfish.cfbDecPost) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
    Proof.Blowfish.cfbDecPost, abi, argRegs, modeContract, cfbDecPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Blowfish.PPC64LE.Modes
