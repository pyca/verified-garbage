module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Proof.Sm4.CbcScratch
public import VerifiedGarbage.Proof.Sm4.FbScratch
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModeCore
import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
public import VerifiedGarbage.Impl.Modes.Ops
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Ofb
public import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedBody
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.PreparedBody

/-!
# SM4's modes on PPC64LE meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/PPC64LE/` over SM4's core (`dirCoreSpec`), with the working
space as the fifth argument (`modeContract`), meet the contracts with a
scratch buffer of 408 words (`Proof.Sm4.cbcEncChainedScratchContract`,
`fbScratchContract`).
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.Modes

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S)
open VG.Proof.Sm4.PPC64LE (dirCoreSpec KeyArgs modeContract modePub)

/-- SM4 under the schedule at `r3`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .r3))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .r3))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .r4) 16
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .r5) (s.gpr .r6).toNat

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

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Dir)
    (hstep : M.step = 16) {s : State} (h : (modeContract 16 post).pre s) :
    SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, -, fV, fD, fS⟩ := h
  have e16 : 4 * (dirCore d).bw = 16 := rfl
  have eS : scrRegion (dirCore d) (S s) = ⟨s.gpr .r7, 8 * (slots + 6)⟩ := rfl
  have eV : ivR s (dirCore d) = ⟨s.gpr .r4, 16⟩ := rfl
  refine ⟨⟨by rw [hwr]; simp [dirCore], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [e16]; exact fV, by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dDS,
    by rw [eV, eS]; exact dVS, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega, by rw [e16]; omega⟩,
    (dirCoreSpec d).layout⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (d : Dir)
    (hstep : M.step = 16) {s : State} (h : (modeContract 16 post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 (dirCore d) M s) (Spec.Sm4.scheduleAt s.mem (s.gpr .r3)) := by
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, fK, -, -, -⟩ := h
  refine ⟨_, rfl, rfl, by rw [hrd]; exact List.mem_singleton_self _, fK, fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .r3) 128).Disjoint ⟨s.gpr .r5, M.step * (s.gpr .r6).toNat⟩
    rw [hstep]; exact dKD
  · exact dKS

/-! ## Correctness -/

theorem cipher_enc (k : Spec.Sm4.Schedule) : (dirCoreSpec .encrypt).cipher k = Spec.Sm4.cipher k := by
  simp only [dirCoreSpec, Proof.Sm4.PPC64LE.dirCipher]
theorem cipher_dec (k : Spec.Sm4.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.Sm4.invCipher k := by
  simp only [dirCoreSpec, Proof.Sm4.PPC64LE.dirCipher]

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract 16 cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 16 cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcEncChained_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cbcEncChained 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cbcEncChained 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract 16 cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 16 cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcDecChained_wp (dirCoreSpec .decrypt)
    (seqPre_of .decrypt (M := Mode.cbcDecChained 4) rfl hs)
    (keyArgs_of .decrypt (M := Mode.cbcDecChained 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_dec] at h2 h3; exact ⟨h1, h2, h3⟩

theorem ofb_correct (s : State) (hs : (modeContract 16 ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract 16 ofbPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.ofb_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.ofb 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ofb 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract 16 cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 16 cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbEnc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbEnc 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cfbEnc 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract 16 cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 16 cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbDec_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbDec 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cfbDec 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
the IV at `0x2000`, no data at `0x3000`, and the scratch buffer at `0x4000`. -/
def modeSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 3264⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified target cbcEncryptChained (Proof.Sm4.cbcEncChainedScratchContract abi (slots + 6)) := by
  refine Verified.of_correct cbcEncryptChained_correct cbcEncryptChained_constantTime ?_
  sig_implies [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig,
    Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, abi, argRegs, modeContract, cbcEncPost,
    modePub_iff, slots_eq] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified target cbcDecryptChained (Proof.Sm4.cbcDecChainedScratchContract abi (slots + 6)) := by
  refine Verified.of_correct cbcDecryptChained_correct cbcDecryptChained_constantTime ?_
  sig_implies [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig,
    Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, abi, argRegs, modeContract, cbcDecPost,
    modePub_iff, slots_eq] [modeSat] using modeSat

theorem ofb_verified :
    Verified target ofb (Proof.Sm4.fbScratchContract abi (slots + 6) Proof.Sm4.ofbPost) := by
  refine Verified.of_correct ofb_correct ofb_constantTime ?_
  sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
    Proof.Sm4.ofbPost, abi, argRegs, modeContract, ofbPost, modePub_iff, slots_eq] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified target cfbEncrypt (Proof.Sm4.fbScratchContract abi (slots + 6) Proof.Sm4.cfbEncPost) := by
  refine Verified.of_correct cfbEncrypt_correct cfbEncrypt_constantTime ?_
  sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
    Proof.Sm4.cfbEncPost, abi, argRegs, modeContract, cfbEncPost, modePub_iff, slots_eq] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified target cfbDecrypt (Proof.Sm4.fbScratchContract abi (slots + 6) Proof.Sm4.cfbDecPost) := by
  refine Verified.of_correct cfbDecrypt_correct cfbDecrypt_constantTime ?_
  sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
    Proof.Sm4.cfbDecPost, abi, argRegs, modeContract, cfbDecPost, modePub_iff, slots_eq] [modeSat] using modeSat

end VG.Proof.Sm4.PPC64LE.Modes
