module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesConstantTime
public import VerifiedGarbage.Proof.Seed.CbcScratch
public import VerifiedGarbage.Proof.Seed.FbScratch
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModeCore
import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
import VerifiedGarbage.Proof.Modes.PPC64LE.Wide
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
public import VerifiedGarbage.Impl.Modes.Ops
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Ofb

/-!
# SEED's modes on PPC64LE meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/PPC64LE/` over SEED's core (`Mode.dirCoreSpec`), with the
working space as the fifth argument (`modeContract`), meet the contracts
with a scratch buffer of 144 words (174 for CBC and CFB decryption) (`Proof.Seed.cbcEncChainedScratchContract`,
`fbScratchContract`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.Modes

open VG VG.PPC64LE VG.Impl.Seed.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S)
open VG.Proof.Seed.PPC64LE (modePub modeContract)
open VG.Proof.Seed.PPC64LE.Mode (coreSpec dirCoreSpec wideCoreSpec KeyArgs)

/-- SEED under the schedule at `r3`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt s.mem (s.gpr .r3))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Seed.invCipher (Spec.Seed.scheduleAt s.mem (s.gpr .r3))
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

/-- `modeContract`'s precondition, with a working space of `w` words, gives
the modes' over the core on `g` blocks, of `w` slots. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Spec.Seed.Direction) {g w : Nat}
    (hg : 0 < g ∧ g ≤ 16) (hw : w = bufSlot + 2 * g + 6)
    (hstep : M.step = 16) {s : State} (h : (modeContract w post).pre s) :
    SeqPre (core d g) M s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h
  subst hw
  have e16 : 4 * (core d g).bw = 16 := rfl
  have eS : scrRegion (core d g) (S s) = ⟨s.gpr .r7, 8 * (bufSlot + 2 * g + 6)⟩ := rfl
  have eV : ivR s (core d g) = ⟨s.gpr .r4, 16⟩ := rfl
  refine ⟨⟨by rw [hwr]; simp [core], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [e16]; exact fV, by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dDS,
    by rw [eV, eS]; exact dVS, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega, by rw [e16]; omega⟩,
    (coreSpec d g hg).layout⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (d : Spec.Seed.Direction) {g w : Nat}
    (hw : w = bufSlot + 2 * g + 6) (hstep : M.step = 16) {s : State} (h : (modeContract w post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 (core d g) M s) (Spec.Seed.scheduleAt s.mem (s.gpr .r3)) := by
  subst hw
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, -, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_singleton_self _, fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .r3) 128).Disjoint ⟨s.gpr .r5, M.step * (s.gpr .r6).toNat⟩
    rw [hstep]; exact dKD
  · exact dKS

/-! ## Correctness -/

theorem cipher_enc {g : Nat} {hg : 0 < g ∧ g ≤ 16} (k : Spec.Seed.Schedule) :
    (coreSpec .encrypt g hg).cipher k = Spec.Seed.cipher k := by
  simp only [coreSpec, Proof.Seed.dirCipher]
theorem cipher_dec {g : Nat} {hg : 0 < g ∧ g ≤ 16} (k : Spec.Seed.Schedule) :
    (coreSpec .decrypt g hg).cipher k = Spec.Seed.invCipher k := by
  simp only [coreSpec, Proof.Seed.dirCipher]

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract 144 cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 144 cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcEncChained_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (g := 1) (by decide) rfl (M := Mode.cbcEncChained 4) rfl hs)
    (keyArgs_of .encrypt (g := 1) rfl (M := Mode.cbcEncChained 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract 174 cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 174 cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcDecWide_wp (wideCoreSpec .decrypt) (lg := 4) (by decide) (by decide) (by decide)
    (seqPre_of .decrypt (g := 16) (by decide) rfl (M := Mode.cbcDecChained 4) rfl hs)
    (keyArgs_of .decrypt (g := 16) rfl (M := Mode.cbcDecChained 4) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => by simp only [cipher_dec] at h2 h3; exact ⟨h1, h2, h3⟩

theorem ofb_correct (s : State) (hs : (modeContract 144 ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract 144 ofbPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.ofb_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (g := 1) (by decide) rfl (M := Mode.ofb 4) rfl hs)
    (keyArgs_of .encrypt (g := 1) rfl (M := Mode.ofb 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract 144 cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 144 cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbEnc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (g := 1) (by decide) rfl (M := Mode.cfbEnc 4) rfl hs)
    (keyArgs_of .encrypt (g := 1) rfl (M := Mode.cfbEnc 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract 174 cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 174 cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbDecWide_wp (wideCoreSpec .encrypt) (lg := 4) (by decide) (by decide) (by decide)
    (seqPre_of .encrypt (g := 16) (by decide) rfl (M := Mode.cfbDecEarly 4) rfl hs)
    (keyArgs_of .encrypt (g := 16) rfl (M := Mode.cfbDecEarly 4) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

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
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 1152⟩]

/-- `modeSat`, with the working space of sixteen blocks' core. -/
def modeSatW : State := { modeSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 1392⟩] }

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified target cbcEncryptChained (Proof.Seed.cbcEncChainedScratchContract abi 144) := by
  refine Verified.of_correct cbcEncryptChained_correct cbcEncryptChained_constantTime ?_
  sig_implies [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig,
    Spec.Seed.cbcChainedSig, Proof.Seed.cbcEncChainedPost, abi, argRegs, modeContract, cbcEncPost,
    modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified target cbcDecryptChained (Proof.Seed.cbcDecChainedScratchContract abi 174) := by
  refine Verified.of_correct cbcDecryptChained_correct cbcDecryptChained_constantTime ?_
  sig_implies [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig,
    Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, abi, argRegs, modeContract, cbcDecPost,
    modePub_iff] [modeSatW, modeSat] using modeSatW

theorem ofb_verified :
    Verified target ofb (Proof.Seed.fbScratchContract abi 144 Proof.Seed.ofbPost) := by
  refine Verified.of_correct ofb_correct ofb_constantTime ?_
  sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig,
    Proof.Seed.ofbPost, abi, argRegs, modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified target cfbEncrypt (Proof.Seed.fbScratchContract abi 144 Proof.Seed.cfbEncPost) := by
  refine Verified.of_correct cfbEncrypt_correct cfbEncrypt_constantTime ?_
  sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig,
    Proof.Seed.cfbEncPost, abi, argRegs, modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified target cfbDecrypt (Proof.Seed.fbScratchContract abi 174 Proof.Seed.cfbDecPost) := by
  refine Verified.of_correct cfbDecrypt_correct cfbDecrypt_constantTime ?_
  sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig,
    Proof.Seed.cfbDecPost, abi, argRegs, modeContract, cfbDecPost, modePub_iff] [modeSatW, modeSat] using modeSatW

end VG.Proof.Seed.PPC64LE.Modes
