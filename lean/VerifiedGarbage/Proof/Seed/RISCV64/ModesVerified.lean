module

public import VerifiedGarbage.Proof.Seed.RISCV64.ModesConstantTime
public import VerifiedGarbage.Proof.Seed.RISCV64.ModeCore
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Modes.RISCV64.Wide
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Seed.RISCV64.ModesConstantTime
meta import VerifiedGarbage.Proof.Seed.RISCV64.ModeCore
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Spec.Seed.Ofb
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# SEED's modes on RISC-V meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/RISCV64/` over SEED's core (`Mode.dirCoreSpec`) meet the
shared contracts, with `stack := frameBytes g`: the mode's frame of
`136 + 2 g` slots below the stack pointer, which holds ECB's scratch buffer
and which it zeroes before returning, for the core on `g` blocks: 1104 bytes
for the modes on one block, 1344 for CBC and CFB decryption, sixteen
(`Proof/Modes/RISCV64/Wide.lean`). The proofs are written against
`modeContract`, which states the frame.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Seed.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb)
open VG.Proof.Seed.RISCV64.Mode (dirCoreSpec KeyArgs layout total_eq)
open VG.Proof.Seed.RISCV64 (modePub)

/-- The frame's bytes, of the core on `g` blocks. -/
abbrev frameBytes (g : Nat) : Nat := 1088 + 16 * g

/-- SEED under the schedule at `a0`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt s.mem (s.gpr .a0))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Seed.invCipher (Spec.Seed.scheduleAt s.mem (s.gpr .a0))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .a1) 16
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .a2) (s.gpr .a3).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (s.gpr .a3).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- A mode's function on RISC-V, with its frame below the stack pointer,
and the postcondition `post`, over the core on `g` blocks. -/
def modeContract (g : Nat) (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a1, 16⟩
    let data : Region := ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes g, frameBytes g⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a1).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes g ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

/-- The frame, of the core on `g` blocks. -/
theorem scr_eq (d : Spec.Seed.Direction) (g : Nat) (s : State) :
    scrRegion (dirCore d g) (Fb s (dirCore d g)) = ⟨s.sp - frameBytes g, frameBytes g⟩ := by
  rw [scrRegion, Fb, total_eq]; rfl

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Spec.Seed.Direction) {g : Nat}
    (hg1 : 1 ≤ g) (hg : g ≤ 16) (hstep : M.step = 16)
    {s : State} (h : (modeContract g post).pre s) : SeqPre (dirCore d g) M s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e16 : 4 * (dirCore d g).bw = 16 := rfl
  have eV : ivR s (dirCore d g) = ⟨s.gpr .a1, 16⟩ := rfl
  refine ⟨al, by rw [total_eq]; exact sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [e16]; exact fV, by rw [hwr, hstep]; simp, by rw [hstep]; exact fD,
    by rw [hstep, scr_eq]; exact dSD.symm, by rw [eV, scr_eq]; exact dSV.symm,
    fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega, by rw [e16]; omega⟩, layout d hg1 hg⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (d : Spec.Seed.Direction) {g : Nat}
    (hstep : M.step = 16) {s : State} (h : (modeContract g post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore d g) M s) (Spec.Seed.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 128).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · rw [scr_eq]; exact dSK.symm

/-! ## Correctness -/

theorem cipher_enc {g : Nat} {h1 : 1 ≤ g} {h2 : g ≤ 16} (k : Spec.Seed.Schedule) :
    (dirCoreSpec .encrypt g h1 h2).cipher k = Spec.Seed.cipher k := by
  simp only [dirCoreSpec, Proof.Seed.dirCipher]
theorem cipher_dec {g : Nat} {h1 : 1 ≤ g} {h2 : g ≤ 16} (k : Spec.Seed.Schedule) :
    (dirCoreSpec .decrypt g h1 h2).cipher k = Spec.Seed.invCipher k := by
  simp only [dirCoreSpec, Proof.Seed.dirCipher]

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract 1 cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 1 cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp (dirCoreSpec .encrypt 1 (by decide) (by decide))
    (seqPre_of .encrypt (by decide) (by decide) (M := Mode.cbcEncChained 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cbcEncChained 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract 16 cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 16 cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcDecWide_wp (lg := 4) (dirCoreSpec .decrypt 16 (by decide) (by decide)) (by decide)
    (by exact (by decide : 2 ^ 4 ≤ 16)) (by exact (by decide : 2 ^ 4 * (4 * 4) ≤ 2032))
    (seqPre_of .decrypt (by decide) (by decide) (M := Mode.cbcDecChained 4) rfl hs)
    (keyArgs_of .decrypt (M := Mode.cbcDecChained 4) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => by simp only [cipher_dec] at h2 h3; exact ⟨h1, h2, h3⟩

theorem ofb_correct (s : State) (hs : (modeContract 1 ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract 1 ofbPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofb_wp (dirCoreSpec .encrypt 1 (by decide) (by decide))
    (seqPre_of .encrypt (by decide) (by decide) (M := Mode.ofb 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ofb 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract 1 cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 1 cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEnc_wp (dirCoreSpec .encrypt 1 (by decide) (by decide))
    (seqPre_of .encrypt (by decide) (by decide) (M := Mode.cfbEnc 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cfbEnc 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract 16 cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 16 cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDecWide_wp (lg := 4) (dirCoreSpec .encrypt 16 (by decide) (by decide)) (by decide)
    (by exact (by decide : 2 ^ 4 ≤ 16)) (by exact (by decide : 2 ^ 4 * (4 * 4) ≤ 2032))
    (seqPre_of .encrypt (by decide) (by decide) (M := Mode.cfbDecEarly 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cfbDecEarly 4) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
the IV at `0x3000`, no data at `0x4000`, and the stack below `0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 0⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified RISCV64.target cbcEncryptChained (Spec.Seed.cbcEncryptChainedContract RISCV64.abi (frameBytes 1)) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  contract_implies [Spec.Seed.cbcEncryptChainedContract, Spec.Seed.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, frameBytes, cbcEncPost, modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified RISCV64.target cbcDecryptChained (Spec.Seed.cbcDecryptChainedContract RISCV64.abi (frameBytes 16)) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  contract_implies [Spec.Seed.cbcDecryptChainedContract, Spec.Seed.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, frameBytes, cbcDecPost, modePub_iff] [modeSat] using modeSat

theorem ofb_verified : Verified RISCV64.target ofb (Spec.Seed.ofbContract RISCV64.abi (frameBytes 1)) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  contract_implies [Spec.Seed.ofbContract, Spec.Seed.ofbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, frameBytes, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified RISCV64.target cfbEncrypt (Spec.Seed.cfbEncryptContract RISCV64.abi (frameBytes 1)) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  contract_implies [Spec.Seed.cfbEncryptContract, Spec.Seed.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, frameBytes, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified RISCV64.target cfbDecrypt (Spec.Seed.cfbDecryptContract RISCV64.abi (frameBytes 16)) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  contract_implies [Spec.Seed.cfbDecryptContract, Spec.Seed.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, frameBytes, cfbDecPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Seed.RISCV64.Modes
