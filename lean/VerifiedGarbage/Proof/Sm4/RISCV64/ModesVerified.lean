module

public import VerifiedGarbage.Proof.Sm4.RISCV64.ModesConstantTime
public import VerifiedGarbage.Proof.Sm4.RISCV64.ModeCore
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Modes.RISCV64.Ctr
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModesConstantTime
meta import VerifiedGarbage.Proof.Sm4.RISCV64.ModeCore
meta import VerifiedGarbage.Spec.Sm4.Cbc
meta import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Spec.Sm4.Ofb
meta import VerifiedGarbage.Spec.Sm4.Ctr
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sm4.RISCV64.PreparedBody
meta import VerifiedGarbage.Proof.Sm4.RISCV64.PreparedBody

/-!
# SM4's modes on RISC-V meet their contracts

`cbcEncryptChained_verified`, `ctr_verified`, … : the modes of
`Proof/Modes/RISCV64/` over SM4's core (`Mode.dirCoreSpec`) meet the
shared contracts, with `stack := 3232`: the mode's frame of 404 slots below
the stack pointer, which holds ECB's scratch buffer and which it zeroes
before returning. The proofs are written against `modeContract`, which
states the frame.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb)
open VG.Proof.Sm4.RISCV64.Mode (dirCoreSpec KeyArgs layout dirCipher)
open VG.Proof.Sm4.RISCV64 (modePub)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 3232

/-- SM4 under the schedule at `a0`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .a0))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .a0))
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
def ctrPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ctr.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ctr.next (ivAt s.mem s) (s.gpr .a3).toNat

/-- A mode's function on RISC-V, with its frame below the stack pointer,
and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a1, 16⟩
    let data : Region := ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Dir) (hstep : M.step = 16)
    {s : State} (h : (modeContract post).pre s) : SeqPre (dirCore d) M s := by
  obtain ⟨-, hwr, -, -, dVD, -, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e16 : 4 * (dirCore d).bw = 16 := rfl
  have eS : scrRegion (dirCore d) (Fb s (dirCore d)) = ⟨s.sp - frameBytes, frameBytes⟩ := rfl
  have eV : ivR s (dirCore d) = ⟨s.gpr .a1, 16⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e16]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega, by rw [e16]; omega⟩,
    layout d⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (d : Dir) (hstep : M.step = 16)
    {s : State} (h : (modeContract post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore d) M s) (Spec.Sm4.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, fK, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fK, fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 128).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-- The data in blocks, as the modes' steps. -/
theorem blocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Cbc.blocksAt m p n = Proof.Modes.chunksAt 16 m p n := rfl

/-! ## Correctness -/

theorem cipher_enc (k : Spec.Sm4.Schedule) : (dirCoreSpec .encrypt).cipher k = Spec.Sm4.cipher k := rfl
theorem cipher_dec (k : Spec.Sm4.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.Sm4.invCipher k := rfl

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cbcEncChained 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cbcEncChained 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcDecChained_wp (dirCoreSpec .decrypt)
    (seqPre_of .decrypt (M := Mode.cbcDecChained 4) rfl hs)
    (keyArgs_of .decrypt (M := Mode.cbcDecChained 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_dec] at h2 h3; exact ⟨h1, h2, h3⟩

theorem ofb_correct (s : State) (hs : (modeContract ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract ofbPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofb_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.ofb 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ofb 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEnc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbEnc 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cfbEnc 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDec_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbDec 4) rfl hs)
    (keyArgs_of .encrypt (M := Mode.cfbDec 4) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

theorem ctr_correct (s : State) (hs : (modeContract ctrPost).pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ (modeContract ctrPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ctr_wp (dirCoreSpec .encrypt) rfl
    (seqPre_of .encrypt (M := Mode.ctr) rfl hs)
    (keyArgs_of .encrypt (M := Mode.ctr) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => by simp only [cipher_enc] at h2 h3; exact ⟨h1, h2, h3⟩

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
    Verified RISCV64.target cbcEncryptChained (Spec.Sm4.cbcEncryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  contract_implies [Spec.Sm4.cbcEncryptChainedContract, Spec.Sm4.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcEncPost, modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified RISCV64.target cbcDecryptChained (Spec.Sm4.cbcDecryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  contract_implies [Spec.Sm4.cbcDecryptChainedContract, Spec.Sm4.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcDecPost, modePub_iff] [modeSat] using modeSat

theorem ofb_verified : Verified RISCV64.target ofb (Spec.Sm4.ofbContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  contract_implies [Spec.Sm4.ofbContract, Spec.Sm4.ofbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified RISCV64.target cfbEncrypt (Spec.Sm4.cfbEncryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  contract_implies [Spec.Sm4.cfbEncryptContract, Spec.Sm4.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified RISCV64.target cfbDecrypt (Spec.Sm4.cfbDecryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  contract_implies [Spec.Sm4.cfbDecryptContract, Spec.Sm4.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbDecPost, modePub_iff] [modeSat] using modeSat

theorem ctr_verified : Verified RISCV64.target ctr (Spec.Sm4.ctrContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ctr_correct (ctr_constantTime _) ?_
  contract_implies [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ctrPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Sm4.RISCV64.Modes
