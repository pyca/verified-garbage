module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesConstantTime
public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.Cfb8
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesConstantTime
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
meta import VerifiedGarbage.Spec.TripleDes.Cbc
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Spec.TripleDes.Cfb8
meta import VerifiedGarbage.Spec.TripleDes.Ofb
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# Triple DES's modes on RISC-V meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/RISCV64/` over Triple DES's core (`Mode.dirCoreSpec`) meet the
shared contracts, with `stack := 640`: the mode's frame of 80 slots below
the stack pointer, which it zeroes before returning (`seq_changes_wp`).
The proofs are written against `modeContract`, which states the frame.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb)
open VG.Proof.TripleDes.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.TripleDes.RISCV64 (modePub)
open VG.Proof.TripleDes (bytesAt_eq)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 640

/-- Triple DES under the schedule at `a0`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.TripleDes.bytesAt m (s.gpr .a1) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) :=
  Spec.TripleDes.cbcBlocksAt m (s.gpr .a2) (s.gpr .a3).toNat
/-- The data, in bytes. -/
abbrev bytesOf (m : Mem) (s : State) : List Byte := Spec.TripleDes.bytesAt m (s.gpr .a2) (s.gpr .a3).toNat

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
def cfb8EncPost (s s' : State) : Prop :=
  bytesOf s'.mem s = Spec.Cfb8.encrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s) ∧
    ivAt s'.mem s = Spec.Cfb8.next (ivAt s.mem s) (Spec.Cfb8.encrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s))
def cfb8DecPost (s s' : State) : Prop :=
  bytesOf s'.mem s = Spec.Cfb8.decrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s) ∧
    ivAt s'.mem s = Spec.Cfb8.next (ivAt s.mem s) (bytesOf s.mem s)

/-- A mode's function on RISC-V, `st` bytes of data a step, with its frame
below the stack pointer, and the postcondition `post`. -/
def modeContract (st : Nat) (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 384⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, st * (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + st * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) (hst : 0 < st) (hst8 : st ≤ 8) {s : State} (h : (modeContract st post).pre s) :
    SeqPre (dirCore d) M s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e8 : 4 * (dirCore d).bw = 8 := rfl
  have eS : scrRegion (dirCore d) (Fb s (dirCore d)) = ⟨s.sp - frameBytes, frameBytes⟩ := rfl
  have eV : ivR s (dirCore d) = ⟨s.gpr .a1, 8⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e8]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega, by rw [e8]; omega⟩,
    layout d⟩

theorem keyArgs_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) {s : State} (h : (modeContract st post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore d) M s) (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 384).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract 8 cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 8 cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cbcEncChained 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cbcEncChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract 8 cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 8 cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcDecChained_wp (dirCoreSpec .decrypt)
    (seqPre_of .decrypt (M := Mode.cbcDecChained 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .decrypt (M := Mode.cbcDecChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem ofb_correct (s : State) (hs : (modeContract 8 ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract 8 ofbPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofb_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.ofb 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.ofb 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract 8 cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 8 cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEnc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbEnc 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfbEnc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract 8 cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 8 cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDec_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbDec 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfbDec 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfb8Encrypt_correct (s : State) (hs : (modeContract 1 cfb8EncPost).pre s) :
    ∃ t s', Exec isa cfb8Encrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 1 cfb8EncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfb8Enc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfb8Enc 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfb8Enc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

theorem cfb8Decrypt_correct (s : State) (hs : (modeContract 1 cfb8DecPost).pre s) :
    ∃ t s', Exec isa cfb8Decrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 1 cfb8DecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfb8Dec_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfb8Dec 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfb8Dec 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
the IV at `0x3000`, no data at `0x4000`, and the stack below `0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 0⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified RISCV64.target cbcEncryptChained
      (Spec.TripleDes.cbcEncryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  contract_implies [Spec.TripleDes.cbcEncryptChainedContract, Spec.TripleDes.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcEncPost, modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified RISCV64.target cbcDecryptChained
      (Spec.TripleDes.cbcDecryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  contract_implies [Spec.TripleDes.cbcDecryptChainedContract, Spec.TripleDes.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcDecPost, modePub_iff] [modeSat] using modeSat

theorem ofb_verified : Verified RISCV64.target ofb (Spec.TripleDes.ofbContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  contract_implies [Spec.TripleDes.ofbContract, Spec.TripleDes.ofbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified RISCV64.target cfbEncrypt (Spec.TripleDes.cfbEncryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  contract_implies [Spec.TripleDes.cfbEncryptContract, Spec.TripleDes.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified RISCV64.target cfbDecrypt (Spec.TripleDes.cfbDecryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  contract_implies [Spec.TripleDes.cfbDecryptContract, Spec.TripleDes.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbDecPost, modePub_iff] [modeSat] using modeSat

theorem cfb8Encrypt_verified :
    Verified RISCV64.target cfb8Encrypt (Spec.TripleDes.cfb8EncryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfb8Encrypt_correct (cfb8Encrypt_constantTime _) ?_
  contract_implies [Spec.TripleDes.cfb8EncryptContract, Spec.TripleDes.cfb8Sig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfb8EncPost, modePub_iff, Nat.one_mul] [modeSat] using modeSat

theorem cfb8Decrypt_verified :
    Verified RISCV64.target cfb8Decrypt (Spec.TripleDes.cfb8DecryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfb8Decrypt_correct (cfb8Decrypt_constantTime _) ?_
  contract_implies [Spec.TripleDes.cfb8DecryptContract, Spec.TripleDes.cfb8Sig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfb8DecPost, modePub_iff, Nat.one_mul] [modeSat] using modeSat

end VG.Proof.TripleDes.RISCV64.Modes
