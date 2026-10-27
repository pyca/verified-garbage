module

public import VerifiedGarbage.Proof.Idea.RISCV64.ModesConstantTime
public import VerifiedGarbage.Proof.Idea.RISCV64.ModeCore
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Idea.ModeBytes
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Idea.RISCV64.ModesConstantTime
meta import VerifiedGarbage.Proof.Idea.RISCV64.ModeCore
meta import VerifiedGarbage.Spec.Idea.Cbc
meta import VerifiedGarbage.Spec.Idea.Cfb
meta import VerifiedGarbage.Spec.Idea.Ofb
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# IDEA's modes on RISC-V meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/RISCV64/` over IDEA's core (`Mode.coreSpec`) meet the shared
contracts, with `stack := 64`: the mode's frame of 8 slots below the stack
pointer, which it zeroes before returning. The proofs are written against
`modeContract`, which states the frame.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.Idea.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb)
open VG.Proof.Idea.RISCV64.Mode (coreSpec KeyArgs layout)
open VG.Proof.Idea.RISCV64 (modePub)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 64

/-- IDEA under the subkeys at `a0`. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.Idea.cipher (Spec.Idea.scheduleAt s.mem (s.gpr .a0))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m (s.gpr .a1) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) :=
  Spec.Idea.cbcBlocksAt m (s.gpr .a2) (s.gpr .a3).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
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
and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 104⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (hstep : M.step = 8) {s : State}
    (h : (modeContract post).pre s) : SeqPre core M s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e8 : 4 * core.bw = 8 := rfl
  have eS : scrRegion core (Fb s core) = ⟨s.sp - frameBytes, frameBytes⟩ := rfl
  have eV : ivR s core = ⟨s.gpr .a1, 8⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e8]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega, by rw [e8]; omega⟩,
    layout⟩

theorem keyArgs_of {post : State → State → Prop} {M : Mode} (hstep : M.step = 8) {s : State}
    (h : (modeContract post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 core M s) (Spec.Idea.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 104).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Idea.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.Idea.cbcBlocksAt, Spec.Idea.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (Proof.Idea.bytesAt_eq m _).symm

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp coreSpec
    (seqPre_of (M := Mode.cbcEncChained 2) rfl hs) (keyArgs_of (M := Mode.cbcEncChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcDecChained_wp coreSpec
    (seqPre_of (M := Mode.cbcDecChained 2) rfl hs) (keyArgs_of (M := Mode.cbcDecChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem ofb_correct (s : State) (hs : (modeContract ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract ofbPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofb_wp coreSpec
    (seqPre_of (M := Mode.ofb 2) rfl hs) (keyArgs_of (M := Mode.ofb 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEnc_wp coreSpec
    (seqPre_of (M := Mode.cfbEnc 2) rfl hs) (keyArgs_of (M := Mode.cfbEnc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDec_wp coreSpec
    (seqPre_of (M := Mode.cfbDec 2) rfl hs) (keyArgs_of (M := Mode.cfbDec 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the subkeys at `0x1000`,
the IV at `0x3000`, no data at `0x4000`, and the stack below `0x8000`. -/
def modeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 0⟩]

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 := by
  simp [modePub]

theorem cbcEncryptChained_verified :
    Verified RISCV64.target cbcEncryptChained
      (Spec.Idea.cbcEncryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  contract_implies [Spec.Idea.cbcEncryptChainedContract, Spec.Idea.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcEncPost, modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified RISCV64.target cbcDecryptChained
      (Spec.Idea.cbcDecryptChainedContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _) ?_
  contract_implies [Spec.Idea.cbcDecryptChainedContract, Spec.Idea.cbcChainedSig,
    RISCV64.abi, RISCV64.argRegs, modeContract, cbcDecPost, modePub_iff] [modeSat] using modeSat

theorem ofb_verified : Verified RISCV64.target ofb (Spec.Idea.ofbContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  contract_implies [Spec.Idea.ofbContract, Spec.Idea.ofbSig, RISCV64.abi, RISCV64.argRegs,
    modeContract, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified RISCV64.target cfbEncrypt (Spec.Idea.cfbEncryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  contract_implies [Spec.Idea.cfbEncryptContract, Spec.Idea.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified RISCV64.target cfbDecrypt (Spec.Idea.cfbDecryptContract RISCV64.abi frameBytes) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _) ?_
  contract_implies [Spec.Idea.cfbDecryptContract, Spec.Idea.cfbSig, RISCV64.abi,
    RISCV64.argRegs, modeContract, cfbDecPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.Idea.RISCV64.Modes
