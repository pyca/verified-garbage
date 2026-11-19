module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.Cfb8
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Ecb
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Ecb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.TripleDes.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit
public import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
public import VerifiedGarbage.Impl.TripleDes.RISCV64.FbFinal
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.FbFinal
meta import VerifiedGarbage.Spec.TripleDes.CfbFinal
meta import VerifiedGarbage.Spec.TripleDes.OfbFinal
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit
public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCoreWide
import VerifiedGarbage.Proof.Modes.RISCV64.Modes
import VerifiedGarbage.Proof.Modes.RISCV64.Wide
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.Modes.Steps
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCoreWide
meta import VerifiedGarbage.Spec.TripleDes.Cbc
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Spec.TripleDes.Cfb8
meta import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes
meta import VerifiedGarbage.Proof.Modes.RISCV64.Modes
meta import VerifiedGarbage.Proof.Modes.RISCV64.Wide
meta import VerifiedGarbage.Proof.Modes.RISCV64.Seq
meta import VerifiedGarbage.Proof.Modes.Steps

/-! ### `TripleDes.RISCV64.FbFinalVerified`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.ModesVerified`, which this module and modules that import it used -/

section

/-! ### `TripleDes.RISCV64.ModesConstantTime`, which only this module used -/

section

/-!
# Constant-time Triple DES modes on RISC-V

Only the pointers and the count (`a0`–`a3`) and the stack pointer are
public. The modes keep their state in `s1`–`s4`, which the block function
never writes (it saves and restores the other callee-saved registers it
uses), and zero the frame through `t3`, a copy of its base made before the
caller's `s1`–`s4` come back from memory.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64

/-- The modes' public arguments: the stack pointer and `a0`–`a3`. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r

theorem modes_ofRegs (s₁ s₂ : State) (h : modePub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cbcDecryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfb8Encrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfb8Decrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

end VG.Proof.TripleDes.RISCV64

end

end

/-!
# Triple DES's modes on RISC-V meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/RISCV64/` over Triple DES's core (`Mode.dirCoreSpec`) meet the
shared contracts, with `stack := 944`: the mode's frame of 118 slots below
the stack pointer, which it zeroes before returning (`seq_changes_wp`).
CBC and CFB decryption, whose blocks' cipher calls do not depend on each
other, are over the core on 64 blocks (`Mode.wideCoreSpec`), by groups of
64, 32, 16, 8 and 4 blocks and then a block at a time by the block function
(`Mode.wideOne_ok`), with `stack := 1120`, its frame of 140 slots.
The proofs are written against `modeContract`, which states the frame.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb)
open VG.Proof.TripleDes.RISCV64.Mode (dirCoreSpec KeyArgs layout wideCoreSpec wideOne_ok layoutS)
open VG.Proof.TripleDes.RISCV64 (modePub)
open VG.Proof.TripleDes (bytesAt_eq)

/-- The frame's bytes. -/
abbrev frameBytes : Nat := 944
/-- The frame's bytes, of the modes over the core on 64 blocks. -/
abbrev wideBytes : Nat := 1120

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
of `frameBytes` bytes below the stack pointer, and the postcondition `post`. -/
def modeContract (frameBytes st : Nat) (post : State → State → Prop) : Contract isa where
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
    (hstep : M.step = st) (hst : 0 < st) (hst8 : st ≤ 8) {s : State} (h : (modeContract frameBytes st post).pre s) :
    SeqPre (dirCore d) M s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e8 : 4 * (dirCore d).bw = 8 := rfl
  have eS : scrRegion (dirCore d) (Fb s (dirCore d)) = ⟨s.sp - frameBytes, frameBytes⟩ := rfl
  have eV : ivR s (dirCore d) = ⟨s.gpr .a1, 8⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e8]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega_using [hstep, hst], by rw [e8]; omega_using [hstep, hst8]⟩,
    layout d⟩

theorem keyArgs_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) {s : State} (h : (modeContract frameBytes st post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore d) M s) (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 384).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-- `seqPre_of` and `keyArgs_of`, for the core on 64 blocks. -/
theorem seqPre_ofW {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = 8) {s : State} (h : (modeContract wideBytes 8 post).pre s) :
    SeqPre (wideCore d) M s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have e8 : 4 * (wideCore d).bw = 8 := rfl
  have eS : scrRegion (wideCore d) (Fb s (wideCore d)) = ⟨s.sp - wideBytes, wideBytes⟩ := rfl
  have eV : ivR s (wideCore d) = ⟨s.gpr .a1, 8⟩ := rfl
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [e8]; exact fV,
    by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, hstep]; exact dVD,
    ⟨by rw [hstep]; decide, by rw [e8, hstep]⟩, layoutS d⟩

theorem keyArgs_ofW {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = 8) {s : State} (h : (modeContract wideBytes 8 post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (wideCore d) M s) (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 384).Disjoint ⟨s.gpr .a2, M.step * (s.gpr .a3).toNat⟩
    rw [hstep]; exact dKD
  · exact dSK.symm

/-- The levels' groups fit the core on 64 blocks and the mode's buffer. -/
theorem levels_fit (d : Spec.TripleDes.Direction) : Proof.Modes.RISCV64.LevelsFit (wideCore d) levels := by
  exact (by decide : ∀ lg ∈ levels, lg ≤ 11 ∧ 2 ^ lg ≤ 64 ∧ 2 ^ lg * (4 * 2) ≤ 2032)

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract frameBytes 8 cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes 8 cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcEncChained_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cbcEncChained 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cbcEncChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContract wideBytes 8 cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧
      (modeContract wideBytes 8 cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cbcDecLevelsWith_wp (wideCoreSpec .decrypt) (wideOne_ok .decrypt)
    (levels_fit .decrypt) (seqPre_ofW .decrypt (M := Mode.cbcDecChained 2) rfl hs)
    (keyArgs_ofW .decrypt (M := Mode.cbcDecChained 2) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem ofb_correct (s : State) (hs : (modeContract frameBytes 8 ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes 8 ofbPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofb_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.ofb 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.ofb 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract frameBytes 8 cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes 8 cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEnc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbEnc 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfbEnc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContract wideBytes 8 cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContract wideBytes 8 cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDecLevelsWith_wp (wideCoreSpec .encrypt) (wideOne_ok .encrypt)
    (levels_fit .encrypt) (seqPre_ofW .encrypt (M := Mode.cfbDecEarly 2) rfl hs)
    (keyArgs_ofW .encrypt (M := Mode.cfbDecEarly 2) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfb8Encrypt_correct (s : State) (hs : (modeContract frameBytes 1 cfb8EncPost).pre s) :
    ∃ t s', Exec isa cfb8Encrypt s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes 1 cfb8EncPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfb8Enc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfb8Enc 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfb8Enc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

theorem cfb8Decrypt_correct (s : State) (hs : (modeContract frameBytes 1 cfb8DecPost).pre s) :
    ∃ t s', Exec isa cfb8Decrypt s t s' ∧ abiPreserved s s' ∧ (modeContract frameBytes 1 cfb8DecPost).post s s' :=
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
      (Spec.TripleDes.cbcDecryptChainedContract RISCV64.abi wideBytes) := by
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
    Verified RISCV64.target cfbDecrypt (Spec.TripleDes.cfbDecryptContract RISCV64.abi wideBytes) := by
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

end

end

/-!
# Triple DES-CFB64 and Triple DES-OFB of a message's last piece on RISC-V meet their contracts

The modes' CFB and OFB over a message's last piece (`Proof.Modes.RISCV64.cfbEncFinal_wp`,
`cfbDecFinal_wp`, `ofbFinal_wp`) over TripleDes's one-block encryption core meet the contracts,
with `stack := 944`, that core's frame (`ModesVerified.lean`), whose
precondition, with the data `len` bytes, is `seq`'s for the data a byte at a
time (`byteMode`). Constant time as the whole-block functions.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Modes

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64 VG.Impl.Modes
open VG.Proof.Modes.RISCV64 (SeqPre ivR scrRegion Fb byteMode)
open VG.Proof.TripleDes.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.TripleDes.RISCV64 (modePub modes_ofRegs)

/-- The final functions' postconditions. -/
def encFinalPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat
def decFinalPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat
def ofbFinalPost (s s' : State) : Prop :=
  Spec.Ofb.CryptFinal (ciph s) 8 s.mem s'.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3).toNat

/-- A final function on RISC-V, with its frame below the stack pointer, the
data `len` bytes, and the postcondition `post`. -/
def finalContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 384⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data
  post := post
  pub := modePub

theorem seqPreF_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    SeqPre (dirCore .encrypt) byteMode s := by
  obtain ⟨-, hwr, -, -, dVD, fV, fD, al, sp, -, dSV, dSD⟩ := h
  have eb : 4 * (dirCore .encrypt).bw = 8 := rfl
  have eS := (show scrRegion (dirCore .encrypt) (Fb s (dirCore .encrypt)) = ⟨s.sp - frameBytes, frameBytes⟩ from rfl)
  have eV : ivR s (dirCore .encrypt) = ⟨s.gpr .a1, 8⟩ := rfl
  have eD : Proof.Modes.RISCV64.dataRegion (s.gpr .a2) byteMode.step (s.gpr .a3).toNat =
      ⟨s.gpr .a2, (s.gpr .a3).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, byteMode, Nat.one_mul]
  refine ⟨al, sp, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp, by rw [eb]; exact fV,
    by rw [eD, hwr]; simp, by simp only [byteMode, Nat.one_mul]; exact fD, by rw [eD, eS]; exact dSD.symm,
    by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD, ⟨by decide, by rw [eb]; decide⟩,
    layout .encrypt⟩

theorem keyArgsF_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    KeyArgs s (Proof.Modes.RISCV64.wrs0 (dirCore .encrypt) byteMode s) (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) := by
  obtain ⟨hrd, -, -, dKD, -, -, -, -, -, dSK, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), fun r hr => ?_⟩
  simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .a0) 384).Disjoint ⟨s.gpr .a2, 1 * (s.gpr .a3).toNat⟩
    rw [Nat.one_mul]; exact dKD
  · exact dSK.symm

theorem cfbEncryptFinal_correct (s : State) (hs : (finalContract encFinalPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract encFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbEncFinal_wp (dirCoreSpec .encrypt) (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decFinalPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.cfbDecFinal_wp (dirCoreSpec .encrypt) (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

theorem ofbFinal_correct (s : State) (hs : (finalContract ofbFinalPost).pre s) :
    ∃ t s', Exec isa ofbFinal s t s' ∧ abiPreserved s s' ∧ (finalContract ofbFinalPost).post s s' :=
  WP.mono (Proof.Modes.RISCV64.ofbFinal_wp (dirCoreSpec .encrypt) (seqPreF_of hs) (keyArgsF_of hs))
    fun _ ⟨h1, h2, _⟩ => ⟨h1, h2⟩

/-! ## Constant time -/

theorem cfbEncryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem ofbFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofbFinal :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

/-! ## The contracts -/

theorem cfbEncryptFinal_verified :
    Verified RISCV64.target cfbEncryptFinal (Spec.TripleDes.cfbEncryptFinalContract RISCV64.abi (frameBytes)) := by
  refine Verified.of_correct cfbEncryptFinal_correct (cfbEncryptFinal_constantTime _) ?_
  contract_implies [Spec.TripleDes.cfbEncryptFinalContract, Spec.TripleDes.cfbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, encFinalPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecryptFinal_verified :
    Verified RISCV64.target cfbDecryptFinal (Spec.TripleDes.cfbDecryptFinalContract RISCV64.abi (frameBytes)) := by
  refine Verified.of_correct cfbDecryptFinal_correct (cfbDecryptFinal_constantTime _) ?_
  contract_implies [Spec.TripleDes.cfbDecryptFinalContract, Spec.TripleDes.cfbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, decFinalPost, modePub_iff] [modeSat] using modeSat

theorem ofbFinal_verified :
    Verified RISCV64.target ofbFinal (Spec.TripleDes.ofbFinalContract RISCV64.abi (frameBytes)) := by
  refine Verified.of_correct ofbFinal_correct (ofbFinal_constantTime _) ?_
  contract_implies [Spec.TripleDes.ofbFinalContract, Spec.TripleDes.ofbFinalSig, RISCV64.abi,
    RISCV64.argRegs, finalContract, ofbFinalPost, modePub_iff] [modeSat] using modeSat

end VG.Proof.TripleDes.RISCV64.Modes

end

end

/-! ### `TripleDes.RISCV64.Bitsliced.Verified`, which only this module used -/

section

/-!
# Bitsliced Triple DES ECB on RISC-V meets its contract

The proof is written against `ecbC`, which states the frame of 1056 bytes
below the stack pointer, and moved to the shared contracts of
`Spec/TripleDes/Contract.lean` with `stack := 1056`.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64.Bitslice
open VG.Spec.TripleDes (Direction)

/-- The ECB contract as the code sees it. -/
def ecbC (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 384⟩
    let data : Region := ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
    let stack : Region := ⟨s.sp - 1056, 1056⟩
    s.rd = [key] ∧ s.wr = [data] ∧ key.Disjoint data ∧
      (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ 1056 ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint data
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem ecb_ok (d : Direction) (s : State) (hs : (ecbC d).pre s) :
    ∃ t s', Exec isa (ecb d) s t s' ∧ abiPreserved s s' ∧ (ecbC d).post s s' := by
  obtain ⟨rd, wr, kd, fit, al, sp, sk, sd⟩ := hs
  obtain ⟨t, s', he, hp, hb⟩ := ecb_wp d ⟨rd, wr, kd, fit, al, sp, sk, sd⟩
  exact ⟨t, s', he, hp, VG.Proof.TripleDes.Bitslice.ecb_blocks _ _ _ _ _ _ hb⟩

theorem ecb_agree (d : Direction) : ∀ s₁ s₂, (ecbC d).pre s₁ → (ecbC d).pre s₂ → (ecbC d).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem encrypt_ct : ConstantTime isa (ecbC .encrypt).pre (ecbC .encrypt).pub encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (ecb_agree .encrypt)
    (by taint_decide)

theorem decrypt_ct : ConstantTime isa (ecbC .decrypt).pre (ecbC .decrypt).pub decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (ecb_agree .decrypt)
    (by taint_decide)

def ecbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x3000, 0⟩]

theorem encrypt_verified :
    Verified RISCV64.target encrypt (Spec.TripleDes.ecbEncryptContract RISCV64.abi 1056) := by
  refine Verified.of_correct (k := ecbC .encrypt) (ecb_ok .encrypt) encrypt_ct ?_
  contract_implies [Spec.TripleDes.ecbEncryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, RISCV64.abi, RISCV64.argRegs, ecbC] [ecbSat]
    using ecbSat

theorem decrypt_verified :
    Verified RISCV64.target decrypt (Spec.TripleDes.ecbDecryptContract RISCV64.abi 1056) := by
  refine Verified.of_correct (k := ecbC .decrypt) (ecb_ok .decrypt) decrypt_ct ?_
  contract_implies [Spec.TripleDes.ecbDecryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, RISCV64.abi, RISCV64.argRegs, ecbC] [ecbSat]
    using ecbSat

end VG.Proof.TripleDes.RISCV64.Bitsliced

end

end

/-!
# TripleDes on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.scrubOf`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/TripleDes/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Scrub

open VG.Spec.TripleDes VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (Spec.TripleDes.expandKeyContract RISCV64.abi stack) (Spec.TripleDes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.expandKeyPostOut_local _)

theorem cbcEncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cbcEncryptChainedContract RISCV64.abi stack) (Spec.TripleDes.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcEncChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfbEncryptContract RISCV64.abi stack) (Spec.TripleDes.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbEncPostOut_local _)

theorem cbcDecryptOut (stack : Nat) : PostOut (Spec.TripleDes.cbcDecryptChainedContract RISCV64.abi stack) (Spec.TripleDes.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcDecChainedPostOut_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfbDecryptContract RISCV64.abi stack) (Spec.TripleDes.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbDecPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (Spec.TripleDes.cfbEncryptFinalContract RISCV64.abi stack) (Spec.TripleDes.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (Spec.TripleDes.cfbDecryptFinalContract RISCV64.abi stack) (Spec.TripleDes.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem cfb8EncryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfb8EncryptContract RISCV64.abi stack) (Spec.TripleDes.cfb8Sig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8EncPostOut_local _)

theorem cfb8DecryptOut (stack : Nat) : PostOut (Spec.TripleDes.cfb8DecryptContract RISCV64.abi stack) (Spec.TripleDes.cfb8Sig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8DecPostOut_local _)

theorem ofbOut (stack : Nat) : PostOut (Spec.TripleDes.ofbContract RISCV64.abi stack) (Spec.TripleDes.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (Spec.TripleDes.ofbFinalContract RISCV64.abi stack) (Spec.TripleDes.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem ecbOut (d : Spec.TripleDes.Direction) (stack : Nat) : PostOut (Spec.TripleDes.ecbContract RISCV64.abi d stack) (Spec.TripleDes.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ecbPostOut_local _ d)

/-! ## The registrations -/

/-- `Spec.TripleDes.expandKeyApi`. -/
def expandKeyReg : Registration Spec.TripleDes.expandKeyApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.Key.expandKey, verified := Proof.TripleDes.RISCV64.Key.verified }
    (expandKeyOut _)

/-- `Spec.TripleDes.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.TripleDes.ecbEncryptApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.Bitslice.encrypt, verified := Proof.TripleDes.RISCV64.Bitsliced.encrypt_verified }
    (ecbOut .encrypt _)

/-- `Spec.TripleDes.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.TripleDes.ecbDecryptApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.Bitslice.decrypt, verified := Proof.TripleDes.RISCV64.Bitsliced.decrypt_verified }
    (ecbOut .decrypt _)

/-- `Spec.TripleDes.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.TripleDes.cbcEncryptChainedApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.cbcEncryptChained, verified := Proof.TripleDes.RISCV64.Modes.cbcEncryptChained_verified }
    (cbcEncryptOut _)

/-- `Spec.TripleDes.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.TripleDes.cbcDecryptChainedApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.cbcDecryptChained, verified := Proof.TripleDes.RISCV64.Modes.cbcDecryptChained_verified }
    (cbcDecryptOut _)

/-- `Spec.TripleDes.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.TripleDes.cfbEncryptApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.cfbEncrypt, verified := Proof.TripleDes.RISCV64.Modes.cfbEncrypt_verified }
    (cfbEncryptOut _)

/-- `Spec.TripleDes.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.TripleDes.cfbDecryptApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.cfbDecrypt, verified := Proof.TripleDes.RISCV64.Modes.cfbDecrypt_verified }
    (cfbDecryptOut _)

/-- `Spec.TripleDes.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.TripleDes.cfbEncryptFinalApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.cfbEncryptFinal, verified := Proof.TripleDes.RISCV64.Modes.cfbEncryptFinal_verified }
    (cfbEncryptFinalOut _)

/-- `Spec.TripleDes.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.TripleDes.cfbDecryptFinalApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.cfbDecryptFinal, verified := Proof.TripleDes.RISCV64.Modes.cfbDecryptFinal_verified }
    (cfbDecryptFinalOut _)

/-- `Spec.TripleDes.cfb8EncryptApi`. -/
def cfb8EncryptReg : Registration Spec.TripleDes.cfb8EncryptApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.cfb8Encrypt, verified := Proof.TripleDes.RISCV64.Modes.cfb8Encrypt_verified }
    (cfb8EncryptOut _)

/-- `Spec.TripleDes.cfb8DecryptApi`. -/
def cfb8DecryptReg : Registration Spec.TripleDes.cfb8DecryptApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.cfb8Decrypt, verified := Proof.TripleDes.RISCV64.Modes.cfb8Decrypt_verified }
    (cfb8DecryptOut _)

/-- `Spec.TripleDes.ofbApi`. -/
def ofbReg : Registration Spec.TripleDes.ofbApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.ofb, verified := Proof.TripleDes.RISCV64.Modes.ofb_verified }
    (ofbOut _)

/-- `Spec.TripleDes.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.TripleDes.ofbFinalApi RISCV64.target :=
  scrubOf { code := Impl.TripleDes.RISCV64.ofbFinal, verified := Proof.TripleDes.RISCV64.Modes.ofbFinal_verified }
    (ofbFinalOut _)

end VG.Proof.TripleDes.RISCV64.Scrub
