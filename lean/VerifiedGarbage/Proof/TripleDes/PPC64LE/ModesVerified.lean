module

public import VerifiedGarbage.Proof.TripleDes.CbcScratch
public import VerifiedGarbage.Proof.TripleDes.FbScratch
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModeCoreWide
import VerifiedGarbage.Proof.Modes.PPC64LE.Wide
import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Permutation
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Permutation
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! ### `TripleDes.PPC64LE.ModesConstantTime`, which only this module used -/

section

/-! # Constant-time Triple DES modes on PPC64LE

Only the pointers and the count (`r3`–`r7`) are public. The block functions
are analysed at their calls; they never write `r29`–`r31`, which hold the
IV's address, the steps left and the data pointer, nor `r3` and `r5`, which
hold the schedule and the scratch buffer.

CBC and CFB64 decryption run the bitsliced ECB inline, which saves `r29`–`r31`
in the scratch buffer and restores them from there: their analysis is
`VG.PPC64LE.slotTaint`, which knows that those slots survive ECB's stores, all
at fixed offsets of the scratch buffer (the third writable region, at `r7`
on entry), as for SM4's modes (`Proof/Sm4/PPC64LE/ModesVerified.lean`). -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The modes' public arguments. -/
abbrev modePub : State → State → Prop := PublicRegs [.r3, .r4, .r5, .r6, .r7]

theorem modes_ofRegs (s₁ s₂ : State) (h : modePub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem cbcEncryptChained_constantTime (pre : State → Prop) :
    ConstantTime isa pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

/-- The writable regions of CBC and CFB64 decryption: the IV, the data and
the scratch buffer of 200 words, apart. -/
def WidePre (s : State) : Prop :=
  let iv : Region := ⟨s.gpr .r4, 8⟩
  let data : Region := ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
  let scratch : Region := ⟨s.gpr .r7, 1600⟩
  s.wr = [iv, data, scratch] ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .r5).toNat + 8 * (s.gpr .r6).toNat ≤ 2 ^ 64

/-- The taint on entry: the arguments public, the IV, the data and the
scratch buffer the writable regions at `r4`, `r5` and `r7`, the scratch
buffer's whole length known. -/
def wideTaint : SlotTaint.T := SlotTaint.mk' [.r3, .r4, .r5, .r6, .r7] [8, 0, 1600]
  [(.r4, 0), (.r5, 1), (.r7, 2)]

theorem wide_agree (s₁ s₂ : State) (h₁ : WidePre s₁) (h₂ : WidePre s₂) (hp : modePub s₁ s₂) :
    SlotTaint.Agree wideTaint s₁ s₂ := by
  obtain ⟨hw₁, dVD, dVS, dDS, fD⟩ := h₁
  obtain ⟨hw₂, -⟩ := h₂
  obtain ⟨hsp, hr⟩ := hp
  have r4 := hr .r4 (by simp)
  have r5 := hr .r5 (by simp)
  have r6 := hr .r6 (by simp)
  have r7 := hr .r7 (by simp)
  refine SlotTaint.agree_mk' hsp (fun r h => hr r (by simpa using h)) (by rw [hw₁, hw₂, r4, r5, r6, r7])
    ?_ ?_ ?_ ?_ ?_
  · rw [hw₁]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · rw [hw₁]
    refine .cons (fun r hr => ?_) (.cons (fun r hr => ?_) (.cons (fun r hr => absurd hr List.not_mem_nil) .nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dVD
      · exact dVS
    · simp only [List.mem_singleton] at hr; subst hr; exact dDS
  · rw [hw₁]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_arith
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [SlotTaint.region, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [SlotTaint.region, hw₂]

theorem cbcDecryptChained_constantTime (pre : State → Prop) (hpre : ∀ s, pre s → WidePre s) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := slotTaint) wideTaint
    (fun s₁ s₂ h₁ h₂ hp => wide_agree s₁ s₂ (hpre _ h₁) (hpre _ h₂) hp) (by taint_decide)

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) (hpre : ∀ s, pre s → WidePre s) :
    ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := slotTaint) wideTaint
    (fun s₁ s₂ h₁ h₂ hp => wide_agree s₁ s₂ (hpre _ h₁) (hpre _ h₂) hp) (by taint_decide)

theorem cfb8Encrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfb8Decrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

end VG.Proof.TripleDes.PPC64LE

end

end

/-!
# Triple DES's modes on PPC64LE meet their contracts

`cbcEncryptChained_verified`, `ofb_verified`, … : the modes of
`Proof/Modes/PPC64LE/` over Triple DES's core (`Mode.dirCoreSpec`), with the
working space as the fifth argument (`modeContract`, whose data is `st`
bytes a step: 8, or 1 for CFB8), meet the contracts with a scratch buffer of
72 words (`Proof.TripleDes.cbcEncChainedScratchContract`,
`fbScratchContract`, `cfb8ScratchContract`). CBC and CFB64 decryption run
over the core on 64 blocks (`Mode.wideCoreSpec`), by the groups of
`levels` (64, then 32, 16, 8 and 4 blocks a step), then one by the block
function (`Mode.wideOne_ok`), with a scratch buffer of 200 words.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Modes

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S)
open VG.Proof.TripleDes.PPC64LE.Mode (dirCoreSpec wideCoreSpec wideOne_ok KeyArgs layout layoutW)

/-- Triple DES under the schedule at `r3`, and its inverse. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3))
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.TripleDes.bytesAt m (s.gpr .r4) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.TripleDes.cbcBlocksAt m (s.gpr .r5) (s.gpr .r6).toNat
/-- The data, in bytes. -/
abbrev bytesOf (m : Mem) (s : State) : List Byte := Spec.TripleDes.bytesAt m (s.gpr .r5) (s.gpr .r6).toNat

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
def cfb8EncPost (s s' : State) : Prop :=
  bytesOf s'.mem s = Spec.Cfb8.encrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s) ∧
    ivAt s'.mem s = Spec.Cfb8.next (ivAt s.mem s) (Spec.Cfb8.encrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s))
def cfb8DecPost (s s' : State) : Prop :=
  bytesOf s'.mem s = Spec.Cfb8.decrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s) ∧
    ivAt s'.mem s = Spec.Cfb8.next (ivAt s.mem s) (bytesOf s.mem s)

/-- A mode's function on PPC64LE with its working space of `w` words as the
fifth argument, `st` bytes of data a step, and the postcondition `post`. -/
def modeContractW (w st : Nat) (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 384⟩
    let iv : Region := ⟨s.gpr .r4, 8⟩
    let data : Region := ⟨s.gpr .r5, st * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 8 * w⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r4).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + st * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 8 * w ≤ 2 ^ 64
  post := post
  pub := modePub

/-- `modeContractW` with the 72 words of the core on one block. -/
abbrev modeContract (st : Nat) (post : State → State → Prop) : Contract isa := modeContractW 72 st post

/-- `modeContract`'s precondition gives the modes'. -/
theorem seqPre_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) (hst : 0 < st) (hst8 : st ≤ 8) {s : State} (h : (modeContract st post).pre s) :
    SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h
  have e8 : 4 * (dirCore d).bw = 8 := rfl
  have eS : scrRegion (dirCore d) (S s) = ⟨s.gpr .r7, 8 * 72⟩ := rfl
  have eV : ivR s (dirCore d) = ⟨s.gpr .r4, 8⟩ := rfl
  refine ⟨⟨by rw [hwr]; simp [dirCore], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [e8]; exact fV, by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dDS,
    by rw [eV, eS]; exact dVS, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega_using [hstep, hst], by rw [e8]; omega_using [hstep, hst8]⟩, layout d⟩

theorem keyArgs_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) {s : State} (h : (modeContract st post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 (dirCore d) M s) (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) := by
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, -, -, -⟩ := h
  refine ⟨rfl, ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    Region.contains_self _ _⟩, fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .r3) 384).Disjoint ⟨s.gpr .r5, M.step * (s.gpr .r6).toNat⟩
    rw [hstep]; exact dKD
  · exact dKS

/-- `modeContractW`'s precondition, with 200 words, gives the modes' over the
core on 64 blocks. -/
theorem seqPreW_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) (hst : 0 < st) (hst8 : st ≤ 8) {s : State} (h : (modeContractW 200 st post).pre s) :
    SeqPre (wideCore d) M s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h
  have e8 : 4 * (wideCore d).bw = 8 := rfl
  have eS : scrRegion (wideCore d) (S s) = ⟨s.gpr .r7, 8 * 200⟩ := rfl
  have eV : ivR s (wideCore d) = ⟨s.gpr .r4, 8⟩ := rfl
  refine ⟨⟨by rw [hwr]; simp [wideCore, wideBuf], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [e8]; exact fV, by rw [hwr, hstep]; simp, by rw [hstep]; exact fD, by rw [hstep, eS]; exact dDS,
    by rw [eV, eS]; exact dVS, fun _ => by rw [eV, hstep]; exact dVD, ⟨by omega_using [hstep, hst], by rw [e8]; omega_using [hstep, hst8]⟩, layoutW d⟩

theorem keyArgsW_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) {s : State} (h : (modeContractW 200 st post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 (wideCore d) M s) (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) := by
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, -, -, -⟩ := h
  refine ⟨rfl, ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    Region.contains_self _ _⟩, fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .r3) 384).Disjoint ⟨s.gpr .r5, M.step * (s.gpr .r6).toNat⟩
    rw [hstep]; exact dKD
  · exact dKS

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

/-! ## Correctness -/

theorem cbcEncryptChained_correct (s : State) (hs : (modeContract 8 cbcEncPost).pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ (modeContract 8 cbcEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcEncChained_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cbcEncChained 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cbcEncChained 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cbcDecryptChained_correct (s : State) (hs : (modeContractW 200 8 cbcDecPost).pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ (modeContractW 200 8 cbcDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cbcDecLevelsWith_wp (wideCoreSpec .decrypt) (wideOne_ok .decrypt) (by decide)
    (seqPreW_of .decrypt (M := Mode.cbcDecChained 2) rfl (by decide) (by decide) hs)
    (keyArgsW_of .decrypt (M := Mode.cbcDecChained 2) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem ofb_correct (s : State) (hs : (modeContract 8 ofbPost).pre s) :
    ∃ t s', Exec isa ofb s t s' ∧ abiPreserved s s' ∧ (modeContract 8 ofbPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.ofb_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.ofb 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.ofb 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2, h3⟩

theorem cfbEncrypt_correct (s : State) (hs : (modeContract 8 cfbEncPost).pre s) :
    ∃ t s', Exec isa cfbEncrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 8 cfbEncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbEnc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfbEnc 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfbEnc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfbDecrypt_correct (s : State) (hs : (modeContractW 200 8 cfbDecPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (modeContractW 200 8 cfbDecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbDecLevelsWith_wp (wideCoreSpec .encrypt) (wideOne_ok .encrypt) (by decide)
    (seqPreW_of .encrypt (M := Mode.cfbDecEarly 2) rfl (by decide) (by decide) hs)
    (keyArgsW_of .encrypt (M := Mode.cfbDecEarly 2) rfl hs))
    fun _ ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [dataAt, dataAt, cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2,
      by rw [dataAt, cbcBlocksAt_eq]; exact h3⟩

theorem cfb8Encrypt_correct (s : State) (hs : (modeContract 1 cfb8EncPost).pre s) :
    ∃ t s', Exec isa cfb8Encrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 1 cfb8EncPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfb8Enc_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfb8Enc 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfb8Enc 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

theorem cfb8Decrypt_correct (s : State) (hs : (modeContract 1 cfb8DecPost).pre s) :
    ∃ t s', Exec isa cfb8Decrypt s t s' ∧ abiPreserved s s' ∧ (modeContract 1 cfb8DecPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfb8Dec_wp (dirCoreSpec .encrypt)
    (seqPre_of .encrypt (M := Mode.cfb8Dec 2) rfl (by decide) (by decide) hs)
    (keyArgs_of .encrypt (M := Mode.cfb8Dec 2) rfl hs))
    fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

/-- The regions of `modeContractW 200`, for the analysis of constant time. -/
theorem widePre_of {post : State → State → Prop} {s : State} (h : (modeContractW 200 8 post).pre s) :
    WidePre s := by
  obtain ⟨-, hwr, -, -, -, dVD, dVS, dDS, -, fD, -⟩ := h
  exact ⟨hwr, dVD, dVS, dDS, fD⟩

/-! ## The contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`,
the IV at `0x2000`, no data at `0x3000`, and the scratch buffer at `0x4000`. -/
def modeSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

/-- `modeSat`, with the working space of the core on 64 blocks. -/
def modeSatW : State := { modeSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 1600⟩] }

theorem modePub_iff (s₁ s₂ : State) : modePub s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 := by
  simp [modePub, PublicRegs]

theorem cbcEncryptChained_verified :
    Verified target cbcEncryptChained (Proof.TripleDes.cbcEncChainedScratchContract abi 72) := by
  refine Verified.of_correct cbcEncryptChained_correct (cbcEncryptChained_constantTime _) ?_
  sig_implies [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
    Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, abi, argRegs, modeContract, modeContractW, cbcEncPost,
    modePub_iff] [modeSat] using modeSat

theorem cbcDecryptChained_verified :
    Verified target cbcDecryptChained (Proof.TripleDes.cbcDecChainedScratchContract abi 200) := by
  refine Verified.of_correct cbcDecryptChained_correct (cbcDecryptChained_constantTime _ fun _ h => widePre_of h) ?_
  sig_implies [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
    Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, abi, argRegs, modeContractW, cbcDecPost,
    modePub_iff] [modeSatW, modeSat] using modeSatW

theorem ofb_verified :
    Verified target ofb (Proof.TripleDes.fbScratchContract abi 72 Proof.TripleDes.ofbPost) := by
  refine Verified.of_correct ofb_correct (ofb_constantTime _) ?_
  sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
    Proof.TripleDes.ofbPost, abi, argRegs, modeContract, modeContractW, ofbPost, modePub_iff] [modeSat] using modeSat

theorem cfbEncrypt_verified :
    Verified target cfbEncrypt (Proof.TripleDes.fbScratchContract abi 72 Proof.TripleDes.cfbEncPost) := by
  refine Verified.of_correct cfbEncrypt_correct (cfbEncrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
    Proof.TripleDes.cfbEncPost, abi, argRegs, modeContract, modeContractW, cfbEncPost, modePub_iff] [modeSat] using modeSat

theorem cfbDecrypt_verified :
    Verified target cfbDecrypt (Proof.TripleDes.fbScratchContract abi 200 Proof.TripleDes.cfbDecPost) := by
  refine Verified.of_correct cfbDecrypt_correct (cfbDecrypt_constantTime _ fun _ h => widePre_of h) ?_
  sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
    Proof.TripleDes.cfbDecPost, abi, argRegs, modeContractW, cfbDecPost, modePub_iff] [modeSatW, modeSat]
    using modeSatW

theorem cfb8Encrypt_verified :
    Verified target cfb8Encrypt (Proof.TripleDes.cfb8ScratchContract abi 72 Proof.TripleDes.cfb8EncPost) := by
  refine Verified.of_correct cfb8Encrypt_correct (cfb8Encrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
    Proof.TripleDes.cfb8EncPost, abi, argRegs, modeContract, modeContractW, cfb8EncPost, modePub_iff, Nat.one_mul] [modeSat] using modeSat

theorem cfb8Decrypt_verified :
    Verified target cfb8Decrypt (Proof.TripleDes.cfb8ScratchContract abi 72 Proof.TripleDes.cfb8DecPost) := by
  refine Verified.of_correct cfb8Decrypt_correct (cfb8Decrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
    Proof.TripleDes.cfb8DecPost, abi, argRegs, modeContract, modeContractW, cfb8DecPost, modePub_iff, Nat.one_mul] [modeSat] using modeSat

end VG.Proof.TripleDes.PPC64LE.Modes
