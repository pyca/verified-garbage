module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaintMono
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintMono
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintMono
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! # Constant-time Triple DES modes on PPC64LE

Only the pointers and the count (`r3`–`r7`) are public. The block functions
are analysed at their calls; they never write `r29`–`r31`, which hold the
IV's address, the steps left and the data pointer, nor `r3` and `r5`, which
hold the schedule and the scratch buffer.

CBC and CFB64 decryption run the bitsliced ECB inline, which saves `r29`–`r31`
in the scratch buffer and restores them from there: their analysis is
`VG.PPC64LE.slotTaint`, which knows that those slots survive ECB's stores, all
at fixed offsets of the scratch buffer (the third writable region, at `r7`
on entry), as for SM4's modes (`Proof/Sm4/PPC64LE/ModesConstantTime.lean`).

The bitsliced ECB of the two directions is the same code but for the order
of its passes, whose rounds are those of one direction or the other: its
blocks (the copy in and the transposition, two rounds in each direction,
and the transposition back, the copy out and the registers' restoring) are
analysed once, as summaries (`inSum`, `roundsEncSum`, `roundsDecSum`,
`outSum`), which the checks of CBC and CFB64 decryption use
(`taint_decide_sum`) in place of their analysis in each. -/

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

/-- What ECB has public where it copies the blocks in, after its `setup`, of what the summary
needs: the buffer (`r4`), the schedule (`r7`) and the working space (`r10`), the slots where it
saved the modes' `r29`–`r31`, and the registers that hold addresses of the working space. A
summary of this analysis applies only where the taint knows the same lengths and bases
(`Proof/Framework/PPC64LE/SlotTaintMono.lean`). -/
def τIn : SlotTaint.T :=
  { regs := .ofList [.r4, .r7, .r10], lens := [8, 0, 1600],
    bases := [(.r5, 2, 0), (.r6, 2, 0), (.r4, 2, 1024), (.r10, 2, 0), (.r8, 2, 0)],
    slots := [(2, 704, 8), (2, 696, 8), (2, 688, 8)] }

/-- The same in ECB's passes and after them, where the rounds' loops have also the key pointer
(`r3`) and their count (`r5`) public, and know the bases that the rounds keep. -/
def τRounds : SlotTaint.T :=
  { regs := .ofList [.r3, .r4, .r5, .r7, .r10], lens := [8, 0, 1600],
    bases := [(.r4, 2, 1024), (.r10, 2, 0), (.r8, 2, 0)],
    slots := [(2, 704, 8), (2, 696, 8), (2, 688, 8)] }

/-! The constant-time analysis of ECB's copy in and transposition, once for both directions. -/
taint_summary inSum : slotTaint τIn (.block (Bitslice.copyIn64 ++ Bitslice.transpose))

/-! The same of two rounds, in each direction: the body of the loop of every pass. -/
taint_summary roundsEncSum : slotTaint τRounds (.block (Bitslice.roundPair .encrypt))

taint_summary roundsDecSum : slotTaint τRounds (.block (Bitslice.roundPair .decrypt))

/-! The same of ECB's transposition back, copy out and restoring of the registers, which leaves
the modes' `r29`–`r31` public, from their slots. -/
taint_summary outSum : slotTaint τRounds
  (.block (Bitslice.transpose ++ Bitslice.copyOut64 ++ Bitslice.finish))

theorem cbcDecryptChained_constantTime (pre : State → Prop) (hpre : ∀ s, pre s → WidePre s) :
    ConstantTime isa pre modePub cbcDecryptChained :=
  VG.Taint.constantTime_of_exists (A := slotTaint) wideTaint
    (fun s₁ s₂ h₁ h₂ hp => wide_agree s₁ s₂ (hpre _ h₁) (hpre _ h₂) hp)
    (by taint_decide_sum [inSum, roundsEncSum, roundsDecSum, outSum])

theorem ofb_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbEncrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfbDecrypt_constantTime (pre : State → Prop) (hpre : ∀ s, pre s → WidePre s) :
    ConstantTime isa pre modePub cfbDecrypt :=
  VG.Taint.constantTime_of_exists (A := slotTaint) wideTaint
    (fun s₁ s₂ h₁ h₂ hp => wide_agree s₁ s₂ (hpre _ h₁) (hpre _ h₂) hp)
    (by taint_decide_sum [inSum, roundsEncSum, roundsDecSum, outSum])

theorem cfb8Encrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

theorem cfb8Decrypt_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfb8Decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => modes_ofRegs _ _ hp) (by taint_decide)

end VG.Proof.TripleDes.PPC64LE
