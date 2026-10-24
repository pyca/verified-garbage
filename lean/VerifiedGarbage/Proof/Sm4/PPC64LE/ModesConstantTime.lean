module

public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! # Constant-time SM4 modes on PPC64LE

Only the pointers and the count (`r3`–`r7`) are public. The analysis is
`VG.PPC64LE.slotTaint`: the modes keep their state (the IV's address, the
steps left and the data pointer) in `r29`–`r31`, which the prepared functions
save in their working space (the scratch buffer, the third writable region,
whose base is `r7` on entry) and restore from there, and the analysis knows
that those slots survive the functions' stores, all at known offsets of the
working space. The prepared functions are analysed at their calls.

`modeContract st post` is the modes' contract with the working space as the
fifth argument and `st` bytes of data a step: its precondition gives the
writable regions and the registers that point at them (`modes_agree`). -/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE

/-- The modes' public arguments. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], s₁.gpr r = s₂.gpr r

/-- A mode's function on PPC64LE with its working space as the fifth
argument, `st` bytes of data a step, and the postcondition `post`. -/
def modeContract (st : Nat) (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 128⟩
    let iv : Region := ⟨s.gpr .r4, 16⟩
    let data : Region := ⟨s.gpr .r5, st * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 8 * (slots + 6)⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + st * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 8 * (slots + 6) ≤ 2 ^ 64
  post := post
  pub := modePub

/-- The taint on entry: the arguments public, the IV, the data and the
scratch buffer the writable regions at `r4`, `r5` and `r7`, the scratch
buffer's whole length known. -/
def modeTaint : SlotTaint.T := SlotTaint.mk' [.r3, .r4, .r5, .r6, .r7] [16, 0, 8 * (slots + 6)]
  [(.r4, 0), (.r5, 1), (.r7, 2)]

theorem modes_agree {st : Nat} {post : State → State → Prop} (s₁ s₂ : State)
    (h₁ : (modeContract st post).pre s₁) (h₂ : (modeContract st post).pre s₂) (hp : modePub s₁ s₂) :
    SlotTaint.Agree modeTaint s₁ s₂ := by
  obtain ⟨-, hw₁, -, -, -, dVD, dVS, dDS, -, fV, fD, fS⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
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
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [SlotTaint.region, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [SlotTaint.region, hw₂]

theorem cbcEncryptChained_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract 16 post).pre modePub cbcEncryptChained :=
  VG.Taint.constantTime (A := slotTaint) modeTaint modes_agree (by taint_decide)

theorem cbcDecryptChained_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract 16 post).pre modePub cbcDecryptChained :=
  VG.Taint.constantTime (A := slotTaint) modeTaint modes_agree (by taint_decide)

theorem ofb_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract 16 post).pre modePub ofb :=
  VG.Taint.constantTime (A := slotTaint) modeTaint modes_agree (by taint_decide)

theorem cfbEncrypt_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract 16 post).pre modePub cfbEncrypt :=
  VG.Taint.constantTime (A := slotTaint) modeTaint modes_agree (by taint_decide)

theorem cfbDecrypt_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract 16 post).pre modePub cfbDecrypt :=
  VG.Taint.constantTime (A := slotTaint) modeTaint modes_agree (by taint_decide)

end VG.Proof.Sm4.PPC64LE
