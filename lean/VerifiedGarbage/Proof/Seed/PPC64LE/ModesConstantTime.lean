module

public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Seed.PPC64LE.CallSum
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Seed.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Constant-time SEED modes on PPC64LE

Only the pointers and the count (`r3`–`r7`) are public. The analysis is
`VG.PPC64LE.slotTaint`: the modes keep their state (the IV's address, the
steps left and the data pointer) in `r29`–`r31`, which the blocks function
saves in its working space (the scratch buffer, the third writable region)
around each batch's rounds and restores from there; between the two it
stores only at known offsets of the working space, so the analysis knows
that those slots survive, and finds them as public after the call as before.
The core takes `sb` back from `r8`, which the analysis knows to point at the
scratch buffer. The blocks functions are analysed once, as summaries of their
calls (`CallSum.lean`).

`modeContract post` is the modes' contract with the working space as the
fifth argument: its precondition gives the writable regions and the
registers that point at them (`modes_agree`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.Impl.Seed.PPC64LE

/-- The modes' public arguments: the stack pointer and `r3`–`r7`. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], s₁.gpr r = s₂.gpr r

/-- A mode's function on PPC64LE with its working space as the fifth
argument, and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 128⟩
    let iv : Region := ⟨s.gpr .r4, 16⟩
    let data : Region := ⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 8 * 144⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r4).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 16 * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 8 * 144 ≤ 2 ^ 64
  post := post
  pub := modePub

/-- The taint on entry: the arguments public, the IV, the data and the
scratch buffer the writable regions at `r4`, `r5` and `r7`, the scratch
buffer's whole length known. -/
def modeTaint : SlotTaint.T := SlotTaint.mk' [.r3, .r4, .r5, .r6, .r7] [16, 0, 8 * 144]
  [(.r4, 0), (.r5, 1), (.r7, 2)]

theorem modes_agree {post : State → State → Prop} (s₁ s₂ : State)
    (h₁ : (modeContract post).pre s₁) (h₂ : (modeContract post).pre s₂) (hp : modePub s₁ s₂) :
    SlotTaint.Agree modeTaint s₁ s₂ := by
  obtain ⟨-, hw₁, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h₁
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
    ConstantTime isa (modeContract post).pre modePub cbcEncryptChained :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [encryptSum])

theorem cbcDecryptChained_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract post).pre modePub cbcDecryptChained :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [decryptSum])

theorem ofb_constantTime {post : State → State → Prop} : ConstantTime isa (modeContract post).pre modePub ofb :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [encryptSum])

theorem cfbEncrypt_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract post).pre modePub cfbEncrypt :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [encryptSum])

theorem cfbDecrypt_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract post).pre modePub cfbDecrypt :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [encryptSum])

end VG.Proof.Seed.PPC64LE
