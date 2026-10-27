module

public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Modes
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.CallSum
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Constant-time Camellia modes on PPC64LE

Only the pointers, the number of rounds and the count (`r3`–`r8`) are
public. The analysis is `VG.PPC64LE.slotTaint`: the modes keep the number of
rounds in `r28` and their state (the IV's address, the steps left and the
data pointer) in `r29`–`r31`. The inlined body of
`vg_camellia_prepare_keys` stores through a pointer the analysis cannot
place, so the core keeps them meanwhile in registers the body does not
write; `vg_camellia_crypt_prepared` saves them in its working space (the
scratch buffer, the third writable region, whose base is `r8` on entry) and
restores them from there, and the analysis knows that those slots survive
its stores, all at known offsets of the working space. The function is
analysed once, as a summary of its call (`CallSum.lean`).

`modeContract post` is the modes' contract with the working space as the
sixth argument: its precondition gives the writable regions and the
registers that point at them (`modes_agree`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.Impl.Camellia.PPC64LE

/-- The modes' public arguments: the stack pointer and `r3`–`r8`. -/
def modePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8], s₁.gpr r = s₂.gpr r

/-- A mode's function on PPC64LE with its working space as the sixth
argument, and the postcondition `post`. -/
def modeContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 272⟩
    let iv : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * modeSlots⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r3).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 16 * (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * modeSlots ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 18 ∨ (s.gpr .r4).toNat = 24)
  post := post
  pub := modePub

/-- The taint on entry: the arguments public, the IV, the data and the
scratch buffer the writable regions at `r5`, `r6` and `r8`, the scratch
buffer's whole length known. -/
def modeTaint : SlotTaint.T := SlotTaint.mk' [.r3, .r4, .r5, .r6, .r7, .r8] [16, 0, 8 * modeSlots]
  [(.r5, 0), (.r6, 1), (.r8, 2)]

theorem modes_agree {post : State → State → Prop} (s₁ s₂ : State)
    (h₁ : (modeContract post).pre s₁) (h₂ : (modeContract post).pre s₂) (hp : modePub s₁ s₂) :
    SlotTaint.Agree modeTaint s₁ s₂ := by
  obtain ⟨-, hw₁, -, -, -, dVD, dVS, dDS, -, fV, fD, fS, -⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
  obtain ⟨hsp, hr⟩ := hp
  have r5 := hr .r5 (by simp)
  have r6 := hr .r6 (by simp)
  have r7 := hr .r7 (by simp)
  have r8 := hr .r8 (by simp)
  refine SlotTaint.agree_mk' hsp (fun r h => hr r (by simpa using h)) (by rw [hw₁, hw₂, r5, r6, r7, r8])
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
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [cryptSum])

theorem cbcDecryptChained_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract post).pre modePub cbcDecryptChained :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [cryptSum])

theorem ofb_constantTime {post : State → State → Prop} : ConstantTime isa (modeContract post).pre modePub ofb :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [cryptSum])

theorem cfbEncrypt_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract post).pre modePub cfbEncrypt :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [cryptSum])

theorem cfbDecrypt_constantTime {post : State → State → Prop} :
    ConstantTime isa (modeContract post).pre modePub cfbDecrypt :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [cryptSum])

theorem ctr_constantTime {post : State → State → Prop} : ConstantTime isa (modeContract post).pre modePub ctr :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree (by taint_decide_sum [cryptSum])

end VG.Proof.Camellia.PPC64LE
