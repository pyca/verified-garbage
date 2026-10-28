module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.RedLeaves
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Linear
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Reduce
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Rows
import VerifiedGarbage.Proof.Framework.Omega

/-! # The batched inverse's compound operations in both runs

Each is its parts' lemmas joined by `RelCT.seq`, given the analysis's check of each part (`Ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt

/-- The analysis checks `c` from `τS`. -/
def Ok (c : Prog isa) : Prop := ∃ hc, (VG.Taint.check sseTaint τS c hc).isSome = true

variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

/-- What the batches need of the lengths: the sixteen arrays fit, and `n` is even, at least 2 and
small enough to count its batches and doublings in a word. -/
structure Fits (Z len : Nat) : Prop where
  fit : 160 + 16 * (8 * nw len + 8) ≤ Z
  two : 2 ≤ nw len
  even : nw len % 2 = 0
  small : nw len ≤ 1024

local notation "T2" => fun _ : Reg → BitVec 32 => True ∧ True

theorem relCorrection {c i : Nat} (hL : L.ws = 14) (F : Fits Z len) (hc4 : c + 4 ≤ 160) (hi : i < 11)
    (h₁ : Ok (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a i) (nBytes .edx 0)))
    (h₂ : Ok (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf c))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0)))) :
    RelCT isa (Both L B Z len N args sp C T2) (correction L c (a 11) (a i) tmp) (Both L B Z len N args sp C T2) := by
  have F1 := F.fit
  have r11 := rv_a len 11; have ri := rv_a len i; have r12 := rv_a len 12
  have e4 := rv_byte (kw len) (a 11) 4
  have rt : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have hiS : i * (8 * nw len + 8) + (8 * nw len + 8) ≤ 11 * (8 * nw len + 8) :=
    by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂
  exact RelCT.seq (relChainSub (X := fun _ => True) hL (stable_true _) (fun _ _ => trivial) (by decide) rfl
      (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega)
      (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega) h₁)
    (relMaskOfSel hL (stable_true _) hc4 (by omega) (by omega) (by omega) h₂)

theorem relLinear {u v i j e : Nat} (hL : L.ws = 14) (F : Fits Z len) (hu : u + 4 ≤ 160) (hv : v + 4 ≤ 160)
    (he : e ≤ 1) (hi : i < 11) (hj : j < 11)
    (h₁ : Ok (rowAdd L true u (a 11) (a i) (nBytes .esi e)))
    (h₂ : Ok (rowAdd L false v (a 11) (a j) (nBytes .esi e)))
    (h₃ : Ok (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a i) (nBytes .edx 0)))
    (h₄ : Ok (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf u))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0))))
    (h₅ : Ok (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a j) (nBytes .edx 0)))
    (h₆ : Ok (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf v))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0)))) :
    RelCT isa (Both L B Z len N args sp C T2) (linear L u v (a 11) (a i) (a j) tmp e)
      (Both L B Z len N args sp C T2) := by
  have F1 := F.fit
  have F2 := F.two
  have r11 := rv_a len 11; have ri := rv_a len i; have rj := rv_a len j
  have hiS : i * (8 * nw len + 8) + (8 * nw len + 8) ≤ 11 * (8 * nw len + 8) :=
    by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  have hjS : j * (8 * nw len + 8) + (8 * nw len + 8) ≤ 11 * (8 * nw len + 8) :=
    by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂
  unfold linear linearUnsigned
  exact RelCT.seq (RelCT.seq
      (relRowAdd hL (stable_true _) hu (by omega) rfl (by omega) (by omega) (by omega) h₁)
      (relRowAdd hL (stable_true _) hv (by omega) rfl (by omega) (by omega) (by omega) h₂))
    (RelCT.seq (relCorrection hL F hu hi h₃ h₄) (relCorrection hL F hv hj h₅ h₆))

theorem relRedSum (hL : L.ws = 14) (F : Fits Z len)
    (h₁ : Ok (.block (redHead L { arr := 11 })))
    (h₂ : Ok (mulRow L false { arr := 11 } mo (nBytes .esi 0)))
    (h₃ : Ok (.block (redTail L { arr := 11 }))) :
    RelCT isa (Both L B Z len N args sp C T2) (redSum L { arr := 11 }) (Both L B Z len N args sp C T2) := by
  have F1 := F.fit
  have r11 := rv_a len 11; have r2 := rv_a len 2
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have ra : rv (kw len) { arr := 11 } = rv (kw len) (a 11) := rfl
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂; obtain ⟨_, h₃⟩ := h₃
  exact RelCT.seq (relRedHead hL (stable_true _) rfl rfl (by omega) h₁)
    (RelCT.seq (relMulRow hL (stable_true _) (by decide) rfl (by omega) (by omega) (by omega) h₂)
      (relRedTail hL (stable_true _) rfl rfl (by omega) h₃))

/-- `csub src o` with any register facts that it keeps (`esi`'s, in the doublings). -/
theorem relCsub {G : (Reg → BitVec 32) → Prop} {src o : Ref} (hL : L.ws = 14)
    (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G) (F : Fits Z len) (hsh : src.half = 0) (hoh : o.half = 0)
    (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z) (hoz : rv (kw len) o + 4 * nw len ≤ Z)
    (hts : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) tmp)
    (hos : o ≠ src → rv (kw len) o + 4 * nw len ≤ rv (kw len) src ∨ rv (kw len) src + 4 * nw len ≤ rv (kw len) o)
    (hot : rv (kw len) o + 4 * nw len ≤ rv (kw len) tmp ∨ rv (kw len) tmp + 4 * nw len ≤ rv (kw len) o)
    (h₁ : Ok (chain L .sbb tmp src mo (nBytes .edx 0))) (h₂ : Ok (.block (borrowMask L src)))
    (h₃ : Ok (if o = src then selIn L o tmp (nBytes .edi 0)
      else .seq (.block (ptr L .ebp src .edx ++ ptr L .ebx tmp .edx ++ nBytes .edx 0 ++ ptr L .edi o .eax))
        (.seq select3LoopX (.block (restoreEdi L))))) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.csub L src o)
      (Both L B Z len N args sp C fun g => G g ∧ True) := by
  have F1 := F.fit
  have r12 := rv_a len 12; have r2 := rv_a len 2
  have rt : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have rs := rv_ge (kw len) src
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂; obtain ⟨_, h₃⟩ := h₃
  unfold VG.Impl.Rsa.X86.InvBatchRt.csub
  refine RelCT.seq (relChainSub (X := Mask) hL hG (fun _ h => h) (by decide) rfl
      (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega)
      (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega) h₁)
    (RelCT.seq (relBorrowMask hL (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) hsh hsz h₂) ?_)
  by_cases ho : o = src
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ho)] at h₃ ⊢
    subst ho
    exact relSelIn hL (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) (by decide)
      (by simpa using hoz) (by simpa using (by omega : rv (kw len) tmp + 4 * nw len ≤ Z)) (by simp only [Nat.add_zero]; omega) h₃
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ho)] at h₃ ⊢
    exact relSelect3 hL (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) hoh hoz (by omega) (by omega)
      (hos ho) hot h₃

theorem relReduce {j : Nat} (hL : L.ws = 14) (F : Fits Z len) (hj : 13 ≤ j) (hj' : j < 16)
    (h₁ : Ok (.block (redHead L { arr := 11 })))
    (h₂ : Ok (mulRow L false { arr := 11 } mo (nBytes .esi 0)))
    (h₃ : Ok (.block (redTail L { arr := 11 })))
    (h₄ : Ok (chain L .adc tmp { arr := 11, byte := 4 } mo (nBytes .edx 0)))
    (h₅ : Ok (.block (negTop L { arr := 11, byte := 4 })))
    (h₆ : Ok (selIn L { arr := 11, byte := 4 } tmp (nBytes .edi 1)))
    (h₇ : Ok (chain L .sbb tmp { arr := 11, byte := 4 } mo (nBytes .edx 0)))
    (h₈ : Ok (.block (borrowMask L { arr := 11, byte := 4 })))
    (h₉ : Ok (.seq (.block (ptr L .ebp { arr := 11, byte := 4 } .edx ++ ptr L .ebx tmp .edx ++ nBytes .edx 0 ++
      ptr L .edi (a j) .eax)) (.seq select3LoopX (.block (restoreEdi L))))) :
    RelCT isa (Both L B Z len N args sp C T2) (reduce L (a j)) (Both L B Z len N args sp C T2) := by
  have F1 := F.fit
  have r11 := rv_a len 11; have r12 := rv_a len 12; have r2 := rv_a len 2; have rj := rv_a len j
  have rt : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have r4 : rv (kw len) { arr := 11, byte := 4 } = rv (kw len) (a 11) + 4 := rv_byte (kw len) (a 11) 4
  have j13 : 13 * (8 * nw len + 8) ≤ j * (8 * nw len + 8) := Nat.mul_le_mul_right _ hj
  have j15 : j * (8 * nw len + 8) + (8 * nw len + 8) ≤ 16 * (8 * nw len + 8) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj'
  have ne : a j ≠ { arr := 11, byte := 4 } := by intro e; cases e
  obtain ⟨_, h₄⟩ := h₄; obtain ⟨_, h₅⟩ := h₅; obtain ⟨_, h₆⟩ := h₆
  unfold reduce addIfNeg
  refine RelCT.seq (relRedSum hL F h₁ h₂ h₃) (RelCT.seq (RelCT.seq
    (relChainAdd (X := Mask) hL (stable_true _) (fun _ h => h) (by decide) rfl
      (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega)
      (by simp only [Nat.add_zero]; omega) (by simp only [Nat.add_zero]; omega) h₄)
    (RelCT.seq (relNegTop hL (stable_true _) rfl (by omega) (by omega) (by omega) h₅)
      (relSelIn hL (stable_true _) (by decide) (by omega) (by omega) (by omega) h₆)))
    (relCsub hL (stable_true _) F rfl rfl (by omega) (by omega) (by omega) (fun _ => by omega) (by omega)
      h₇ h₈ (by rw [ite_eq_right_of_eq_false _ _ (eq_false ne)]; exact h₉)))

end VG.Proof.Rsa.X86.InvBatchRt.Time
