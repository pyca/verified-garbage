module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Step

/-! # The batched inverse's compound operations in both runs

Each is its parts' lemmas joined by `RelCT.seq`, given the analysis's check of each part (`Ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt

/-- The analysis checks `c` from `τS`. -/
def Ok (L : Lay) (c : Prog isa) : Prop := ∃ hc, (VG.Taint.check sseTaint (τS L) c hc).isSome = true

variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

/-- What the operations need of the lengths: the sixteen arrays fit, and `n` is at least 2. -/
structure Room (Z len : Nat) : Prop where
  fit : 160 + 16 * (8 * nw len + 8) ≤ Z
  two : 2 ≤ nw len

/-- What the batches need of the lengths: `Room`, and `n` even and small enough to count its
batches and doublings in a word. -/
structure Fits (Z len : Nat) : Prop extends Room Z len where
  even : nw len % 2 = 0
  small : nw len ≤ 1024

local notation "T2" => fun _ : Reg → BitVec 32 => True ∧ True

theorem relCorrection {c i : Nat} (F : Room Z len) (hc4 : c + 4 ≤ 160) (hi : i < 11)
    (h₁ : Ok L (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a i) (nBytes .edx 0)))
    (h₂ : Ok L (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf c))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0)))) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2) (correction L c (a 11) (a i) tmp)
      (Both L B Z len N (nw len) args sp C T2) := by
  have F1 := F.fit
  have r11 := rv_a len 11 (nw len); have ri := rv_a len i (nw len); have r12 := rv_a len 12 (nw len)
  have e4 := rv_byte (kw len) (a 11) 4 (nw len)
  have rt : rv (kw len) tmp (nw len) = rv (kw len) (a 12) (nw len) := rfl
  have hiS : i * (8 * nw len + 8) + (8 * nw len + 8) ≤ 11 * (8 * nw len + 8) :=
    by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂
  exact RelCT.seq (relChainSub (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
      (by simp only [Nat.add_zero]; omega_using [F1, r12, rt]) (by simp only [Nat.add_zero]; omega_using [F1, r11, e4]) (by simp only [Nat.add_zero]; omega_using [F1, ri, hiS])
      (by simp only [Nat.add_zero]; omega_using [r11, r12, e4, rt]) (by simp only [Nat.add_zero]; omega_using [ri, r12, rt, hiS]) h₁)
    (relMaskOfSel (stable_true _) hc4 (by omega_using [F1, r11]) (by omega_using [F1, r12, rt]) (by omega_using [r11, r12, rt]) h₂)

theorem relLinear {u v i j e : Nat} (F : Room Z len) (hu : u + 4 ≤ 160) (hv : v + 4 ≤ 160)
    (he : e ≤ 1) (hi : i < 11) (hj : j < 11)
    (h₁ : Ok L (rowAdd L true u (a 11) (a i) (nBytes .esi e)))
    (h₂ : Ok L (rowAdd L false v (a 11) (a j) (nBytes .esi e)))
    (h₃ : Ok L (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a i) (nBytes .edx 0)))
    (h₄ : Ok L (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf u))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0))))
    (h₅ : Ok L (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a j) (nBytes .edx 0)))
    (h₆ : Ok L (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf v))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0)))) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2) (linear L u v (a 11) (a i) (a j) tmp e)
      (Both L B Z len N (nw len) args sp C T2) := by
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
      (relRowAdd (stable_true _) hu (by omega_using [he]) rfl (by omega_using [he, F1, r11]) (by omega_using [he, F1, ri, hiS]) (by omega_using [he, r11, ri, hiS]) h₁)
      (relRowAdd (stable_true _) hv (by omega_using [he]) rfl (by omega_using [he, F1, r11]) (by omega_using [he, F1, rj, hjS]) (by omega_using [he, r11, rj, hjS]) h₂))
    (RelCT.seq (relCorrection F hu hi h₃ h₄) (relCorrection F hv hj h₅ h₆))

/-- `csub src o` with any register facts that it keeps (`esi`'s, in the doublings). -/
theorem relCsub {G : (Reg → BitVec 32) → Prop} {src o : Ref}
    (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G) (F : Room Z len) (hsh : src.half = 0) (hoh : o.half = 0)
    (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z) (hoz : rv (kw len) o + 4 * nw len ≤ Z)
    (hts : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) tmp)
    (hos : o ≠ src → rv (kw len) o + 4 * nw len ≤ rv (kw len) src ∨ rv (kw len) src + 4 * nw len ≤ rv (kw len) o)
    (hot : rv (kw len) o + 4 * nw len ≤ rv (kw len) tmp ∨ rv (kw len) tmp + 4 * nw len ≤ rv (kw len) o)
    (h₁ : Ok L (chain L .sbb tmp src mo (nBytes .edx 0))) (h₂ : Ok L (.block (borrowMask L src)))
    (h₃ : Ok L (if o = src then selIn L o tmp (nBytes .edi 0)
      else .seq (.block (ptr L .ebp src .edx ++ ptr L .ebx tmp .edx ++ nBytes .edx 0 ++ ptr L .edi o .eax))
        (.seq select3LoopX (.block (restoreEdi L))))) :
    RelCT isa (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.csub L src o)
      (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) := by
  have F1 := F.fit
  have r12 := rv_a len 12; have r2 := rv_a len 2
  have rt : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have rs := rv_ge (kw len) src
  -- The parts' statements at rows of `nw len` words, the same places.
  have qs : rv (kw len) src (nw len) = rv (kw len) src := rfl
  have qo : rv (kw len) o (nw len) = rv (kw len) o := rfl
  have qt : rv (kw len) tmp (nw len) = rv (kw len) tmp := rfl
  have qm : rv (kw len) mo (nw len) = rv (kw len) mo := rfl
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂; obtain ⟨_, h₃⟩ := h₃
  unfold VG.Impl.Rsa.X86.InvBatchRt.csub
  refine RelCT.seq (relChainSub (X := Mask) hG (fun _ h => h) (by decide) rfl
      (by simp only [Nat.add_zero]; omega_using [F1, r12, rt, qt]) (by simp only [Nat.add_zero]; omega_using [hsz, qs]) (by simp only [Nat.add_zero]; omega_using [F1, r2, rmo, qm])
      (by simp only [Nat.add_zero]; omega_using [hts, qs, qt]) (by simp only [Nat.add_zero]; omega_using [r12, r2, rt, rmo, qt, qm]) h₁)
    (RelCT.seq (relBorrowMask (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) hsh hsz h₂) ?_)
  by_cases ho : o = src
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ho)] at h₃ ⊢
    subst ho
    exact relSelIn (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) (by decide)
      (by simpa using hoz) (by simpa using (by omega_using [F1, r12, rt] : rv (kw len) tmp + 4 * nw len ≤ Z)) (by simp only [Nat.add_zero]; omega_using [hot, qo, qt]) h₃
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ho)] at h₃ ⊢
    exact relSelect3 (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) hoh hoz (by omega_using [hsz]) (by omega_using [F1, r12, rt])
      (hos ho) hot h₃

end VG.Proof.Rsa.X86.InvBatchRt.Time
