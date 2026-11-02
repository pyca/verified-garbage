module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Exp7
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont2

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont9
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont8
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont5
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint6
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Inv
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Rsa.Arm.RvMont5
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

/-! # A candidate on ARMv7: the Montgomery forms of 1 and −1 (`montB_vp`)

`R mod c` from `1 · R²` into the key arrays `mBase + 1` and `mBase + 9`
(Montgomery multiplication's array 9, the round's `one`), and
`c − R mod c` into `mBase + 10` (its `minusOne`): the stage `SM`. The
steps of the key working space keep `MS` (`copy_keepM`, `sub3_keepM`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP sub32)

/-- `R mod c`. -/
abbrev Rm (P : CP) (σ : State) : Nat := 2 ^ (64 * P.w) % cv P σ

def AB2 (P : CP) (σ : State) : Nat → Nat :=
  upd (upd (AX P σ) (mBase + 9) (Rm P σ)) (mBase + 10) (cv P σ - Rm P σ)
abbrev LB2 : List Nat := [mBase + 10, mBase + 9, mBase + 27, aCm1, aTwo, aOne, aC]

/-- Montgomery multiplication modulo `c` ready, with the forms of 1 and −1. -/
abbrev SM (P : CP) (E : State → Prop) (σ s : State) : Prop := St P E (AB2 P) LB2 (V3 P) [sUsed] σ s ∧ MS P σ s

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem St.inSp {σ s : State} (h : St P E A L V LS σ s) : In P σ ∧ s.sp = P.sp :=
  ⟨h.2.1.pre, h.2.1.sp.trans h.2.1.pre.sp⟩

theorem copy_keepM {o a : Nat} (ho : o < nArr) (ha : a ∈ L) (hoa : o ≠ a) (hM : MOk o) :
    ∀ σ s, St P E A L V LS σ s → WP isa (copy o a) s fun t => ∃ js ds, Keep P.B P.W js ds s.mem t.mem ∧
      (∀ j ∈ js, MOk j) ∧ (∀ d ∈ ds, d + 4 ≤ hdr) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  fun _ _ ⟨_, h, hw⟩ => WP.mono (copy_ok hw ho (h.live_lt a ha) (by decide) hoa) fun _ ⟨_, k, _, r, _⟩ =>
    ⟨[o], [], k, by simp [hM], by simp, r.sp, r.rd, r.wr⟩

theorem sub3_keepM {o a b : Nat} (ho : o < nArr) (ha : a ∈ L) (hb : b ∈ L) (hoa : o ≠ a) (hob : o ≠ b)
    (hM : MOk o) :
    ∀ σ s, St P E A L V LS σ s → WP isa (sub3 o a b) s fun t => ∃ js ds, Keep P.B P.W js ds s.mem t.mem ∧
      (∀ j ∈ js, MOk j) ∧ (∀ d ∈ ds, d + 4 ≤ hdr) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  fun _ _ ⟨_, h, hw⟩ => WP.mono (sub3_ok hw ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob)
    fun _ ⟨_, k, _, _, r⟩ => ⟨[o], [], k, by simp [hM], by simp, r.sp, r.rd, r.wr⟩

theorem Rm_lt {σ : State} (pre : In P σ) : Rm P σ < cv P σ := Nat.mod_lt _ (by have := cv_gt pre; omega)

theorem R_coprime {σ : State} (pre : In P σ) : Nat.Coprime (2 ^ (64 * P.w)) (cv P σ) := by
  have hodd := (cv_shape (σ := σ) pre).1
  exact Nat.Coprime.pow_left _ (by show Nat.gcd 2 (cv P σ) = 1; rw [Nat.gcd_rec, hodd]; rfl)

theorem key_lt_R {σ : State} (pre : In P σ) {x : Nat} (hx : x < cv P σ) : x < 2 ^ (32 * P.W) := by
  have := cv_lt pre
  have : 2 ^ (64 * P.w) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by have := pre.W_eq; omega)
  omega

theorem montB_vp : VP (fun σ s => SX P E σ s ∧ MS P σ s) montB (SM P E) := by
  simp only [montB, seqs]
  refine VP.seq (VP.withMS (St.pcopy (E := E) (A := AX P) (L := LX) (V := V3 P) (LS := [sUsed]) copy1One_taint
    (by decide) (by simp) (by decide)) (fun σ s h => h.inSp)
    (copy_keepM (by decide) (by simp) (by decide) (by decide))) ?_
  refine VP.seq St.pmont0 ?_
  refine VP.seq ((St.pmontOp (o := 1) (a := 1) (b := 4) (L' := LX) ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ (by decide) (by decide) (na := fun _ => 1) (nb := r2v P) (fun σ s h m => ⟨?_, m.r2⟩) (fun σ e pre => ?_)
    (fun j hj => ⟨by mem_sub, by mem_sub, by mem_sub, by mem_sub⟩)).mono (fun _ _ h => h)
    fun σ s ⟨k, m, lt, val⟩ => (⟨k, m, by
      have pre := k.2.pre
      refine VG.Proof.RsaKeyGen.mont_inj (R_coprime pre) lt (Rm_lt pre) ?_
      rw [val, Nat.one_mul]
      show 2 ^ (128 * P.w) % cv P σ % cv P σ = 2 ^ (64 * P.w) % cv P σ * 2 ^ (64 * P.w) % cv P σ
      rw [Nat.mod_mod, Nat.mod_mul_mod, ← Nat.pow_add, show 64 * P.w + 64 * P.w = 128 * P.w by omega]⟩ :
      (E σ ∧ KS P σ _ LX (V3 P σ) [sUsed] s) ∧ MS P σ s ∧ numAt s.mem (State.addr P.M0) P.w 1 = Rm P σ)) ?_
  · have pre := h.2.1.pre
    have e := h.2.1.arrs (mBase + 1) (by simp)
    have v1 : AX P σ aOne = 1 := by simp (config := {decide := true}) only [AX, A3, A0, upd, ↓reduceIte]
    simp only [upd_self, v1] at e
    rw [pre.numAt_eq (by rw [e]; exact Nat.one_lt_two_pow (by have := pre.w4; omega)), e]
  · exact Nat.mod_lt _ (by have := cv_gt pre; omega)
  refine VP.seq (St.pctxClr clrTop1_taint (by decide) (by decide)) ?_
  refine VP.seq (VP.withMS (St.pcopy copy9_taint (by decide) (by simp) (by decide)) (fun σ s h => h.inSp)
    (copy_keepM (by decide) (by simp) (by decide) (by decide))) ?_
  refine (VP.withMS (St.psub3 sub10_taint (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun σ s h => h.inSp) (sub3_keepM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))).mono
    (fun _ _ h => h) fun σ s ⟨h, m⟩ => ⟨h.mono (fun j hj => ⟨by mem_sub, ?_⟩) (fun d hd => ⟨hd, rfl⟩), m⟩
  have pre := h.2.1.pre
  have hlt := Rm_lt pre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AB2, AX, A3, A0]
    have c1 : cv P σ < 2 ^ (32 * P.W) := by
      have := cv_lt pre
      have : 2 ^ (64 * P.w) ≤ 2 ^ (32 * P.W) := Nat.pow_le_pow_right (by decide) (by have := pre.W_eq; omega)
      omega
    rw [sub32_val c1 (key_lt_R pre hlt), ite_eq_right (by omega)]
  all_goals simp (config := {decide := true}) only [upd, ↓reduceIte, AB2, AX]

end

end VG.Proof.Dsa.Arm.Prime
