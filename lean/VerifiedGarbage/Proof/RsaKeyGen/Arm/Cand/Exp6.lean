module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Exp5
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: conditional halvings and the exponent's top word

`St.phalfIf sl`: `[aEx]` halved if the header word `sl` holds 1;
`St.pexpTop`: the words `W − 2` and `W − 1` of the array `mBase + 27` set
from the header words `sLo` and `sHi`; `shift_div`: the halvings under the
masks divide by `2^σ`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

/-- Halved if `b` is 1. -/
def hIf (x b : Nat) : Nat := if b = 0 then x else x / 2

/-- The halvings under the masks of `σ > 1`, `σ > 2` and `σ > 3` divide by
`2^σ`, `σ = 4` for `t ≡ 0` and `t mod 4` otherwise. -/
theorem shift_div (c t : Nat) :
    hIf (hIf (hIf (c / 2) (b2n (decide (t % 4 ≠ 1)))) (b2n (decide (t % 4 = 3 ∨ t % 4 = 0))))
      (b2n (decide (t % 4 = 0))) = c / 2 ^ (if t % 4 = 0 then 4 else t % 4) := by
  have h := Nat.mod_lt t (show 0 < 4 by decide)
  rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with e | e | e | e <;>
    simp [e, hIf, b2n, Nat.div_div_eq_div_mul]

/-- For an odd `c`, `(c − 1) / 2^σ = c / 2^σ` (`σ ≥ 1`). -/
theorem odd_div {c s : Nat} (hc : c % 2 = 1) (hs : 1 ≤ s) : (c - 1) / 2 ^ s = c / 2 ^ s := by
  obtain ⟨q, rfl⟩ : ∃ q, c = 2 * q + 1 := ⟨c / 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ r), ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1; omega

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `halfIf sl`: `[aEx]` halved if the header word `sl` holds 1. -/
theorem St.phalfIf {sl : Nat} (cs : Cert (sel aEx aH1 aH2 sl)) (hx : aEx ∈ L) (hsl : sl ∈ LS)
    (bit : ∀ σ, E σ → V σ sl ≤ 1) :
    VP (St P E A L V LS) (seqs (halfIf sl))
      (St P E (fun σ => upd (upd (upd (A σ) aH1 (A σ aEx)) aH2 (A σ aEx / 2)) aEx (hIf (A σ aEx) (V σ sl)))
        (aEx :: aH2 :: aH1 :: L) V LS) := by
  simp only [halfIf, seqs]
  refine VP.seq (St.pcopy copyH1Ex_taint (by decide) hx (by decide)) ?_
  refine VP.seq (St.pcopy copyH2Ex_taint (by decide) (by simp [hx]) (by decide)) ?_
  refine VP.seq (St.pmov11 mov11_taint) ?_
  refine VP.seq (St.phalf halfH2_taint (by simp)) ?_
  refine (St.psel cs (by decide) (by simp) (by simp) (by decide) (by decide) hsl bit).mono (fun _ _ h => h)
    fun σ s h => h.mono (fun j hj => ⟨by
      simp only [List.mem_cons] at hj ⊢; rcases hj with h | h | h | h <;> simp [h], ?_⟩) fun j hj => ⟨hj, rfl⟩
  simp only [List.mem_cons] at hj
  by_cases e1 : j = aEx
  · subst e1; simp (config := {decide := true}) only [upd, ↓reduceIte, hIf]
  · by_cases e2 : j = aH2
    · subst e2; simp (config := {decide := true}) only [upd, ↓reduceIte]
    · by_cases e3 : j = aH1
      · subst e3; simp (config := {decide := true}) only [upd, ↓reduceIte]
      · simp only [upd, e1, e2, e3, ↓reduceIte]

/-- `expTop`: the words `W − 2` and `W − 1` of `[mBase + 27]` := the header
words `sLo` and `sHi`. -/
theorem St.pexpTop (cert : Cert (.block expTop)) (hj : mBase + 27 ∈ L) (hlo : sLo ∈ LS) (hhi : sHi ∈ LS)
    (hv : ∀ σ, E σ → In P σ → A σ (mBase + 27) < 2 ^ (32 * (P.W - 2)) ∧ V σ sLo < 2 ^ 32 ∧ V σ sHi < 2 ^ 32) :
    VP (St P E A L V LS) (.block expTop)
      (St P E (fun σ => upd (A σ) (mBase + 27)
        (A σ (mBase + 27) + 2 ^ (32 * (P.W - 2)) * (V σ sLo + 2 ^ 32 * V σ sHi))) ((mBase + 27) :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    have pre := h.pre
    obtain ⟨ha, hl, hh⟩ := hv σ e pre
    have hW := pre.W_eq
    have wl := pre.wle
    have wg := pre.wge
    have fit := hw.arr_fit (j := mBase + 27) (by decide)
    have hS : S P.W = 4 * (P.W + 2) := rfl
    have nw := hw.nowrap
    have ea := h.arrs _ hj
    unfold expTop
    refine ptr_ok hw (by decide) (by decide) fun s1 p1 r1 m1 h1 => ?_
    refine wp_dp (op2_lsl (by decide)) fun s2 u2 => wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
    have e3 : s3.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W (mBase + 27) + 4 * (P.W - 2)) := by
      rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, h1.r9]
      have : BitVec.ofNat 32 P.W <<< 2 = BitVec.ofNat 32 (P.W * 2 ^ 2) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (a := P.W) (by omega)]
      rw [this, BitVec.add_assoc, BitVec.ofNat_add_ofNat, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
        VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega)]
      congr 2; omega
    have k3 : Rest [.r0] s s3 := (r1.mono (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))
    have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, m1]
    have h3 := h.of_rest k3 m3
    have hw3 := hw.rest k3
    refine h3.ldr hw3 hlo (r := .r1) (by decide) fun s4 h4 hw4 u4 => ?_
    have a4 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr P.B) (arr P.W (mBase + 27) + 4 * (P.W - 2)) := by
      rw [u4.other _ (by decide), e3, BitVec.add_zero]; exact hw.addr (by omega)
    refine wp_str (by decide) a4 (hw4.write (by omega)) fun s5 m5 => ?_
    have o5 := writeW32_outside s4.mem (State.addr P.B) (d := arr P.W (mBase + 27) + 4 * (P.W - 2)) (s4.gpr .r1)
      (by omega)
    rw [← m5.mem] at o5
    have n5 : num s5.mem P.B P.W (mBase + 27) = A σ (mBase + 27) + 2 ^ (32 * (P.W - 2)) * V σ sLo := by
      change val32 _ _ _ _ = _
      rw [m5.mem, val32_write_any _ _ _ (show P.W - 2 < P.W by omega) (by omega), u4.gpr,
        ofNat_toNat_lt hl]
      have e4 : val32 s4.mem (State.addr P.B) (arr P.W (mBase + 27)) P.W = A σ (mBase + 27) := by
        rw [u4.mem, m3]; exact ea
      rw [e4, Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide)
        (by omega)))]
      omega
    have h5 := h4.write1 (o := mBase + 27) (ds := []) (Keep.of_arr (d := 4 * (P.W - 2)) o5 (by omega) (by simp))
      (by decide) (by simp) m5.sp m5.rd m5.wr n5 (by simp)
    have hw5 := hw4.of_mupd m5
    refine h5.ldr hw5 hhi (r := .r1) (by decide) fun s6 h6 hw6 u6 => ?_
    have a6 : State.addr (s6.gpr .r0 + BitVec.ofNat 32 4) =
        off (State.addr P.B) (arr P.W (mBase + 27) + 4 * (P.W - 1)) := by
      rw [u6.other _ (by decide), m5.gpr, u4.other _ (by decide), e3, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [show arr P.W (mBase + 27) + 4 * (P.W - 2) + 4 = arr P.W (mBase + 27) + 4 * (P.W - 1) by omega]
      exact hw.addr (by omega)
    refine wp_str (by decide) a6 (hw6.write (by omega)) fun s7 m7 => WP.block_nil ⟨e, ?_, hw6.of_mupd m7⟩
    have o7 := writeW32_outside s6.mem (State.addr P.B) (d := arr P.W (mBase + 27) + 4 * (P.W - 1)) (s6.gpr .r1)
      (by omega)
    rw [← m7.mem] at o7
    have n7 : num s7.mem P.B P.W (mBase + 27) =
        A σ (mBase + 27) + 2 ^ (32 * (P.W - 2)) * (V σ sLo + 2 ^ 32 * V σ sHi) := by
      change val32 _ _ _ _ = _
      rw [m7.mem, val32_write_any _ _ _ (show P.W - 1 < P.W by omega) (by omega), u6.gpr,
        ofNat_toNat_lt hh]
      have e6 : val32 s6.mem (State.addr P.B) (arr P.W (mBase + 27)) P.W =
          A σ (mBase + 27) + 2 ^ (32 * (P.W - 2)) * V σ sLo := by rw [u6.mem]; exact n5
      rw [e6]
      have p1 : 2 ^ (32 * (P.W - 1)) = 2 ^ (32 * (P.W - 2)) * 2 ^ 32 := by
        rw [← Nat.pow_add]; congr 1 <;> omega
      have p2 : 2 ^ (32 * (P.W - 1 + 1)) = 2 ^ (32 * (P.W - 2)) * 2 ^ 32 * 2 ^ 32 := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1 <;> omega
      have lt1 : A σ (mBase + 27) + 2 ^ (32 * (P.W - 2)) * V σ sLo < 2 ^ (32 * (P.W - 1)) := by
        rw [p1]
        have : 2 ^ (32 * (P.W - 2)) * V σ sLo + 2 ^ (32 * (P.W - 2)) ≤ 2 ^ (32 * (P.W - 2)) * 2 ^ 32 := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
        omega
      rw [Nat.mod_eq_of_lt lt1, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le lt1 (Nat.pow_le_pow_right (by decide)
        (by omega))), p1, Nat.mul_zero, Nat.add_zero, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    have h7 := h6.write1 (o := mBase + 27) (ds := []) (Keep.of_arr (d := 4 * (P.W - 1)) o7 (by omega) (by simp))
      (by decide) (by simp) m7.sp m7.rd m7.wr n7 (by simp)
    refine h7.mono (fun j hj' => ⟨?_, ?_⟩) fun d hd => ⟨hd, rfl⟩
    · simp only [List.mem_cons] at hj' ⊢; rcases hj' with h' | h' <;> simp [h']
    · dsimp only
      by_cases e' : j = mBase + 27
      · subst e'; rw [upd_self, upd_self]
      · rw [upd_ne _ _ e', upd_ne _ _ e', upd_ne _ _ e']

end

end VG.Proof.RsaKeyGen.Arm.Cand
