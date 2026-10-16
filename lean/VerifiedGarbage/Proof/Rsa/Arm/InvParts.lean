module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyEq
public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.Rsa.KeyMath
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `inverse` on ARMv7: the differences and halvings modulo `m`

`subModP_ok`: `subModP o a b` computes `subMod m a b` for `a, b < m`, and
`halfModP_ok`: the end of a step computes `halfMod m` of `[aT3]`, with the
negated modulus `2^(32 w) - m` in `aNM` and zero in `aZero`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa (subMod halfMod)

theorem wp_seqs_cons {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (c :: l)) s Q ↔ WP isa c s (fun t => WP isa (seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem wp_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s : State}
    {Q : State → Prop} :
    WP isa (seqs (l₁ ++ l₂)) s Q ↔ WP isa (seqs l₁) s (fun t => WP isa (seqs l₂) t Q) := by
  induction l₁ generalizing s with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · exact wp_seqs_cons h₂
    · rw [List.cons_append, wp_seqs_cons (by simp), wp_seqs_cons (by simp)]
      exact ⟨fun h => WP.mono h fun t ht => (ih (by simp)).mp ht,
        fun h => WP.mono h fun t ht => (ih (by simp)).mpr ht⟩

/-- Index side conditions. -/
macro "idx" : tactic => `(tactic| (simp only [aM, aNM, aZero, aT1, aT2, aT3, aT4, sOdd, sB, sC, sT,
  List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, hdr] at * <;> omega))

theorem subMod_impl {P M a b t1 β t4 e β' : Nat} (hM : M ≤ P) (hb : b < M)
    (h1 : t1 + b = a + P * β) (ht1 : t1 < P) (hβ : β ≤ 1) (h4 : t4 = if β = 0 then 0 else P - M)
    (h2 : e + t4 = t1 + P * β') (he : e < P) (hβ' : β' ≤ 1) : e = subMod M a b := by
  unfold subMod
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl <;>
  rcases (by omega : β' = 0 ∨ β' = 1) with rfl | rfl <;>
  split at h4 <;> split <;> omega

theorem halfMod_impl {P M X t4 y β c : Nat} (hM : M ≤ P) (hX : X < P)
    (h4 : t4 = if X % 2 = 0 then 0 else P - M) (h3 : y + t4 = X + P * β) (hy : y < P) (hβ : β ≤ 1)
    (hc : c = (β + X % 2) % 2) : (y + P * c) / 2 = halfMod M X := by
  unfold halfMod
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl <;>
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
  split at h4 <;> split <;> omega

/-- `subModP o a b`: `[o] = [a] - [b] mod m`. -/
theorem subModP_ok {s : State} {B : BitVec 32} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 256) (ho : o < N) (ha : a < N) (hb : b < N)
    (hoT1 : o ≠ aT1) (hoT4 : o ≠ aT4) (haT1 : a ≠ aT1) (hbT1 : b ≠ aT1) :
    WP isa (seqs (subModP o a b)) s fun t => Ws t B Z w N ∧ Keep B w [aT1, aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w a < num s.mem B w aM → num s.mem B w b < num s.mem B w aM →
        num t.mem B w o = subMod (num s.mem B w aM) (num s.mem B w a) (num s.mem B w b)) ∧
      Rest opRegs s t := by
  have hsB : sB + 4 ≤ hdr := by decide
  unfold subModP
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (sub3_ok h (by idx) ha hb hN (by idx) (by idx)) fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [wp_seqs_cons (by simp)]
  refine wp_strSlot h1 hsB fun t2 m2 => WP.block_nil ?_
  have h2 := h1.of_mupd m2
  have k2 : Keep B w [] [sB] t1.mem t2.mem := by rw [m2.mem]; exact keep_write _ _ (by simp) (by decide)
  have s2 : slot t2.mem B sB = (t1.gpr .r11).toNat := by rw [m2.mem, slot_write_self]
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (sel_ok h2 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsB (by rw [s2]; exact b1))
    fun t3 ⟨h3, k3, v3, r3⟩ => ?_
  refine WP.mono (sub3_ok h3 ho (by idx) (by idx) hN hoT1 hoT4) fun t ⟨h4, k4, v4, b4, r4⟩ => ?_
  refine ⟨h4, Keep.join (k1.join k2 (js := [aT1, aT4, o]) (ds := [sB])) (k3.join k4 (js := [aT1, aT4, o]) (ds := [sB])),
    fun hNM hZ ha' hb' => ?_, r1.trans ((m2.rest _).trans (r3.trans r4))⟩
  have P := h.wpos
  -- The values at the later states.
  have fz := h.fit64 (j := aZero) (by idx)
  have fn := h.fit64 (j := aNM) (by idx)
  have fT1 := h.fit64 (j := aT1) (by idx)
  have z3 : num t2.mem B w aZero = 0 := by
    rw [k2.num (by simp) (by simp; decide) fz, k1.num (by idx) (by simp) fz, hZ]
  have n3 : num t2.mem B w aNM = num s.mem B w aNM := by
    rw [k2.num (by simp) (by simp; decide) fn, k1.num (by idx) (by simp) fn]
  have t13 : num t3.mem B w aT1 = num t1.mem B w aT1 := by
    rw [k3.num (by idx) (by simp) fT1, k2.num (by simp) (by simp; decide) fT1]
  have ft4 := h.fit64 (j := aT4) (by idx)
  rw [t13] at v4
  rw [s2, z3, n3] at v3
  refine subMod_impl (P := 2 ^ (32 * w)) (by omega) hb' v1 (val32_lt _ _ _ _) b1 ?_ v4 (val32_lt _ _ _ _) b4
  rw [v3]
  split <;> omega

end VG.Proof.Rsa.Arm.Keys
