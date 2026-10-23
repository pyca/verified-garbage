module

public meta import VerifiedGarbage.Proof.Framework.PlainSimp

public import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Rsa.X86.KeySub

/-! # Subtraction modulo the odd RSA inverse modulus -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
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
macro "idx" : tactic => `(tactic| plain_simp_names ((try simp only [aM, aNM, aZero, aT1, aT2, aT3, aT4, sOdd, sB, sC, sT,
  List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, hdr, ne_eq]) <;> omega_arith))

/-- `subModP o a b`: `[o] = [a] - [b] mod m`. -/
theorem subModP_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (ho : o < N) (ha : a < N) (hb : b < N)
    (hoT1 : o ≠ aT1) (hoT4 : o ≠ aT4) (haT1 : a ≠ aT1) (hbT1 : b ≠ aT1) :
    WP isa (seqs (subModP w o a b)) s fun t => Ws t B Z w N ∧ Keep B w [aT1, aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w a < num s.mem B w aM → num s.mem B w b < num s.mem B w aM →
        num t.mem B w o = subMod (num s.mem B w aM) (num s.mem B w a) (num s.mem B w b)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hsB : sB + 4 ≤ hdr := by decide
  simp only [aT1, aT4] at hoT1 hoT4 haT1 hbT1
  unfold subModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h (by idx) ha hb (by idx) (by idx)) fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_slot h1 hsB .ebx) fun t2 ⟨h2, k2, s2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h2 (by idx) (by idx) (by idx) hsB (by rw [s2]; exact b1))
    fun t3 ⟨h3, k3, v3, r3⟩ => ?_
  refine WP.mono (sub3_ok h3 ho (by idx) (by idx) hoT1 hoT4) fun t ⟨h4, k4, v4, b4, r4⟩ => ?_
  refine ⟨h4, Keep.join (k1.join k2 (js := [aT1, aT4, o]) (ds := [sB])) (k3.join k4 (js := [aT1, aT4, o]) (ds := [sB])),
    fun hNM hZ ha' hb' => ?_, r1.trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans r4))⟩
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

end VG.Proof.Rsa.X86.Keys
