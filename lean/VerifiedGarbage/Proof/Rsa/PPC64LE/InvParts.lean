module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Inverse
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
public import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep

/-!
# `inverse` on PPC64LE: the differences and halvings modulo `m`

As on ARMv7 (`Proof/Rsa/Arm/InvParts.lean`, `InvHalf.lean`): `subModP_ok`:
`subModP o a b` computes `subMod m a b` for `a, b < m`, and `halfModP_ok`:
the end of a step computes `halfMod m` of `[aT3]`, with the negated modulus
`2^(32 w) - m` in `aNM` and zero in `aZero`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (seqs sub3 sel bitOf stBorrow half subModP aM aNM aZero aT1 aT2 aT3 aT4
  sOdd sB sC)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)
open VG.Proof.Rsa (subMod halfMod subMod_impl halfMod_impl)

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
macro "idx" : tactic => `(tactic| ((try simp only [aM, aNM, aZero, aT1, aT2, aT3, aT4, sOdd, sB, sC,
  VG.Proof.Rsa.KeyWorkspace.hdr,
  List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, ne_eq]) <;>
    omega_arith))

/-- `subModP o a b`: `[o] = [a] - [b] mod m`. -/
theorem subModP_ok {s : State} {B : Addr} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 256) (ho : o < N) (ha : a < N) (hb : b < N)
    (hoT1 : o ≠ aT1) (hoT4 : o ≠ aT4) (haT1 : a ≠ aT1) (hbT1 : b ≠ aT1) :
    WP isa (seqs (subModP o a b)) s fun t => Ws t B Z w N ∧
      KeyWorkspace.Keep B w [aT1, aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w a < num s.mem B w aM → num s.mem B w b < num s.mem B w aM →
        num t.mem B w o = subMod (num s.mem B w aM) (num s.mem B w a) (num s.mem B w b)) ∧
      Keep opRegs s t := by
  have hsB : sB + 4 ≤ 160 := by decide
  simp only [aT1, aT4] at hoT1 hoT4 haT1 hbT1
  unfold subModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h (by idx) ha hb hN (by idx) (by idx)) fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (stBorrow sB)]
  refine stBorrow_ok h1 hsB b1 fun t2 h2 k2 s2 r2 => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h2 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsB (by rw [s2]; exact b1))
    fun t3 ⟨h3, k3, v3, r3⟩ => ?_
  refine WP.mono (sub3_ok h3 ho (by idx) (by idx) hN hoT1 hoT4) fun t ⟨h4, k4, v4, b4, r4⟩ => ?_
  refine ⟨h4, KeyWorkspace.Keep.join (k1.join k2 (js := [aT1, aT4, o]) (ds := [sB]))
      (k3.join k4 (js := [aT1, aT4, o]) (ds := [sB])),
    fun hNM hZ ha' hb' => ?_, r1.trans' (r2.trans' (r3.trans' r4))⟩
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
  rw [t13] at v4
  rw [s2, z3, n3] at v3
  refine subMod_impl (P := 2 ^ (32 * w)) (by omega) hb' v1 (val32_lt _ _ _ _) b1 ?_ v4 (val32_lt _ _ _ _) b4
  rw [v3]
  split <;> omega

/-- The halving of `[aT3]` modulo `m` into `[o]`. -/
def halfModP (o : Nat) : List (Prog isa) := [
  .block (bitOf sB aT3), sel aT4 aZero aNM sB, sub3 o aT3 aT4,
  .block [.load .w .r0 .r31 sB, .logic .xor .r9 .r9 .r0], half o]

/-- The exclusive or of two bits. -/
theorem xor_bits {x y : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x ^^^ y).toNat = (x.toNat + y.toNat) % 2 := by
  rw [BitVec.toNat_xor]
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with e | e <;>
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega) with f | f <;> rw [e, f] <;> decide

theorem halfModP_ok {s : State} {B : Addr} {Z w N o : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 256) (ho : o < N) (hoT3 : o ≠ aT3) (hoT4 : o ≠ aT4) :
    WP isa (seqs (halfModP o)) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num t.mem B w o = halfMod (num s.mem B w aM) (num s.mem B w aT3)) ∧
      Keep opRegs s t := by
  have hsB : sB + 4 ≤ 160 := by decide
  simp only [aT3, aT4] at hoT3 hoT4
  unfold halfModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (bitOf sB aT3)]
  refine bitOf_ok h (by idx) hN hsB fun t1 h1 k1 s1 r1 => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have b1 : slot t1.mem B sB ≤ 1 := by rw [s1]; omega
  refine WP.mono (sel_ok h1 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsB b1)
    fun t2 ⟨h2, k2, v2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 ho (by idx) (by idx) hN hoT3 hoT4) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hz : 160 ≤ Z := h3.hdr_le
  have sB3 : slot t3.mem B sB = slot t1.mem B sB := by
    rw [k3.slot hsB (by simp), k2.slot hsB (by simp)]
  have hx : WP isa (.block [.load .w .r0 .r31 sB, .logic .xor .r9 .r9 .r0]) t3 fun t4 =>
      (t4.gpr .r9 = t3.gpr .r9 ^^^ (t3.mem.readW (off B sB) 32).setWidth 64 ∧ t4.mem = t3.mem) ∧
        Keep [.r0, .r9] t3 t4 := by
    refine WP.keep _ ?_ (by decide)
    prun [h3.r31, h3.scr.ld (show sB + 4 ≤ Z by simp only [sB] at hsB ⊢; omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sB < 2 ^ 15 by decide)]
  refine WP.mono hx fun t4 ⟨⟨u9, m4⟩, k4⟩ => ?_
  have h5 : Ws t4 B Z w N := h3.of_keep k4
  have c4 : (t4.gpr .r9).toNat = ((t3.gpr .r9).toNat + num s.mem B w aT3 % 2) % 2 := by
    have e : (t3.mem.readW (off B sB) 32).toNat = num s.mem B w aT3 % 2 := by
      change slot t3.mem B sB = _; rw [sB3, s1]
    rw [u9, xor_bits b3 (by rw [toNat_ext32, e]; omega), toNat_ext32, e]
  refine WP.mono (half_ok h5 ho hN (by rw [c4]; omega)) fun t ⟨h6, k6, v6, r6⟩ => ?_
  rw [m4] at k6 v6
  refine ⟨h6, (k1.join k2 (js := [aT4, o]) (ds := [sB])).join (k3.join k6 (js := [aT4, o]) (ds := [sB]))
      (js := [aT4, o]) (ds := [sB]), fun hNM hZ => ?_,
    r1.trans' (r2.trans' (r3.trans' ((k4.mono).trans' r6)))⟩
  have f3 := h.fit64 (j := aT3) (by idx)
  have fz := h.fit64 (j := aZero) (by idx)
  have fn := h.fit64 (j := aNM) (by idx)
  have x2 : num t2.mem B w aT3 = num s.mem B w aT3 := by
    rw [k2.num (by idx) (by simp) f3, k1.num (by simp) (by simp; decide) f3]
  have z1 : num t1.mem B w aZero = 0 := by rw [k1.num (by simp) (by simp; decide) fz, hZ]
  have n1 : num t1.mem B w aNM = num s.mem B w aNM := k1.num (by simp) (by simp; decide) fn
  rw [x2] at v3
  rw [s1, z1, n1] at v2
  rw [v6, c4]
  refine halfMod_impl (P := 2 ^ (32 * w)) (by omega) (val32_lt _ _ _ _) ?_ v3 (val32_lt _ _ _ _) b3 rfl
  rw [v2]; split <;> omega

end VG.Proof.Rsa.PPC64LE.Keys
