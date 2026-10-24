module

import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLoop
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvStep
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env
public import VerifiedGarbage.Spec.Rsa

/-!
# `vg_rsa_keygen_key` on PPC64LE: the inverse and the loads as values

`invOfE`: `invOf a m` (`inverse` from `(a, m, 1, 0)`): array 1 holds
`gcd(a, m)` and array 3 an `x < m` with `m ∣ x a - gcd(a, m)`, for an odd
`m > 1`. `loadE`: `load j` reads bytes into a zero array.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 inverse aM aNM aZero aT1 aT3 aT4 sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.CrtValues (load)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aOne invOf)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The arrays `invOf` writes. -/
abbrev invOfArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aM, aNM, aT1, VG.Impl.Rsa.PPC64LE.Keys.aT2, aT3, aT4]

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

theorem invOf_eq (a m : Nat) : invOf a m =
    .seq (copy aM m) (.seq (copy 0 a) (.seq (copy 1 aM) (.seq (copy 2 aOne) (.seq (copy 3 aZero)
      (.seq (sub3 aNM aZero aM) inverse))))) := rfl

/-- `invOf a m`. -/
theorem invOfE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {a m : Nat} (ha : a < nArr := by decide)
    (hm : m < nArr := by decide) (hma : a ∉ invOfArrs := by decide) (hmm : m ≠ aM := by decide)
    (one : V aOne = 1) (zero : V aZero = 0) (odd : V m % 2 = 1) (gt : 1 < V m) :
    WP isa (invOf a m) s fun u => Ws u B Z w nArr ∧
      (∃ V', KS u.mem B w V' F ∧ (∀ j < nArr, j ∉ invOfArrs → V' j = V j) ∧
        V' 1 = Nat.gcd (V a) (V m) ∧ ((V m : Nat) : Int) ∣ (V' 3 : Int) * V a - V' 1 ∧ V' 3 < V m) ∧
      KK B w s.mem u.mem ∧ Keep opsRegs s u := by
  have ham : a ≠ aM := fun e => hma (by rw [e]; decide)
  have ha0 : a ≠ 0 := fun e => hma (by rw [e]; decide)
  rw [invOf_eq]
  refine WP.seq (WP.mono (copyE h ks (o := aM) (a := m) (by decide) hm (Ne.symm hmm)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_)
  refine WP.seq (WP.mono (copyE h1 k1 (o := 0) (a := a) (by decide) ha (Ne.symm ha0)) fun t2 ⟨h2, k2, f2, r2⟩ => ?_)
  refine WP.seq (WP.mono (copyE h2 k2 (o := 1) (a := aM)) fun t3 ⟨h3, k3, f3, r3⟩ => ?_)
  refine WP.seq (WP.mono (copyE h3 k3 (o := 2) (a := aOne)) fun t4 ⟨h4, k4, f4, r4⟩ => ?_)
  refine WP.seq (WP.mono (copyE h4 k4 (o := 3) (a := aZero)) fun t5 ⟨h5, k5, f5, r5⟩ => ?_)
  refine WP.seq (WP.mono (sub3E h5 k5 (o := aNM) (a := aZero) (b := aM)) fun t6 ⟨h6, k6, _, f6, r6⟩ => ?_)
  -- The values before `inverse`.
  have zero' : V 10 = 0 := zero
  have one' : V 15 = 1 := one
  have ham' : a ≠ 8 := ham
  have ha0' : a ≠ 0 := ha0
  have vM : num t6.mem B w aM = V m := by rw [k6.arrs aM (by decide)]; simp [upd, aM, aNM]
  have vNM : num t6.mem B w aNM = subW w 0 (V m) := by
    rw [k6.arrs aNM (by decide)]; simp [upd, aM, aNM, aZero, zero']
  have v0 : num t6.mem B w 0 = V a := by rw [k6.arrs 0 (by decide)]; simp [upd, aM, aNM, ham']
  have v1 : num t6.mem B w 1 = V m := by rw [k6.arrs 1 (by decide)]; simp [upd, aM, aNM]
  have v2 : num t6.mem B w 2 = 1 := by rw [k6.arrs 2 (by decide)]; simp [upd, aM, aNM, aOne, one']
  have v3 : num t6.mem B w 3 = 0 := by rw [k6.arrs 3 (by decide)]; simp [upd, aM, aNM, aZero, zero']
  have vZ : num t6.mem B w aZero = 0 := by rw [k6.arrs aZero (by decide)]; simp [upd, aM, aNM, aZero, zero']
  have vO : ∀ j < nArr, j ∉ invOfArrs → num t6.mem B w j = V j := by
    intro j hj hn
    simp only [invOfArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n0, n1, n2, n3, -, -, -, -, nM, nNM, -⟩ := hn
    rw [k6.arrs j hj]; simp [upd, n0, n1, n2, n3, nM, nNM]
  refine WP.mono (inverse_ok h6 (by decide) nArr_le) fun u ⟨hu, ku, kr, v⟩ => ⟨hu, ?_, ?_, ?_⟩
  · have hlt := ks.lt hm
    have hNM : num t6.mem B w aNM + num t6.mem B w aM = 2 ^ (32 * w) := by
      rw [vNM, vM]
      unfold subW
      rw [Nat.zero_add, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos _) (by omega_arith))]
      omega_arith
    have hZ : num t6.mem B w aZero = 0 := vZ
    have hod : num t6.mem B w aM % 2 = 1 := by rw [vM]; exact odd
    have hgt : 1 < num t6.mem B w aM := by rw [vM]; exact gt
    have hb : bank t6.mem B w 0 = (num t6.mem B w 0, num t6.mem B w aM, 1, 0) := by
      simp only [bank, v1, v2, v3, vM]
    obtain ⟨g, dv, lt⟩ := v hNM hZ hod hgt hb
    simp only [v0, vM] at g dv lt
    refine ⟨fun j => num u.mem B w j, ?_, fun j hj hn => ?_, g, dv, lt⟩
    · refine k6.step ku (fit_of h6) (V' := fun j => num u.mem B w j) (fun j hj hn => ?_) (fun j _ => rfl)
        (fun _ _ _ => rfl) (fun d hd hf => ?_) (fun hj => absurd hj (by decide))
      · rw [← k6.arrs j hj]
        exact ku.num (fun x hx e => hn (e ▸ hx)) (by decide) (fit_of h6 j hj)
      · simp only [invSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl <;> exact absurd hf (by decide)
    · have sub : ∀ x ∈ invArrs, x ∈ invOfArrs := by decide
      have hn' : j ∉ invArrs := fun hm' => hn (sub j hm')
      show num u.mem B w j = V j
      rw [ku.num (fun x hx e => hn' (by rw [← e]; exact hx)) (by decide) (fit_of h6 j hj), vO j hj hn]
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans (KK.of ku (by decide) (by decide))
  · exact (((((r1.trans' r2).trans' r3).trans' r4).trans' r5).trans' r6).trans' kr.mono

/-- `load j` from `L` bytes at `P`, readable and apart from the working space, into a zero array. -/
theorem loadE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {j : Nat} (hj : j < nArr := by decide)
    (hjdv : j ≠ aDv := by decide) {P : Addr} {L : Nat} (h6 : s.gpr .r6 = P)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hLw : L ≤ 4 * w)
    (hP : ∀ i < L, InRegions (s.rd ++ s.wr) (off P i) 1) (hsep : ∀ i < L, ∀ x, ofs B x < Z → off P i ≠ x)
    (hz : V j = 0) :
    WP isa (load j) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd V j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P L))) F ∧ KK B w s.mem t.mem ∧
      Keep opsRegs s t := by
  have hv : val32 s.mem B (arr w j) w = 0 := by rw [← hz, ← ks.arrs j hj]
  refine WP.mono (load_ok h hj nArr_le h6 h8 hL hLw hP hsep
    (fun p hp => by rw [← off_add]; exact byte_zero_of_val32 hv hp)) fun t ⟨ht, kt, v, kr, _⟩ =>
      ⟨ht, ?_, KK.of kt (arr_mem hj) (by simp), kr.mono⟩
  refine ks.step kt (fit_of h) (fun i hi hn => ?_) (fun i hi => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi, upd_self, v]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact absurd hd.symm hjdv

end

end VG.Proof.RsaKeyGen.PPC64LE.Key
