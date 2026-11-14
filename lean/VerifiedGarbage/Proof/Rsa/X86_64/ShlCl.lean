module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# x86-64 RSA: a shift left by `cl` bits into another array

`wordLoop 1 shlClBody` puts `A 2^c mod 2^(64 N)` for `c = cl < 64` into
another array of `N` words (`shlCl_ok`), each word from two of `A`'s; with the
facts about the shift counts that `shlClBody` and its shift right counterpart
use (`cl_eq`, `cl_xor`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The immediate `63`. -/
theorem se63 : BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 63 := by decide

theorem cl_eq {c : Nat} (hc : c < 64) : (BitVec.ofNat 64 c).toNat % 64 = c := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hc]), Nat.mod_eq_of_lt hc]

theorem cl_xor {c : Nat} (hc : c < 64) : (BitVec.ofNat 64 c ^^^ BitVec.ofNat 64 63).toNat % 64 = 63 - c := by
  have : BitVec.ofNat 64 c ^^^ BitVec.ofNat 64 63 = BitVec.ofNat 64 (63 - c) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hc]), Nat.mod_eq_of_lt (show 63 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (show 63 - c < 2 ^ 64 by omega_using [])]
    have : ∀ c < 64, c ^^^ 63 = 63 - c := by decide
    exact this c hc
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]

theorem xor_back (a b : BitVec 64) : a ^^^ b ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- `y / 2^(64 - c)`, as two shifts. -/
theorem shr_low (y : BitVec 64) {c : Nat} (hc : c < 64) :
    ((y >>> 1) >>> (63 - c)).toNat = y.toNat / 2 ^ (64 - c) := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, show 1 + (63 - c) = 64 - c by omega_using [hc]]

/-- A word of `shlClBody`. -/
theorem shlCl_word (x y : BitVec 64) {c : Nat} (hc : c < 64) :
    (x <<< c + (y >>> 1) >>> (63 - c)).toNat = x.toNat * 2 ^ c % 2 ^ 64 + y.toNat / 2 ^ (64 - c) := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, shr_low y hc]
  apply Nat.mod_eq_of_lt
  have hP : (2 : Nat) ^ 64 = 2 ^ (64 - c) * 2 ^ c := by rw [← Nat.pow_add]; congr 1; omega_using [hc]
  have h1 : x.toNat * 2 ^ c % 2 ^ 64 = 2 ^ c * (x.toNat % 2 ^ (64 - c)) := by
    rw [hP, Nat.mul_comm (2 ^ (64 - c)), Nat.mul_comm x.toNat, Nat.mul_mod_mul_left]
  have h2 : y.toNat / 2 ^ (64 - c) < 2 ^ c := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show c + (64 - c) = 64 by omega_using [hc]]; exact y.isLt
  have h3 : x.toNat % 2 ^ (64 - c) < 2 ^ (64 - c) := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [h1, hP]
  calc 2 ^ c * (x.toNat % 2 ^ (64 - c)) + y.toNat / 2 ^ (64 - c)
      < 2 ^ c * (x.toNat % 2 ^ (64 - c)) + 2 ^ c := by omega_using [h2]
    _ = 2 ^ c * (x.toNat % 2 ^ (64 - c) + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ 2 ^ c * 2 ^ (64 - c) := Nat.mul_le_mul_left _ h3
    _ = 2 ^ (64 - c) * 2 ^ c := Nat.mul_comm _ _

structure ShlClInv (s₀ : State) (B : Addr) (Z eo eA c : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rcx, .r14] s₀ t
  rcx : t.gpr .rcx = BitVec.ofNat 64 c
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B (eo + 8) (8 * (j - 1)) s₀.mem t.mem
  val : wv t.mem B eo j + 2 ^ (64 * j) * ((word s₀.mem B (eA + 8 * (j - 1))).toNat / 2 ^ (64 - c)) =
    wv s₀.mem B eA j * 2 ^ c

theorem shlClStep_ok {s₀ : State} {B : Addr} {Z w eo eA c : Nat} (hc : c < 64)
    (hsi : s₀.gpr .rsi = off B eo) (h8 : s₀.gpr .r8 = off B eA) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (ho : eo + 8 * w ≤ Z) (hA : eA + 8 * w ≤ Z) (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j < w) {t : State} (hI : ShlClInv s₀ B Z eo eA c j t) :
    WP isa (.block (shlClBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ ShlClInv s₀ B Z eo eA c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = off B eo := (hI.keep.gpr (by decide)).trans hsi
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) :=
    hI.out.word (by omega_arith) (by omega_arith)
  have hy : word t.mem B (eA + 8 * (j - 1)) = word s₀.mem B (eA + 8 * (j - 1)) :=
    hI.out.word (by omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t₁ => t₁.gpr .rcx = BitVec.ofNat 64 c ∧ ∃ r : BitVec 64,
      t₁.mem = t.mem.writeW (off B (eo + 8 * j)) r ∧
      r.toNat = (word s₀.mem B (eA + 8 * j)).toNat * 2 ^ c % 2 ^ 64 +
        (word s₀.mem B (eA + 8 * (j - 1))).toNat / 2 ^ (64 - c)) ?_ rfl)
    fun t₁ ⟨⟨h1cx, r, hm, hr⟩, k₁⟩ => ?_
  · unfold shlClBody
    xrun [State.ea, ix, addr0 tsi hI.r14, addr0 t8 hI.r14, addrm8 t8 hI.r14 hj1, hI.rcx, execShiftCl, VarShiftOp.eval,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith), hI.scr.ld (show eA + 8 * (j - 1) + 8 ≤ Z by omega_arith),
      hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_arith), hx, hy, se63, cl_eq hc, cl_xor hc, xor_back]
    exact ⟨_, rfl, shlCl_word _ _ hc⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    (k'.gpr (by decide)).trans h1cx, h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hr, show j + 1 - 1 = j by omega_using []]
    have hv := hI.val
    rw [show wv s₀.mem B eA (j + 1) = wv s₀.mem B eA j + 2 ^ (64 * j) * (word s₀.mem B (eA + 8 * j)).toNat from rfl,
      pow64_succ]
    have hP : (2 : Nat) ^ 64 = 2 ^ (64 - c) * 2 ^ c := by rw [← Nat.pow_add]; congr 1; omega_using [hc]
    have h2 := Nat.div_add_mod ((word s₀.mem B (eA + 8 * j)).toNat * 2 ^ c) (2 ^ 64)
    have h3 : (word s₀.mem B (eA + 8 * j)).toNat * 2 ^ c / 2 ^ 64 = (word s₀.mem B (eA + 8 * j)).toNat / 2 ^ (64 - c) := by
      rw [hP, Nat.mul_comm (2 ^ (64 - c)), ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    rw [h3] at h2
    generalize (word s₀.mem B (eA + 8 * j)).toNat * 2 ^ c % 2 ^ 64 = lo at h2 ⊢
    generalize (word s₀.mem B (eA + 8 * j)).toNat / 2 ^ (64 - c) = hi at h2 ⊢
    generalize (word s₀.mem B (eA + 8 * (j - 1))).toNat / 2 ^ (64 - c) = y at hv ⊢
    generalize (word s₀.mem B (eA + 8 * j)).toNat = x at h2 ⊢
    generalize 2 ^ (64 * j) = P at hv ⊢
    generalize 2 ^ c = C at h2 hv ⊢
    grind

/-- `wordLoop 1 shlClBody` over `N ≥ 2` words, `rcx = c < 64`, after word 0 of
`[rsi]` was set to `a₀ 2^c mod 2^64`: `[rsi] = A 2^c mod 2^(64 N)`. -/
theorem shlCl_ok {s : State} {B : Addr} {Z N eo eA c : Nat} (hc : c < 64) (hs : Scr s B Z)
    (hsi : s.gpr .rsi = off B eo) (h8 : s.gpr .r8 = off B eA) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hN : 2 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hA : eA + 8 * N ≤ Z)
    (sA : eo + 8 * N ≤ eA ∨ eA + 8 * N ≤ eo)
    (h0w : (word s.mem B eo).toNat = (word s.mem B eA).toNat * 2 ^ c % 2 ^ 64) :
    WP isa (wordLoop 1 shlClBody) s fun t =>
      wv t.mem B eo N = wv s.mem B eA N * 2 ^ c % 2 ^ (64 * N) ∧
      word t.mem B eo = word s.mem B eo ∧
      Outside B (eo + 8) (8 * (N - 1)) s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  have hn := hs.nowrap
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      ShlClInv s B Z eo eA c 1 t := fun t h14 hm k _ => by
    refine ⟨hs.congr k.2.2, k.mono (by decide), (k.gpr (by decide)).trans hcx, h14,
      by rw [hm]; exact Outside.refl _ _ _ _, ?_⟩
    rw [hm, show wv s.mem B eo 1 = (word s.mem B eo).toNat by simp [wv],
      show wv s.mem B eA 1 = (word s.mem B eA).toNat by simp [wv], show 8 * (1 - 1) = 0 by rfl, Nat.add_zero, h0w]
    have hP : (2 : Nat) ^ 64 = 2 ^ (64 - c) * 2 ^ c := by rw [← Nat.pow_add]; congr 1; omega_using [hc]
    have h2 := Nat.mod_add_div ((word s.mem B eA).toNat * 2 ^ c) (2 ^ 64)
    rw [show (word s.mem B eA).toNat * 2 ^ c / 2 ^ 64 = (word s.mem B eA).toNat / 2 ^ (64 - c) by
      rw [hP, Nat.mul_comm (2 ^ (64 - c)), ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]] at h2
    simpa using h2
  refine WP.mono (wordLoop_ok (start := 1) (N := N) (by omega_arith) hN' (ShlClInv s B Z eo eA c) h0
    (fun j hj1 hj t hI => shlClStep_ok hc hsi h8 h12 ho hA sA hj1 hj hI)) fun t hI => ⟨?_, ?_, ?_, ?_⟩
  · have hv := hI.val
    have hlt : wv t.mem B eo N < 2 ^ (64 * N) := wv_lt _ _ _ _
    have hdl : (word s.mem B (eA + 8 * (N - 1))).toNat / 2 ^ (64 - c) < 2 ^ c := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show c + (64 - c) = 64 by omega_using [hc]]; exact BitVec.isLt _
    rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · exact hI.out.word (by omega_arith) (by omega_arith)
  · exact hI.out
  · refine ⟨fun r hr => ?_, hI.keep.2.1, hI.keep.2.2⟩
    by_cases e : r = .rcx
    · subst e; rw [hI.rcx, hcx]
    · refine hI.keep.1 r ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      intro h
      rcases h with h | h | h | h <;> simp_all

end VG.Proof.Rsa.X86_64
