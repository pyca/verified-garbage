module

public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
public import VerifiedGarbage.Proof.Rsa.X86_64.ShlCl
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the loops of the stages and the square root

The loops over the words that `RecoverDet`'s shifts by stages and square root
add to those of `Proof/Rsa/X86_64/Loops.lean`: the OR of the words of one or
two numbers (`or1_ok`, `or2_ok`) and a shift right by `cl < 64` bits into
another array (`shrCl_ok`; the shift left, `shlCl_ok`, is in `Proof/Rsa/X86_64/ShlCl.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## The OR of the words -/

structure Or1Inv (s₀ : State) (B : Addr) (Z eA : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : t.mem = s₀.mem
  val : t.gpr .rbp = 0 ↔ (s₀.gpr .rbp = 0 ∧ wv s₀.mem B eA j = 0)

theorem wv_succ_zero {m : Mem} {B : Addr} {e j : Nat} :
    wv m B e (j + 1) = 0 ↔ wv m B e j = 0 ∧ word m B (e + 8 * j) = 0 := by
  rw [show wv m B e (j + 1) = wv m B e j + 2 ^ (64 * j) * (word m B (e + 8 * j)).toNat from rfl]
  have : (word m B (e + 8 * j) = 0) ↔ (word m B (e + 8 * j)).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  rw [this]
  have := Nat.two_pow_pos (64 * j)
  constructor
  · intro h
    have h1 : (word m B (e + 8 * j)).toNat = 0 := by
      rcases Nat.eq_zero_or_pos (word m B (e + 8 * j)).toNat with h0 | h0
      · exact h0
      · exfalso; have := Nat.mul_pos this h0; omega
    rw [h1, Nat.mul_zero, Nat.add_zero] at h
    exact ⟨h, h1⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]; rfl

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine ⟨BitVec.eq_of_getLsbD_eq fun i hi => ?_, BitVec.eq_of_getLsbD_eq fun i hi => ?_⟩ <;>
    · have := congrArg (fun v => v.getLsbD i) h
      simp only [BitVec.getLsbD_or] at this ⊢
      simp_all
  · rintro ⟨rfl, rfl⟩; rfl

theorem or1Step_ok {s₀ : State} {B : Addr} {Z w eA : Nat}
    (hbx : s₀.gpr .rbx = off B eA) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hA : eA + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : Or1Inv s₀ B Z eA j t) :
    WP isa (.block (or1Body ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ Or1Inv s₀ B Z eA (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eA := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .rbp = t.gpr .rbp ||| word s₀.mem B (eA + 8 * j)) ?_ rfl) fun t₁ ⟨⟨hm, hb⟩, k₁⟩ => ?_
  · unfold or1Body
    xrun [State.ea, ix, addr0 tbx hI.r14, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith), hI.mem]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14,
    by rw [hm', hm, hI.mem], ?_⟩
  rw [(k'.gpr (by decide)).trans hb, or_eq_zero, hI.val, wv_succ_zero]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

/-- `wordLoop 0 or1Body` over `N` words: `rbp` zero exactly when it was and the words are. -/
theorem or1_ok {s : State} {B : Addr} {Z N eA : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B eA) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hA : eA + 8 * N ≤ Z) :
    WP isa (wordLoop 0 or1Body) s fun t =>
      (t.gpr .rbp = 0 ↔ (s.gpr .rbp = 0 ∧ wv s.mem B eA N = 0)) ∧ t.mem = s.mem ∧ Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      Or1Inv s B Z eA 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, hm, by rw [k.gpr (by decide)]; simp [wv]⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega_arith) hN' (Or1Inv s B Z eA) h0
    (fun j _ hj t hI => or1Step_ok hbx h12 hA hj hI)) fun t hI => ⟨hI.val, hI.mem, hI.keep⟩

structure Or2Inv (s₀ : State) (B : Addr) (Z eA eB : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : t.mem = s₀.mem
  val : t.gpr .rbp = 0 ↔ (s₀.gpr .rbp = 0 ∧ wv s₀.mem B eA j = 0 ∧ wv s₀.mem B eB j = 0)

theorem or2Step_ok {s₀ : State} {B : Addr} {Z w eA eB : Nat}
    (hbx : s₀.gpr .rbx = off B eA) (h10 : s₀.gpr .r10 = off B eB) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hA : eA + 8 * w ≤ Z) (hB : eB + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : Or2Inv s₀ B Z eA eB j t) :
    WP isa (.block (or2Body ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ Or2Inv s₀ B Z eA eB (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eA := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eB := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .rbp = t.gpr .rbp ||| (word s₀.mem B (eA + 8 * j) ||| word s₀.mem B (eB + 8 * j))) ?_ rfl)
    fun t₁ ⟨⟨hm, hb⟩, k₁⟩ => ?_
  · unfold or2Body
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith),
      hI.scr.ld (show eB + 8 * j + 8 ≤ Z by omega_arith), hI.mem]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14,
    by rw [hm', hm, hI.mem], ?_⟩
  rw [(k'.gpr (by decide)).trans hb, or_eq_zero, or_eq_zero, hI.val, wv_succ_zero, wv_succ_zero]
  exact ⟨fun ⟨⟨a, b, c⟩, d, e⟩ => ⟨a, ⟨b, d⟩, c, e⟩, fun ⟨a, ⟨b, d⟩, c, e⟩ => ⟨⟨a, b, c⟩, d, e⟩⟩

/-- `wordLoop 0 or2Body` over `N` words of two numbers. -/
theorem or2_ok {s : State} {B : Addr} {Z N eA eB : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B eA) (h10 : s.gpr .r10 = off B eB) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hA : eA + 8 * N ≤ Z) (hB : eB + 8 * N ≤ Z) :
    WP isa (wordLoop 0 or2Body) s fun t =>
      (t.gpr .rbp = 0 ↔ (s.gpr .rbp = 0 ∧ wv s.mem B eA N = 0 ∧ wv s.mem B eB N = 0)) ∧ t.mem = s.mem ∧
        Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      Or2Inv s B Z eA eB 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, hm, by rw [k.gpr (by decide)]; simp [wv]⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega_arith) hN' (Or2Inv s B Z eA eB) h0
    (fun j _ hj t hI => or2Step_ok hbx h10 h12 hA hB hj hI)) fun t hI => ⟨hI.val, hI.mem, hI.keep⟩

/-! ## Shifts by `cl` bits -/

/-- `y 2^(64 - c) mod 2^64`, as two shifts. -/
theorem shl_top (y : BitVec 64) {c : Nat} (hc : c < 64) :
    ((y <<< 1) <<< (63 - c)).toNat = 2 ^ (64 - c) * (y.toNat % 2 ^ c) := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, show 1 + (63 - c) = 64 - c by omega,
    show (2 : Nat) ^ 64 = 2 ^ (64 - c) * 2 ^ c by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_comm, Nat.mul_mod_mul_left]

/-- A word of `shrClBody`. -/
theorem shrCl_word (x y : BitVec 64) {c : Nat} (hc : c < 64) :
    (x >>> c + (y <<< 1) <<< (63 - c)).toNat = x.toNat / 2 ^ c + 2 ^ (64 - c) * (y.toNat % 2 ^ c) := by
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, shl_top y hc]
  apply Nat.mod_eq_of_lt
  have h1 : x.toNat / 2 ^ c < 2 ^ (64 - c) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 64 - c + c = 64 by omega]; exact x.isLt
  have h2 : y.toNat % 2 ^ c < 2 ^ c := Nat.mod_lt _ (Nat.two_pow_pos _)
  calc x.toNat / 2 ^ c + 2 ^ (64 - c) * (y.toNat % 2 ^ c) < 2 ^ (64 - c) + 2 ^ (64 - c) * (y.toNat % 2 ^ c) := by
        omega
    _ = 2 ^ (64 - c) * (y.toNat % 2 ^ c + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    _ ≤ 2 ^ (64 - c) * 2 ^ c := Nat.mul_le_mul_left _ h2
    _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega

structure ShrClInv (s₀ : State) (B : Addr) (Z eo eA c : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rcx, .r14] s₀ t
  rcx : t.gpr .rcx = BitVec.ofNat 64 c
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j * 2 ^ c + (word s₀.mem B eA).toNat % 2 ^ c =
    wv s₀.mem B eA j + 2 ^ (64 * j) * ((word s₀.mem B (eA + 8 * j)).toNat % 2 ^ c)

theorem shrClStep_ok {s₀ : State} {B : Addr} {Z w eo eA c : Nat} (hc : c < 64)
    (hsi : s₀.gpr .rsi = off B eo) (h8 : s₀.gpr .r8 = off B eA) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (ho : eo + 8 * w ≤ Z) (hA : eA + 8 * (w + 1) ≤ Z) (sA : eo ≤ eA ∨ eA + 8 * (w + 1) ≤ eo)
    {j : Nat} (hj : j < w) {t : State} (hI : ShrClInv s₀ B Z eo eA c j t) :
    WP isa (.block (shrClBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ ShrClInv s₀ B Z eo eA c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = off B eo := (hI.keep.gpr (by decide)).trans hsi
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) :=
    hI.out.word (by omega_arith) (by omega_arith)
  have hy : word t.mem B (eA + 8 * j + 8) = word s₀.mem B (eA + 8 * j + 8) :=
    hI.out.word (by omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t₁ => t₁.gpr .rcx = BitVec.ofNat 64 c ∧ ∃ r : BitVec 64,
      t₁.mem = t.mem.writeW (off B (eo + 8 * j)) r ∧
      r.toNat = (word s₀.mem B (eA + 8 * j)).toNat / 2 ^ c +
        2 ^ (64 - c) * ((word s₀.mem B (eA + 8 * j + 8)).toNat % 2 ^ c)) ?_ rfl)
    fun t₁ ⟨⟨h1cx, r, hm, hr⟩, k₁⟩ => ?_
  · unfold shrClBody
    xrun [State.ea, ix, addr0 tsi hI.r14, addr0 t8 hI.r14, addr8 t8 hI.r14, hI.rcx, execShiftCl, VarShiftOp.eval,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith), hI.scr.ld (show eA + 8 * j + 8 + 8 ≤ Z by omega_arith),
      hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_arith), hx, hy, se63, cl_eq hc, cl_xor hc, xor_back]
    exact ⟨_, rfl, shrCl_word _ _ hc⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    (k'.gpr (by decide)).trans h1cx, h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hr]
    have hv := hI.val
    rw [show wv s₀.mem B eA (j + 1) = wv s₀.mem B eA j + 2 ^ (64 * j) * (word s₀.mem B (eA + 8 * j)).toNat from rfl,
      pow64_succ, show eA + 8 * (j + 1) = eA + 8 * j + 8 by omega]
    have h2 := Nat.div_add_mod (word s₀.mem B (eA + 8 * j)).toNat (2 ^ c)
    have hP : (2 : Nat) ^ 64 = 2 ^ (64 - c) * 2 ^ c := by rw [← Nat.pow_add]; congr 1; omega
    generalize (word s₀.mem B (eA + 8 * j)).toNat = x at h2 hv ⊢
    generalize (word s₀.mem B (eA + 8 * j + 8)).toNat % 2 ^ c = y
    generalize 2 ^ (64 * j) = P at hv ⊢
    generalize 2 ^ c = C at h2 hv hP ⊢
    generalize 2 ^ (64 - c) = D at hP ⊢
    rw [hP]
    grind

/-- `wordLoop 0 shrClBody` over `N` words, `rcx = c < 64`:
`[rsi] 2^c + A mod 2^c = A + 2^(64 N) (a_N mod 2^c)` for the `N + 1` words `A` at `r8`. -/
theorem shrCl_ok {s : State} {B : Addr} {Z N eo eA c : Nat} (hc : c < 64) (hs : Scr s B Z)
    (hsi : s.gpr .rsi = off B eo) (h8 : s.gpr .r8 = off B eA) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hA : eA + 8 * (N + 1) ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * (N + 1) ≤ eo) :
    WP isa (wordLoop 0 shrClBody) s fun t =>
      wv t.mem B eo N * 2 ^ c + (word s.mem B eA).toNat % 2 ^ c =
        wv s.mem B eA N + 2 ^ (64 * N) * ((word s.mem B (eA + 8 * N)).toNat % 2 ^ c) ∧
      Outside B eo (8 * N) s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      ShrClInv s B Z eo eA c 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), (k.gpr (by decide)).trans hcx, h14,
      by rw [hm]; exact Outside.refl _ _ _ _, by simp [wv]⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega_arith) hN' (ShrClInv s B Z eo eA c) h0
    (fun j _ hj t hI => shrClStep_ok hc hsi h8 h12 ho hA sA hj hI)) fun t hI => ⟨hI.val, hI.out, ?_⟩
  refine ⟨fun r hr => ?_, hI.keep.2.1, hI.keep.2.2⟩
  by_cases e : r = .rcx
  · subst e; rw [hI.rcx, hcx]
  · refine hI.keep.1 r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    intro h
    rcases h with h | h | h | h <;> simp_all

end VG.Proof.Rsa.X86_64.Rd
