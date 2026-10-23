module

public import VerifiedGarbage.Proof.Mont.PPC64LE.Csub
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step

/-!
# Montgomery arithmetic on PPC64LE: sums and differences

`add M acc` stores the digits of `[r5] + [r6]` at `[r3 + acc]` (`adds_ok`),
then reduces them (`csub`); `sub M acc` stores those of `[r5] + m - [r6]`
(`subs_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- Digit `j` of `[r5] + [r6]`, from the carry `r10`, to `[r3 + acc + 4j]`. -/
theorem addDigit_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {acc A B j : Nat}
    (h3 : At s base .r3 0) (h5 : At s base .r5 A) (h6 : At s base .r6 B) (hc : (s.gpr .r10).toNat < 2 ^ 32)
    (hA : A + 4 * j + 4 ≤ size) (hB : B + 4 * j + 4 ≤ size) (hacc : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (addDigit acc j)) s fun u =>
      u.mem = s.mem.writeW (off base (acc + 4 * j)) (BitVec.ofNat 32
        (w32 s.mem base (A + 4 * j) + w32 s.mem base (B + 4 * j) + (s.gpr .r10).toNat)) ∧
      (u.gpr .r10).toNat = (w32 s.mem base (A + 4 * j) + w32 s.mem base (B + 4 * j) + (s.gpr .r10).toNat) / 2 ^ 32 ∧
      Kp [.r10, .r11, .r12] s u := by
  have t0 := w32_lt s.mem base (A + 4 * j)
  have t1 := w32_lt s.mem base (B + 4 * j)
  simp only [addDigit]
  refine wp_step (lwz_ok hs h5 (by decide) (by omega)) ?_
  refine wp_step (lwz_ok (hs.write _ _) (h6.write _) (by decide) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (stw0_ok ((((hs.write _ _).write _ _).write _ _).write _ _)
    ((((h3.write _).write _).write _).write _) (by decide) hacc) ?_
  refine wp_step (exec_lsr_d (by decide)) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  have e : (BitVec.ofNat 64 (w32 s.mem base (A + 4 * j)) + BitVec.ofNat 64 (w32 s.mem base (B + 4 * j)) +
      s.gpr .r10).toNat = w32 s.mem base (A + 4 * j) + w32 s.mem base (B + 4 * j) + (s.gpr .r10).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
    omega
  refine ⟨by rw [e], by rw [BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow], ?_⟩
  exact ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false], rfl, rfl, rfl, rfl⟩

/-- The first `k` digits of the sum. -/
def adds (acc k : Nat) : List Instr := (List.range k).flatMap (addDigit acc)

theorem adds_succ (acc k : Nat) : adds acc (k + 1) = adds acc k ++ addDigit acc k := by
  simp only [adds, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` digits of `[r5] + [r6] + r10` to `[acc]`, the carry to `r10`. -/
theorem adds_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {acc A B W : Nat}
    (h3 : At s base .r3 0) (h5 : At s base .r5 A) (h6 : At s base .r6 B) (hc : (s.gpr .r10).toNat ≤ 1)
    (hA : A + 4 * W ≤ size) (hB : B + 4 * W ≤ size) (hacc : acc + 4 * W ≤ size)
    (s1 : A + 4 * W ≤ acc ∨ acc + 4 * W ≤ A) (s2 : B + 4 * W ≤ acc ∨ acc + 4 * W ≤ B) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block (adds acc k)) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧
      val32 u.mem base acc k + 2 ^ (32 * k) * (u.gpr .r10).toNat =
        val32 s.mem base A k + val32 s.mem base B k + (s.gpr .r10).toNat ∧
      (u.gpr .r10).toNat ≤ 1 ∧ Kp [.r10, .r11, .r12] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [val32], hc, Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [adds_succ]
    refine wp_append (WP.mono (adds_ok hs h3 h5 h6 hc hA hB hacc s1 s2 (k := k) (by omega))
      fun s₁ ⟨O₁, V₁, C₁, K₁⟩ => ?_)
    refine WP.mono (addDigit_ok (K₁.ws hs) (K₁.at h3) (K₁.at h5) (K₁.at h6) (by omega) (j := k)
      (by omega) (by omega) (by omega)) fun u ⟨m₂, c₂, K₂⟩ => ?_
    have ak : w32 s₁.mem base (A + 4 * k) = w32 s.mem base (A + 4 * k) := O₁.w32 (by omega) (by omega)
    have bk : w32 s₁.mem base (B + 4 * k) = w32 s.mem base (B + 4 * k) := O₁.w32 (by omega) (by omega)
    rw [ak, bk] at m₂ c₂
    have W := writeW32_outside s₁.mem base (d := acc + 4 * k)
      (BitVec.ofNat 32 (w32 s.mem base (A + 4 * k) + w32 s.mem base (B + 4 * k) + (s₁.gpr .r10).toNat)) (by omega)
    rw [← m₂] at W
    have hlow : val32 u.mem base acc k = val32 s₁.mem base acc k := W.val32 (by omega) (by omega)
    have htop : w32 u.mem base (acc + 4 * k) = (w32 s.mem base (A + 4 * k) + w32 s.mem base (B + 4 * k) +
        (s₁.gpr .r10).toNat) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    have t0 := w32_lt s.mem base (A + 4 * k)
    have t1 := w32_lt s.mem base (B + 4 * k)
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, ?_, K₁.trans K₂⟩
    · rw [val32_succ, val32_succ, val32_succ, hlow, htop, c₂, pow32_succ]
      generalize hxd : w32 s.mem base (A + 4 * k) + w32 s.mem base (B + 4 * k) + (s₁.gpr .r10).toNat = x at *
      have hx' := Nat.div_add_mod x (2 ^ 32)
      generalize 2 ^ (32 * k) = P at *
      grind
    · rw [c₂]; omega

/-- Digit `j` of `[r5] + m - [r6]`, from the carry `r10`, to `[r3 + acc + 4j]`. -/
theorem subDigit_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {acc A B j : Nat}
    (h3 : At s base .r3 0) (h5 : At s base .r5 A) (h6 : At s base .r6 B) (h0 : s.gpr .r0 = M32)
    (hc : (s.gpr .r10).toNat < 2 ^ 32)
    (hA : A + 4 * j + 4 ≤ size) (hB : B + 4 * j + 4 ≤ size) (hmo : M.mo + 4 * j + 4 ≤ size)
    (hacc : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (subDigit M acc j)) s fun u =>
      u.mem = s.mem.writeW (off base (acc + 4 * j)) (BitVec.ofNat 32
        (w32 s.mem base (A + 4 * j) + w32 s.mem base (M.mo + 4 * j) + (2 ^ 32 - 1 - w32 s.mem base (B + 4 * j)) +
          (s.gpr .r10).toNat)) ∧
      (u.gpr .r10).toNat = (w32 s.mem base (A + 4 * j) + w32 s.mem base (M.mo + 4 * j) +
        (2 ^ 32 - 1 - w32 s.mem base (B + 4 * j)) + (s.gpr .r10).toNat) / 2 ^ 32 ∧
      Kp [.r10, .r11, .r12] s u := by
  have t0 := w32_lt s.mem base (A + 4 * j)
  have t1 := w32_lt s.mem base (B + 4 * j)
  have t2 := w32_lt s.mem base (M.mo + 4 * j)
  simp only [subDigit]
  refine wp_step (lwz_ok hs h5 (by decide) (by omega)) ?_
  refine wp_step (lwz0_ok (hs.write _ _) (h3.write _) (by decide) hmo) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step (lwz_ok ((((hs.write _ _).write _ _).write _ _).write _ _)
    ((((h6.write _).write _).write _).write _) (by decide) (by omega)) ?_
  refine wp_step exec_sub ?_
  refine wp_step exec_add ?_
  refine wp_step (stw0_ok (((((((hs.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _).write _ _)
    (((((((h3.write _).write _).write _).write _).write _).write _).write _) (by decide) hacc) ?_
  refine wp_step (exec_lsr_d (by decide)) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true, h0]
  have e : (BitVec.ofNat 64 (w32 s.mem base (A + 4 * j)) + BitVec.ofNat 64 (w32 s.mem base (M.mo + 4 * j)) + M32 -
      BitVec.ofNat 64 (w32 s.mem base (B + 4 * j)) + s.gpr .r10).toNat =
      w32 s.mem base (A + 4 * j) + w32 s.mem base (M.mo + 4 * j) + (2 ^ 32 - 1 - w32 s.mem base (B + 4 * j)) +
        (s.gpr .r10).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega), show M32.toNat = 2 ^ 32 - 1 from rfl]
    omega
  refine ⟨by rw [e], by rw [BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow], ?_⟩
  exact ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false], rfl, rfl, rfl, rfl⟩

/-- The first `k` digits of the difference. -/
def subs (M : Mod) (acc k : Nat) : List Instr := (List.range k).flatMap (subDigit M acc)

theorem subs_succ (M : Mod) (acc k : Nat) : subs M acc (k + 1) = subs M acc k ++ subDigit M acc k := by
  simp only [subs, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` digits of `[r5] + m + 2^(32 k) - [r6]` (from the carry
`r10 = 1`) to `[acc]`, the carry to `r10`. -/
theorem subs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {acc A B W : Nat}
    (h3 : At s base .r3 0) (h5 : At s base .r5 A) (h6 : At s base .r6 B) (h0 : s.gpr .r0 = M32)
    (hc : (s.gpr .r10).toNat = 1)
    (hA : A + 4 * W ≤ size) (hB : B + 4 * W ≤ size) (hmo : M.mo + 4 * W ≤ size) (hacc : acc + 4 * W ≤ size)
    (s1 : A + 4 * W ≤ acc ∨ acc + 4 * W ≤ A) (s2 : B + 4 * W ≤ acc ∨ acc + 4 * W ≤ B)
    (s3 : M.mo + 4 * W ≤ acc ∨ acc + 4 * W ≤ M.mo) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block (subs M acc k)) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧
      val32 u.mem base acc k + 2 ^ (32 * k) * (u.gpr .r10).toNat + val32 s.mem base B k =
        val32 s.mem base A k + val32 s.mem base M.mo k + 2 ^ (32 * k) ∧
      (u.gpr .r10).toNat ≤ 2 ∧ Kp [.r10, .r11, .r12] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [val32, hc], by omega, Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [subs_succ]
    refine wp_append (WP.mono (subs_ok hs h3 h5 h6 h0 hc hA hB hmo hacc s1 s2 s3 (k := k) (by omega))
      fun s₁ ⟨O₁, V₁, C₁, K₁⟩ => ?_)
    refine WP.mono (subDigit_ok (M := M) (K₁.ws hs) (K₁.at h3) (K₁.at h5) (K₁.at h6) (by rw [K₁.g]; exact h0)
      (by omega) (j := k) (by omega) (by omega) (by omega) (by omega)) fun u ⟨m₂, c₂, K₂⟩ => ?_
    have ak : w32 s₁.mem base (A + 4 * k) = w32 s.mem base (A + 4 * k) := O₁.w32 (by omega) (by omega)
    have bk : w32 s₁.mem base (B + 4 * k) = w32 s.mem base (B + 4 * k) := O₁.w32 (by omega) (by omega)
    have mk : w32 s₁.mem base (M.mo + 4 * k) = w32 s.mem base (M.mo + 4 * k) := O₁.w32 (by omega) (by omega)
    rw [ak, bk, mk] at m₂ c₂
    have W := writeW32_outside s₁.mem base (d := acc + 4 * k)
      (BitVec.ofNat 32 (w32 s.mem base (A + 4 * k) + w32 s.mem base (M.mo + 4 * k) +
        (2 ^ 32 - 1 - w32 s.mem base (B + 4 * k)) + (s₁.gpr .r10).toNat)) (by omega)
    rw [← m₂] at W
    have hlow : val32 u.mem base acc k = val32 s₁.mem base acc k := W.val32 (by omega) (by omega)
    have htop : w32 u.mem base (acc + 4 * k) = (w32 s.mem base (A + 4 * k) + w32 s.mem base (M.mo + 4 * k) +
        (2 ^ 32 - 1 - w32 s.mem base (B + 4 * k)) + (s₁.gpr .r10).toNat) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    have t0 := w32_lt s.mem base (A + 4 * k)
    have t1 := w32_lt s.mem base (B + 4 * k)
    have t2 := w32_lt s.mem base (M.mo + 4 * k)
    have hv : val32 u.mem base acc (k + 1) + 2 ^ (32 * (k + 1)) * (u.gpr .r10).toNat + val32 s.mem base B (k + 1) =
        val32 s.mem base A (k + 1) + val32 s.mem base M.mo (k + 1) + 2 ^ (32 * (k + 1)) := by
      rw [val32_succ, val32_succ, val32_succ, val32_succ, hlow, htop, c₂, pow32_succ]
      generalize hxd : w32 s.mem base (A + 4 * k) + w32 s.mem base (M.mo + 4 * k) +
        (2 ^ 32 - 1 - w32 s.mem base (B + 4 * k)) + (s₁.gpr .r10).toNat = x at *
      have hx' := Nat.div_add_mod x (2 ^ 32)
      generalize 2 ^ (32 * k) = P at *
      have : x + w32 s.mem base (B + 4 * k) = w32 s.mem base (A + 4 * k) + w32 s.mem base (M.mo + 4 * k) +
        2 ^ 32 - 1 + (s₁.gpr .r10).toNat := by omega
      grind
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), hv, ?_, K₁.trans K₂⟩
    have := val32_lt s.mem base A (k + 1)
    have := val32_lt s.mem base M.mo (k + 1)
    have hP : 0 < 2 ^ (32 * (k + 1)) := Nat.two_pow_pos _
    by_contra hc3
    have : 2 ^ (32 * (k + 1)) * 3 ≤ 2 ^ (32 * (k + 1)) * (u.gpr .r10).toNat := Nat.mul_le_mul_left _ (by omega)
    omega

end VG.Proof.Mont.PPC64LE
