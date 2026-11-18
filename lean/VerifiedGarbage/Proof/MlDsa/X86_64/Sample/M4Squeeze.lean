module

import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base
import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask4
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBounded
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedLoop
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask
public import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedLoop
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask
meta import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes

/-! ### `MlDsa.X86_64.Sample.ExpandMask`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86_64.Sample.ExpandMaskLoop`, which only this module used -/

section

/-!
# ML-DSA on x86-64: the loop of `vg_mldsa_expand_mask_poly`

Coefficient `k` of a group reads the 32-bit word at byte `⌊ck/8⌋` of the
group, whose bits from `ck mod 8` on are those of the output from bit `ci` on
(`word_bits`: only its first 3 bytes matter); it stores `γ₁` minus their low
`c` bits modulo `q` (`etaF_eq`) to `a[i]` (`emCoef_run`, `emCoef_val`). A
group stores 4 coefficients (`emBody_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q ofInt)
open VG.Proof.MlDsa (coeffAt)

/-! ## Values -/

/-- `(g - x) mod q`, computed with a mask from the borrow. -/
theorem etaF_eq {g x : BitVec 32} (hg : g.toNat < q) (hx : x.toNat < q + g.toNat) :
    etaF g x = zw (ofInt ((g.toNat : Int) - x.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat]
  simp only [ofInt, Fin.val_ofNat]
  simp only [q] at hg hx ⊢
  unfold etaF
  by_cases h : g.toNat < x.toNat
  · rw [decide_eq_true h, show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true) &&& qImm) = qImm by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show qImm.toNat = 8380417 from rfl]
    omega_arith
  · rw [decide_eq_false h, show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false) &&& qImm) = 0 by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]
    omega_arith

/-- Bit `j` of a 32-bit little-endian word. -/
theorem readW32_getLsbD (m : Mem) (a : Addr) {j : Nat} (hj : j < 32) :
    (m.readW a 32).getLsbD j = (m (a + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  rw [Mem.readW_byte m a (by omega_arith), BitVec.getLsbD_extractLsb']
  simp only [show j % 8 < 8 by omega_arith, decide_true, Bool.true_and]
  congr 1; omega_arith

/-- The `c` bits from bit `sh` of the word at `a` are those of `X` from bit
`8o + sh`, if its first 3 bytes are those of `X` from byte `o`. -/
theorem word_bits (m : Mem) (a : Addr) (X : List Byte) {o sh c : Nat} (hc : sh + c ≤ 24)
    (hb : ∀ b < 3, m (a + BitVec.ofNat 64 b) = X.getD (o + b) 0) :
    (m.readW a 32).toNat / 2 ^ sh % 2 ^ c = leNat X / 2 ^ (8 * o + sh) % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < c
  · simp only [hj, decide_true, Bool.true_and]
    rw [← BitVec.getLsbD, readW32_getLsbD m a (j := j + sh) (by omega_arith), hb ((j + sh) / 8) (by omega_arith),
      testBit_leNat, show (j + (8 * o + sh)) / 8 = o + (j + sh) / 8 by omega_arith,
      show (j + (8 * o + sh)) % 8 = (j + sh) % 8 by omega_arith]
  · simp [hj]

/-! ## A coefficient -/

/-- The value stored for coefficient `i` of `c` bits from the output `X`. -/
abbrev emV (X : List Byte) (c i : Nat) : BitVec 32 :=
  zw (ofInt (((2 ^ (c - 1) : Nat) : Int) - (leNat X / 2 ^ (i * c) % 2 ^ c : Nat)))

theorem emCoef_run (c k : Nat) (hk : c * k % 8 < 8) (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) 4)
    (h1 : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (emCoef c k)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 (4 * k))
        (etaF (BitVec.ofNat 32 (2 ^ (c - 1)))
          (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) 32 >>> (c * k % 8) &&&
            BitVec.ofNat 32 (2 ^ c - 1)))) ∧ Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by
    unfold writesOnly emCoef
    split <;> rfl)
  by_cases hs : c * k % 8 = 0
  · simp only [emCoef, hs, ite_true, List.nil_append, List.cons_append]
    xrun [h0, h1]
    rw [BitVec.ushiftRight_zero]; rfl
  · simp only [emCoef, hs, ite_false, List.cons_append, List.nil_append]
    xrun [h0, h1, show 1 ≤ c * k % 8 by omega_arith, show c * k % 8 ≤ 31 by omega_arith]
    rfl

/-- The widths of the coefficients. -/
def emOk (c : Nat) : Prop := c = 18 ∨ c = 20

/-- The value of a coefficient, from the word read and the output `X`. -/
theorem emCoef_val {c : Nat} (hc : emOk c) (m : Mem) (a : Addr) (X : List Byte) {g k : Nat}
    (hb : ∀ b < 3, m (a + BitVec.ofNat 64 b) = X.getD (c / 2 * g + c * k / 8 + b) 0) :
    etaF (BitVec.ofNat 32 (2 ^ (c - 1))) (m.readW a 32 >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)) =
      emV X c (4 * g + k) := by
  have hc' : c ≤ 20 := by rcases hc with rfl | rfl <;> omega_arith
  have hsh : c * k % 8 + c ≤ 24 := by rcases hc with rfl | rfl <;> omega_arith
  have e1 : (m.readW a 32 >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)).toNat =
      leNat X / 2 ^ ((4 * g + k) * c) % 2 ^ c := by
    rw [BitVec.toNat_and, shr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 ^ c - 1) (by
      have : 2 ^ c ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hc'; omega_arith), Nat.and_two_pow_sub_one_eq_mod,
      word_bits m a X hsh hb]
    have e : 8 * (c / 2 * g + c * k / 8) + c * k % 8 = (4 * g + k) * c := by
      rcases hc with rfl | rfl <;> omega_arith
    rw [e]
  have e2 : (BitVec.ofNat 32 (2 ^ (c - 1))).toNat = 2 ^ (c - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have : 2 ^ (c - 1) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) (by omega_arith); omega_arith)]
  have hp : 2 ^ c = 2 * 2 ^ (c - 1) := by
    rw [← Nat.pow_succ']; congr 1; rcases hc with rfl | rfl <;> rfl
  rw [etaF_eq (by rw [e2]; rcases hc with rfl | rfl <;> decide) (by
    rw [e1, e2]; have := Nat.mod_lt (leNat X / 2 ^ ((4 * g + k) * c)) (Nat.two_pow_pos c)
    have : 2 ^ (c - 1) < q := by rcases hc with rfl | rfl <;> decide
    omega_arith), e1, e2]

/-! ## A group of 4 coefficients -/

theorem emOk_le {c : Nat} (hc : emOk c) : c / 2 * 63 + c * 3 / 8 ≤ 637 := by rcases hc with rfl | rfl <;> decide

/-- The facts a group needs. -/
structure GPre (c : Nat) (X : List Byte) (out aP : Addr) (g : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = aP + BitVec.ofNat 64 (16 * g)
  g_lt : g < 64
  bytes : ∀ j < 640, s.mem (out + BitVec.ofNat 64 j) = X.getD j 0
  rd : ∀ j ≤ 637, InRegions (s.rd ++ s.wr) (out + BitVec.ofNat 64 j) 4
  wr : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  apart : ∀ j < 640, ¬ (pR aP).Contains (out + BitVec.ofNat 64 j) 1

/-- The 4 coefficients of group `g`. -/
theorem emGroup_ok {c : Nat} (hc : emOk c) {X : List Byte} {out aP : Addr} {g : Nat} {s : State}
    (h : GPre c X out aP g s) :
    WP isa (.block ((List.range 4).flatMap (emCoef c))) s fun s' =>
      Keep [.rax, .rdx] s s' ∧ Frame [pR aP] s.mem s'.mem ∧
        (∀ k < 4, coeffAt s'.mem aP (4 * g + k) = emV X c (4 * g + k)) ∧
        (∀ i < 256, (i < 4 * g ∨ 4 * g + 4 ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i) := by
  have hg := h.g_lt
  have hle := emOk_le hc
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (fun k s' => Keep [.rax, .rdx] s s' ∧
      Frame [pR aP] s.mem s'.mem ∧ (∀ j < k, coeffAt s'.mem aP (4 * g + j) = emV X c (4 * g + j)) ∧
      (∀ i < 256, (i < 4 * g ∨ 4 * g + k ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i))
    (fun k s' hk ⟨k', hf, hst, hsame⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩) fun s' h => h
  have hsi : s'.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * g) := by rw [k'.gpr (by decide), h.rsi]
  have hdi : s'.gpr .rdi = aP + BitVec.ofNat 64 (16 * g) := by rw [k'.gpr (by decide), h.rdi]
  have ha : s'.gpr .rdi + BitVec.ofNat 64 (4 * k) = coeffAddr aP (4 * g + k) := by
    rw [hdi, offAdd]; congr 2; omega_arith
  have hr : s'.gpr .rsi + BitVec.ofNat 64 (c * k / 8) = out + BitVec.ofNat 64 (c / 2 * g + c * k / 8) := by
    rw [hsi, offAdd]
  have hkk : c * k / 8 ≤ c * 3 / 8 := Nat.div_le_div_right (Nat.mul_le_mul_left c (by omega_arith))
  have hg' : c / 2 * g ≤ c / 2 * 63 := Nat.mul_le_mul_left _ (by omega_arith)
  refine WP.mono (emCoef_run c k (by omega_arith) s' (by rw [hr, k'.2.1, k'.2.2]; exact h.rd _ (by omega_arith))
    (by rw [ha, k'.2.2]; exact h.wr _ (by omega_arith))) fun s'' ⟨hm, k''⟩ => ?_
  have hv := emCoef_val hc s'.mem (s'.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) X (g := g) (k := k) (fun b hb => by
    rw [hr, offAdd, hf _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact h.apart _ (by omega_arith)]
    exact h.bytes _ (by omega_arith))
  rw [ha, hv] at hm
  refine ⟨k'.trans k'' |>.mono (by simp), ?_, fun j hj => ?_, fun i hi hi' => ?_⟩
  · rw [hm]; exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by omega_arith))
  · rw [hm, coeffAt_writeW _ _ (by omega_arith) (by omega_arith)]
    by_cases e : j = k
    · subst e; rw [ifT rfl]
    · rw [ifF (by omega_arith)]; exact hst j (by omega_arith)
  · rw [hm, coeffAt_writeW _ _ hi (by omega_arith), ifF (by omega_arith)]
    exact hsame i hi (by omega_arith)

theorem sxHalf {c : Nat} (hc : emOk c) : BitVec.signExtend 64 (BitVec.ofNat 32 (c / 2)) = BitVec.ofNat 64 (c / 2) := by
  rcases hc with rfl | rfl <;> decide

/-- An iteration: a group, and the pointers and counter advanced. -/
theorem emBody_ok {c : Nat} (hc : emOk c) {X : List Byte} {out aP : Addr} {g : Nat} {s : State}
    (h : GPre c X out aP g s) :
    WP isa (.block (emBody c)) s fun s' =>
      Keep [.rax, .rdx, .rsi, .rdi, .rcx] s s' ∧ Frame [pR aP] s.mem s'.mem ∧
        (∀ k < 4, coeffAt s'.mem aP (4 * g + k) = emV X c (4 * g + k)) ∧
        (∀ i < 256, (i < 4 * g ∨ 4 * g + 4 ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i) ∧
        s'.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * (g + 1)) ∧ s'.gpr .rdi = aP + BitVec.ofNat 64 (16 * (g + 1)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  unfold emBody
  rw [WP.block_append_iff]
  refine WP.mono (emGroup_ok hc h) fun s1 ⟨k1, hf1, hst1, hsame1⟩ => ?_
  refine WP.mono (WP.keep [.rsi, .rdi, .rcx] (Q := fun s' => s'.mem = s1.mem ∧
      s'.gpr .rsi = s1.gpr .rsi + BitVec.ofNat 64 (c / 2) ∧ s'.gpr .rdi = s1.gpr .rdi + BitVec.ofNat 64 16 ∧
      s'.gpr .rcx = s1.gpr .rcx - 1 ∧ s'.zf = some (s1.gpr .rcx - 1 == 0)) (by xrun [sxHalf hc]; rfl)
    (by rfl)) fun s2 ⟨⟨hm2, hsi2, hdi2, hcx2, hz2⟩, k2⟩ => ?_
  have hcx1 : s1.gpr .rcx = s.gpr .rcx := k1.gpr (by decide)
  refine ⟨k1.trans k2 |>.mono (by simp), by rw [hm2]; exact hf1, fun k hk => by rw [hm2]; exact hst1 k hk,
    fun i hi hi' => by rw [hm2]; exact hsame1 i hi hi', ?_, ?_, by rw [hcx2, hcx1], by rw [hz2, hcx1]⟩
  · rw [hsi2, k1.gpr (by decide), h.rsi, offAdd, Nat.mul_succ]
  · rw [hdi2, k1.gpr (by decide), h.rdi, offAdd, Nat.mul_succ]

end VG.Proof.MlDsa.X86_64.Sample

end

end

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly`

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ′, 640)` (`J6`), the branch on `γ₁`, and the loop for `c = 1 + bitlen (γ₁ -
1)`, iteration `g` of which starts from `EAt σ c g` with the coefficients of
the first `g` groups stored. It is constant time: the taint analysis proves
each piece but the sponge, whose proof is `sponge_ct`, from the pointers and
`γ₁`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H toRq bitUnpack bitlen)
open VG.Proof.MlDsa (PolyIs coeffAt)
open VG.Spec.Sha3 (bytesAt)

/-- `γ₁`, the `u32` argument in `esi`. -/
abbrev gOf (s : State) : Nat := ((s.gpr .rsi).setWidth 32).toNat

/-- `vg_mldsa_expand_mask_poly(seed = rdi, gamma1 = esi, a = rdx, scratch = rcx)`,
with 16 bytes of stack below `rsp`. -/
def emK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 66⟩] ∧ s.wr = [pR (s.gpr .rdx), ⟨s.gpr .rcx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 66⟩ (pR (s.gpr .rdx)) ∧ Region.Disjoint ⟨s.gpr .rdi, 66⟩ ⟨s.gpr .rcx, 2048⟩ ∧
    (pR (s.gpr .rdx)).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rdx)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧ (s.gpr .rcx).toNat + 2048 ≤ 2 ^ 64 ∧
    (gOf s = 2 ^ 17 ∨ gOf s = 2 ^ 19)
  post s s' :=
    PolyIs s'.mem (s.gpr .rdx) (toRq (bitUnpack (H (bytesAt s.mem (s.gpr .rdi) 66) (32 * (1 + bitlen (gOf s - 1))))
      (gOf s - 1) (gOf s)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace ExpandMask

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .rdi, 66, σ.gpr .rcx, σ.gpr .rdx, BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32)⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 66

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 640

section
variable {σ : State} (hp : emK.pre σ)
include hp

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1,
    by show (66 : Nat) < 2 ^ 64; decide⟩

theorem gamma : gOf σ = 2 ^ 17 ∨ gOf σ = 2 ^ 19 := hp.2.2.2.2.2.2.2.2.2.2.2.2

theorem pro_ok : WP isa (.block (pro .rcx .rdx (.reg .rsi) (.imm 66))) σ (J0 (spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdx ∧
        s.gpr .r12 = BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32) ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 66)
    (by unfold pro; xrun [inScrσ (spOk hp) (a := 2024) (n := 8) (by omega_using []),
      inScrσ (spOk hp) (a := 2032) (n := 8) (by omega_using []), inScrσ (spOk hp) (a := 2040) (n := 8) (by omega_using []),
      RejBounded.sx66])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ => pro_J0 hm hbx hbp h12 hcx h8 k

/-! ## The loop -/

/-- At the start of iteration `g` of the loop for `c`. -/
structure EAt (σ : State) (c g : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 640 = X σ
  rsi : s.gpr .rsi = (spOf σ).at' 840 + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = σ.gpr .rdx + BitVec.ofNat 64 (16 * g)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (64 - g)
  st : ∀ i < 4 * g, coeffAt s.mem (σ.gpr .rdx) i = emV (X σ) c i

theorem gpre {c g : Nat} (hg : g < 64) {s : State} (h : EAt σ c g s) :
    GPre c (X σ) ((spOf σ).at' 840) (σ.gpr .rdx) g s := by
  have hp' := spOk hp
  refine ⟨h.rsi, h.rdi, hg, fun j hj => ?_, fun j hj => ?_,
    fun i hi => ⟨_, by rw [h.env.wr, hp.2.1]; simp, coeff_contains _ hi⟩, fun j hj hc => ?_⟩
  · have := congrArg (fun L => L.getD j 0) h.out
    rw [MlKem.bytesAt_getD _ _ hj] at this
    exact this
  · rw [at_add]; exact inScrRd hp' h.env (by omega_using [hj])
  · rw [at_add] at hc
    exact a_scr' hp' (a := 840 + j) (n := 1) (by omega_using [hj]) _ hc (Region.contains_self _ _)

/-- An iteration, from `EAt`. -/
theorem eat_step {c g : Nat} (hc : emOk c) (hg : g < 64) {s : State} (h : EAt σ c g s) :
    WP isa (.block (emBody c)) s fun s' => EAt σ c (g + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (64 - g) - 1 == 0) := by
  have hp' := spOk hp
  refine WP.mono (emBody_ok hc (gpre hp hg h)) fun s' ⟨hk, hf, hst, hsame, hsi, hdi, hcx, hz⟩ => ?_
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((spOf σ).at' k) 64 = s.mem.readW ((spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp],
    fun r hr => by rw [hk'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega_using []) (by omega_using []), hsv 2032 (by omega_using []) (by omega_using []), hsv 2040 (by omega_using []) (by omega_using [])];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 640) (by omega_using [])).symm)
      (by omega_using [])]; exact h.out, hsi, hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega_using [hg]) (by omega_using [])]; rfl,
    fun i hi => ?_⟩, by rw [hz, h.rcx]⟩
  by_cases hlo : i < 4 * g
  · rw [hsame i (by omega_using [hg, hi]) (.inl hlo)]; exact h.st i hlo
  · have := hst (i - 4 * g) (by omega_using [hi])
    rwa [show 4 * g + (i - 4 * g) = i by omega_using [hlo]] at this

/-- The loop for `c`, from the sponge's output. -/
theorem loop_ok {c : Nat} (hc : emOk c) {s : State} (h : J6 136 640 (spOf σ) σ s) :
    WP isa (emLoop c) s (EAt σ c 64) := by
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (spOf σ).at' 840 ∧ s'.gpr .rdi = σ.gpr .rdx) (by xrun [h.env.rbx, h.env.rbp, sx840])
    (by decide)) fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 64)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_)
  have he1 := h.env.keep hm1 (k1.mono (by decide))
  refine wp_countdown (N := 64) (by decide) (by decide) (EAt σ c) (fun g hg s hI _ =>
    WP.mono (eat_step hp hc hg hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he1.keep hm2 (k2.mono (by decide)), by rw [hm2, hm1, h.out]; exact (H_eq _ _).symm,
      by rw [k2.gpr (by decide), hsi1]; simp, by rw [k2.gpr (by decide), hdi1]; simp, hcx,
      fun i hi => absurd hi (by omega_using [])⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega_using [hg]) (by omega_using [])]; rfl

/-- The branch on `γ₁`, and the loop for it. -/
theorem sel_ok {s : State} (h : J6 136 640 (spOf σ) σ s) :
    WP isa (.seq (.block [.alu32 .cmp .r12 (.imm 0x20000)]) (.ite .e (emLoop 18) (emLoop 20))) s
      (EAt σ (emC (gOf σ)) 64) := by
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r12) - 0x20000 == 0)) (by xrun) (by rfl))
    fun s1 ⟨⟨hm1, h12, hz1⟩, k1⟩ => ?_)
  have k1' : Keep [] s s1 := ⟨fun r hr => by
    by_cases e : r = .r12
    · subst e; exact h12
    · exact k1.gpr (by simp [e]), k1.2⟩
  have hr12 : BitVec.setWidth 32 (s.gpr .r12) = BitVec.ofNat 32 (gOf σ) := by
    rw [h.env.r12]; rw [sw32_64, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hJ : J6 136 640 (spOf σ) σ s1 := ⟨h.env.keep hm1 (k1'.mono (by decide)), by rw [hm1]; exact h.out⟩
  rcases gamma hp with he | he
  · refine WP.ite true (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [show emC (gOf σ) = 18 by rw [he]; rfl]; exact loop_ok hp (.inl rfl) hJ
  · refine WP.ite false (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun hb => absurd hb (by decide)) (fun _ => ?_)
    rw [show emC (gOf σ) = 20 by rw [he]; rfl]; exact loop_ok hp (.inr rfl) hJ

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : EAt σ (emC (gOf σ)) 64 s) :
    WP isa (.block epi) s fun s' => emK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.mono (epi_ok (spOk hp) h.env) fun s' ⟨⟨hbx, hbp, h12, hm⟩, k⟩ =>
    ⟨?_, gpr_end (spOk hp) h.env hbx hbp h12 (k.mono (by simp)) hm⟩
  obtain ⟨_, _, hγ⟩ := emC_eq (gamma hp)
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [expandMask_getElem _ (gamma hp) hi, hm, h.st i (by omega)]
  simp only [emV]
  congr 3
  rw [← hγ]

end

end ExpandMask

theorem expandMask_correct (σ : State) (hp : emK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.expandMask σ t s' ∧ abiPreserved σ s' ∧ emK.post σ s' := by
  open ExpandMask in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 136) (outlen := 640) (.inl rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (sel_ok hp h2) fun s3 h3 => end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

namespace ExpandMask

theorem hok : ∀ σ, emK.pre σ → SpOk (spOf σ) σ := fun _ hp => spOk hp

theorem hpub : ∀ σ₁ σ₂, emK.pre σ₁ → emK.pre σ₂ → emK.pub σ₁ σ₂ → SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  fun _ _ _ _ hq => ⟨hq.1, rfl, hq.2.2.2.1, hq.2.2.1, by simp only [hq.2.1], hq.2.2.2.2⟩

end ExpandMask

open ExpandMask in
theorem expandMask_ct : ConstantTime isa emK.pre emK.pub Impl.MlDsa.X86_64.Sample.expandMask := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (spOf σ) σ)
    (fun σ s hp h => by subst h; exact pro_ok hp)
    (taintRel [.rdi, .rdx, .rcx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]) (by taint_decide))) ?_)
  refine RelCT.seq (sponge_ct hok hpub (.inl rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact taintSp hpub (J := J6 136 640) (fun _ _ h => h.env) [] nil_regs (by taint_decide)

/-- A state satisfying the precondition. -/
def emSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x20000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem expandMask_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.expandMask (Proof.MlDsa.expandMaskContract X86_64.abi 16) :=
  Verified.of_correct expandMask_correct expandMask_ct
    { pre := by sig_implies_pre [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, emK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, emK, X86_64.abi, X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, emK, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp⟩
      sat := by sig_implies_sat [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, emK, X86_64.abi,
        X86_64.argRegs] [emSat] using emSat }

end VG.Proof.MlDsa.X86_64.Sample

end

end

/-! ### `MlDsa.X86_64.Sample.M4Base`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4`, the layout

Untrusted: everything here is checked by Lean. The contract the proofs are
written against (`em4K`), what holds between the pieces of the functions
(`Env`, relative to the entry state `σ`), and the prologue, as for
`vg_mlkem_sample_ntt4` (`Proof/MlKem/X86_64/S4Base.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64 (Keep WP.keep retR)
open VG.Proof.MlDsa.X86_64.Sample (gOf)
open VG.Spec.MlDsa (H toRq bitUnpack bitlen)
open VG.Proof.MlDsa (PolyIs seed66)
open VG.Spec.Sha3 (bytesAt)

/-- The output polynomial `k` of four at `a`. -/
abbrev poly4 (a : Addr) (k : Nat) : Addr := a + BitVec.ofNat 64 (1024 * k)

/-- `vg_mldsa_expand_mask_poly4(seeds = rdi, gamma1 = esi, a = rdx, scratch = rcx)`,
with 24 bytes of stack below `rsp`. -/
def em4K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 264⟩] ∧ s.wr = [⟨s.gpr .rdx, 4096⟩, ⟨s.gpr .rcx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 264⟩ ⟨s.gpr .rdx, 4096⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 264⟩ ⟨s.gpr .rcx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 4096⟩ ⟨s.gpr .rcx, 8192⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 264⟩ ∧ (retR s).Disjoint ⟨s.gpr .rdx, 4096⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 264⟩ ∧ (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, 4096⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 4096 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧
    (gOf s = 2 ^ 17 ∨ gOf s = 2 ^ 19)
  post s s' := ∀ k < 4, PolyIs s'.mem (poly4 (s.gpr .rdx) k)
    (toRq (bitUnpack (H (seed66 s.mem (s.gpr .rdi) k) (32 * (1 + bitlen (gOf s - 1)))) (gOf s - 1) (gOf s)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

section
variable (σ : State)
abbrev sd : Addr := σ.gpr .rdi
abbrev aP : Addr := σ.gpr .rdx
abbrev scr : Addr := σ.gpr .rcx
/-- Seed `k`. -/
abbrev B (k : Nat) : List Byte := seed66 σ.mem (sd σ) k
abbrev sdR : Region := ⟨sd σ, 264⟩
abbrev aR : Region := ⟨aP σ, 4096⟩
abbrev scrR : Region := ⟨scr σ, 8192⟩
abbrev stkR : Region := below (σ.gpr .rsp) 24
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := scr σ + BitVec.ofNat 64 off
end

/-- The precondition, by name. -/
structure Pre (σ : State) : Prop where
  rd : σ.rd = [sdR σ]
  wr : σ.wr = [aR σ, scrR σ]
  sd_a : (sdR σ).Disjoint (aR σ)
  sd_scr : (sdR σ).Disjoint (scrR σ)
  a_scr : (aR σ).Disjoint (scrR σ)
  ret_sd : (retR σ).Disjoint (sdR σ)
  ret_a : (retR σ).Disjoint (aR σ)
  ret_scr : (retR σ).Disjoint (scrR σ)
  stk_sd : (stkR σ).Disjoint (sdR σ)
  stk_a : (stkR σ).Disjoint (aR σ)
  stk_scr : (stkR σ).Disjoint (scrR σ)
  a_lt : (aP σ).toNat + 4096 ≤ 2 ^ 64
  scr_lt : (scr σ).toNat + 8192 ≤ 2 ^ 64
  gamma : gOf σ = 2 ^ 17 ∨ gOf σ = 2 ^ 19

theorem pre_of {σ : State} (h : em4K.pre σ) : Pre σ :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- What holds between the pieces. -/
structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = scr σ
  r12 : s.gpr .r12 = sd σ
  r13 : s.gpr .r13 = aP σ
  r14 : s.gpr .r14 = σ.gpr .rsi
  rsp : s.gpr .rsp = σ.gpr .rsp
  r15 : s.gpr .r15 = σ.gpr .r15
  saved : ∀ i < 5, s.mem.readW (at' σ (oSave + 8 * i)) 64 = σ.gpr (saved.getD i .rbx)
  frame : Frame [aR σ, scrR σ, stkR σ] σ.mem s.mem

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 8192) : Region.Sub ⟨at' σ a, n⟩ (scrR σ) := Offset.sub_base _ h

omit hp in
theorem sub_poly {k : Nat} (hk : k < 4) : Region.Sub ⟨poly4 (aP σ) k, 1024⟩ (aR σ) :=
  Offset.sub_base _ (by omega_using [hk])

theorem in_scr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) : InRegions s.wr (at' σ a) n := by
  rw [hw, hp.wr]; exact ⟨scrR σ, by simp, Offset.contains_base _ h (by omega_using [h])⟩

theorem in_scr' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (at' σ a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨scrR σ, by simp, Offset.contains_base _ h (by omega_using [h])⟩

theorem in_sd' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 264) :
    InRegions (s.rd ++ s.wr) (sd σ + BitVec.ofNat 64 a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨sdR σ, by simp, Offset.contains_base _ h (by omega_using [h])⟩

/-- The seeds are not written. -/
theorem seeds_frame {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) {a : Nat} (ha : a < 264) :
    m (sd σ + BitVec.ofNat 64 a) = σ.mem (sd σ + BitVec.ofNat 64 a) :=
  hf.bytes (R := sdR σ) (by simpa using ⟨hp.sd_a, hp.sd_scr, hp.stk_sd.symm⟩) (by simp) ha

/-- Byte `a` of seed `k`. -/
theorem seed_byte {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) {k a : Nat} (hk : k < 4) (ha : a < 66) :
    m (sd σ + BitVec.ofNat 64 (66 * k + a)) = (B σ k).getD a 0 := by
  rw [seeds_frame hp hf (by omega_using [hk, ha]), B, seed66, ← Offset.add_add]
  simp [bytesAt, ha]

end

/-! ## The prologue -/

/-- A read of 8 bytes at `scratch + d` after a write of 8 elsewhere. -/
theorem rd64_off {σ : State} {m : Mem} {d e : Nat} {v : BitVec 64} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : (m.writeW (at' σ e) v).readW (at' σ d) 64 = m.readW (at' σ d) 64 :=
  readW_writeW_off m _ v (n := 8) (by omega_using [hd]) (by omega_using [he]) h

theorem pro_eq : pro = [.store (VG.Impl.MlKem.X86_64.at_ .rcx 5088) .rbx, .store (VG.Impl.MlKem.X86_64.at_ .rcx 5096) .rbp,
    .store (VG.Impl.MlKem.X86_64.at_ .rcx 5104) .r12, .store (VG.Impl.MlKem.X86_64.at_ .rcx 5112) .r13,
    .store (VG.Impl.MlKem.X86_64.at_ .rcx 5120) .r14, .mov .rbx (.reg .rcx), .mov .r12 (.reg .rdi),
    .mov .r13 (.reg .rdx), .mov .r14 (.reg .rsi)] := rfl

theorem pro_ok {σ : State} (hp : Pre σ) : WP isa (.block pro) σ (Env σ) := by
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .r12, .r13, .r14] (Q := fun s =>
      s.mem = ((((σ.mem.writeW (at' σ 5088) (σ.gpr .rbx)).writeW (at' σ 5096) (σ.gpr .rbp)).writeW (at' σ 5104)
          (σ.gpr .r12)).writeW (at' σ 5112) (σ.gpr .r13)).writeW (at' σ 5120) (σ.gpr .r14) ∧
        s.gpr .rbx = scr σ ∧ s.gpr .r12 = sd σ ∧ s.gpr .r13 = aP σ ∧ s.gpr .r14 = σ.gpr .rsi)
    (by xrun [in_scr hp rfl (a := 5088) (n := 8) (by omega_using []), in_scr hp rfl (a := 5096) (n := 8) (by omega_using []),
      in_scr hp rfl (a := 5104) (n := 8) (by omega_using []), in_scr hp rfl (a := 5112) (n := 8) (by omega_using []),
      in_scr hp rfl (a := 5120) (n := 8) (by omega_using [])])
    (by decide)) fun s1 ⟨⟨hm1, hbx, h12, h13, h14⟩, k1⟩ => ⟨k1.2.1, k1.2.2, hbx, h12, h13, h14,
      k1.gpr (by decide), k1.gpr (by decide), fun i hi => ?_, ?_⟩
  · rw [hm1]
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega_using []) only [oSave, Mem.readW_writeW_self64, rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [hm1]
    have hin : ∀ a, a + 8 ≤ 8192 → (scrR σ).Contains (at' σ a) (64 / 8) := fun a ha =>
      Offset.contains_base _ (by omega_using [ha]) (by omega_using [ha])
    exact ((((((Frame.refl _ _).writeW (by simp) _ (hin 5088 (by omega_using []))).writeW (by simp) _
      (hin 5096 (by omega_using []))).writeW (by simp) _ (hin 5104 (by omega_using []))).writeW (by simp) _
      (hin 5112 (by omega_using []))).writeW (by simp) _ (hin 5120 (by omega_using [])))

end VG.Proof.MlDsa.X86_64.Mask4

end

end

/-! ### `MlDsa.X86_64.Sample.M4Absorb`, which only this module used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, the round constants and the padded seeds

Untrusted: everything here is checked by Lean. After the prologue, the
table of the round constants (`rc_ok`), and the four states holding the
padded 66-byte seeds, byte by byte (`absorb_ok`), as for
`vg_mlkem_sample_ntt4_avx2` (`Proof/MlKem/X86_64/S4Squeeze.lean`, whose
lemmas on the bytes of the states it uses).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (zero4 oRc)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlKem.X86_64.S4 (wb_in wb_out off4 bytes_write byte_setWidth)
open VG.Proof.Sha3.X86_64.X4 (q4 VUpd la ba Lanes4 wp_vmovq wp_vbcast wp_vst wp_vxor readW_write256 q4_ymm)
open VG.Proof.Sha3.X86_64 (wp_movi64)

/-- `Env` after writes below the saved registers. -/
theorem Env.write {σ s s' : State} (he : Env σ s) {a n : Nat} (h : a + n ≤ oSave)
    (hf : Frame [⟨at' σ a, n⟩] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r) : Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .r14 (by simp), he.r14], by rw [hg .rsp (by simp), he.rsp],
    by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using Offset.disjoint (scr σ) (d := oSave + 8 * i) (n := 8) (e := a) (k := n) (by simp only [oSave] at h ⊢; omega_arith)
          (by simp only [oSave]; omega_arith) (by simp only [oSave] at h; omega_arith)) (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR σ, by simp, Offset.sub_base _ (by simp only [oSave] at h; omega_arith)⟩

/-! ## The round constants -/

/-- After the first `n` round constants. -/
structure RcInv (σ s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.rax] s₀ s
  frame : Frame [⟨at' σ oRc, 768⟩] s₀.mem s.mem
  rc : ∀ r < n, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = Spec.Sha3.RC r

theorem rc_step {σ : State} (hp : Pre σ) {s₀ : State} (he : Env σ s₀) {r : Nat} (hr : r < 24) {s : State}
    (h : RcInv σ s₀ r s) :
    WP isa (.block [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax),
      .vop (.vpbroadcastq .l256 .xmm0 .xmm0), Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0]) s
      (RcInv σ s₀ (r + 1)) := by
  have hbx : s.gpr .rbx = scr σ := by rw [h.keep.gpr (by decide), he.rbx]
  refine wp_movi64 fun s₁ u₁ => wp_vmovq fun s₂ u₂ => wp_vbcast fun s₃ u₃ =>
    wp_vst (a := at' σ (32 * (50 + r))) (by rw [VG.Proof.Sha3.X86_64.ea_at, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hbx]; rfl)
      (by rw [u₃.wr, u₂.wr, u₁.wr, h.keep.2.2, he.wr]; exact in_scr hp rfl (by omega_arith))
      fun s₄ g₄ _ m₄ r₄ w₄ => VG.Proof.Sha3.X86_64.wp_nil ?_
  have hv : ∀ k < 4, q4 s₃ .xmm0 k = Spec.Sha3.RC r := fun k hk => by
    rw [u₃.val k hk, u₂.val 0 (by decide), ite_eq_left rfl, u₁.gpr]
  have hm : s₄.mem = s.mem.writeW (at' σ (32 * (50 + r))) (s₃.ymm .xmm0) := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun g hg => by rw [g₄, u₃.gpr, u₂.gpr, u₁.other g (by simpa using hg), h.keep.gpr hg],
      by rw [r₄, u₃.rd, u₂.rd, u₁.rd, h.keep.2.1], by rw [w₄, u₃.wr, u₂.wr, u₁.wr, h.keep.2.2]⟩, ?_,
    fun r' hr' k hk => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [oRc]; omega_arith)
      (by simp only [oRc]; omega_arith) (by simp only [oRc]; omega_arith))
  · rw [hm]
    by_cases e : r' = r
    · subst e
      rw [la, ← Offset.add_add, readW_write256 _ _ _ hk, q4_ymm _ _ hk, hv k hk]
    · have e := readW_writeW_off s.mem (scr σ) (s₃.ymm .xmm0) (d := 32 * (50 + r') + 8 * k)
        (e := 32 * (50 + r)) (n := 8) (by omega_arith) (by omega_arith) (by omega_arith)
      exact e.trans (h.rc r' (by omega_arith) k hk)

theorem rcTable_eq : Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) = (List.range 24).flatMap fun r =>
    [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0] := rfl

/-- The table of the round constants. -/
theorem rc_ok {σ : State} (hp : Pre σ) {s₀ : State} (he : Env σ s₀) :
    WP isa (.block (Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32))) s₀ (RcInv σ s₀ 24) := by
  rw [rcTable_eq]
  exact wp_range_flatMap (M := isa) (RcInv σ s₀) (fun r s hr h => rc_step hp he hr h) 24 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩


/-! ## The states, byte by byte -/

/-- The four states hold `F`. -/
def SB (σ : State) (m : Mem) (F : Nat → Nat → Byte) : Prop :=
  ∀ k < 4, ∀ q < 200, m (ba (scr σ) k q) = F k q

/-- During the writes to the states, after the round constants (in `m₁`). -/
structure AI (σ : State) (m₁ : Mem) (s : State) : Prop where
  env : Env σ s
  frame : Frame [⟨scr σ, 800⟩] m₁ s.mem

theorem AI.write {σ : State} {m₁ : Mem} {s s' : State} (h : AI σ m₁ s) {e n : Nat} (hn : e + n ≤ 800)
    (hm : ∃ v : BitVec (8 * n), s'.mem = s.mem.writeW (at' σ e) v) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) : AI σ m₁ s' := by
  obtain ⟨v, hv⟩ := hm
  have hf : Frame [⟨at' σ e, n⟩] s.mem s'.mem := by
    rw [hv]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      rw [show 8 * n / 8 = n by omega_arith]; exact Region.contains_self _ _)
  refine ⟨h.env.write (by simp only [oSave]; omega_arith) hf hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    h.frame.trans (hf.sub fun r hr => ?_)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ hn⟩

/-! ### Zeroing -/

/-- After zeroing the first `n` lanes of each state. -/
structure ZInv (σ : State) (m₁ : Mem) (n : Nat) (s : State) : Prop where
  ai : AI σ m₁ s
  x0 : ∀ k < 4, q4 s .xmm0 k = 0
  bytes : ∀ k < 4, ∀ q < 200, q / 8 < n → s.mem (ba (scr σ) k q) = 0

theorem zero_step {σ : State} (hp : Pre σ) {m₁ : Mem} {i : Nat} (hi : i < 25) {s : State} (h : ZInv σ m₁ i s) :
    WP isa (.block [Impl.Sha3.X86_64.X4.st .rbx i .xmm0]) s (ZInv σ m₁ (i + 1)) := by
  refine wp_vst (a := at' σ (32 * i)) (by rw [VG.Proof.Sha3.X86_64.ea_at, h.ai.env.rbx])
    (by rw [h.ai.env.wr]; exact in_scr hp rfl (by omega_arith)) fun s' g' q' m' r' w' => VG.Proof.Sha3.X86_64.wp_nil ?_
  refine ⟨h.ai.write (e := 32 * i) (n := 32) (by omega_arith) ⟨_, m'⟩ r' w' fun r _ => by rw [g'],
    fun k hk => by rw [q', h.x0 k hk], fun k hk q hq hn => ?_⟩
  rw [m']
  have hb := bytes_write (m := s.mem) (p := scr σ) (F := fun k q => s.mem (ba (scr σ) k q))
    (fun _ _ _ _ => rfl) (s.ymm .xmm0) (e := 32 * i) (by decide) (by omega_arith) hk hq
  rw [hb]
  split
  · rename_i hc
    simp only [off4] at hc ⊢
    rw [show 8 * (32 * (q / 8) + 8 * k + q % 8 - 32 * i) = 64 * k + 8 * (q % 8) by omega_arith, ← extract_extract (s.ymm .xmm0) (64 * k) 64 (8 * (q % 8)) 8 (by omega_arith),
      q4_ymm _ _ hk, h.x0 k hk]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · rename_i hc
    simp only [off4] at hc
    exact h.bytes k hk q hq (by omega_arith)

theorem zero4_eq : zero4 = Impl.Sha3.X86_64.X4.vb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 25).flatMap fun i => [Impl.Sha3.X86_64.X4.st .rbx i .xmm0] := rfl

theorem zero_ok {σ : State} (hp : Pre σ) {m₁ : Mem} {s : State} (h : AI σ m₁ s) :
    WP isa (.block zero4) s (fun s' => AI σ m₁ s' ∧ SB σ s'.mem fun _ _ => 0) := by
  rw [zero4_eq]
  refine wp_vxor fun s₁ u₁ => WP.mono (wp_range_flatMap (M := isa) (ZInv σ m₁) (fun i s hi h => zero_step hp hi h)
    25 (Nat.le_refl _) s₁ ⟨h.write (e := 0) (n := 0) (by omega_arith) ⟨0, ?_⟩ u₁.rd u₁.wr fun r _ => by rw [u₁.gpr],
      fun k hk => by rw [u₁.val k hk, BitVec.xor_self]; rfl, fun _ _ _ _ h => absurd h (by omega_arith)⟩)
    fun s' h' => ⟨h'.ai, fun k hk q hq => h'.bytes k hk q hq (by omega_arith)⟩
  rw [u₁.mem]
  funext x
  simp [Mem.writeW, Mem.write]


/-! ### The seeds -/

/-- Byte `q` of seed `k` (0 past its end). -/
abbrev Bq (σ : State) (k q : Nat) : Byte := (B σ k).getD q 0

/-- The states after the first `K` seeds, and the first `i` lanes of seed `K`. -/
def HF (σ : State) (K i : Nat) (k q : Nat) : Byte :=
  if (k < K ∧ q < 66) ∨ (k = K ∧ q < 8 * i) then Bq σ k q else 0

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
theorem lane_step {σ : State} (hp : Pre σ) {m₁ : Mem} {K i : Nat} (hK : K < 4) (hi : i < 8) {s : State}
    (h : AI σ m₁ s ∧ SB σ s.mem (HF σ K i)) :
    WP isa (.block [.mov .rax (.mem (at_ .r12 (66 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) s
      (fun s' => AI σ m₁ s' ∧ SB σ s'.mem (HF σ K (i + 1))) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movm (a := sd σ + BitVec.ofNat 64 (66 * K + 8 * i)) (by rw [ea_at, ha.env.r12])
    (in_sd' hp ha.env.rd ha.env.wr (by omega_arith)) fun s₁ u₁ => wp_store (a := at' σ (32 * i + 8 * K))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact in_scr hp ha.env.wr (by omega_arith))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (32 * i + 8 * K)) (s.mem.readW (sd σ + BitVec.ofNat 64 (66 * K + 8 * i)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨ha.write (e := 32 * i + 8 * K) (n := 8) (by omega_arith) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega_arith) hk hq]
  simp only [off4]
  by_cases hc : 32 * i + 8 * K ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 32 * i + 8 * K + 64 / 8
  · have hk' : k = K := by omega_arith
    have hq' : q / 8 = i := by omega_arith
    subst hk'
    rw [ifp hc, HF, ifp (.inr ⟨rfl, by omega_arith⟩),
      show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * i + 8 * k)) = 8 * (q % 8) by omega_arith,
      byte_readW _ _ (by omega_arith), Offset.add_add, show 66 * k + 8 * i + q % 8 = 66 * k + q by omega_arith,
      seed_byte hp ha.env.frame hK (by omega_arith)]
  · rw [ifn hc, HF, HF]
    by_cases hc' : (k < K ∧ q < 66) ∨ (k = K ∧ q < 8 * i)
    · rw [ifp hc', ifp (by omega_arith)]
    · rw [ifn hc', ifn (by omega_arith)]

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
/-- Byte `64 + j` of seed `K`. -/
theorem byte_step {σ : State} (hp : Pre σ) {m₁ : Mem} {K j : Nat} (hK : K < 4) (hj : j < 2) {s : State}
    (h : AI σ m₁ s ∧ SB σ s.mem fun k q => if (k < K ∧ q < 66) ∨ (k = K ∧ q < 64 + j) then Bq σ k q else 0) :
    WP isa (.block [.movzx8 .rax (at_ .r12 (66 * K + (64 + j))), .store8 (at_ .rbx (256 + 8 * K + j)) .rax]) s
      (fun s' => AI σ m₁ s' ∧
        SB σ s'.mem fun k q => if (k < K ∧ q < 66) ∨ (k = K ∧ q < 64 + (j + 1)) then Bq σ k q else 0) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movzx8 (a := sd σ + BitVec.ofNat 64 (66 * K + (64 + j))) (by rw [ea_at, ha.env.r12])
    (in_sd' hp ha.env.rd ha.env.wr (by omega_arith)) fun s₁ u₁ => wp_store8 (a := at' σ (256 + 8 * K + j))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact in_scr hp ha.env.wr (by omega_arith))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (256 + 8 * K + j)) (s.mem (sd σ + BitVec.ofNat 64 (66 * K + (64 + j)))) := by
    rw [m₂, u₁.mem, u₁.gpr, byte_setWidth]
  refine ⟨ha.write (e := 256 + 8 * K + j) (n := 1) (by omega_arith) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega_arith) hk hq]
  simp only [off4]
  by_cases hc : 256 + 8 * K + j ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 256 + 8 * K + j + 8 / 8
  · have hk' : k = K := by omega_arith
    have hq' : q = 64 + j := by omega_arith
    subst hk' hq'
    rw [ifp hc, ifp (.inr ⟨rfl, by omega_arith⟩), show 8 * (32 * ((64 + j) / 8) + 8 * k + (64 + j) % 8 -
      (256 + 8 * k + j)) = 0 by omega_arith, Proof.Sha3.extractLsb'_byte, seed_byte hp ha.env.frame hK (by omega_arith)]
  · rw [ifn hc]
    by_cases hc' : (k < K ∧ q < 66) ∨ (k = K ∧ q < 64 + j)
    · rw [ifp hc', ifp (by omega_arith)]
    · rw [ifn hc', ifn (by omega_arith)]

theorem seedLanes_eq (K : Nat) : seedLanes K = (List.range 8).flatMap (fun i =>
    [.mov .rax (.mem (at_ .r12 (66 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) ++
    (([.movzx8 .rax (at_ .r12 (66 * K + (64 + 0))), .store8 (at_ .rbx (256 + 8 * K + 0)) .rax] : List Instr) ++
      ([.movzx8 .rax (at_ .r12 (66 * K + (64 + 1))), .store8 (at_ .rbx (256 + 8 * K + 1)) .rax] : List Instr)) := by
  simp only [seedLanes, Nat.add_zero]; rfl

/-- The states after the first `K` seeds. -/
def GF (σ : State) (K : Nat) (k q : Nat) : Byte := if k < K ∧ q < 66 then Bq σ k q else 0

theorem seed_step {σ : State} (hp : Pre σ) {m₁ : Mem} {K : Nat} (hK : K < 4) {s : State}
    (h : AI σ m₁ s ∧ SB σ s.mem (GF σ K)) :
    WP isa (.block (seedLanes K)) s (fun s' => AI σ m₁ s' ∧ SB σ s'.mem (GF σ (K + 1))) := by
  rw [seedLanes_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s => AI σ m₁ s ∧ SB σ s.mem (HF σ K i))
    (fun i s hi h => lane_step hp hK hi h) 8 (Nat.le_refl _) s ⟨h.1, fun k hk q hq => ?_⟩) fun s₁ h₁ => ?_
  · rw [h.2 k hk q hq, GF, HF]
    by_cases hc : k < K ∧ q < 66
    · rw [ifp hc, ifp (.inl hc)]
    · rw [ifn hc, ifn (by omega_arith)]
  rw [WP.block_append_iff]
  refine WP.mono (byte_step hp (j := 0) hK (by decide) ⟨h₁.1, fun k hk q hq => ?_⟩) fun s₂ h₂ =>
    WP.mono (byte_step hp (j := 1) hK (by decide) h₂) fun s₃ ⟨h₃, b₃⟩ => ⟨h₃, fun k hk q hq => ?_⟩
  · rw [h₁.2 k hk q hq, HF]
  · rw [b₃ k hk q hq, GF]
    dsimp only
    by_cases hc : (k < K ∧ q < 66) ∨ (k = K ∧ q < 64 + (1 + 1))
    · rw [ifp hc]
      by_cases hc' : k < K + 1 ∧ q < 66
      · rw [ifp hc']
      · rw [ifn hc']; omega_arith
    · rw [ifn hc]
      by_cases hc' : k < K + 1 ∧ q < 66
      · omega_arith
      · rw [ifn hc']


/-! ### The padding -/

open VG.Proof.Sha3.X86_64 (wp_store8 wp_mov32i wp_nil) in
/-- The byte `c` (in `rax`) to byte `q₀` of state `K`. -/
theorem cbyte_step {σ : State} (hp : Pre σ) {m₁ : Mem} {F : Nat → Nat → Byte} {K q₀ : Nat} (hK : K < 4)
    (hq₀ : q₀ < 200) {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : AI σ m₁ s ∧ SB σ s.mem F) :
    WP isa (.block [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * K + q₀ % 8)) .rax]) s
      (fun s' => AI σ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        SB σ s'.mem fun k q => if k = K ∧ q = q₀ then c else F k q) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_store8 (a := at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) (by rw [ea_at, ha.env.rbx])
    (by exact in_scr hp ha.env.wr (by omega_arith)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) c := by
    rw [m₂, hax, byte_setWidth]
  refine ⟨ha.write (n := 1) (by omega_arith) ⟨_, hm⟩ r₂ w₂ fun r _ => by rw [g₂], by rw [g₂], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega_arith) hk hq]
  simp only [off4]
  by_cases hc : 32 * (q₀ / 8) + 8 * K + q₀ % 8 ≤ 32 * (q / 8) + 8 * k + q % 8 ∧
      32 * (q / 8) + 8 * k + q % 8 < 32 * (q₀ / 8) + 8 * K + q₀ % 8 + 8 / 8
  · have e : k = K ∧ q = q₀ := by omega_arith
    rw [ifp hc, ifp e, show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * (q₀ / 8) + 8 * K + q₀ % 8)) = 0 by omega_arith,
      Proof.Sha3.extractLsb'_byte]
  · rw [ifn hc, ifn (by omega_arith)]

/-- The four states hold their padded seeds. -/
def PF (σ : State) (k q : Nat) : Byte :=
  if q < 66 then Bq σ k q else if q = 66 then 0x1f else if q = 135 then 0x80 else 0

/-- The byte `c` to byte `q₀` of each state. -/
theorem cbytes_ok {σ : State} (hp : Pre σ) {m₁ : Mem} {F : Nat → Nat → Byte} {q₀ : Nat} (hq₀ : q₀ < 200)
    {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : AI σ m₁ s ∧ SB σ s.mem F) :
    WP isa (.block ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * k + q₀ % 8)) .rax])) s
      (fun s' => AI σ m₁ s' ∧ SB σ s'.mem fun k q => if q = q₀ then c else F k q) := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s' => AI σ m₁ s' ∧ s'.gpr .rax = c.setWidth 64 ∧
      SB σ s'.mem fun k q => if k < K ∧ q = q₀ then c else F k q)
    (fun K s' hK ⟨ha, hx, hb⟩ => WP.mono (cbyte_step hp hK hq₀ hx ⟨ha, hb⟩) fun s'' ⟨ha', hx', hb'⟩ =>
      ⟨ha', hx'.trans hx, fun k hk q hq => ?_⟩) 4 (Nat.le_refl _) s ⟨h.1, hax, fun k hk q hq => ?_⟩)
    fun s' ⟨ha, _, hb⟩ => ⟨ha, fun k hk q hq => ?_⟩
  · rw [hb' k hk q hq]
    dsimp only
    by_cases e : k = K ∧ q = q₀
    · rw [ifp e, ifp (by omega_arith)]
    · rw [ifn e]
      by_cases e' : k < K ∧ q = q₀
      · rw [ifp e', ifp (by omega_arith)]
      · rw [ifn e', ifn (by omega_arith)]
  · rw [h.2 k hk q hq]; dsimp only; rw [ifn (by omega_arith)]
  · rw [hb k hk q hq]
    dsimp only
    by_cases e : q = q₀
    · rw [ifp e, ifp ⟨hk, e⟩]
    · rw [ifn e, ifn (by omega_arith)]

theorem absorb4_eq : absorb4 = zero4 ++ ((List.range 4).flatMap seedLanes ++
    (([.mov32 .rax (.imm 0x1f)] : List Instr) ++ ((List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (66 / 8) + 8 * k + 66 % 8)) .rax]) ++
    (([.mov32 .rax (.imm 0x80)] : List Instr) ++ (List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (135 / 8) + 8 * k + 135 % 8)) .rax]))))) := by
  simp only [absorb4, List.append_assoc, List.cons_append, List.nil_append]

open VG.Proof.Sha3.X86_64 (wp_mov32i) in
/-- The padded seeds in the four states. -/
theorem absorb_ok {σ : State} (hp : Pre σ) {m₁ : Mem} {s : State} (h : AI σ m₁ s) :
    WP isa (.block absorb4) s (fun s' => AI σ m₁ s' ∧ SB σ s'.mem (PF σ)) := by
  rw [absorb4_eq, WP.block_append_iff]
  refine WP.mono (zero_ok hp h) fun s₁ ⟨h₁, z₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => AI σ m₁ s ∧ SB σ s.mem (GF σ K))
    (fun K s hK h => seed_step hp hK h) 4 (Nat.le_refl _) s₁ ⟨h₁, fun k hk q hq => ?_⟩) fun s₂ h₂ => ?_
  · rw [z₁ k hk q hq, GF, ifn (by omega_arith)]
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₃ u₃ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₃ => AI σ m₁ s₃ ∧ s₃.gpr .rax = (0x1f : Byte).setWidth 64 ∧ SB σ s₃.mem (GF σ 4))
    ⟨h₂.1.write (e := 0) (n := 0) (by omega_arith) ⟨0, ?_⟩ u₃.rd u₃.wr fun r hr => u₃.other r hr, by rw [u₃.gpr]; rfl,
      by rw [u₃.mem]; exact h₂.2⟩) fun s₃ ⟨a₃, x₃, b₃⟩ => ?_
  · rw [u₃.mem]; funext x; simp [Mem.writeW, Mem.write]
  rw [WP.block_append_iff]
  refine WP.mono (cbytes_ok hp (by decide) x₃ ⟨a₃, b₃⟩) fun s₄ ⟨a₄, b₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₅ u₅ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₅ => AI σ m₁ s₅ ∧ s₅.gpr .rax = (0x80 : Byte).setWidth 64 ∧
      SB σ s₅.mem fun k q => if q = 66 then 0x1f else GF σ 4 k q)
    ⟨a₄.write (e := 0) (n := 0) (by omega_arith) ⟨0, ?_⟩ u₅.rd u₅.wr fun r hr => u₅.other r hr, by rw [u₅.gpr]; rfl,
      by rw [u₅.mem]; exact b₄⟩) fun s₅ ⟨a₅, x₅, b₅⟩ => ?_
  · rw [u₅.mem]; funext x; simp [Mem.writeW, Mem.write]
  refine WP.mono (cbytes_ok hp (by decide) x₅ ⟨a₅, b₅⟩) fun s₆ ⟨a₆, b₆⟩ => ⟨a₆, fun k hk q hq => ?_⟩
  rw [b₆ k hk q hq, PF]
  dsimp only
  rw [GF]
  by_cases e1 : q < 66
  · rw [ifn (show ¬ q = 135 by omega_arith), ifn (show ¬ q = 66 by omega_arith), ifp (show k < 4 ∧ q < 66 from ⟨hk, e1⟩),
      ifp e1]
  · rw [ifn e1, ifn (show ¬ (k < 4 ∧ q < 66) by omega_arith)]
    by_cases e2 : q = 66
    · rw [ifn (show ¬ q = 135 by omega_arith), ifp e2, ifp e2]
    · rw [ifn e2, ifn e2]

end VG.Proof.MlDsa.X86_64.Mask4

end

end


/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, squeezing

Untrusted: everything here is checked by Lean. The padded seeds are the
states that `Keccak-f` turns into the absorbed ones (`padded_A0`), and the
four states hold them after `absorb4` (`lanes_A0`). Each `squeeze`
permutes the four states (`permute4_ok`) and copies the first 136 bytes of
each to block `n` of its output, at `rbp`, which then holds the first
`136 (n + 1)` bytes of SHAKE256 of the seed (`hByte`, `sq_ok`); `squeezes`
runs the five in a loop (`sqs_ok`), as for `vg_mlkem_sample_ntt4_avx2`
(`Proof/MlKem/X86_64/S4Squeeze.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (permArgs oBuf)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlKem.X86_64.S4 (wb_in wb_out sx800 sx1600 sx2368 blocks_ok)
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (padded shake256_eq)
open VG.Proof.Sha3 (squeeze_getElem length_squeeze)
open VG.Proof.Sha3.X86_64.X4 (la ba Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok)

/-! ## The padded seeds -/

/-- The state whose permutation is the absorbed padded seed. -/
def A0 (Bs : List Byte) : Spec.Sha3.State := xorByte (xorByte (Rep 136 Bs) 66 0x1f) 135 0x80

theorem padded_A0 {Bs : List Byte} (h : Bs.length = 66) :
    padded 136 Spec.Sha3.shakeSuffix Bs = keccakF (A0 Bs) := by
  rw [padded, absorb_pad (by decide) (by decide), h]; rfl

theorem byteOf_A0 {Bs : List Byte} (h : Bs.length = 66) {q : Nat} (hq : q < 200) :
    byteOf (A0 Bs) q = if q < 66 then Bs.getD q 0 else if q = 66 then 0x1f else if q = 135 then 0x80 else 0 := by
  have hz : byteOf Spec.Sha3.zero q = 0 := by
    simp only [byteOf, Spec.Sha3.zero, getElem!_pos (Vector.replicate 25 (0 : BitVec 64)) (q / 8) (by omega_arith),
      Vector.getElem_replicate]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  have ha : Spec.Sha3.absorb 136 Bs = Spec.Sha3.zero := by simp [Spec.Sha3.absorb, h]
  have hr : byteOf (Rep 136 Bs) q = Bs.getD q 0 := by
    rw [Rep, ha, byteOf_xorBytes _ _ hq, hz, h, show 136 * (66 / 136) = 0 from rfl, List.drop_zero]
    exact BitVec.zero_xor
  have hd : ∀ q, 66 ≤ q → Bs.getD q 0 = 0 := fun q hq' => by
    rw [List.getD, List.getElem?_eq_none (by omega_arith)]; rfl
  rw [A0, byteOf_xorByte _ _ _ hq, byteOf_xorByte _ _ _ hq, hr]
  by_cases e1 : q < 66
  · rw [ifn (show ¬ q = 135 by omega_arith), ifn (show ¬ q = 66 by omega_arith), ifp e1]
  · rw [ifn e1, hd q (by omega_arith)]
    by_cases e2 : q = 66
    · rw [ifn (show ¬ q = 135 by omega_arith), ifp e2, ifp e2]; exact BitVec.zero_xor
    · rw [ifn e2, ifn e2]
      by_cases e3 : q = 135
      · rw [ifp e3, ifp e3]; exact BitVec.zero_xor
      · rw [ifn e3, ifn e3]

theorem B_length (σ : State) (k : Nat) : (B σ k).length = 66 := VG.Proof.Sha3.bytesAt_length _ _ _

/-- Byte `p` of SHAKE256 of `B`: byte `p mod 136` of the padded state after
`⌊p / 136⌋` more permutations. -/
def hByte (B : List Byte) (p : Nat) : Byte :=
  byteOf (iterF (p / 136) (padded 136 Spec.Sha3.shakeSuffix B)) (p % 136)

theorem H_getD (B : List Byte) {ℓ p : Nat} (hp : p < ℓ) : (Spec.MlDsa.H B ℓ).getD p 0 = hByte B p := by
  have hl : (Spec.MlDsa.H B ℓ).length = ℓ := length_squeeze (by decide) (by decide) _ _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact hp), Option.getD_some]
  exact squeeze_getElem (by decide) (by decide) _ hp

/-- Byte `p` of SHAKE256 of `Bs`, from the states. -/
theorem hByte_A0 {Bs : List Byte} (h : Bs.length = 66) {n p : Nat} (hp : p < 136) :
    hByte Bs (136 * n + p) = byteOf (iterF (n + 1) (A0 Bs)) p := by
  rw [hByte, show (136 * n + p) / 136 = n by omega_arith, show (136 * n + p) % 136 = p by omega_arith, padded_A0 h,
    iterF_keccakF]

/-! ## `Env` after writes -/

/-- `Env` after writes below the saved registers. -/
theorem Env.low {σ s s' : State} (he : Env σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨scr σ, oSave⟩)
    (hf : Frame rs s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r) : Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .r14 (by simp), he.r14], by rw [hg .rsp (by simp), he.rsp],
    by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => ((Offset.base_disjoint (scr σ) (k := oSave)
        (e := oSave + 8 * i) (n := 8) (by omega_arith) (by simp only [oSave]; omega_arith)).symm).sub_right (hrs r hr))
      (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ⟨scrR σ, by simp, fun x hx => Offset.sub_base (scr σ) (d := 0)
      (n := oSave) (k := 8192) (by simp only [oSave]; omega_arith) x (by rw [BitVec.add_zero]; exact hrs r hr x hx)⟩)

/-- `Env` after code that writes no memory and keeps its registers. -/
theorem Env.keep {σ s s' : State} (he : Env σ s) (hm : s'.mem = s.mem) {rs : List Reg} (hk : Keep rs s s')
    (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], r ∉ rs) : Env σ s' :=
  Env.low he (rs := []) (by simp) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2 fun r hr => hk.gpr (hrs r hr)

/-! ## The squeezes -/

/-- After `n` squeezes. -/
structure SqInv (σ : State) (n : Nat) (s : State) : Prop where
  env : Env σ s
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) fun k => iterF n (A0 (B σ k))
  buf : ∀ k < 4, ∀ p < 136 * n, s.mem (at' σ (oBuf + 680 * k + p)) = hByte (B σ k) p

theorem lanes_A0 {σ : State} {m : Mem} (h : SB σ m (PF σ)) : Lanes4 m (scr σ) fun k => iterF 0 (A0 (B σ k)) :=
  lanes4_of_bytes fun k hk q hq => by
    rw [h k hk q hq, show iterF 0 (A0 (B σ k)) = A0 (B σ k) from rfl, byteOf_A0 (B_length σ k) hq, PF]



theorem la_tbl (σ : State) (r k : Nat) : la (at' σ 1600) r k = la (scr σ) (50 + r) k := by
  rw [la, la, at', Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by omega_arith]

theorem args_ok {σ s : State} (he : Env σ s) :
    WP isa (.block permArgs) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = scr σ ∧ s'.gpr .rsi = at' σ 800 ∧
      s'.gpr .rdx = at' σ 1600 ∧ s'.gpr .rcx = at' σ 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  unfold permArgs
  xrun [he.rbx, sx800, sx1600, sx2368]

/-- The permutation's precondition, in the scratch space. -/
theorem pre4 {σ : State} (hp : Pre σ) {s : State} (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    (hrc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) :
    Pre4 s (scr σ) (at' σ 800) (at' σ 1600) :=
  ⟨fun i _ => in_scr hp hwr (a := 32 * i) (by omega_arith),
    fun i _ => by rw [at', Offset.add_add]; exact in_scr hp hwr (by omega_arith),
    fun r _ => by rw [at', Offset.add_add]; exact in_scr' hp hrd hwr (by omega_arith),
    Offset.base_disjoint _ (by omega_arith) (by omega_arith),
    Offset.base_disjoint _ (by omega_arith) (by omega_arith),
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith),
    fun r hr k hk => by rw [la_tbl]; exact hrc r hr k hk⟩

/-- A buffer byte, read through a frame of the states. -/
theorem buf_frame {σ : State} {m m' : Mem} {rs : List Region}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨at' σ oBuf, 2720⟩ r) (hf : Frame rs m m') {k p : Nat} (hk : k < 4)
    (hp' : p < 680) : m' (at' σ (oBuf + 680 * k + p)) = m (at' σ (oBuf + 680 * k + p)) := by
  have := hf.bytes (R := ⟨at' σ oBuf, 2720⟩) hd (by simp only; omega_arith) (i := 680 * k + p) (by simp only; omega_arith)
  simpa only [at', Offset.add_add, Nat.add_assoc] using this

/-- The permutation, after `n` squeezes. -/
theorem perm_ok {fast : Bool} {σ : State} (hp : Pre σ) {n : Nat} (hn : n < 5) {s : State} (h : SqInv σ n s)
    {rest : Prog isa} {Q : State → Prop} (kont : ∀ s', Env σ s' ∧
      (∀ r < 24, ∀ k < 4, s'.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) ∧
      Lanes4 s'.mem (scr σ) (fun k => iterF (n + 1) (A0 (B σ k))) ∧
      (∀ k < 4, ∀ p < 136 * n, s'.mem (at' σ (oBuf + 680 * k + p)) = hByte (B σ k) p) ∧
      s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 → WP isa rest s' Q) :
    WP isa (.seq (.block permArgs) (.seq (Impl.Sha3.X86_64.X4.permute4 fast) rest)) s Q := by
  refine WP.seq (WP.mono (args_ok h.env) fun s₁ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k₁⟩ => ?_)
  have hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  have hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (fast := fast) (A := fun k => iterF n (A0 (B σ k))) (pre4 hp hrd hwr (by rw [hm]; exact h.rc))
    hdi hsi hdx (by rw [hcx, at', at', Offset.add_add]) (by rw [hm]; exact h.lanes))
    fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  have hsub : ∀ r ∈ [(⟨scr σ, 800⟩ : Region), ⟨at' σ 800, 800⟩], Region.Sub r ⟨scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega_arith)
    · exact Offset.sub_base _ (by simp only [oSave]; omega_arith)
  refine ⟨Env.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_,
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide)], by rw [hg _ (by decide) (by decide), k₁.gpr (by decide)]⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega_arith) (by omega_arith),
          Offset.disjoint (scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega_arith) (by omega_arith)
            (by omega_arith)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · intro i hi k hk
    rw [hl i hi k hk]
    rfl
  · rw [buf_frame (by simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := oBuf) (n := 2720) (by simp only [oBuf]; omega_arith)
        (by simp only [oBuf]; omega_arith), Offset.disjoint (scr σ) (d := oBuf) (n := 2720) (e := 800) (k := 800)
          (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith) (by omega_arith)⟩) hf hk (by omega_arith), hm]
    exact h.buf k hk p hp'


/-! ## Copying the output -/

/-- During the copy of block `n`: the first `I` lanes of state `K` copied,
and all of the states before it. -/
structure EXI (σ : State) (n K I : Nat) (s : State) : Prop where
  env : Env σ s
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) (fun k => iterF (n + 1) (A0 (B σ k)))
  buf : ∀ k < 4, ∀ p < 680, (p < 136 * n ∨ (136 * n ≤ p ∧ p < 136 * n + 136 ∧ (k < K ∨ (k = K ∧ p < 136 * n + 8 * I)))) →
    s.mem (at' σ (oBuf + 680 * k + p)) = hByte (B σ k) p
  rbp : s.gpr .rbp = at' σ (oBuf + 136 * n)

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem ext_step {σ : State} (hp : Pre σ) {n K I : Nat} (hn : n < 5) (hK : K < 4) (hI : I < 17) {s : State}
    (h : EXI σ n K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))),
      .store (at_ .rbp (680 * K + 8 * I)) .rax]) s (EXI σ n K (I + 1)) := by
  refine wp_movm (a := at' σ (32 * I + 8 * K)) (by rw [ea_at, h.env.rbx])
    (in_scr' hp h.env.rd h.env.wr (by omega_arith)) fun s₁ u₁ => wp_store (a := at' σ (oBuf + 680 * K + 136 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.rbp, at', at', Offset.add_add,
        show oBuf + 136 * n + (680 * K + 8 * I) = oBuf + 680 * K + 136 * n + 8 * I by omega_arith])
      (by rw [u₁.wr]; exact in_scr hp h.env.wr (by simp only [oBuf]; omega_arith))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (oBuf + 680 * K + 136 * n + 8 * I)) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  have hf : Frame [⟨at' σ (oBuf + 680 * K + 136 * n + 8 * I), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨Env.low h.env (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by simp only [oBuf, oSave]; omega_arith)) hf (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by
        rw [g₂, u₁.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)],
    fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' hc => ?_, by rw [g₂, u₁.other _ (by decide), h.rbp]⟩
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * (50 + r) + 8 * k)
      (e := oBuf + 680 * K + 136 * n + 8 * I) (n := 8) (by omega_arith) (by simp only [oBuf]; omega_arith)
      (by simp only [oBuf]; omega_arith)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 680 * K + 136 * n + 8 * I) (n := 8) (by omega_arith) (by simp only [oBuf]; omega_arith)
      (by simp only [oBuf]; omega_arith)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 136 * n + 8 * I ≤ p ∧ p < 136 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega_arith) (by simp only [oBuf]; omega_arith) (by decide),
        show 8 * (oBuf + 680 * k + p - (oBuf + 680 * k + 136 * n + 8 * I)) = 8 * (p - 136 * n - 8 * I) by omega_arith,
        byte_readW _ _ (by omega_arith), at', Offset.add_add,
        show 32 * I + 8 * k + (p - 136 * n - 8 * I) = 32 * ((8 * I + (p - 136 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 136 * n - 8 * I)) % 8 by omega_arith,
        byte_of_lanes4 h.lanes hk (by omega_arith), ← hByte_A0 (B_length σ k) (by omega_arith),
        show 136 * n + (8 * I + (p - 136 * n - 8 * I)) = p by omega_arith]
    · rw [wb_out _ _ _ (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith)]
      exact h.buf k hk p hp' (by omega_arith)

theorem extract_eq : extract = (List.range 4).flatMap fun K => (List.range 17).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))), .store (at_ .rbp (680 * K + 8 * I)) .rax] := rfl

/-- Block `n` of each state's output. -/
theorem extract_ok {σ : State} (hp : Pre σ) {n : Nat} (hn : n < 5) {s : State} (h : EXI σ n 0 0 s) :
    WP isa (.block extract) s (SqInv σ (n + 1)) := by
  rw [extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => EXI σ n K 0 s) (fun K s hK h => ?_) 4 (Nat.le_refl _) s h)
    fun s' h' => ⟨h'.env, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega_arith) (by omega_arith)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => EXI σ n K I s) (fun I s hI h => ext_step hp hn hK hI h)
    17 (Nat.le_refl _) s h) fun s' h' =>
      ⟨h'.env, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega_arith), h'.rbp⟩

/-- `squeeze`, to block `n`: after `n + 1` squeezes, with `rbp` and `r10` kept. -/
theorem sq_ok {fast : Bool} {σ : State} (hp : Pre σ) {n : Nat} (hn : n < 5) {s : State} (h : SqInv σ n s)
    (hbp : s.gpr .rbp = at' σ (oBuf + 136 * n)) :
    WP isa (squeeze fast) s fun s' => SqInv σ (n + 1) s' ∧ s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 := by
  unfold squeeze
  exact perm_ok (fast := fast) hp hn h fun s' ⟨he, hrc, hl, hb, h₁, h₂⟩ =>
    WP.mono (WP.keep [.rax] (extract_ok hp hn ⟨he, hrc, hl, fun k hk p _ hc => hb k hk p (by omega_arith),
      by rw [h₁, hbp]⟩) (by decide)) fun s'' ⟨h', k⟩ =>
        ⟨h', by rw [k.gpr (by decide), h₁], by rw [k.gpr (by decide), h₂]⟩

/-- `SqInv` does not depend on `rbp`, `r10` or the flags. -/
theorem SqInv.frame {σ : State} {n : Nat} {s s' : State} (h : SqInv σ n s) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r, r ≠ .rbp → r ≠ .r10 → s'.gpr r = s.gpr r) :
    SqInv σ n s' := by
  have k : Keep [.rbp, .r10] s s' := ⟨fun r hr => hg r (fun e => hr (by simp [e])) (fun e => hr (by simp [e])), hrd, hwr⟩
  exact ⟨h.env.keep hm k (by decide), by rw [hm]; exact h.rc, by rw [hm]; exact h.lanes, by rw [hm]; exact h.buf⟩

/-- `squeezes`: the five squeezes. -/
theorem sqs_ok {fast : Bool} {σ : State} (hp : Pre σ) {s : State} (h : SqInv σ 0 s) : WP isa (squeezes fast) s (SqInv σ 5) := by
  unfold squeezes
  refine blocks_ok (b := 0) (n := 5) (by decide) (by decide) (by decide) (by decide) (fun _ _ _ h => h.frame)
    (fun i t _ hi hi' hbp => sq_ok (fast := fast) hp (by omega_arith) hi' ?_) h
  rw [hbp, h.env.rbx, Offset.add_add, at', Nat.sub_zero]

end VG.Proof.MlDsa.X86_64.Mask4
