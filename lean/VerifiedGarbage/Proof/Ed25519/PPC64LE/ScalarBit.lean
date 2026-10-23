module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub
import VerifiedGarbage.Proof.Ed25519.PPC64LE.MulFn
import VerifiedGarbage.Proof.X25519.PPC64LE.Cswap
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Word
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 on PPC64LE: one bit of the reduction modulo `L`

`scalarBit j` takes bit `j` of the byte in `r16` into the remainder at `SR`:
from `r < L` there, it leaves `(2 r + bit) mod L` (`scalarBit_ok`). The
remainder is doubled with the bit as the carry in; `SR + (2^256 - 1 - L) + 1`
goes to `SD`, whose carry out is 1 exactly when the doubled remainder is at
least `L`; and that carry selects `SD` into `SR`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (L)

theorem SR_eq : SR = 160 := rfl
theorem SD_eq : SD = 192 := rfl

theorem L_lt : L < 2 ^ 253 := by decide

theorem scalarComplement_lt (k : Nat) : scalarComplement k < 2 ^ 32 := by
  unfold scalarComplement; omega

/-- The complement's words are those of `2^256 - 1 - L`. -/
theorem val32_complement : val32 scalarComplement 8 = 2 ^ 256 - 1 - L := by decide

/-- A pass's output, as a number: below `2^256`, and with the carry out it is the sum. -/
theorem pass_value {c : Nat → Nat} {cin : Nat} :
    val32 (out c cin) 8 + 2 ^ 256 * chain c cin 8 = val32 c 8 + cin ∧ val32 (out c cin) 8 < 2 ^ 256 :=
  ⟨chain_val c cin 8, val32_lt fun k _ => Nat.mod_lt _ (by decide)⟩

/-- Bit `j` of a byte, as `lsl` and `lsr` take it. -/
theorem bit_of_byte : ∀ w < 256, ∀ j < 8, w * 2 ^ (63 - j) % 2 ^ 64 / 2 ^ 63 = w / 2 ^ j % 2 := by
  decide +kernel

section
variable {b : Addr}

/-- The pass from `SR` to `SR` doubling it, with `r8`'s bit as the carry in. -/
theorem double_ok {s : State} (hc : Ctx b s) {β : Nat} (hβ : β < 2) (h8 : (s.gpr .r8).toNat = β)
    (hr : V s.mem b SR < L) :
    WP isa (.block (pass .r6 SR scalarDoubleSrc)) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ Frame [⟨b + BitVec.ofNat 64 SR, 32⟩] s.mem t.mem ∧
      V t.mem b SR = 2 * V s.mem b SR + β := by
  have hS := SR_eq
  have hl : ∀ k < 8, limb s.mem b SR k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  refine WP.mono (pass_ok (s0 := s) (c := fun k => 2 * limb s.mem b SR k) (cin := β) (by decide) (by decide)
    (by omega) (fun k hk => by rw [hc.r6]; exact hc.inW (by omega)) h8
    (fun k hk => by have := hl k hk; omega) (by omega) ?_) fun t hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc.of_rest hp.rest (by decide)
    simp only [scalarDoubleSrc]
    refine lw0_ok hc' (d := SR + 4 * k) (by omega) fun t1 v1 => wp_add fun t2 v2 => WP.block_nil ⟨?_, ?_, ?_⟩
    · have ex : wd s'.mem b (SR + 4 * k) = limb s.mem b SR k := by
        rw [wd_pass hc hp.frame (by omega) (by omega) (by omega)]; rfl
      have := hl k hk
      rw [v2.gpr, v1.gpr]
      unfold wd at ex
      rw [toNat_add_lt (by rw [toNat_ext32, ex]; omega), toNat_ext32, ex]; omega
    · exact (v1.rest (by decide)).trans (v2.rest (by decide))
    · rw [v2.mem, v1.mem]
  · refine ⟨hp.rest, by have := hp.frame; rwa [hc.r6] at this, ?_⟩
    have hpo : ∀ j < 8, limb t.mem b SR j = out (fun k => 2 * limb s.mem b SR k) β j := fun j hj => by
      have := hp.outs j hj; rwa [hc.r6] at this
    obtain ⟨hv, hlt⟩ := pass_value (c := fun k => 2 * limb s.mem b SR k) (cin := β)
    have hd : val32 (fun k => 2 * limb s.mem b SR k) 8 = 2 * V s.mem b SR := by
      rw [show (fun k => 2 * limb s.mem b SR k) = fun k => limb s.mem b SR k + limb s.mem b SR k from
        funext fun k => by omega, val32_add]; unfold V; omega
    have := L_lt
    rw [V, val32_congr hpo]
    have hch : chain (fun k => 2 * limb s.mem b SR k) β 8 = 0 := by
      rcases Nat.eq_zero_or_pos (chain (fun k => 2 * limb s.mem b SR k) β 8) with h | h
      · exact h
      · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h; omega
    rw [hch, Nat.mul_zero, Nat.add_zero, hd] at hv
    exact hv

/-- The pass from `SR` to `SD` adding the complement of `L` and 1: its carry out says whether
`SR ≥ L`. -/
theorem subtract_ok {s : State} (hc : Ctx b s) (h8 : s.gpr .r8 = 1) :
    WP isa (.block (pass .r6 SD scalarSubtractSrc)) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ Frame [⟨b + BitVec.ofNat 64 SD, 32⟩] s.mem t.mem ∧
      (∀ k < 8, limb t.mem b SR k = limb s.mem b SR k) ∧
      (t.gpr .r8).toNat = (if L ≤ V s.mem b SR then 1 else 0) ∧
      (L ≤ V s.mem b SR → V t.mem b SD = V s.mem b SR - L) := by
  have hS := SR_eq
  have hD := SD_eq
  have hl : ∀ k < 8, limb s.mem b SR k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  let c : Nat → Nat := fun k => limb s.mem b SR k + scalarComplement k
  refine WP.mono (pass_ok (s0 := s) (c := c) (cin := 1) (by decide) (by decide)
    (by omega) (fun k hk => by rw [hc.r6]; exact hc.inW (by omega)) (by rw [h8]; rfl)
    (fun k hk => by have := hl k hk; have := scalarComplement_lt k; simp only [c]; omega) (by decide) ?_)
    fun t hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc.of_rest hp.rest (by decide)
    simp only [scalarSubtractSrc]
    refine lw0_ok hc' (d := SR + 4 * k) (by omega) fun t1 v1 => wp_lis fun t2 v2 => wp_ori fun t3 v3 => ?_
    refine wp_rotr0 fun t4 v4 => wp_add fun t5 v5 => WP.block_nil ⟨?_, ?_, ?_⟩
    · have ex : wd s'.mem b (SR + 4 * k) = limb s.mem b SR k := by
        rw [wd_pass hc hp.frame (by omega) (by omega) (by omega)]; rfl
      have e5 : (t4.gpr .r5).toNat = scalarComplement k := by
        rw [v4.gpr, v3.gpr, v2.gpr, lis_ori_word, Nat.mod_eq_of_lt (scalarComplement_lt k)]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := scalarComplement_lt k; omega)]
      have e7 : (t4.gpr .r7).toNat = limb s.mem b SR k := by
        rw [v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.gpr, toNat_ext32]
        exact ex
      have := hl k hk; have := scalarComplement_lt k
      rw [v5.gpr, toNat_add_lt (by rw [e7, e5]; omega), e7, e5]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        ((v4.rest (by decide)).trans (v5.rest (by decide)))))
    · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  · have hf : Frame [⟨b + BitVec.ofNat 64 SD, 32⟩] s.mem t.mem := by have := hp.frame; rwa [hc.r6] at this
    have hpo : ∀ j < 8, limb t.mem b SD j = out c 1 j := fun j hj => by
      have := hp.outs j hj; rwa [hc.r6] at this
    obtain ⟨hv, hlt⟩ := pass_value (c := c) (cin := 1)
    have hcv : val32 c 8 = V s.mem b SR + (2 ^ 256 - 1 - L) := by
      simp only [c]; rw [val32_add, val32_complement]; rfl
    have hVlt := V_lt s.mem b SR
    have := L_lt
    rw [hcv] at hv
    have hch : chain c 1 8 = if L ≤ V s.mem b SR then 1 else 0 := by
      split
      · have : chain c 1 8 ≤ 1 := by
          rcases Nat.lt_or_ge (chain c 1 8) 2 with h | h
          · omega
          · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h; omega
        rcases Nat.eq_zero_or_pos (chain c 1 8) with h | h
        · rw [h] at hv; omega
        · omega
      · rcases Nat.eq_zero_or_pos (chain c 1 8) with h | h
        · exact h
        · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h; omega
    refine ⟨hp.rest, hf, fun k hk => ?_, by rw [hp.r8, hch], fun hge => ?_⟩
    · refine wd_frame hf fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · rw [V, val32_congr hpo]
      rw [hch, ite_eq_left_iff.mpr (fun h => absurd hge h)] at hv
      omega

/-- **One bit**: bit `j` of the byte in `r16` into the remainder at `SR`. -/
theorem scalarBit_ok {s : State} (hc : Ctx b s) {w j : Nat} (hw : w < 256) (hj : j < 8)
    (h16 : (s.gpr .r16).toNat = w) (hr : V s.mem b SR < L) :
    WP isa (.block (scalarBit j)) s fun t =>
      Rest [.r5, .r7, .r8, .r11] s t ∧
      Frame [⟨b + BitVec.ofNat 64 SR, 32⟩, ⟨b + BitVec.ofNat 64 SD, 32⟩] s.mem t.mem ∧
      V t.mem b SR = (2 * V s.mem b SR + w / 2 ^ j % 2) % L := by
  have hS := SR_eq
  have hD := SD_eq
  unfold scalarBit
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_lsl (by omega) fun s1 u1 => wp_lsr (by decide) fun s2 u2 => ?_
  have e8 : (s2.gpr .r8).toNat = w / 2 ^ j % 2 := by
    rw [u2.gpr, toNat_shr, u1.gpr, toNat_shl, h16, bit_of_byte w hw j hj]
  have hr2 : Rest [.r8] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine WP.append (double_ok hc2 (Nat.mod_lt _ (by decide)) e8 (by rw [hm2]; exact hr))
    fun s3 ⟨hr3, hf3, hv3⟩ => ?_
  rw [hm2] at hv3 hf3
  have hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine wp_li (by decide) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r8]) (by decide)) (by decide)
  obtain ⟨u, hu⟩ : ∃ u, u = 2 * V s.mem b SR + w / 2 ^ j % 2 := ⟨_, rfl⟩
  have hV3 : V s3.mem b SR = u := by rw [hv3, hu]
  have hul : u < 2 * L := by have := Nat.mod_lt (w / 2 ^ j) (show 0 < 2 by decide); omega
  refine WP.append (subtract_ok hc4 (by rw [u4.gpr]; rfl)) fun s5 ⟨hr5, hf5, hsr5, hc5, hd5⟩ => ?_
  rw [u4.mem, hV3] at hc5 hd5
  rw [u4.mem] at hsr5 hf5
  have hc5' : Ctx b s5 := hc4.of_rest hr5 (by decide)
  refine wp_li (by decide) fun s6 u6 => wp_sub fun s7 u7 => ?_
  obtain ⟨sw, hsw'⟩ : ∃ sw, sw = if L ≤ u then 1 else 0 := ⟨_, rfl⟩
  have hsw : sw ≤ 1 := by rw [hsw']; split <;> decide
  have h11 : s7.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
    rw [u7.gpr, u6.gpr, u6.other _ (by decide)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [hc5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hsw']
  have hr7 : Rest [.r11] s5 s7 := (u6.rest (by decide)).trans (u7.rest (by decide))
  have hc7 : Ctx b s7 := hc5'.of_rest hr7 (by decide)
  have hm7 : s7.mem = s5.mem := by rw [u7.mem, u6.mem]
  refine WP.mono (cswap_ok (by omega) (by omega) (by omega) hc7 hsw h11) fun t ht => ⟨?_, ?_, ?_⟩
  · exact (hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (((u4.rest (by decide))).trans
      ((hr5.mono (by decide)).trans ((hr7.mono (by decide)).trans (ht.rest.mono (by decide))))))
  · have f1 : Frame [⟨b + BitVec.ofNat 64 SR, 32⟩, ⟨b + BitVec.ofNat 64 SD, 32⟩] s.mem s3.mem :=
      hf3.mono fun r hr => by simp [List.mem_singleton.mp hr]
    have f2 : Frame [⟨b + BitVec.ofNat 64 SR, 32⟩, ⟨b + BitVec.ofNat 64 SD, 32⟩] s3.mem s5.mem :=
      hf5.mono fun r hr => by simp [List.mem_singleton.mp hr]
    have f3 := ht.frame
    rw [hm7] at f3
    exact f1.trans (f2.trans f3)
  · have hl : ∀ k < 8, limb t.mem b SR k = sel sw (limb s5.mem b SR k) (limb s5.mem b SD k) := fun k hk => by
      rw [ht.lx k hk, hm7]
    rw [V, val32_congr hl, Proof.Ed25519.reduce_bit (r := V s.mem b SR) hr (Nat.mod_lt _ (by decide)), ← hu]
    by_cases hge : L ≤ u
    · have e1 : sw = 1 := by rw [hsw']; simp [hge]
      have e2 : ¬ u < L := by omega
      simp only [sel, e1, ite_true, e2, ite_false]
      rw [← hd5 hge]; rfl
    · have e1 : sw = 0 := by rw [hsw']; simp [hge]
      have e2 : u < L := by omega
      simp only [sel, e1, e2, ite_true]
      rw [← hV3]
      exact val32_congr fun k hk => by simp only [show (0 : Nat) ≠ 1 by decide, ite_false]; exact hsr5 k hk

end

end VG.Proof.Ed25519.PPC64LE
