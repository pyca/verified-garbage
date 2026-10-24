module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.X448.PPC64LE.Cswap
import VerifiedGarbage.Proof.Ed448.Binary
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed448 on PPC64LE: one bit of the reduction modulo `L`

`scalarBit o j` takes bit `j` of the byte in `r16` into the remainder at `o`:
from `r < L` there, it leaves `(2 r + bit) mod L` (`scalarBit_ok`). The
remainder is doubled with the bit as the carry in; `o + (2⁴⁴⁸ - 1 - L) + 1`
goes to `SD`, whose carry out is 1 exactly when the doubled remainder is at
least `L`; and that carry selects `SD` into `o`.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Impl.X448.PPC64LE (pass cswap)
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.Ed448 (L)

theorem SD_eq : SD = 56 := rfl

theorem L_lt : L < 2 ^ 224 * 2 ^ 222 := by decide +kernel

theorem scalarComplement_lt (k : Nat) : scalarComplement k < 2 ^ 32 := by
  unfold scalarComplement; omega

/-- The complement's words are those of `2⁴⁴⁸ - 1 - L`. -/
theorem val32_complement : val32 scalarComplement 14 = 2 ^ 224 * 2 ^ 224 - 1 - L := by decide +kernel

/-- `rlwinm d, n, 0, 0, 31`: the low word of `n`. -/
theorem wp_rotr0 {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat % 2 ^ 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rotr .w d n 0 :: is)) s Q := by
  have e : (((s.gpr n).setWidth 32).rotateRight 0).setWidth 64 = BitVec.ofNat 64 ((s.gpr n).toNat % 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    have r0 : ∀ v : BitVec 32, v.rotateRight 0 = v := fun v => by
      simp [BitVec.rotateRight, BitVec.rotateRightAux]
    simp only [r0, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact WP.cons (exec_rotr_w (by decide)) (by rw [e]; exact k _ (Upd.write _ _ _))

/-- `lis` of the high half of a word and `ori` of its low half: the word in
the low 32 bits. -/
theorem lis_ori_word (w : Nat) :
    (((BitVec.ofNat 16 (w / 2 ^ 16) ++ (0 : BitVec 16)).signExtend 64 |||
      (BitVec.ofNat 16 w).setWidth 64)).toNat % 2 ^ 32 = w % 2 ^ 32 := by
  have h := lis_ori (BitVec.ofNat 32 w)
  have e1 : (BitVec.ofNat 32 w).extractLsb' 16 16 = BitVec.ofNat 16 (w / 2 ^ 16) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show (2 : Nat) ^ 32 = 2 ^ 16 * 2 ^ 16 from rfl, Nat.mod_mul_right_div_self, Nat.mod_mod]
  have e2 : (BitVec.ofNat 32 w).extractLsb' 0 16 = BitVec.ofNat 16 w := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    exact Nat.mod_mod_of_dvd _ (by decide)
  rw [e1, e2] at h
  rw [← toNat_lo32, h, BitVec.toNat_ofNat]

/-- Bit `j` of a byte, as `lsl` and `lsr` take it. -/
theorem bit_of_byte : ∀ w < 256, ∀ j < 8, w * 2 ^ (63 - j) % 2 ^ 64 / 2 ^ 63 = w / 2 ^ j % 2 := by
  decide +kernel

/-- A remainder's place: within the first 4096 bytes and apart from `SD`. -/
structure Rem (o : Nat) : Prop where
  fits : o + 56 ≤ 4096
  sep : o + 56 ≤ SD ∨ SD + 56 ≤ o

section
variable {b : Addr}

/-- The pass over the remainder at `o` doubling it, with `r8`'s bit as the carry in. -/
theorem double_ok {o : Nat} (ho : Rem o) {s : State} (hc : Ctx b s) {β : Nat} (hβ : β < 2)
    (h8 : (s.gpr .r8).toNat = β) (hr : V s.mem b o < L) :
    WP isa (.block (pass .r6 o (scalarDoubleSrc o))) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem t.mem ∧
      V t.mem b o = 2 * V s.mem b o + β := by
  have hf := ho.fits
  have hl : ∀ k < 14, limb s.mem b o k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  refine WP.mono (pass_ok (s0 := s) (c := fun k => 2 * limb s.mem b o k) (cin := β) (by decide) (by decide)
    (by omega) (fun k hk => by rw [hc.r6]; exact hc.inW (by omega)) h8
    (fun k hk => by have := hl k hk; omega) (by omega) ?_) fun t hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc.of_rest hp.rest (by decide)
    simp only [scalarDoubleSrc]
    refine lw0_ok hc' (d := o + 4 * k) (by omega) fun t1 v1 => wp_add fun t2 v2 => WP.block_nil ⟨?_, ?_, ?_⟩
    · have ex : wd s'.mem b (o + 4 * k) = limb s.mem b o k := by
        rw [wd_pass hc hp.frame (by omega) (by omega) (by omega)]; rfl
      have := hl k hk
      rw [v2.gpr, v1.gpr]
      unfold wd at ex
      rw [toNat_add_lt (by rw [toNat_ext32, ex]; omega), toNat_ext32, ex]; omega
    · exact (v1.rest (by decide)).trans (v2.rest (by decide))
    · rw [v2.mem, v1.mem]
  · refine ⟨hp.rest, by have := hp.frame; rwa [hc.r6] at this, ?_⟩
    have hpo : ∀ j < 14, limb t.mem b o j = out (fun k => 2 * limb s.mem b o k) β j := fun j hj => by
      have := hp.outs j hj; rwa [hc.r6] at this
    have hv := chain_val (fun k => 2 * limb s.mem b o k) β 14
    rw [pow448] at hv
    have hd : val32 (fun k => 2 * limb s.mem b o k) 14 = 2 * V s.mem b o := by
      rw [show (fun k => 2 * limb s.mem b o k) = fun k => limb s.mem b o k + limb s.mem b o k from
        funext fun k => by omega, val32_add]; unfold V; omega
    have := L_lt
    rw [V, val32_congr hpo]
    rw [hd] at hv
    have hlt := val32_lt (f := out (fun k => 2 * limb s.mem b o k) β) (n := 14) fun k _ => out_lt _ _ _
    rw [pow448] at hlt
    unfold V at hv hr ⊢
    omega

/-- The pass from the remainder at `o` to `SD` adding the complement of `L`
and 1: its carry out says whether the remainder is at least `L`. -/
theorem subtract_ok {o : Nat} (ho : Rem o) {s : State} (hc : Ctx b s) (h8 : s.gpr .r8 = 1) :
    WP isa (.block (pass .r6 SD (scalarSubtractSrc o))) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ Frame [⟨b + BitVec.ofNat 64 SD, 56⟩] s.mem t.mem ∧
      (∀ k < 14, limb t.mem b o k = limb s.mem b o k) ∧
      (t.gpr .r8).toNat = (if L ≤ V s.mem b o then 1 else 0) ∧
      (L ≤ V s.mem b o → V t.mem b SD = V s.mem b o - L) := by
  have hf := ho.fits
  have hs := ho.sep
  have hD := SD_eq
  have hl : ∀ k < 14, limb s.mem b o k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  let c : Nat → Nat := fun k => limb s.mem b o k + scalarComplement k
  refine WP.mono (pass_ok (s0 := s) (c := c) (cin := 1) (by decide) (by decide)
    (by omega) (fun k hk => by rw [hc.r6]; exact hc.inW (by omega)) (by rw [h8]; rfl)
    (fun k hk => by have := hl k hk; have := scalarComplement_lt k; simp only [c]; omega) (by decide) ?_)
    fun t hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc.of_rest hp.rest (by decide)
    simp only [scalarSubtractSrc]
    refine lw0_ok hc' (d := o + 4 * k) (by omega) fun t1 v1 => wp_lis fun t2 v2 => wp_ori fun t3 v3 => ?_
    refine wp_rotr0 fun t4 v4 => wp_add fun t5 v5 => WP.block_nil ⟨?_, ?_, ?_⟩
    · have ex : wd s'.mem b (o + 4 * k) = limb s.mem b o k := by
        rw [wd_pass hc hp.frame (by omega) (by omega) (by omega)]; rfl
      have e5 : (t4.gpr .r5).toNat = scalarComplement k := by
        rw [v4.gpr, v3.gpr, v2.gpr, lis_ori_word, Nat.mod_eq_of_lt (scalarComplement_lt k)]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := scalarComplement_lt k; omega)]
      have e7 : (t4.gpr .r7).toNat = limb s.mem b o k := by
        rw [v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.gpr, toNat_ext32]
        exact ex
      have := hl k hk; have := scalarComplement_lt k
      rw [v5.gpr, toNat_add_lt (by rw [e7, e5]; omega), e7, e5]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        ((v4.rest (by decide)).trans (v5.rest (by decide)))))
    · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  · have hfr : Frame [⟨b + BitVec.ofNat 64 SD, 56⟩] s.mem t.mem := by have := hp.frame; rwa [hc.r6] at this
    have hpo : ∀ j < 14, limb t.mem b SD j = out c 1 j := fun j hj => by
      have := hp.outs j hj; rwa [hc.r6] at this
    have hv := chain_val c 1 14
    rw [pow448] at hv
    have hlt := val32_lt (f := out c 1) (n := 14) fun k _ => out_lt _ _ _
    rw [pow448] at hlt
    have hcv : val32 c 14 = V s.mem b o + (2 ^ 224 * 2 ^ 224 - 1 - L) := by
      simp only [c]; rw [val32_add, val32_complement]; rfl
    have hVlt := V_lt s.mem b o
    have := L_lt
    rw [hcv] at hv
    have hch : chain c 1 14 = if L ≤ V s.mem b o then 1 else 0 := by
      split <;> omega
    refine ⟨hp.rest, hfr, fun k hk => ?_, by rw [hp.r8, hch], fun hge => ?_⟩
    · refine wd_frame hfr fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · rw [V, val32_congr hpo]
      rw [hch, ite_eq_left_iff.mpr (fun h => absurd hge h)] at hv
      omega

/-- **One bit**: bit `j` of the byte in `r16` into the remainder at `o`. -/
theorem scalarBit_ok {o : Nat} (ho : Rem o) {s : State} (hc : Ctx b s) {w j : Nat} (hw : w < 256)
    (hj : j < 8) (h16 : (s.gpr .r16).toNat = w) (hr : V s.mem b o < L) :
    WP isa (.block (scalarBit o j)) s fun t =>
      Rest [.r5, .r7, .r8, .r11] s t ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 SD, 56⟩] s.mem t.mem ∧
      V t.mem b o = (2 * V s.mem b o + w / 2 ^ j % 2) % L := by
  have hf := ho.fits
  have hs := ho.sep
  have hD := SD_eq
  unfold scalarBit
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_lsl (by omega) fun s1 u1 => wp_lsr (by decide) fun s2 u2 => ?_
  have e8 : (s2.gpr .r8).toNat = w / 2 ^ j % 2 := by
    rw [u2.gpr, toNat_shr, u1.gpr, toNat_shl, h16, bit_of_byte w hw j hj]
  have hr2 : Rest [.r8] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine WP.append (double_ok ho hc2 (Nat.mod_lt _ (by decide)) e8 (by rw [hm2]; exact hr))
    fun s3 ⟨hr3, hf3, hv3⟩ => ?_
  rw [hm2] at hv3 hf3
  have hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine wp_li (by decide) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r8]) (by decide)) (by decide)
  obtain ⟨u, hu⟩ : ∃ u, u = 2 * V s.mem b o + w / 2 ^ j % 2 := ⟨_, rfl⟩
  have hV3 : V s3.mem b o = u := by rw [hv3, hu]
  have hul : u < 2 * L := by have := Nat.mod_lt (w / 2 ^ j) (show 0 < 2 by decide); omega
  refine WP.append (subtract_ok ho hc4 (by rw [u4.gpr]; rfl)) fun s5 ⟨hr5, hf5, hsr5, hc5, hd5⟩ => ?_
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
  · have f1 : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 SD, 56⟩] s.mem s3.mem :=
      hf3.mono fun r hr => by simp [List.mem_singleton.mp hr]
    have f2 : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 SD, 56⟩] s3.mem s5.mem :=
      hf5.mono fun r hr => by simp [List.mem_singleton.mp hr]
    have f3 := ht.frame
    rw [hm7] at f3
    exact f1.trans (f2.trans f3)
  · have hl : ∀ k < 14, limb t.mem b o k = sel sw (limb s5.mem b o k) (limb s5.mem b SD k) := fun k hk => by
      rw [ht.lx k hk, hm7]
    rw [V, val32_congr hl, Proof.Ed448.reduce_bit (r := V s.mem b o) hr (Nat.mod_lt _ (by decide)), ← hu]
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

end VG.Proof.Ed448.PPC64LE
