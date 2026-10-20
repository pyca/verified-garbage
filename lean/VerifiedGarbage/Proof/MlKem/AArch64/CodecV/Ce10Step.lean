module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeLoop
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM on AArch64: an iteration of `ce10Body`

Coefficients `16 k … 16 k + 15` to bytes `20 k … 20 k + 19` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The constants of `ce10Body` besides those of `cmpV`. -/
abbrev K10 (s : State) : Prop := s.v .v20 = idxVec ce10Idx ∧ s.v .v21 = idxVec ce10IdxHi

/-- Byte `b` of group `g` of the output for `d = 10`. -/
theorem L10 (s₀ : State) {g b : Nat} (hg : g < 64) (hb : b < 5) :
    L width10 s₀ (5 * g + b) = BitVec.ofNat 8 (grp10 (C width10 s₀) g / 2 ^ (8 * b)) := by
  have := L_eq width10_ok s₀ (g := g) (j := b) hg hb
  rw [show width10.nb = 5 from rfl] at this
  rw [this]
  congr 2
  rw [show width10.c = 4 from rfl, acc_succ, acc_succ, acc_succ, acc_succ, acc, List.range_zero, List.map_nil,
    digits_nil]
  simp only [show width10.d = 10 from rfl, show width10.c = 4 from rfl, Nat.add_zero, grp10]
  omega

theorem step10 {s₀ : State} (hp : Pre width10 s₀) {k : Nat} (hk : k < 16) {s : State}
    (h : VInv width10 4 K10 s₀ k s) :
    WP isa (.block ce10Body) s fun t =>
      VInv width10 4 K10 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 16) := by
  have src := h.src hp
  have e0 : s.gpr .x0 = coeffAddr (fP s₀) (16 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[16 * k + i]!).val
  unfold ce10Body
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 16 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega)) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  have cs1 : CConsts width10 s1 := h.cs.chg c1
  refine WP.mono (ce10Math_ok cs1 (by rw [c1.get .v20 (by decide)]; exact h.K.1)
    (by rw [c1.get .v21 (by decide)]; exact h.K.2) (X := X) (fun i _ => val_lt _) l0
    (l1.congr fun e _ => by show _ = X (4 + e); congr 2; omega)
    (l2.congr fun e _ => by show _ = X (8 + e); congr 2; omega)
    (l3.congr fun e _ => by show _ = X (12 + e); congr 2; omega)) fun s2 ⟨c2, b6, b7⟩ => ?_
  have g2 : s2.gpr = s.gpr := by rw [c2.gpr, c1.gpr]
  have m2 : s2.mem = s.mem := by rw [c2.mem, c1.mem]
  have w2 : s2.wr = s.wr := by rw [c2.wr, c1.wr]
  refine wp_strq (a := oP s₀ + BitVec.ofNat 64 (20 * k)) (by decide) (by rw [g2, ptr_zero, h.x2]; rfl)
    (by rw [w2, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width10]; omega) (by decide)))
    fun s3 h3 => ?_
  refine wp_umov_w0 fun s4 o4 v4 x9 => ?_
  refine wp_strw' (a := oP s₀ + BitVec.ofNat 64 (20 * k + 16)) (by decide)
    (by rw [o4.get .x2, h3.gpr, g2, h.x2, ptr_add]; rfl)
    (by rw [o4.wr, h3.wr, w2, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width10]; omega) (by decide)))
    fun s5 h5 v5 => ?_
  have k4 : k < 256 / (width10.c * 4) := by simp [width10]; omega
  have gs : ∀ r, r ≠ .x9 → s5.gpr r = s.gpr r := fun r hr => by
    rw [h5.gpr, o4.gpr r (by simpa using hr), h3.gpr, g2]
  refine WP.mono (tail_ok (w := width10) (G := 4) (s₀ := s₀) k4 (by rw [gs .x0 (by decide), h.x0])
    (by rw [gs .x2 (by decide), h.x2]) (by rw [gs .x11 (by decide), h.x11]) (by decide) (by decide))
    fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  have hv : t.v = s2.v := by rw [v, v5, v4, h3.v]
  refine ⟨⟨by rw [o.rd, h5.rd, o4.rd, h3.rd, c2.rd, c1.rd, h.rd], by rw [o.wr, h5.wr, o4.wr, h3.wr, w2, h.wr],
    by rw [o.sp, h5.sp, o4.sp, h3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, ?_, ?_, ?_⟩,
    by rw [show 256 / (width10.c * 4) = 16 from rfl] at tc; exact tc⟩
  · have cs2 : CConsts width10 s2 := cs1.chg c2
    exact ⟨by rw [hv]; exact cs2.m, by rw [hv]; exact cs2.a, by rw [hv]; exact cs2.k⟩
  · exact ⟨by rw [hv, c2.get .v20 (by decide), c1.get .v20 (by decide)]; exact h.K.1,
      by rw [hv, c2.get .v21 (by decide), c1.get .v21 (by decide)]; exact h.K.2⟩
  · have out := h.out
    rw [show width10.nb * 4 * k = 20 * k by simp [width10]] at out
    have out1 := bytes_write (n := 16) out (by decide) (by simp [width10]; omega) (x := s2.v .v6)
      fun j hj => by
        change vbyte _ j = _
        rw [show 20 * k + j = 5 * (4 * k + j / 5) + j % 5 by omega, L10 s₀ (by omega) (by omega)]
        apply BitVec.eq_of_toNat_eq
        rw [b6 j hj, BitVec.toNat_ofNat]
        simp only [grp10, C_cf width10_ok]
        rw [show 4 * (4 * k + j / 5) = 16 * k + 4 * (j / 5) by omega]
        simp only [show ∀ e, 16 * k + 4 * (j / 5) + e = 16 * k + (4 * (j / 5) + e) from fun e => by omega]
        rfl
    rw [o.mem, h5.mem, o4.mem, h3.mem, m2, show width10.nb * 4 * (k + 1) = 20 * k + 16 + 4 by
      simp [width10]; omega]
    refine bytes_write (n := 4) out1 (by decide) (by simp [width10]; omega) fun j hj => ?_
    rw [x9, h3.v]
    have e : BitVec.extractLsb' (8 * j) 8 (((((s2.v .v7).extractLsb' 0 32).setWidth 64).setWidth 32).setWidth
        (8 * (32 / 8))) = vbyte (s2.v .v7) j := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [vbyte, hi, show 8 * j + i < 32 by omega]
    rw [e, show 20 * k + 16 + j = 5 * (4 * k + 3) + (1 + j) by omega, L10 s₀ (by omega) (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [b7 j hj, BitVec.toNat_ofNat]
    simp only [grp10, C_cf width10_ok]
    rw [show 4 * (4 * k + 3) = 16 * k + 12 by omega]
  · rw [o.mem, h5.mem, o4.mem, h3.mem, m2]
    exact (h.frame.write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width10]; omega) (by decide))).write (n := 32 / 8) (List.mem_singleton_self _) _
      (contains_off (by simp [width10]; omega) (by decide))

end VG.Proof.MlKem.AArch64.CE
