module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Ce5
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM-1024 on AArch64: an iteration of `ce5Body`

Coefficients `32 k … 32 k + 31` to bytes `20 k … 20 k + 19` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.CE VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Byte `b` of group `g` of the output for `d = 5`. -/
theorem L5 (s₀ : State) {g b : Nat} (hg : g < 32) (hb : b < 5) :
    L width5 s₀ (5 * g + b) = BitVec.ofNat 8 (grp5 (C width5 s₀) g / 2 ^ (8 * b)) := by
  have := L_eq width5_ok s₀ (g := g) (j := b) hg hb
  rw [show width5.nb = 5 from rfl] at this
  rw [this]
  refine congrArg (fun x => BitVec.ofNat 8 (x / 2 ^ (8 * b))) ?_
  rw [show width5.c = 8 from rfl, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ,
    acc_succ, acc, List.range_zero, List.map_nil, digits_nil]
  simp only [show width5.d = 5 from rfl, show width5.c = 8 from rfl, Nat.add_zero, grp5, w5, z5,
    Nat.reduceMul, Nat.reducePow]
  rw [show 2 * (2 * (2 * g) + 1) + 1 = 8 * g + 3 by omega, show 2 * (2 * (2 * g) + 1) = 8 * g + 2 by omega,
    show 2 * (2 * (2 * g + 1)) + 1 = 8 * g + 5 by omega, show 2 * (2 * (2 * g + 1)) = 8 * g + 4 by omega,
    show 2 * (2 * (2 * g + 1) + 1) + 1 = 8 * g + 7 by omega,
    show 2 * (2 * (2 * g + 1) + 1) = 8 * g + 6 by omega, show 2 * (2 * (2 * g)) + 1 = 8 * g + 1 by omega,
    show 2 * (2 * (2 * g)) = 8 * g by omega]
  omega

/-- The groups of coefficients from `32 k` are the groups from `4 k`. -/
theorem grp5_shift (F : Nat → Nat) (k l : Nat) : grp5 (fun i => F (32 * k + i)) l = grp5 F (4 * k + l) := by
  simp only [grp5, w5, z5]
  rw [show 32 * k + 2 * (2 * (2 * l)) = 2 * (2 * (2 * (4 * k + l))) by omega,
    show 32 * k + (2 * (2 * (2 * l)) + 1) = 2 * (2 * (2 * (4 * k + l))) + 1 by omega,
    show 32 * k + 2 * (2 * (2 * l) + 1) = 2 * (2 * (2 * (4 * k + l)) + 1) by omega,
    show 32 * k + (2 * (2 * (2 * l) + 1) + 1) = 2 * (2 * (2 * (4 * k + l)) + 1) + 1 by omega,
    show 32 * k + 2 * (2 * (2 * l + 1)) = 2 * (2 * (2 * (4 * k + l) + 1)) by omega,
    show 32 * k + (2 * (2 * (2 * l + 1)) + 1) = 2 * (2 * (2 * (4 * k + l) + 1)) + 1 by omega,
    show 32 * k + 2 * (2 * (2 * l + 1) + 1) = 2 * (2 * (2 * (4 * k + l) + 1) + 1) by omega,
    show 32 * k + (2 * (2 * (2 * l + 1) + 1) + 1) = 2 * (2 * (2 * (4 * k + l) + 1) + 1) + 1 by omega]

theorem step5 {s₀ : State} (hp : Pre width5 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : VInv width5 4 K10 s₀ k s) :
    WP isa (.block ce5Body) s fun t =>
      VInv width5 4 K10 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have src := h.src hp
  have e0 : s.gpr .x0 = coeffAddr (fP s₀) (32 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[32 * k + i]!).val
  unfold ce5Body ld8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 32 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega)) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok (src.chg c1) .v4 .v5 .v6 .v7 (o := 64) (j := 32 * k + 16) (by decide)
    (by rw [c1.gpr, e0]; exact coeffAddr_off _ _ 16) (by omega))
    fun s2 ⟨c2, l4, l5, l6, l7⟩ => ?_
  rw [WP.block_append_iff]
  have cs2 : CConsts width5 s2 := (h.cs.chg c1).chg c2
  refine WP.mono (ce5Math_ok cs2 (by rw [c2.get .v20, c1.get .v20]; exact h.K.1)
    (by rw [c2.get .v21, c1.get .v21]; exact h.K.2) (X := X) (fun i _ => val_lt _)
    (Lanes.chg c2 (by decide) l0)
    ((Lanes.chg c2 (by decide) l1).congr fun e _ => by show _ = X (4 + e); congr 2; omega)
    ((Lanes.chg c2 (by decide) l2).congr fun e _ => by show _ = X (8 + e); congr 2; omega)
    ((Lanes.chg c2 (by decide) l3).congr fun e _ => by show _ = X (12 + e); congr 2; omega)
    (l4.congr fun e _ => by show _ = X (16 + e); congr 2; omega)
    (l5.congr fun e _ => by show _ = X (20 + e); congr 2; omega)
    (l6.congr fun e _ => by show _ = X (24 + e); congr 2; omega)
    (l7.congr fun e _ => by show _ = X (28 + e); congr 2; omega)) fun s3 ⟨c3, b6, b7⟩ => ?_
  have g3 : s3.gpr = s.gpr := by rw [c3.gpr, c2.gpr, c1.gpr]
  have m3 : s3.mem = s.mem := by rw [c3.mem, c2.mem, c1.mem]
  have w3 : s3.wr = s.wr := by rw [c3.wr, c2.wr, c1.wr]
  refine wp_strq (a := oP s₀ + BitVec.ofNat 64 (20 * k)) (by decide) (by rw [g3, ptr_zero, h.x2]; rfl)
    (by rw [w3, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width5]; omega) (by decide)))
    fun s4 h4 => ?_
  refine wp_umov_w0 fun s5 o5 v5 x9 => ?_
  refine wp_strw' (a := oP s₀ + BitVec.ofNat 64 (20 * k + 16)) (by decide)
    (by rw [o5.get .x2, h4.gpr, g3, h.x2, ptr_add]; rfl)
    (by rw [o5.wr, h4.wr, w3, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width5]; omega) (by decide)))
    fun s6 h6 v6 => ?_
  have k4 : k < 256 / (width5.c * 4) := by simp [width5]; omega
  have gs : ∀ r, r ≠ .x9 → s6.gpr r = s.gpr r := fun r hr => by
    rw [h6.gpr, o5.gpr r (by simpa using hr), h4.gpr, g3]
  refine WP.mono (tail_ok (w := width5) (G := 4) (s₀ := s₀) k4 (by rw [gs .x0 (by decide), h.x0])
    (by rw [gs .x2 (by decide), h.x2]) (by rw [gs .x11 (by decide), h.x11]) (by decide) (by decide))
    fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  have hv : t.v = s3.v := by rw [v, v6, v5, h4.v]
  refine ⟨⟨by rw [o.rd, h6.rd, o5.rd, h4.rd, c3.rd, c2.rd, c1.rd, h.rd], by rw [o.wr, h6.wr, o5.wr, h4.wr, w3, h.wr],
    by rw [o.sp, h6.sp, o5.sp, h4.sp, c3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, ?_, ?_, ?_⟩,
    by rw [show 256 / (width5.c * 4) = 8 from rfl] at tc; exact tc⟩
  · have cs3 : CConsts width5 s3 := cs2.chg c3
    exact ⟨by rw [hv]; exact cs3.m, by rw [hv]; exact cs3.a, by rw [hv]; exact cs3.k⟩
  · exact ⟨by rw [hv, c3.get .v20, c2.get .v20, c1.get .v20]; exact h.K.1,
      by rw [hv, c3.get .v21, c2.get .v21, c1.get .v21]; exact h.K.2⟩
  · have out := h.out
    rw [show width5.nb * 4 * k = 20 * k by simp [width5]] at out
    have hC : C width5 s₀ = fun i => cf width5 ((P s₀)[i]!).val := funext (C_cf width5_ok s₀)
    have sh : ∀ l, grp5 (fun i => cf width5 (X i)) l = grp5 (C width5 s₀) (4 * k + l) := fun l => by
      rw [hC]; exact grp5_shift (fun i => cf width5 ((P s₀)[i]!).val) k l
    have out1 := bytes_write (n := 16) out (by decide) (by simp [width5]; omega) (x := s3.v .v6)
      fun j hj => by
        change vbyte _ j = _
        rw [show 20 * k + j = 5 * (4 * k + j / 5) + j % 5 by omega, L5 s₀ (by omega) (by omega)]
        apply BitVec.eq_of_toNat_eq
        rw [b6 j hj, BitVec.toNat_ofNat, sh]
    rw [o.mem, h6.mem, o5.mem, h4.mem, m3, show width5.nb * 4 * (k + 1) = 20 * k + 16 + 4 by
      simp [width5]; omega]
    refine bytes_write (n := 4) out1 (by decide) (by simp [width5]; omega) fun j hj => ?_
    rw [x9, h4.v]
    have e : BitVec.extractLsb' (8 * j) 8 (((((s3.v .v7).extractLsb' 0 32).setWidth 64).setWidth 32).setWidth
        (8 * (32 / 8))) = vbyte (s3.v .v7) j := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [vbyte, hi, show 8 * j + i < 32 by omega]
    rw [e, show 20 * k + 16 + j = 5 * (4 * k + 3) + (1 + j) by omega, L5 s₀ (by omega) (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [b7 j hj, BitVec.toNat_ofNat, sh]
  · rw [o.mem, h6.mem, o5.mem, h4.mem, m3]
    exact (h.frame.write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width5]; omega) (by decide))).write (n := 32 / 8) (List.mem_singleton_self _) _
      (contains_off (by simp [width5]; omega) (by decide))

end VG.Proof.MlKem1024.AArch64.CE
