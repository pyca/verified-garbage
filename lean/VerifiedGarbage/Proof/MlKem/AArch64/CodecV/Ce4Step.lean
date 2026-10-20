module

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeLoop
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM on AArch64: an iteration of `ce4Body`

Coefficients `32 k … 32 k + 31` to bytes `16 k … 16 k + 15` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A compressed coefficient, as the code computes it. -/
theorem C_cf {w : Width} (hw : WOk w) (s₀ : State) (i : Nat) :
    C w s₀ i = cf w ((P s₀)[i]!).val := hw.cmp _

/-- Byte `j` of the output for `d = 4`: two coefficients. -/
theorem L4 (s₀ : State) {g : Nat} (hg : g < 128) :
    L width4 s₀ g = BitVec.ofNat 8 (C width4 s₀ (2 * g) + C width4 s₀ (2 * g + 1) * 2 ^ 4) := by
  have := L_eq width4_ok s₀ (g := g) (j := 0) hg (by decide)
  rw [show width4.nb * g + 0 = g from by simp [width4]] at this
  rw [this]
  congr 1
  rw [show width4.c = 2 from rfl, acc_succ, acc_succ, acc, List.range_zero, List.map_nil, digits_nil]
  simp only [show width4.d = 4 from rfl, show width4.c = 2 from rfl, Nat.add_zero]
  omega

theorem step4 {s₀ : State} (hp : Pre width4 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : VInv width4 16 (fun _ => True) s₀ k s) :
    WP isa (.block ce4Body) s fun t =>
      VInv width4 16 (fun _ => True) s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have src := h.src hp
  have e0 : s.gpr .x0 = coeffAddr (fP s₀) (32 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[32 * k + i]!).val
  unfold ce4Body ld8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 32 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega)) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok (src.chg c1) .v4 .v5 .v6 .v7 (o := 64) (j := 32 * k + 16) (by decide)
    (by rw [c1.gpr, e0]; exact coeffAddr_off _ _ 16) (by omega))
    fun s2 ⟨c2, l4, l5, l6, l7⟩ => ?_
  rw [WP.block_append_iff]
  have cs2 : CConsts width4 s2 := (h.cs.chg c1).chg c2
  refine WP.mono (ce4Math_ok cs2 (X := X) (fun i _ => val_lt _)
    (Lanes.chg c2 (by decide) l0)
    ((Lanes.chg c2 (by decide) l1).congr fun e _ => by show _ = X (4 + e); congr 2; omega)
    ((Lanes.chg c2 (by decide) l2).congr fun e _ => by show _ = X (8 + e); congr 2; omega)
    ((Lanes.chg c2 (by decide) l3).congr fun e _ => by show _ = X (12 + e); congr 2; omega)
    (l4.congr fun e _ => by show _ = X (16 + e); congr 2; omega)
    (l5.congr fun e _ => by show _ = X (20 + e); congr 2; omega)
    (l6.congr fun e _ => by show _ = X (24 + e); congr 2; omega)
    (l7.congr fun e _ => by show _ = X (28 + e); congr 2; omega)) fun s3 ⟨c3, hb⟩ => ?_
  have g3 : s3.gpr = s.gpr := by rw [c3.gpr, c2.gpr, c1.gpr]
  have m3 : s3.mem = s.mem := by rw [c3.mem, c2.mem, c1.mem]
  have w3 : s3.wr = s.wr := by rw [c3.wr, c2.wr, c1.wr]
  refine wp_strq (a := oP s₀ + BitVec.ofNat 64 (16 * k)) (by decide) (by rw [g3, ptr_zero, h.x2]; rfl)
    (by rw [w3, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width4]; omega) (by decide)))
    fun s4 h4 => ?_
  have k4 : k < 256 / (width4.c * 16) := by simp [width4]; omega
  refine WP.mono (tail_ok (w := width4) (G := 16) (s₀ := s₀) k4 (by rw [h4.gpr, g3, h.x0])
    (by rw [h4.gpr, g3, h.x2]) (by rw [h4.gpr, g3, h.x11]) (by decide) (by decide)) fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  refine ⟨⟨by rw [o.rd, h4.rd, c3.rd, c2.rd, c1.rd, h.rd], by rw [o.wr, h4.wr, w3, h.wr],
    by rw [o.sp, h4.sp, c3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, trivial, ?_, ?_⟩,
    by rw [show 256 / (width4.c * 16) = 8 from rfl] at tc; exact tc⟩
  · have cs3 : CConsts width4 s3 := cs2.chg c3
    exact ⟨by rw [v, h4.v]; exact cs3.m, by rw [v, h4.v]; exact cs3.a, by rw [v, h4.v]; exact cs3.k⟩
  · rw [o.mem, h4.mem, m3, show width4.nb * 16 * (k + 1) = 16 * k + 16 by simp [width4]; omega]
    have out := h.out
    rw [show width4.nb * 16 * k = 16 * k by simp [width4]] at out
    refine bytes_write (n := 16) out
      (by decide) (by simp [width4]; omega) fun j hj => ?_
    change vbyte _ j = _
    rw [L4 s₀ (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [hb j hj, BitVec.toNat_ofNat, C_cf width4_ok, C_cf width4_ok,
      show 2 * (16 * k + j) = 32 * k + 2 * j by omega, show 32 * k + 2 * j + 1 = 32 * k + (2 * j + 1) by omega]
    have : cf width4 (X (2 * j)) < 2 ^ 4 := cf_lt width4 _
    have : cf width4 (X (2 * j + 1)) < 2 ^ 4 := cf_lt width4 _
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [o.mem, h4.mem, m3]
    exact h.frame.write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width4]; omega) (by decide))

end VG.Proof.MlKem.AArch64.CE
