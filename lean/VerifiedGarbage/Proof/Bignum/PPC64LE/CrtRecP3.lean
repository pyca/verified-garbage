module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: `h`

`recP3_ok`: in `p`'s working space, `a qInv mod p` into array 4, for `a` in
array 3, `R² mod p` in array 7 and `qInv` from `X`'s array 7, by two
Montgomery multiplications.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- Two Montgomery multiplications, the second by `R² mod P`: the product. -/
theorem mont_chain {P R a q x5 x4 : Nat} (hR : Nat.Coprime R P) (h5 : x5 * R % P = a * q % P)
    (h4 : x4 * R % P = x5 * (R * R % P) % P) (h4P : x4 < P) : x4 = a * q % P := by
  have e : x4 * R % P = a * q * R % P := by
    rw [h4, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, h5, Nat.mod_mul_mod]
  rw [← Nat.mod_eq_of_lt h4P]
  exact VG.Proof.Bignum.mont_cancel hR e

/-- `recombineP`'s end, in `p`'s working space `off BX oA` (`-p⁻¹ mod 2³²` in
`r12`): `qInv` (`w_P` words of `X`'s array 7) into array 6, then
`a qInv R⁻¹ mod p` into array 5 and `a qInv mod p` into array 4. -/
theorem recP3_ok {s : State} {BX : Addr} {Z oA wP wX Pv a QI : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem (off BX oA) (slot wP 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hPodd : Pv % 2 = 1)
    (ha : val32 s.mem (off BX oA) (slot wP 3) (2 * wP) = a)
    (hRR : val32 s.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv)
    (hQ : wv s.mem BX (slot wX 7) wP = QI) (hQP : QI < Pv) :
    WP isa (.seq (.block (PublicChecked.base .r14 6 ++ xb .r15 7)) (.seq copyN
      (.seq (PublicChecked.montOp 5 3 6) (PublicChecked.montOp 4 5 7)))) s fun t =>
      (val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = a * QI % Pv ∧
        Outside BX oA (slot wP 24) s.mem t.mem) ∧ Keep (.r14 :: .r15 :: Pub.montRegs) s t := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wP 0; have eA2 := e wP 2; have eA3 := e wP 3; have eA4 := e wP 4; have eA5 := e wP 5
  have eA6 := e wP 6; have eA7 := e wP 7; have eA8 := e wP 24
  have sX7 := slot_le (w := wX) (show 7 < 8 by decide)
  have hsA := hs.sub hA
  have hnA := hsA.nowrap
  have hA' : oA + slot wP 24 ≤ 2 ^ 64 := by omega_arith
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 6) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) 7) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (b := oA + slot wP 6) (hs.congr k12.wr) a15
    (by rw [k2.gpr _ (by decide), a14, off_off]) ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw'
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  have o3 : Mont.Outside (off BX oA) (slot wP 6) (8 * wP) s.mem s₃.mem :=
    fun x hx => out_super out3 (by omega_arith) x hx
  have v6 : val32 s₃.mem (off BX oA) (slot wP 6) (2 * wP) = QI := by
    rw [Pre.val32_eq_wv, wv_off, ← hQ]; exact wv_congr2 fun i hi => hw3 i hi
  have v0 : val32 s₃.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [o3.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  have v3 : val32 s₃.mem (off BX oA) (slot wP 3) (2 * wP) = a := by
    rw [o3.val32 (Or.inl (by omega_arith)) (by omega_arith), ha]
  have v7 : val32 s₃.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv := by
    rw [o3.val32 (Or.inr (by omega_arith)) (by omega_arith), hRR]
  have w0 : w32 s₃.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) :=
    o3.w32 (Or.inl (by omega_arith)) (by omega_arith)
  have g12 : s₃.gpr .r12 = s.gpr .r12 := k13.gpr _ (by decide)
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 5) (a := 3) (b := 6) (hsA.congr k13.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by unfold slot; omega_arith)
    ((k13.gpr _ (by decide)).trans h10) ((k13.gpr _ (by decide)).trans h29)
    ((k13.gpr _ (by decide)).trans h11) (by rw [g12]; exact h12) (by rw [g12, w0]; exact hinv)
    (by rw [v6, v0]; exact hQP)) fun s₄ ⟨⟨l5, e5, o4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  rw [v0, v3, v6] at e5
  rw [v0] at l5
  have hpr : ∀ j, j ≠ 2 → j ≠ 3 → j ≠ 5 → j < 8 →
      ∀ r ∈ [(slot wP 2, 8 * (wP + 2)), (slot wP 3, 8 * (wP + 2)), (slot wP 5, 8 * (wP + 2))],
        slot wP j + 4 * (2 * wP) ≤ r.1 ∨ r.1 + r.2 ≤ slot wP j := by
    intro j h2 h3 h5 h8 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have s2 := slot_sep (w := wP) h2; have s3 := slot_sep (w := wP) h3; have s5 := slot_sep (w := wP) h5
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  have v0' : val32 s₄.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [o4.val32 (hpr 0 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), v0]
  have v7' : val32 s₄.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv := by
    rw [o4.val32 (hpr 7 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), v7]
  have w0' : w32 s₄.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) := by
    rw [← w0]
    refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => o4 _ fun r hr => ?_)
    have := hpr 0 (by decide) (by decide) (by decide) (by decide) r hr
    rw [Mont.ofs_off (off BX oA) (d := slot wP 0) (i := i) (by omega_arith)]; omega_arith
  have g12' : s₄.gpr .r12 = s.gpr .r12 := k14.gpr _ (by decide)
  refine WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 7) (hsA.congr k14.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by unfold slot; omega_arith)
    ((k14.gpr _ (by decide)).trans h10) ((k14.gpr _ (by decide)).trans h29)
    ((k14.gpr _ (by decide)).trans h11) (by rw [g12']; exact h12) (by rw [g12', w0']; exact hinv)
    (by rw [v7', v0']; exact Nat.mod_lt _ (by omega_arith))) fun t ⟨⟨l4, e4, o5⟩, k5⟩ => ⟨⟨?_, ?_⟩, (k14.trans k5).mono⟩
  · rw [v0', v7'] at e4
    rw [v0'] at l4
    exact mont_chain (VG.Proof.Bignum.coprime_pow2 hPodd _) e5 e4 l4
  · have f4 := outs_sub o4 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) hA' (by omega_arith)
    have f5 := outs_sub o5 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) hA' (by omega_arith)
    exact ((out3.mono (by omega_arith) (by omega_arith)).trans f4).trans f5

end VG.Proof.Bignum.PPC64LE.Crt
