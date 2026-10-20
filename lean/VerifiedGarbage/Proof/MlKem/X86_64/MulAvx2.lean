module

import VerifiedGarbage.Proof.MlKem.X86_64.Mul
public import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Impl.MlKem.X86_64.MulAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.VMul
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: products of NTTs with AVX2, the shared pieces

What the AVX2 products (`AccY.lean`) need of `Impl/MlKem/X86_64/MulAvx2.lean`:
in each lane, the SSE2 code's `deint` and `vbase` (`Mul.lean`) do what they
do on SSE2 registers (`lane_deintS0`, `lane_vbase`, with `ylanes`); the
loads of 32 coefficients (`yload4_ok`), the stores of 256 bits
(`coeffAt_write256`), and the order of the `γ`s in the table (`gIdxY_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The SSE2 code of each lane -/

theorem deintS_ok0 (s : State) :
    WP isa (.block (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5)) s fun s' =>
      (s'.xmm .xmm0 = deE (s.xmm .xmm0) (s.xmm .xmm1) (s.xmm .xmm2) (s.xmm .xmm3) ∧
        s'.xmm .xmm4 = deO (s.xmm .xmm0) (s.xmm .xmm1) (s.xmm .xmm2) (s.xmm .xmm3)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] s s' := by
  simp only [deintS]
  vrunm [eval_movdqa]
  exact ⟨⟨rfl, rfl⟩, by xonly⟩

theorem deintS_ok6 (s : State) :
    WP isa (.block (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11)) s fun s' =>
      (s'.xmm .xmm6 = deE (s.xmm .xmm6) (s.xmm .xmm7) (s.xmm .xmm8) (s.xmm .xmm9) ∧
        s'.xmm .xmm10 = deO (s.xmm .xmm6) (s.xmm .xmm7) (s.xmm .xmm8) (s.xmm .xmm9)) ∧
      XOnly [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  simp only [deintS]
  vrunm [eval_movdqa]
  exact ⟨⟨rfl, rfl⟩, by xonly⟩

theorem lane_deintS0 : laneSseBlock (toY (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5)) =
    some (deintS .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5) := by decide +kernel
theorem lane_deintS6 : laneSseBlock (toY (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11)) =
    some (deintS .xmm6 .xmm7 .xmm8 .xmm9 .xmm10 .xmm11) := by decide +kernel
theorem lane_vbase : laneSseBlock (toY vbase) = some vbase := by decide +kernel

/-! ## Loads and stores -/

/-- Four 256-bit loads. -/
theorem yload4_ok {p : Reg} {a b c d : XReg} (hd : [a, b, c, d].Nodup) {s : State}
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 0) 32)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 32) 32)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 64) 32)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 96) 32) :
    WP isa (.block (yload4 p a b c d)) s fun s' =>
      (∀ l < 2, s'.lane a l = s.mem.readW (s.gpr p + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane b l = s.mem.readW (s.gpr p + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane c l = s.mem.readW (s.gpr p + BitVec.ofNat 64 64 + BitVec.ofNat 64 (16 * l)) 128 ∧
        s'.lane d l = s.mem.readW (s.gpr p + BitVec.ofNat 64 96 + BitVec.ofNat 64 (16 * l)) 128) ∧
      YOnly [a, b, c, d] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hd
  obtain ⟨⟨ab, ac, ad⟩, ⟨bc, bd⟩, cd⟩ := hd
  simp only [yload4]
  rw [show ∀ x y z w : Instr, [x, y, z, w] = [x] ++ [y] ++ [z] ++ [w] from fun _ _ _ _ => rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yld_ok h0) fun s1 ⟨l1, o1⟩ => ?_
  have r1 : InRegions (s1.rd ++ s1.wr) (s1.gpr p + BitVec.ofNat 64 32) 32 := by
    rw [o1.rd, o1.wr, o1.gpr]; exact h1
  refine WP.mono (yld_ok r1) fun s2 ⟨l2, o2⟩ => ?_
  have r2 : InRegions (s2.rd ++ s2.wr) (s2.gpr p + BitVec.ofNat 64 64) 32 := by
    rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact h2
  refine WP.mono (yld_ok r2) fun s3 ⟨l3, o3⟩ => ?_
  have r3 : InRegions (s3.rd ++ s3.wr) (s3.gpr p + BitVec.ofNat 64 96) 32 := by
    rw [o3.rd, o3.wr, o3.gpr, o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact h3
  refine WP.mono (yld_ok r3) fun s4 ⟨l4, o4⟩ => ⟨fun l hl => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o4.lane _ (by simpa using ad) l hl, o3.lane _ (by simpa using ac) l hl,
      o2.lane _ (by simpa using ab) l hl, l1 l hl]
  · rw [o4.lane _ (by simpa using bd) l hl, o3.lane _ (by simpa using bc) l hl, l2 l hl,
      o1.gpr, o1.mem]
  · rw [o4.lane _ (by simpa using cd) l hl, l3 l hl, o2.gpr, o2.mem, o1.gpr, o1.mem]
  · rw [l4 l hl, o3.gpr, o3.mem, o2.gpr, o2.mem, o1.gpr, o1.mem]
  · exact ((o1.trans o2).trans (o3.trans o4)).mono (by simp)

theorem coeffAt_write256 (m : Mem) (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) (x : BitVec 256) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p j) x) p i =
      if j ≤ i ∧ i < j + 8 then x.extractLsb' (8 * (4 * (i - j))) (8 * 4) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_off, show j + (i - j) = i by bdd_omega]]
    exact readW_writeW_inside (k := 4 * (i - j)) (n := 4) _ _ _ (by bdd_omega) (by decide)
  · exact Mem.readW_writeW_sep (Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)) (by decide)

/-! ## The table -/

theorem gTabY_lt (p : Nat) : gTabY p < 65536 := gTab_lt _

/-- The pair of word `e` of lane `l` in iteration `i`. -/
abbrev pairY (i l e : Nat) : Nat := 16 * i + 4 * (e / 2) + e % 2 + 2 * l

theorem gIdxY_eq {i l e : Nat} (hl : l < 2) (he : e < 8) : gIdxY (16 * i + 8 * l + e) = pairY i l e := by
  unfold gIdxY pairY; omega

end VG.Proof.MlKem.X86_64
