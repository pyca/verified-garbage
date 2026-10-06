import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareGroupedValue

namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare (DiagInv)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem group_ok {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h8 : s₀.gpr .r8 = off B A) (h9 : s₀.gpr .r9 = off B eb)
    (h10 : s₀.gpr .r10 = BitVec.ofNat 64 w) (hw : w < 2 ^ 60) (hi : i+4 ≤ w)
    (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb)
    (hI : DiagInv s₀ B Z A eb i t) (hc : (t.gpr .r15).toNat ≤ 2) :
    WP isa AdxSquareGrouped.group t fun t' =>
      t'.zf = some (decide (i+4 = w)) ∧ DiagInv s₀ B Z A eb (i+4) t' ∧
        (t'.gpr .r15).toNat ≤ 2 := by
  have v0 : ValueInv s₀ B A eb i (t.gpr .r15).toNat t := ⟨hI.out,hI.val⟩
  have l0 : Keep stepRegs t t := Keep.refl _ _
  have g0 := hI.keep
  simp only [AdxSquareGrouped.group, seqs]
  refine WP.seq (WP.mono (initialStep_ok (k := 0) (hI.scr.congr l0.2.2)
    ((g0.gpr (by decide)).trans h8) ((g0.gpr (by decide)).trans h9)
    ((l0.gpr (by decide)).trans hI.rbp) ((l0.gpr (by decide)).trans hI.r14)
    (by omega) (by omega) hc) fun s1 ⟨cf1, of1, c1, o1, z1, e1, out1, k1⟩ => ?_)
  have l1 : Keep stepRegs t s1 := (l0.trans k1).mono (by simp)
  have g1 := hI.keep.trans l1
  have v1 : ValueInv s₀ B A eb (i+1) (cf1.toNat + of1.toNat) s1 := by
    have e : wv s1.mem B (A+16*(i+0)) 2 + 2^128*(cf1.toNat+of1.toNat) =
        2*wv t.mem B (A+16*(i+0)) 2 +
          (word t.mem B (eb+8*(i+0))).toNat * (word t.mem B (eb+8*(i+0))).toNat +
          (t.gpr .r15).toNat := by omega
    simpa only [Nat.add_zero, Nat.add_assoc] using
      value_step (hI.scr.congr l0.2.2) (by omega : i+0<w) hA hb sep (by simpa using v0) e out1
  refine WP.seq (WP.mono (nextStep_ok (k := 1) (hI.scr.congr l1.2.2)
    ((g1.gpr (by decide)).trans h8) ((g1.gpr (by decide)).trans h9)
    ((l1.gpr (by decide)).trans hI.rbp) ((l1.gpr (by decide)).trans hI.r14)
    (by omega) (by omega) c1 o1 z1) fun s2 ⟨cf2, of2, c2, o2, z2, e2, out2, k2⟩ => ?_)
  have l2 : Keep stepRegs t s2 := (l1.trans k2).mono (by simp)
  have g2 := hI.keep.trans l2
  have v2 : ValueInv s₀ B A eb (i+2) (cf2.toNat + of2.toNat) s2 := by
    have e : wv s2.mem B (A+16*(i+1)) 2 + 2^128*(cf2.toNat+of2.toNat) =
        2*wv s1.mem B (A+16*(i+1)) 2 +
          (word s1.mem B (eb+8*(i+1))).toNat * (word s1.mem B (eb+8*(i+1))).toNat +
          (cf1.toNat+of1.toNat) := by omega
    simpa only [Nat.add_zero, Nat.add_assoc] using
      value_step (hI.scr.congr l1.2.2) (by omega : i+1<w) hA hb sep (by simpa using v1) e out2
  refine WP.seq (WP.mono (nextStep_ok (k := 2) (hI.scr.congr l2.2.2)
    ((g2.gpr (by decide)).trans h8) ((g2.gpr (by decide)).trans h9)
    ((l2.gpr (by decide)).trans hI.rbp) ((l2.gpr (by decide)).trans hI.r14)
    (by omega) (by omega) c2 o2 z2) fun s3 ⟨cf3, of3, c3, o3, z3, e3, out3, k3⟩ => ?_)
  have l3 : Keep stepRegs t s3 := (l2.trans k3).mono (by simp)
  have g3 := hI.keep.trans l3
  have v3 : ValueInv s₀ B A eb (i+3) (cf3.toNat + of3.toNat) s3 := by
    have e : wv s3.mem B (A+16*(i+2)) 2 + 2^128*(cf3.toNat+of3.toNat) =
        2*wv s2.mem B (A+16*(i+2)) 2 +
          (word s2.mem B (eb+8*(i+2))).toNat * (word s2.mem B (eb+8*(i+2))).toNat +
          (cf2.toNat+of2.toNat) := by omega
    simpa only [Nat.add_zero, Nat.add_assoc] using
      value_step (hI.scr.congr l2.2.2) (by omega : i+2<w) hA hb sep (by simpa using v2) e out3
  refine WP.seq (WP.mono (nextStep_ok (k := 3) (hI.scr.congr l3.2.2)
    ((g3.gpr (by decide)).trans h8) ((g3.gpr (by decide)).trans h9)
    ((l3.gpr (by decide)).trans hI.rbp) ((l3.gpr (by decide)).trans hI.r14)
    (by omega) (by omega) c3 o3 z3) fun s4 ⟨cf4, of4, c4, o4, z4, e4, out4, k4⟩ => ?_)
  have l4 : Keep stepRegs t s4 := (l3.trans k4).mono (by simp)
  have g4 := hI.keep.trans l4
  have v4 : ValueInv s₀ B A eb (i+4) (cf4.toNat + of4.toNat) s4 := by
    have e : wv s4.mem B (A+16*(i+3)) 2 + 2^128*(cf4.toNat+of4.toNat) =
        2*wv s3.mem B (A+16*(i+3)) 2 +
          (word s3.mem B (eb+8*(i+3))).toNat * (word s3.mem B (eb+8*(i+3))).toNat +
          (cf3.toNat+of3.toNat) := by omega
    simpa only [Nat.add_zero, Nat.add_assoc] using
      value_step (hI.scr.congr l3.2.2) (by omega : i+3<w) hA hb sep (by simpa using v3) e out4
  rw [WP.block_append_iff]
  refine WP.mono (close_ok s4 z4 c4 o4) fun s5 ⟨e5, bound5, k5⟩ => ?_
  have l5 := l4.trans k5.keep
  have g5 := hI.keep.trans l5
  have hbp5 : s5.gpr .rbp = BitVec.ofNat 64 i := (l5.gpr (by decide)).trans hI.rbp
  have h145 : s5.gpr .r14 = BitVec.ofNat 64 (2*i) := (l5.gpr (by decide)).trans hI.r14
  have h105 : s5.gpr .r10 = BitVec.ofNat 64 w := (g5.gpr (by decide)).trans h10
  have count : BitVec.ofNat 64 (2*i) + 8 = BitVec.ofNat 64 (2*(i+4)) := by
    rw [show 2*(i+4) = 2*i+8 by omega, BitVec.ofNat_add]; rfl
  have finish : WP isa (.block [.alu .add .rbp (.imm 4), .alu .add .r14 (.imm 8), .alu .cmp .rbp (.reg .r10)]) s5 fun u =>
      u.gpr .rbp = BitVec.ofNat 64 (i+4) ∧ u.gpr .r14 = BitVec.ofNat 64 (2*(i+4)) ∧
      u.zf = some (decide (i+4=w)) ∧ u.mem = s5.mem ∧ Keep [.rbp,.r14] s5 u := by
    refine WP.mono (WP.keep [.rbp,.r14] (Q := fun u =>
      u.gpr .rbp = BitVec.ofNat 64 (i+4) ∧ u.gpr .r14 = BitVec.ofNat 64 (2*(i+4)) ∧
      u.zf = some (decide (i+4=w)) ∧ u.mem = s5.mem) ?_ rfl)
      fun u ⟨h,k⟩ => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,k⟩
    xrun [hbp5,h145,h105,ofNat_add_four,count,
      ofNat_sub_beq (show i+4 < 2^64 by omega) (show w < 2^64 by omega)]
  refine WP.mono finish fun u ⟨bp, r14, hz, hm, ku⟩ => ?_
  have gu := g5.trans ku
  have h15 : u.gpr .r15 = s5.gpr .r15 := ku.gpr (by decide)
  refine ⟨hz, ⟨hI.scr.congr (l5.trans ku).2.2, gu.mono (by simp [stepRegs]), bp, r14, ?_, ?_⟩, ?_⟩
  · rw [hm,k5.2.1]; exact v4.out
  · rw [hm,k5.2.1,h15,e5]; exact v4.val
  · rw [h15]; exact bound5

end VG.Proof.Bignum.X86_64.AdxSquareGrouped
