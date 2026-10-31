module

public import VerifiedGarbage.Impl.Mont.ArmPacked
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Mont.Arm.PackedShift
import VerifiedGarbage.Proof.Mont.Arm.PackedRow
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! One packed Montgomery round in the curve workspace. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont
open VG.Impl.Mont.Arm.Packed VG.Proof.Bignum.Arm
open VG.Proof.Weierstrass.Arm (wp_movt movImm_val)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_movw wp_mul wp_dp wp_subs op2_reg op2_imm dpVal)

abbrev roundClob : List Reg := [.r0, .r1, .r2, .r3, .r5, .r6, .r7, .r8, .r9]

 theorem round_ok (u : Bool) {s : State} {base : Addr} {size acc a b i n m : Nat} {M : Mod}
    (hs : Scr s base size) (hMn : 2 * M.n = n)
    (pa : s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * i))
    (pb : s.gpr .r4 = s.gpr .r12 + BitVec.ofNat 32 b)
    (fa : a + 4 * (i + 1) ≤ size) (fb : b + 4 * n ≤ size)
    (fm : M.mo + 4 * n ≤ size) (ft : acc + 4 * (n + 2) ≤ size)
    (sb : acc + 4 * (n + 2) ≤ b ∨ b + 4 * n ≤ acc)
    (sm : acc + 4 * (n + 2) ≤ M.mo ∨ M.mo + 4 * n ≤ acc)
    (modulus : val32 s.mem base M.mo n = m)
    (inverse : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (operand : val32 s.mem base b n < m) (bound : val32 s.mem base acc (n + 2) < 2 * m)
    :
    WP isa (.block (round M acc u)) s fun t =>
      (∃ q < 2 ^ 32, 2 ^ 32 * val32 t.mem base acc (n + 2) =
        val32 s.mem base acc (n + 2) + w32 s.mem base (a + 4 * i) * val32 s.mem base b n + q * m) ∧
      val32 t.mem base acc (n + 2) < 2 * m ∧
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClob s t ∧
      t.gpr .r1 = s.gpr .r1 + 4 ∧ t.gpr .r9 = s.gpr .r9 - 1 ∧ t.z = (s.gpr .r9 - 1 == 0) := by
  have hn := hs.nowrap
  have mlt : m < 2 ^ (32 * n) := by rw [← modulus]; exact val32_lt _ _ _ _
  simp only [round, hMn, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using hs.ea_off (d := 0) pa (by omega))
    (hs.read (d := a + 4 * i) (by omega)) fun s1 u1 => ?_
  let x := s.mem.readW (off base (a + 4 * i)) 32
  have scalar : s1.gpr .r2 = x := u1.gpr
  have k1 : Rest rowClob s s1 := u1.rest (by simp)
  have h1 := hs.of_rest k1 (by decide)
  have pb1 : s1.gpr .r4 = s1.gpr .r12 + BitVec.ofNat 32 b := by rw [u1.other _ (by decide), u1.other _ (by decide)]; exact pb
  have fits1 : val32 s1.mem base acc (n + 2) + (s1.gpr .r2).toNat * val32 s1.mem base b n < 2 ^ (32 * (n + 2)) := by
    rw [u1.mem, scalar]
    have f := round_fit bound x.isLt operand (by decide : 0 < 2 ^ 32) mlt
    simpa only [Nat.zero_mul, Nat.add_zero] using f
  refine VG.Proof.X25519.Arm.WP.append (rowWith_ok u h1 pb1 (Nat.add_zero _) (by decide) ft fb sb fits1)
    fun s2 ⟨v2, o2, k2⟩ => ?_
  have k12 : Rest rowClob s s2 := k1.trans (k2.mono (by simp))
  have h2 := hs.of_rest k12 (by decide)
  have v2' : val32 s2.mem base acc (n + 2) = val32 s.mem base acc (n + 2) + x.toNat * val32 s.mem base b n := by
    rw [v2, u1.mem, scalar]
  have mo2 : val32 s2.mem base M.mo n = m := by rw [o2.val32 (by omega) (by omega), u1.mem]; exact modulus
  refine wp_ldr (h2.off_lt (by omega)) (h2.ea (by omega)) (h2.read (by omega)) fun s3 u3 => ?_
  refine wp_movw fun s4 u4 => wp_movt fun s5 u5 => wp_mul fun s6 u6 => ?_
  have k6 : Rest rowClob s s6 := k12.trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp)))))
  have h6 := hs.of_rest k6 (by decide)
  have mem6 : s6.mem = s2.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem]
  have inv7 : s5.gpr .r7 = BitVec.ofNat 32 M.minv.toNat := by rw [u5.gpr, u4.gpr, movImm_val]
  have coeff : (s6.gpr .r2).toNat = val32 s2.mem base acc (n + 2) * (BitVec.ofNat 32 M.minv.toNat).toNat % 2 ^ 32 := by
    rw [u6.gpr, inv7, u5.other _ (by decide), u4.other _ (by decide), u3.gpr, BitVec.mul_comm]
    exact coefficient_value _ _ _ _ (n + 1)
  have fits2 : val32 s6.mem base acc (n + 2) + (s6.gpr .r2).toNat * val32 s6.mem base M.mo n < 2 ^ (32 * (n + 2)) := by
    rw [mem6, mo2, v2']
    exact round_fit bound x.isLt operand (s6.gpr .r2).isLt mlt
  refine VG.Proof.X25519.Arm.WP.append (rowWith_ok u h6 (K := 0) (by simp) (Nat.zero_add _) (by decide) ft fm sm fits2)
    fun s7 ⟨v7, o7, k7⟩ => ?_
  have sum : val32 s7.mem base acc (n + 2) = val32 s2.mem base acc (n + 2) + (s6.gpr .r2).toNat * m := by
    rw [v7, mem6, mo2]
  have cancel : val32 s7.mem base acc (n + 2) % 2 ^ 32 = 0 :=
    round_cancel (inverse32 inverse) coeff sum
  have k : Rest rowClob s s7 := k6.trans (k7.mono (by simp))
  refine VG.Proof.X25519.Arm.WP.append (shift_ok (hs.of_rest k (by decide)) ft) fun s8 ⟨o8, v8, k8⟩ => ?_
  have k' : Rest rowClob s s8 := k.trans (k8.mono (by simp))
  refine wp_dp (op2_imm (by decide)) fun s9 u9 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u10 z10 => WP.block_nil ?_
  have mem : t.mem = s8.mem := by rw [u10.mem, u9.mem]
  have exactValue : 2 ^ 32 * val32 t.mem base acc (n + 2) = val32 s.mem base acc (n + 2) +
      x.toNat * val32 s.mem base b n + (s6.gpr .r2).toNat * m := by
    rw [mem, v8, round_div_exact cancel, sum, v2']
  refine ⟨⟨(s6.gpr .r2).toNat, (s6.gpr .r2).isLt, exactValue⟩,
    round_lt exactValue bound x.isLt operand (s6.gpr .r2).isLt, ?_,
    (k'.mono (by simp)).trans ((u9.rest (by simp)).trans (u10.rest (by simp))), ?_, ?_, ?_⟩
  · rw [mem, u1.mem] at *
    exact o2.trans (by rw [mem6] at o7; exact o7.trans o8)
  · rw [u10.other _ (by decide), u9.gpr, dpVal, k'.gpr .r1 (by decide)]
  · rw [u10.gpr, u9.other _ (by decide), k'.gpr .r9 (by decide)]
  · rw [z10, u9.other _ (by decide), k'.gpr .r9 (by decide)]

end VG.Proof.Mont.Arm.Packed
