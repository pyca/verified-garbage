import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
import VerifiedGarbage.Proof.Framework.Omega

/-! Doubling the cross products and adding the diagonal of an ADX square. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

/-- The two-word doubling and diagonal addition, with the carry out. -/
theorem diagonalCore_ok (s : State) :
    WP isa (.block AdxSquare.diagonalCore) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
        2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
          (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + (s.gpr .r15).toNat ∧
      Keeps [.rsi, .rbx, .rax, .rcx, .r11, .r12] s t := by
  rw [show AdxSquare.diagonalCore = (([.alu32 .xor .rsi (.reg .rsi)] : List Instr) ++ (([.mov32 .rbx (.imm 0)] : List Instr) ++ (([.mulx .rax .rcx (.reg .rdx)] : List Instr) ++ (([.adcx .r11 (.reg .r11)] : List Instr) ++ (([.adox .r11 (.reg .rcx)] : List Instr) ++ (([.adcx .r12 (.reg .r12)] : List Instr) ++ (([.adox .r12 (.reg .rax)] : List Instr) ++ (([.adcx .rbx (.reg .rsi)] : List Instr) ++ (([.adox .rbx (.reg .rsi)] : List Instr) ++ (([.adcx .r11 (.reg .r15)] : List Instr) ++ (([.adcx .r12 (.reg .rsi)] : List Instr) ++ (([.adcx .rbx (.reg .rsi)] : List Instr))))))))))))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (xorRsi_ok s) fun s1 ⟨z1, c1, o1, k1⟩ => ?_
  have K1 := k1
  have v1_rsi : s1.gpr .rsi = 0 := z1
  have v1_r11 : s1.gpr .r11 = s.gpr .r11 := k1.gpr (by decide)
  have v1_r12 : s1.gpr .r12 = s.gpr .r12 := k1.gpr (by decide)
  have v1_rdx : s1.gpr .rdx = s.gpr .rdx := k1.gpr (by decide)
  have v1_r15 : s1.gpr .r15 = s.gpr .r15 := k1.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movZero_ok s1 .rbx) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  have cf2 := c2.trans c1
  have of2 := o2.trans o1
  have K2 := K1.trans k2
  have v2_rsi : s2.gpr .rsi = 0 := (k2.gpr (by decide)).trans v1_rsi
  have v2_rbx : s2.gpr .rbx = 0 := z2
  have v2_r11 : s2.gpr .r11 = s.gpr .r11 := (k2.gpr (by decide)).trans v1_r11
  have v2_r12 : s2.gpr .r12 = s.gpr .r12 := (k2.gpr (by decide)).trans v1_r12
  have v2_rdx : s2.gpr .rdx = s.gpr .rdx := (k2.gpr (by decide)).trans v1_rdx
  have v2_r15 : s2.gpr .r15 = s.gpr .r15 := (k2.gpr (by decide)).trans v1_r15
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s2 (hi := .rax) (lo := .rcx) (src := .reg .rdx) rfl
    (fun _ h => nomatch h) (by decide)) fun s3 ⟨e3, c3, o3, k3⟩ => ?_
  have cf3 := c3.trans cf2
  have of3 := o3.trans of2
  simp only [v2_rdx] at e3
  have K3 := K2.trans k3
  have v3_rsi : s3.gpr .rsi = 0 := (k3.gpr (by decide)).trans v2_rsi
  have v3_rbx : s3.gpr .rbx = 0 := (k3.gpr (by decide)).trans v2_rbx
  have v3_r11 : s3.gpr .r11 = s.gpr .r11 := (k3.gpr (by decide)).trans v2_r11
  have v3_r12 : s3.gpr .r12 = s.gpr .r12 := (k3.gpr (by decide)).trans v2_r12
  have v3_r15 : s3.gpr .r15 = s.gpr .r15 := (k3.gpr (by decide)).trans v2_r15
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok s3 (dst := .r11) (src := .reg .r11) rfl
    (fun _ h => nomatch h) cf3) fun s4 ⟨b4, f4, g4, e4, k4⟩ => ?_
  have of4 := g4.trans of3
  simp only [v3_r11, Bool.toNat_false] at e4
  have K4 := K3.trans k4
  have v4_rsi : s4.gpr .rsi = 0 := (k4.gpr (by decide)).trans v3_rsi
  have v4_rbx : s4.gpr .rbx = 0 := (k4.gpr (by decide)).trans v3_rbx
  have v4_rax : s4.gpr .rax = s3.gpr .rax := k4.gpr (by decide)
  have v4_rcx : s4.gpr .rcx = s3.gpr .rcx := k4.gpr (by decide)
  have v4_r12 : s4.gpr .r12 = s.gpr .r12 := (k4.gpr (by decide)).trans v3_r12
  have v4_r15 : s4.gpr .r15 = s.gpr .r15 := (k4.gpr (by decide)).trans v3_r15
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok s4 (dst := .r11) (src := .reg .rcx) rfl
    (fun _ h => nomatch h) of4) fun s5 ⟨b5, f5, g5, e5, k5⟩ => ?_
  have cf5 := g5.trans f4
  simp only [v4_rcx, Bool.toNat_false] at e5
  have K5 := K4.trans k5
  have v5_rsi : s5.gpr .rsi = 0 := (k5.gpr (by decide)).trans v4_rsi
  have v5_rbx : s5.gpr .rbx = 0 := (k5.gpr (by decide)).trans v4_rbx
  have v5_rax : s5.gpr .rax = s3.gpr .rax := (k5.gpr (by decide)).trans v4_rax
  have v5_r12 : s5.gpr .r12 = s.gpr .r12 := (k5.gpr (by decide)).trans v4_r12
  have v5_r15 : s5.gpr .r15 = s.gpr .r15 := (k5.gpr (by decide)).trans v4_r15
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok s5 (dst := .r12) (src := .reg .r12) rfl
    (fun _ h => nomatch h) cf5) fun s6 ⟨b6, f6, g6, e6, k6⟩ => ?_
  have of6 := g6.trans f5
  simp only [v5_r12] at e6
  have K6 := K5.trans k6
  have v6_rsi : s6.gpr .rsi = 0 := (k6.gpr (by decide)).trans v5_rsi
  have v6_rbx : s6.gpr .rbx = 0 := (k6.gpr (by decide)).trans v5_rbx
  have v6_rax : s6.gpr .rax = s3.gpr .rax := (k6.gpr (by decide)).trans v5_rax
  have v6_r11 : s6.gpr .r11 = s5.gpr .r11 := k6.gpr (by decide)
  have v6_r15 : s6.gpr .r15 = s.gpr .r15 := (k6.gpr (by decide)).trans v5_r15
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok s6 (dst := .r12) (src := .reg .rax) rfl
    (fun _ h => nomatch h) of6) fun s7 ⟨b7, f7, g7, e7, k7⟩ => ?_
  have cf7 := g7.trans f6
  simp only [v6_rax] at e7
  have K7 := K6.trans k7
  have v7_rsi : s7.gpr .rsi = 0 := (k7.gpr (by decide)).trans v6_rsi
  have v7_rbx : s7.gpr .rbx = 0 := (k7.gpr (by decide)).trans v6_rbx
  have v7_r11 : s7.gpr .r11 = s5.gpr .r11 := (k7.gpr (by decide)).trans v6_r11
  have v7_r15 : s7.gpr .r15 = s.gpr .r15 := (k7.gpr (by decide)).trans v6_r15
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok s7 (dst := .rbx) (src := .reg .rsi) rfl
    (fun _ h => nomatch h) cf7) fun s8 ⟨b8, f8, g8, e8, k8⟩ => ?_
  have of8 := g8.trans f7
  simp only [v7_rsi, v7_rbx, show (0 : BitVec 64).toNat = 0 from rfl] at e8
  have K8 := K7.trans k8
  have v8_rsi : s8.gpr .rsi = 0 := (k8.gpr (by decide)).trans v7_rsi
  have v8_r11 : s8.gpr .r11 = s5.gpr .r11 := (k8.gpr (by decide)).trans v7_r11
  have v8_r12 : s8.gpr .r12 = s7.gpr .r12 := k8.gpr (by decide)
  have v8_r15 : s8.gpr .r15 = s.gpr .r15 := (k8.gpr (by decide)).trans v7_r15
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok s8 (dst := .rbx) (src := .reg .rsi) rfl
    (fun _ h => nomatch h) of8) fun s9 ⟨b9, f9, g9, e9, k9⟩ => ?_
  have cf9 := g9.trans f8
  simp only [v8_rsi, show (0 : BitVec 64).toNat = 0 from rfl] at e9
  have K9 := K8.trans k9
  have v9_rsi : s9.gpr .rsi = 0 := (k9.gpr (by decide)).trans v8_rsi
  have v9_r11 : s9.gpr .r11 = s5.gpr .r11 := (k9.gpr (by decide)).trans v8_r11
  have v9_r12 : s9.gpr .r12 = s7.gpr .r12 := (k9.gpr (by decide)).trans v8_r12
  have v9_r15 : s9.gpr .r15 = s.gpr .r15 := (k9.gpr (by decide)).trans v8_r15
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok s9 (dst := .r11) (src := .reg .r15) rfl
    (fun _ h => nomatch h) cf9) fun s10 ⟨b10, f10, g10, e10, k10⟩ => ?_
  simp only [v9_r11, v9_r15] at e10
  have K10 := K9.trans k10
  have v10_rsi : s10.gpr .rsi = 0 := (k10.gpr (by decide)).trans v9_rsi
  have v10_rbx : s10.gpr .rbx = s9.gpr .rbx := k10.gpr (by decide)
  have v10_r12 : s10.gpr .r12 = s7.gpr .r12 := (k10.gpr (by decide)).trans v9_r12
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok s10 (dst := .r12) (src := .reg .rsi) rfl
    (fun _ h => nomatch h) f10) fun s11 ⟨b11, f11, g11, e11, k11⟩ => ?_
  simp only [v10_rsi, v10_r12, show (0 : BitVec 64).toNat = 0 from rfl] at e11
  have K11 := K10.trans k11
  have v11_rsi : s11.gpr .rsi = 0 := (k11.gpr (by decide)).trans v10_rsi
  have v11_rbx : s11.gpr .rbx = s9.gpr .rbx := (k11.gpr (by decide)).trans v10_rbx
  have v11_r11 : s11.gpr .r11 = s10.gpr .r11 := k11.gpr (by decide)
  refine WP.mono (adcx_ok s11 (dst := .rbx) (src := .reg .rsi) rfl
    (fun _ h => nomatch h) f11) fun s12 ⟨b12, f12, g12, e12, k12⟩ => ?_
  simp only [v11_rsi, v11_rbx, show (0 : BitVec 64).toNat = 0 from rfl] at e12
  have K12 := K11.trans k12
  have v12_r11 : s12.gpr .r11 = s10.gpr .r11 := (k12.gpr (by decide)).trans v11_r11
  have v12_r12 : s12.gpr .r12 = s11.gpr .r12 := k12.gpr (by decide)
  refine ⟨?_, K12.mono (by decide)⟩
  rw [v12_r11, v12_r12]
  have bnd6 := Bool.toNat_le b6
  have bnd7 := Bool.toNat_le b7
  have bnd8 := Bool.toNat_le b8
  have bnd9 := Bool.toNat_le b9
  have bnd11 := Bool.toNat_le b11
  have bnd12 := Bool.toNat_le b12
  omega_using [e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, bnd6, bnd7, bnd8, bnd9, bnd11, bnd12]

end VG.Proof.Bignum.X86_64.AdxSquare
