module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Verified
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Order
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Fn
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Verified

/-!
# Arithmetic modulo P-256's order on RISC-V: verified

As the functions modulo `p` (`Proof/Weierstrass/RISCV64/P256Field/Verified.lean`),
whose lemmas this uses: each function meets a contract by register from
`fn_ok`, which the shared contracts of `Proof/Weierstrass/MontContract.lean` imply, and
is constant time by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Order

open VG VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P256Field (fn)
open VG.Proof.Weierstrass.RISCV64.P256Field (numAt_d4 keeps_of_frame fn_ct read_zero satWs CoreOk fn_ok d4)
open VG.Impl.Weierstrass.RISCV64.P256Order (mulFn addFn subFn)
open VG.Impl.Weierstrass.Mont (numAt Keeps p256n Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)

theorem n_eq : p256n.m = N := by decide

/-- `fn core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {s : State} (hs : rvPre p256n s) (hp : pre (arg p256n s .a2) (arg p256n s .a3)) :
    ∃ t s', Exec isa (fn core) s t s' ∧ abiPreserved s s' ∧
      res (arg p256n s .a2) (arg p256n s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 4) ∧
      Keeps 4 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show p256n.k ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, show p256n.k = 4 from rfl, numAt_d4] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

theorem mul_rv (s : State) (hs : (mulRV p256n).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p256n).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (@mulCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v1, by rw [n_eq]; exact v2, k⟩

theorem add_rv (s : State) (hs : (addRV p256n).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p256n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@addCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

theorem sub_rv (s : State) (hs : (subRV p256n).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p256n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@subCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

/-! ## The multiplication with the constants in registers

`mulCoreR` (`mulCoreR_core`) as `mulCore`, by `mulWithF_ok`: its reduction
(`reduceR_ok`) keeps `s7`–`s11` in the copies, as Gen4's does (`save_step`,
`restore_step`), builds `n'`, `n₀` and `n₁` in `s7`–`s9` (`RegK3`), and runs
the rounds as `reduce` does (`roundR_ok`, with `qprodR_ok`). -/

section Regs

open VG.RISCV64.Steps VG.RISCV64.Wide
open VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Impl.Weierstrass.RISCV64.P256Order (qprodR roundR constsR reduceR mulCoreR qk sumN NINV N0 N1)
open VG.Proof.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok clob64 Keeps.rest)
open VG.Impl.Words.RISCV64 (li64)
open VG.Impl.Weierstrass.RISCV64.Gen4 (KR saveM)
open VG.Proof.Weierstrass.RISCV64.Gen4 (rw_cases SvI save_step RsI restore_step prodV_frame regsM KR_idx)

/-- `n'`, `n₀` and `n₁` in `s7`–`s9`. -/
def RegK3 (s : State) : Prop := s.gpr .s7 = NINV ∧ s.gpr .s8 = N0 ∧ s.gpr .s9 = N1

theorem KR3_notM : ∀ r ∈ [Reg.s7, .s8, .s9], r ∉ clobM := by decide

theorem RegK3.of_gpr {s s' : State} (h : RegK3 s) (hg : ∀ r ∈ [Reg.s7, .s8, .s9], s'.gpr r = s.gpr r) :
    RegK3 s' :=
  ⟨by rw [hg _ (by decide)]; exact h.1, by rw [hg _ (by decide)]; exact h.2.1, by rw [hg _ (by decide)]; exact h.2.2⟩

theorem KR3_ne (j : Nat) : ∀ r ∈ [Reg.s7, .s8, .s9], r ≠ rw j := by
  intro r hr e
  subst e
  rcases rw_cases j with h | h | h | h | h <;> rw [h] at hr <;> revert hr <;> decide

/-- `qprod i` with `n'`, `n₀` and `n₁` in `s7`–`s9`. -/
theorem qprodR_ok {s : State} (i : Nat) (hk : RegK3 s) :
    WP isa (.block (qprodR i)) s fun s' =>
      (s'.gpr (rw i)).toNat = (s.gpr (rw i)).toNat * 0xccd1c8aaee00bc4f % 2 ^ 64 ∧
      (s.gpr (rw i)).toNat + (s'.gpr (rw i)).toNat * 0xf3b9cac2fc632551 +
          2 ^ 64 * ((s'.gpr (rw i)).toNat * 0xbce6faada7179e84) =
        2 ^ 64 * ((s'.gpr .a5).toNat + 2 ^ 64 * (s'.gpr .a6).toNat) ∧
      Keeps [rw i, .t0, .a0, .a4, .a5, .a6, .a7] s s' := by
  obtain ⟨n0, na0, -, -, n4, n5, n6, n7, -⟩ := rw_ne i
  have r8 : Reg.s8 ≠ rw i := KR3_ne i _ (by decide)
  have r9 : Reg.s9 ≠ rw i := KR3_ne i _ (by decide)
  unfold qprodR
  simp only [List.cons_append, List.nil_append]
  refine wp_mul fun s2 u2 => wp_mulhu fun s4 u4 => wp_mulhu fun s6 u6 => wp_mul fun s7 u7 => ?_
  refine wp_li (imm := 0) (by decide) fun s8 u8 => wp_sltu fun s9 u9 => wp_add fun s10 u10 => ?_
  refine wp_add fun s11 u11 => wp_sltu fun s12 u12 => wp_add fun s13 u13 => WP.block_nil ?_
  -- The quotient word, through the steps.
  have hq2 : s2.gpr (rw i) = s.gpr (rw i) * NINV := by rw [u2.gpr, hk.1]
  have q6 : s6.gpr (rw i) = s2.gpr (rw i) := by rw [u6.other _ n6, u4.other _ n4]
  have q8 : s8.gpr (rw i) = s2.gpr (rw i) := by
    rw [u8.other _ na0, u7.other _ n5, q6]
  have q13 : s13.gpr (rw i) = s2.gpr (rw i) := by
    rw [u13.other _ n6, u12.other _ n7, u11.other _ n5, u10.other _ n4,
      u9.other _ na0, q8]
  have hqn : (s2.gpr (rw i)).toNat = (s.gpr (rw i)).toNat * 0xccd1c8aaee00bc4f % 2 ^ 64 := by
    rw [hq2, BitVec.toNat_mul]; rfl
  have s9_6 : s6.gpr .s9 = s.gpr .s9 := by
    rw [u6.other _ (by decide), u4.other _ (by decide), u2.other _ r9]
  -- The words.
  have a4_9 : s9.gpr .a4 = s4.gpr .a4 := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide)]
  have hA4 : s4.gpr .a4 = BitVec.ofNat 64 ((s2.gpr (rw i)).toNat * 0xf3b9cac2fc632551 / 2 ^ 64) := by
    rw [u4.gpr, u2.other _ r8, hk.2.1]; rfl
  have hA6 : s6.gpr .a6 = BitVec.ofNat 64 ((s2.gpr (rw i)).toNat * N1.toNat / 2 ^ 64) := by
    rw [u6.gpr, u4.other _ n4, u4.other _ (by decide), u2.other _ r9, hk.2.2]
  have hA5 : s7.gpr .a5 = s2.gpr (rw i) * N1 := by
    rw [u7.gpr, q6, s9_6, hk.2.2]
  have hB : s9.gpr .a0 = if (0 : BitVec 64) < s2.gpr (rw i) then 1 else 0 := by
    rw [u9.gpr, u8.gpr, q8]; rfl
  have hH : s10.gpr .a4 = s4.gpr .a4 + s9.gpr .a0 := by rw [u10.gpr, a4_9]
  have a5_10 : s10.gpr .a5 = s7.gpr .a5 := by
    rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide)]
  have a6_12 : s12.gpr .a6 = s6.gpr .a6 := by
    rw [u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide),
      u8.other _ (by decide), u7.other _ (by decide)]
  have hS : s11.gpr .a5 = s7.gpr .a5 + s10.gpr .a4 := by rw [u11.gpr, a5_10]
  have hC : s12.gpr .a7 = if s11.gpr .a5 < s10.gpr .a4 then 1 else 0 := by
    rw [u12.gpr, u11.other .a4 (by decide)]
  have hY : s13.gpr .a6 = s6.gpr .a6 + s12.gpr .a7 := by rw [u13.gpr, a6_12]
  have hS13 : s13.gpr .a5 = s11.gpr .a5 := by rw [u13.other _ (by decide), u12.other _ (by decide)]
  -- Their numbers.
  have bq := (s2.gpr (rw i)).isLt
  have bA4 : (s4.gpr .a4).toNat + 1 < 2 ^ 64 := by
    rw [hA4, ofNat_lt (Nat.div_lt_of_lt_mul (by omega))]; omega
  have bB : (s9.gpr .a0).toNat ≤ 1 := by rw [hB]; exact carry_le _
  have eH : (s10.gpr .a4).toNat = (s4.gpr .a4).toNat + (s9.gpr .a0).toNat := by
    rw [hH]; exact add_toNat (by omega)
  have mw := mul_words (s2.gpr (rw i)) N1
  rw [← hA5, ← hA6] at mw
  have bA6 : (s6.gpr .a6).toNat + 1 < 2 ^ 64 := by
    have := (s7.gpr .a5).isLt
    have : (s2.gpr (rw i)).toNat * N1.toNat < 2 ^ 64 * (2 ^ 64 - 2) := by
      rw [show N1.toNat = 0xbce6faada7179e84 from rfl]; omega
    omega
  have cc := carry (s7.gpr .a5) (s10.gpr .a4)
  rw [← hS, ← hC] at cc
  have eY : (s13.gpr .a6).toNat = (s6.gpr .a6).toNat + (s12.gpr .a7).toNat := by
    rw [hY]; exact add_toNat (by have := carry_le (s11.gpr .a5 < s10.gpr .a4); rw [← hC] at this; omega)
  have mc := mont_carry (s.gpr (rw i)).toNat (BitVec.isLt _)
  rw [← hqn] at mc
  have eB : (s9.gpr .a0).toNat = if 0 < (s2.gpr (rw i)).toNat then 1 else 0 := by
    rw [hB, sltu_toNat]; rfl
  have eA4 : (s4.gpr .a4).toNat = (s2.gpr (rw i)).toNat * 0xf3b9cac2fc632551 / 2 ^ 64 := by
    rw [hA4]; exact ofNat_lt (Nat.div_lt_of_lt_mul (by omega))
  rw [← eB, ← eA4] at mc
  refine ⟨by rw [q13, hqn], ?_, ?_⟩
  · rw [q13, hS13]
    exact qprod_arith mc eH (by rw [show N1.toNat = 0xbce6faada7179e84 from rfl] at mw; exact mw) cc eY
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, -, h2, h3, h4, h5, h6⟩ := hr
      rw [u13.other _ h5, u12.other _ h6, u11.other _ h4, u10.other _ h3, u9.other _ h2, u8.other _ h2,
        u7.other _ h4, u6.other _ h5, u4.other _ h3, u2.other _ h0]
    · rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u4.mem, u2.mem]
    · rw [u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u4.rd, u2.rd]
    · rw [u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u4.wr, u2.wr]
    · rw [u13.sp, u12.sp, u11.sp, u10.sp, u9.sp, u8.sp, u7.sp, u6.sp, u4.sp, u2.sp]

/-- Round `i`, with the constants in registers. -/
theorem roundR_ok {b : Addr} {s0 : State} (hk0 : RegK3 s0) {i : Nat} (hi : i < 4) {s : State} (h : RedInv b s0 i s) :
    WP isa (.block (roundR i)) s (RedInv b s0 (i + 1)) := by
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34, dk⟩ := rw_facts i hi
  obtain ⟨n02, n04, n05, n06, n07, n0t, n03, c0⟩ := dk 0 (by decide)
  obtain ⟨n12, n14, n15, n16, n17, n1t, n13, c1⟩ := dk 1 (by decide)
  obtain ⟨n22, n24, n25, n26, n27, n2t, n23, c2⟩ := dk 2 (by decide)
  obtain ⟨n32, n34, n35, n36, n37, n3t, n33, c3⟩ := dk 3 (by decide)
  obtain ⟨n42, n44, n45, n46, n47, n4t, n43, c4⟩ := dk 4 (by decide)
  simp only [Nat.add_zero] at n02 n04 n05 n06 n07 n0t n03 c0
  have a0 := fun k => (rw_ne (i + k)).2.1
  have n0a := (rw_ne i).2.1
  have n1a := a0 1
  have n2a := a0 2
  have n3a := a0 3
  have n4a := a0 4
  have hc := h.ctx
  have hd : ACC + 8 * (i + 4) + 8 ≤ 2048 := by simp only [ACC]; omega
  have hk : RegK3 s := hk0.of_gpr fun r hr => h.rest.gpr r (KR3_notM r hr)
  unfold roundR
  simp only [List.append_assoc]
  refine ld_ok hc hd (by simp only [ACC]; omega) fun s1 u1 => ?_
  have hT4 : (s1.gpr (rw (i + 4))).toNat = T s0.mem b (i + 4) := by
    rw [u1.gpr, ← h.mem]; rfl
  have hk1 : RegK3 s1 := hk.of_gpr fun r hr => u1.other r fun e => KR3_ne (i + 4) r hr e
  show WP isa (.block (qprodR i ++ _)) s1 _
  refine WP.block_append (WP.mono (qprodR_ok i hk1) fun s2 ⟨q1, q2, k2⟩ => ?_)
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 1)) (y := .a5) (c := .a0) n15 n1a)
    fun s3 ⟨e3, k3⟩ => ?_)
  refine WP.block_append (WP.mono (adc_ok (d := rw (i + 2)) (x := rw (i + 2)) (y := .a6) (c := .a0) (u := .a7)
    n26 n2a (Ne.symm n27) (by decide)) fun s4 ⟨e4, k4⟩ => ?_)
  refine WP.block_append (WP.mono (quot_ok (r := rw i) n04 n05 n06 n07) fun s5 ⟨x1, x2, x3, x4, k5⟩ => ?_)
  -- The quotient word, kept.
  have g1 : ∀ r, r ≠ rw (i + 4) → s1.gpr r = s.gpr r := u1.other
  have q4 : s4.gpr (rw i) = s2.gpr (rw i) := by
    rw [kp k4 (by simp [d02, n07, n0a]), kp k3 (by simp [d01, n0a])]
  have q5 : s5.gpr (rw i) = s2.gpr (rw i) := by rw [kp k5 (by simp [n04, n05, n06, n07, n0t]), q4]
  rw [q4] at x2
  refine WP.block_append (WP.mono (qk_ok i (by rw [q5]; exact x2)) fun s6 ⟨f6, b6, k6⟩ => ?_)
  rw [q5] at f6
  show WP isa (.block ([.add (rw (i + 2)) (rw (i + 2)) .a4, .sltu .t0 (rw (i + 2)) .a4] ++
    (.add .t0 .t0 .a0 :: _))) s6 _
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 2)) (y := .a4) (c := .t0) n24 n2t)
    fun s7 ⟨e7, k7⟩ => wp_add fun s8 u8 => ?_)
  show WP isa (.block ([.add (rw (i + 3)) (rw (i + 3)) .t0, .sltu .a0 (rw (i + 3)) .t0] ++ _)) s8 _
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 3)) (y := .t0) (c := .a0) n3t n3a)
    fun s9 ⟨e9, k9⟩ => ?_)
  show WP isa (.block ([.add (rw (i + 3)) (rw (i + 3)) .a6, .sltu .a5 (rw (i + 3)) .a6] ++
    (.add .a0 .a0 .a5 :: _))) s9 _
  refine WP.block_append (WP.mono (add1_ok (d := rw (i + 3)) (y := .a6) (c := .a5) n36 n35)
    fun s10 ⟨e10, k10⟩ => wp_add fun s11 u11 => ?_)
  show WP isa (.block [.add .a7 .a7 .a0, .add .a7 .a7 .a2, .add (rw (i + 4)) (rw (i + 4)) .a7,
    .sltu .a2 (rw (i + 4)) .a7]) s11 _
  refine WP.mono (addTop_ok (d := rw (i + 4)) (h := .a7) (c := .a0) (k := .a2) n47 n42 (by decide))
    fun s12 ⟨e12, k12⟩ => ?_
  -- What each step read, through the steps before it.
  have w1_2 : s2.gpr (rw (i + 1)) = s.gpr (rw (i + 1)) := by
    rw [kp k2 (by simp [Ne.symm d01, n1t, n1a, n14, n15, n16, n17]), g1 _ d14]
  have w2_3 : s3.gpr (rw (i + 2)) = s.gpr (rw (i + 2)) := by
    rw [kp k3 (by simp [Ne.symm d12, n2a]), kp k2 (by simp [Ne.symm d02, n2t, n2a, n24, n25, n26, n27]),
      g1 _ d24]
  have a6_3 : s3.gpr .a6 = s2.gpr .a6 := kp k3 (by simp [Ne.symm n16])
  have a0_3 : (s3.gpr .a0).toNat ≤ 1 := by
    have := (s3.gpr (rw (i + 1))).isLt; have := (s2.gpr (rw (i + 1))).isLt; have := (s2.gpr .a5).isLt
    omega
  have e4' := e4 a0_3
  rw [w2_3, a6_3] at e4'
  rw [w1_2] at e3
  have w2_6 : s6.gpr (rw (i + 2)) = s4.gpr (rw (i + 2)) := by
    rw [kp k6 (by simp [n2t, n24, n25, n26, n27]), kp k5 (by simp [n2t, n24, n25, n26, n27])]
  rw [w2_6] at e7
  have a0_7 : s7.gpr .a0 = s4.gpr .a0 := by
    rw [kp k7 (by simp [Ne.symm n2a]), kp k6 (by decide), kp k5 (by decide)]
  have t0_8 : (s8.gpr .t0).toNat = (s7.gpr .t0).toNat + (s4.gpr .a0).toNat := by
    rw [u8.gpr, ← a0_7]
    refine add_toNat ?_
    have := (s7.gpr (rw (i + 2))).isLt; have := (s6.gpr (rw (i + 2))).isLt; have := (s6.gpr .a4).isLt
    have := (s4.gpr (rw (i + 2))).isLt; have := (s.gpr (rw (i + 2))).isLt; have := (s2.gpr .a6).isLt
    rw [a0_7]; omega
  have w3_8 : s8.gpr (rw (i + 3)) = s.gpr (rw (i + 3)) := by
    rw [u8.other _ n3t, kp k7 (by simp [Ne.symm d23, n3t]),
      kp k6 (by simp [n3t, n34, n35, n36, n37]), kp k5 (by simp [n3t, n34, n35, n36, n37]),
      kp k4 (by simp [Ne.symm d23, n37, n3a]), kp k3 (by simp [Ne.symm d13, n3a]),
      kp k2 (by simp [Ne.symm d03, n3t, n3a, n34, n35, n36, n37]), g1 _ d34]
  rw [w3_8] at e9
  have a6_9 : s9.gpr .a6 = s6.gpr .a6 := by
    rw [kp k9 (by simp [Ne.symm n36]), u8.other _ (by decide), kp k7 (by simp [Ne.symm n26])]
  rw [a6_9] at e10
  have a0_10 : s10.gpr .a0 = s9.gpr .a0 := kp k10 (by simp [Ne.symm n3a])
  have a0_11 : (s11.gpr .a0).toNat = (s9.gpr .a0).toNat + (s10.gpr .a5).toNat := by
    rw [u11.gpr, a0_10]
    refine add_toNat ?_
    have := (s9.gpr (rw (i + 3))).isLt; have := (s10.gpr (rw (i + 3))).isLt; have := (s6.gpr .a6).isLt
    have := (s8.gpr (rw (i + 3))).isLt; have := (s.gpr (rw (i + 3))).isLt
    have := (s7.gpr .t0).isLt; have := (s4.gpr .a0).isLt
    omega
  have w4_11 : s11.gpr (rw (i + 4)) = s1.gpr (rw (i + 4)) := by
    rw [u11.other _ n4a, kp k10 (by simp [Ne.symm d34, n45]), kp k9 (by simp [Ne.symm d34, n4a]),
      u8.other _ n4t, kp k7 (by simp [Ne.symm d24, n4t]),
      kp k6 (by simp [n4t, n44, n45, n46, n47]), kp k5 (by simp [n4t, n44, n45, n46, n47]),
      kp k4 (by simp [Ne.symm d24, n47, n4a]), kp k3 (by simp [Ne.symm d14, n4a]),
      kp k2 (by simp [Ne.symm d04, n4t, n4a, n44, n45, n46, n47])]
  have a7_11 : s11.gpr .a7 = s6.gpr .a7 := by
    rw [u11.other _ (by decide), kp k10 (by simp [Ne.symm n37]), kp k9 (by simp [Ne.symm n37]),
      u8.other _ (by decide), kp k7 (by simp [Ne.symm n27])]
  have a2_11 : s11.gpr .a2 = s.gpr .a2 := by
    rw [u11.other _ (by decide), kp k10 (by simp [Ne.symm n32]), kp k9 (by simp [Ne.symm n32]),
      u8.other _ (by decide), kp k7 (by simp [Ne.symm n22]), kp k6 (by decide), kp k5 (by decide),
      kp k4 (by simp [Ne.symm n22]), kp k3 (by simp [Ne.symm n12]),
      kp k2 (by simp [Ne.symm n02]), g1 _ (Ne.symm n42)]
  have hcy := h.cy
  have hcond : (s6.gpr .a7).toNat + (s11.gpr .a0).toNat + (s.gpr .a2).toNat < 2 ^ 64 := by
    rw [a0_11]
    have := (s9.gpr (rw (i + 3))).isLt; have := (s10.gpr (rw (i + 3))).isLt; have := (s6.gpr .a6).isLt
    have := (s8.gpr (rw (i + 3))).isLt; have := (s.gpr (rw (i + 3))).isLt
    rw [t0_8] at e9
    have := (s7.gpr (rw (i + 2))).isLt; have := (s6.gpr .a4).isLt; have := (s4.gpr (rw (i + 2))).isLt
    have := (s.gpr (rw (i + 2))).isLt; have := (s2.gpr .a6).isLt
    omega
  have e12' := e12 (by rw [a7_11, a2_11]; exact hcond)
  rw [w4_11, hT4, a7_11, a2_11] at e12'
  rw [t0_8] at e9
  -- The new registers, read from the last state.
  have o1 : s12.gpr (rw (i + 1)) = s3.gpr (rw (i + 1)) := by
    rw [kp k12 (by simp [d14, n17, n12]), u11.other _ n1a, kp k10 (by simp [d13, n15]),
      kp k9 (by simp [d13, n1a]), u8.other _ n1t, kp k7 (by simp [d12, n1t]),
      kp k6 (by simp [n1t, n14, n15, n16, n17]), kp k5 (by simp [n1t, n14, n15, n16, n17]),
      kp k4 (by simp [d12, n17, n1a])]
  have o2 : s12.gpr (rw (i + 2)) = s7.gpr (rw (i + 2)) := by
    rw [kp k12 (by simp [d24, n27, n22]), u11.other _ n2a, kp k10 (by simp [d23, n25]),
      kp k9 (by simp [d23, n2a]), u8.other _ n2t]
  have o3 : s12.gpr (rw (i + 3)) = s10.gpr (rw (i + 3)) := by
    rw [kp k12 (by simp [d34, n37, n32]), u11.other _ n3a]
  -- The frame.
  have sub : ∀ r ∈ clob64, r ∈ clobM := by decide
  have cons : ∀ {r : Reg} {l : List Reg}, r ∈ clob64 → (∀ x ∈ l, x ∈ clobM) → ∀ x ∈ r :: l, x ∈ clobM :=
    fun hr hl x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact sub _ hr
      · exact hl x hx
  have hrest : Rest clobM s s12 :=
    (u1.rest (sub _ c4)).trans <| ((Keeps.rest k2).mono (cons c0 (by decide))).trans <|
      ((Keeps.rest k3).mono (cons c1 (by decide))).trans <| ((Keeps.rest k4).mono (cons c2 (by decide))).trans <|
      ((Keeps.rest k5).mono (by decide)).trans <| ((Keeps.rest k6).mono (by decide)).trans <|
      ((Keeps.rest k7).mono (cons c2 (by decide))).trans <| (u8.rest (by decide)).trans <|
      ((Keeps.rest k9).mono (cons c3 (by decide))).trans <| ((Keeps.rest k10).mono (cons c3 (by decide))).trans <|
      (u11.rest (by decide)).trans ((Keeps.rest k12).mono (cons c4 (by decide)))
  have hm : s12.mem = s0.mem := by
    rw [k12.2.1, u11.mem, k10.2.1, k9.2.1, u8.mem, k7.2.1, k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1,
      u1.mem, h.mem]
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := idx i
  have hup : upW s0.mem b (i + 4) (4 - i) = T s0.mem b (i + 4) + 2 ^ 64 * upW s0.mem b (i + 5) (3 - i) := by
    rw [i6 hi]; rfl
  rw [g1 _ d04] at q2
  have key : 2 ^ 64 * wv s0.mem b (i + 1) s12 = wv s0.mem b i s + (s2.gpr (rw i)).toNat * N := by
    simp only [wv, i1, i2, i3, i4, i5 hi, hup, o1, o2, o3]
    exact round_arith q2 e3 e4' x2 f6 e7 rfl e9 e10 a0_11 e12'
  obtain ⟨Q, hQ, hv⟩ := h.val
  have cy := carry1 e12' (dw_lt _ _ _) hcond
  obtain ⟨v1, v2⟩ := round_val hQ (BitVec.isLt _) hv key
  refine ⟨hc.of_rest hrest (by decide), h.rest.trans hrest, hm, cy,
    ⟨Q + (s2.gpr (rw i)).toNat * 2 ^ (64 * i), by rw [pow64_succ]; exact v1, by rw [pow64_succ]; exact v2⟩⟩

theorem roundsR_ok {b : Addr} {s0 : State} (hk0 : RegK3 s0) : ∀ n ≤ 4, ∀ s, RedInv b s0 0 s →
    WP isa (.block ((List.range n).flatMap roundR)) s (RedInv b s0 n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (roundsR_ok hk0 n (by omega) s h) fun s1 h1 => roundR_ok hk0 (by omega) h1)

/-- `reduceR`: as `reduce_ok`, writing only the copies. -/
theorem reduceR_ok {b : Addr} {s : State} (hc : Ctx b s) :
    WP isa (.block reduceR) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ Frame (regsM b) s.mem s'.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 256 ∧
        ((s'.gpr X0).toNat + 2 ^ 64 * (s'.gpr X1).toNat + 2 ^ 128 * (s'.gpr X2).toNat +
          2 ^ 192 * (s'.gpr X3).toNat + 2 ^ 256 * (s'.gpr XC).toNat) * 2 ^ 256 = prodV s.mem b + Q * N := by
  have e : reduceR = saveM ++ (constsR ++ (((List.range 4).map
      (fun j => (.load .d (rw j) .a3 (ACC + 8 * j) : Instr)) ++ ([.li .a2 0] : List Instr)) ++
      ((List.range 4).flatMap roundR ++ Impl.Weierstrass.RISCV64.Gen4.restoreM))) := by
    simp only [reduceR, List.append_assoc]
  rw [e]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SvI b s) (fun k s' hk h => save_step hc hk h) 5
    (Nat.le_refl _) s ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s1 h1 => ?_)
  have hc1 : Ctx b s1 := ⟨by rw [h1.gpr]; exact hc.a3, hc.al, by rw [h1.wr]; exact hc.wr⟩
  unfold constsR
  simp only [List.append_assoc]
  refine wp_li64 (by decide) _ fun t1 e1 k1 => wp_li64 (by decide) _ fun t2 e2 k2 =>
    wp_li64 (by decide) _ fun sK e3 k3 => ?_
  have kK : Keeps [.s7, .a0, .s8, .a0, .s9, .a0] s1 sK := (k1.trans k2).trans k3
  have hkK : RegK3 sK :=
    ⟨by rw [k3.1 _ (by decide), k2.1 _ (by decide), e1], by rw [k3.1 _ (by decide), e2], e3⟩
  have hcK : Ctx b sK := hc1.of_rest (Keeps.rest kK) (by decide)
  rw [← List.append_assoc]
  refine WP.block_append (WP.mono (loads_ok hcK) fun s2 h2 => ?_)
  refine WP.block_append (WP.mono (roundsR_ok hkK 4 (Nat.le_refl _) s2 h2) fun s3 h3 => ?_)
  have hm3 : s3.mem = s1.mem := by rw [h3.mem, kK.2.1]
  have hsav : ∀ i < 5, s3.mem.readW (b + BitVec.ofNat 64 (MA + 8 * i)) 64 = s.gpr (KR.getD i .s7) :=
    fun i hi => by rw [hm3]; exact h1.saved i hi
  refine WP.mono (wp_range_flatMap (M := isa) (RsI b s3 fun i => s.gpr (KR.getD i .s7))
    (fun k s' hk h => restore_step h3.ctx hsav hk h) 5 (Nat.le_refl _) s3
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s4 h4 => ?_
  have g4 : ∀ r, r ∉ KR → s4.gpr r = s3.gpr r := h4.others
  have hrest : Rest clobM s s4 := by
    refine ⟨fun r hr => ?_, by rw [h4.rd, h3.rest.rd, kK.2.2.1, h1.rd], by rw [h4.wr, h3.rest.wr, kK.2.2.2.1, h1.wr],
      by rw [h4.sp, h3.rest.sp, kK.2.2.2.2, h1.sp]⟩
    by_cases hK : r ∈ KR
    · obtain ⟨i, hi, rfl⟩ := KR_idx r hK
      exact h4.restored i hi
    · have hx : r ∉ [Reg.s7, .a0, .s8, .a0, .s9, .a0] := fun hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact hK (by decide) | exact hr (by decide)
      rw [g4 r hK, h3.rest.gpr r hr, kK.1 r hx, h1.gpr]
  have hf : Frame (regsM b) s.mem s4.mem := by rw [h4.mem, hm3]; exact h1.frame
  obtain ⟨Q, hQ, hv⟩ := h3.val
  rw [kK.2.1, prodV_frame h1.frame] at hv
  refine ⟨h3.ctx.of_rest ⟨g4, h4.rd, h4.wr, h4.sp⟩ (by decide), hrest, hf,
    by rw [g4 _ (by decide)]; exact h3.cy, Q, by simpa using hQ, ?_⟩
  rw [g4 X0 (by decide), g4 X1 (by decide), g4 X2 (by decide), g4 X3 (by decide), g4 XC (by decide)]
  simpa [wv, upW, X0, X1, X2, X3, XC, rw, RW] using hv

theorem mulCoreR_core : CoreOk mulCoreR (fun _ B => B < N) mulRes :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulWithF_ok N_pos (by decide) reduceR_ok (fun _ => sumN_ok) hw h4 h5 h2 ha8 hb8
      ho8 ha hb ho hdb hB) fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

end Regs

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p256n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P256Order.mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV p256n).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ :=
    P256Field.fnA_rv rfl (@mulCoreR_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v1, by rw [n_eq]; exact v2, k⟩

theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p256n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P256Order.addFnA s t s' ∧ abiPreserved s s' ∧ (addRV p256n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv rfl (@addCore_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p256n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P256Order.subFnA s t s' ∧ abiPreserved s s' ∧ (subRV p256n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv rfl (@subCore_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

/-! ## Constant time -/

open VG.Proof.Ed25519.RISCV64 (mulAgreeLo mulZext_rel)

theorem mulFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub mulFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem addFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub addFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem subFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub subFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem rvPub_agree : ∀ s₁ s₂ : State, rvPre p256n s₁ → rvPre p256n s₂ → rvPub s₁ s₂ → mulAgreeLo s₁ s₂ :=
  fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, h0, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

/-! ## The shared contracts -/

theorem sat_pre : rvPre p256n satWs ∧ arg p256n satWs .a2 = 0 ∧ arg p256n satWs .a3 = 0 := by
  refine ⟨⟨rfl, rfl, by decide, ⟨?_, ?_, ?_⟩, by decide⟩, read_zero _ _, read_zero _ _⟩ <;>
    simp [Fits, VG.Proof.Weierstrass.RISCV64.rvOwn, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes, satWs,
      offArg, p256n]

theorem mul_verified : Verified RISCV64.target mulFn (p256n.mulContract RISCV64.abi) :=
  Verified.of_correct mul_rv (mulFn_ct (Pre := (mulRV p256n).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg,
        mulRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

theorem add_verified : Verified RISCV64.target addFn (p256n.addContract RISCV64.abi) :=
  Verified.of_correct add_rv (addFn_ct (Pre := (addRV p256n).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg,
        addRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

theorem sub_verified : Verified RISCV64.target subFn (p256n.subContract RISCV64.abi) :=
  Verified.of_correct sub_rv (subFn_ct (Pre := (subRV p256n).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg,
        subRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd, Impl.Weierstrass.Mont.ownAt]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

end VG.Proof.Weierstrass.RISCV64.P256Order
