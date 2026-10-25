module
public import VerifiedGarbage.Proof.Bignum.Arm.SquareReduce

import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.Csub
import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The whole ARMv7 Montgomery square: `a² R⁻¹ mod m`, canonical -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqFinish_ok (s : State) (h : RedInv m0 base size out a mod M n inv n s) :
    WP isa sqFinish s fun t =>
      val32 t.mem (State.addr base) out n < val32 m0 (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 m0 (State.addr base) mod n =
        val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n % val32 m0 (State.addr base) mod n ∧
      Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s.mem t.mem ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header; have := env.sepM; have := env.mFits
  have := env.sepO; have := env.outFits
  rw [sqFinish, WP.seq_iff]
  refine WP.mono (sqBase_ok s env .r0) ?_
  rintro s1 ⟨p1, m1, r1⟩
  have e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (sqFinishHeader_ok s1 e1.workspace (by omega_arith) p1 e1.modNow e1.metaNow) ?_
  rintro s2 ⟨q12, q0, m2, r2⟩
  have e2 := e1.of_mem m2 r2
  rw [WP.seq_iff]
  refine WP.mono (sqFinishLoad_ok s2 (n := n) (out := out) e2.workspace (by omega_arith) q0
    (by rw [m2, m1]; exact h.md.count) (by rw [m2, m1]; exact h.md.outPtr)) ?_
  rintro s3 ⟨g7, g9, g3, g0, m3, r3⟩
  have e3 := e2.of_mem m3 r3
  rw [WP.seq_iff]
  refine WP.mono (sqFinishArgs_ok s3 e3.workspace (by omega_arith) (g0.trans q0) g7) ?_
  rintro s4 ⟨m4, g10, glr, g11, r4⟩
  have o4 := writeW32_outside s3.mem (State.addr base) (d := M + 8 * n + 24) (s3.gpr .r3) (by omega_arith)
  rw [← m4] at o4
  have e4 := e3.next (Outs.of_outside (o4.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r4
  -- The number to reduce: `T[n …]` with the carry `c` above it.
  obtain ⟨Q, hQ, value⟩ := h.value
  have ms3 : s3.mem = s.mem := m3.trans (m2.trans m1)
  have hi : val32 s4.mem (State.addr base) (M + 24 + 4 * n) (n + 2) =
      val32 s.mem (State.addr base) (M + 24 + 4 * n) n +
        2 ^ (32 * n) * (s.mem.readW (off (State.addr base) (M + 12)) 32).toNat := by
    rw [val32_top2, show M + 24 + 4 * n + 4 * n = M + 8 * n + 24 by omega_arith, o4.val32 (by omega_arith) (by omega_arith),
      o4.w32 (d := M + 8 * n + 24 + 4) (by omega_arith) (by omega_arith), m4, w32_write_self, g3, m2, m1, ms3]
    have z := h.top
    rw [show M + 24 + 8 * n = M + 8 * n + 24 by omega_arith] at z
    have z' := val32_zero_tail (i := 1) (j := 1) z
    rw [val32, val32, Nat.mul_zero, Nat.add_zero] at z'
    rw [show M + 8 * n + 24 + 4 = M + 8 * n + 24 + 4 * 1 by omega_arith, z']
    simp only [Nat.mul_zero, Nat.add_zero]
  have whole : 2 ^ (32 * n) * val32 s4.mem (State.addr base) (M + 24 + 4 * n) (n + 2) =
      val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n + Q * val32 m0 (State.addr base) mod n := by
    rw [hi, ← value, show 2 * n = n + n by omega_arith, val32_append, h.low, Nat.zero_add,
      show 32 * (n + n) = 32 * n + 32 * n by omega_arith, Nat.pow_add, Nat.mul_add, Nat.mul_assoc]
  have N4 : val32 s4.mem (State.addr base) mod n = val32 m0 (State.addr base) mod n := e4.modVal
  have bound := sq_red_bound env.operand (Nat.le_of_lt (val32_lt m0 (State.addr base) mod n)) hQ whole
  have ctx : CsubCtx s4 base size out (M + 24 + 4 * n) mod M n :=
    ⟨⟨nowrap, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, e4.workspace.writable⟩,
      by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  have p0 : s4.gpr .r0 = base + BitVec.ofNat 32 M := by rw [r4.gpr .r0 (by decide), g0, q0]
  have p12 : s4.gpr .r12 = base + BitVec.ofNat 32 mod := by
    rw [r4.gpr .r12 (by decide), r3.gpr .r12 (by decide), q12]
  have p9 : s4.gpr .r9 = base + BitVec.ofNat 32 out := by rw [r4.gpr .r9 (by decide), g9]
  have p7 : s4.gpr .r7 = BitVec.ofNat 32 n := by rw [r4.gpr .r7 (by decide), g7]
  refine WP.mono (csub_ok s4 ctx (by omega_arith) p0 g10 p12 p9 glr p7 g11 (by rw [N4]; exact bound)) ?_
  rintro t ⟨result, outs, rest⟩
  have hpos : 0 < val32 m0 (State.addr base) mod n := Nat.lt_of_le_of_lt (Nat.zero_le _) env.operand
  rw [N4] at result
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [result]; exact Nat.mod_lt _ hpos
  · rw [result, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, whole, Nat.add_mul_mod_self_right]
  · have A : Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s3.mem s4.mem :=
      Outs.of_outside (o4.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith)) (by simp)
    have B : Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s4.mem t.mem := fun x hx =>
      outs x fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have h1 := hx (M, 4 * (2 * n + 8)) (by simp)
        have h2 := hx (out, 4 * n) (by simp)
        rcases hr with rfl | rfl <;> simp only at h1 h2 ⊢ <;> omega_arith
    rw [ms3] at A
    exact A.trans B
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans
      (rest.mono (by decide)))))

/-- The square from `MontFn.bases`' registers. -/
theorem sqBody_ok (s : State) (h : SqEnv s.mem base size out a mod M n inv s)
    (p6 : s.gpr .r6 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n)
    (p8 : s.gpr .r8 = base + BitVec.ofNat 32 a) (p10 : s.gpr .r10 = base + BitVec.ofNat 32 out) :
    WP isa sqBody s fun t =>
      val32 t.mem (State.addr base) out n < val32 s.mem (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 s.mem (State.addr base) mod n =
        val32 s.mem (State.addr base) a n * val32 s.mem (State.addr base) a n %
          val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [sqBody, WP.seq_iff]
  refine WP.mono (sqInit_ok s h p6 p7 p8 p10) ?_
  rintro s1 ⟨h1, r1⟩
  rw [WP.seq_iff]
  refine WP.mono (crossRows_ok s1 h1) ?_
  rintro s2 ⟨h2, r2⟩
  rw [WP.seq_iff]
  refine WP.mono (sqDouble_ok s2 h2) ?_
  rintro s3 ⟨h3, r3⟩
  rw [WP.seq_iff]
  refine WP.mono (sqDiagPhase_ok s3 h3) ?_
  rintro s4 ⟨h4, r4⟩
  rw [WP.seq_iff]
  refine WP.mono (sqReduce_ok s4 h4) ?_
  rintro s5 ⟨h5, r5⟩
  refine WP.mono (sqFinish_ok s5 h5) ?_
  rintro t ⟨lt, value, outs, r6⟩
  refine ⟨lt, value, ?_, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))⟩
  exact (h5.env.frame.mono (by simp)).trans outs

end

end VG.Proof.Bignum.Arm
