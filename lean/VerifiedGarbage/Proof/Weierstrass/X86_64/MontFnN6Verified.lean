module

import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN6
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnN6
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified
import VerifiedGarbage.Impl.Weierstrass.Slots
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Impl.Weierstrass.Slots
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Mont.X86_64.Blocks
meta import VerifiedGarbage.Proof.Mont.X86_64.CsubS
meta import VerifiedGarbage.Proof.Mont.X86_64.Friendly
meta import VerifiedGarbage.Proof.Mont.X86_64.Round
meta import VerifiedGarbage.Proof.Mont.X86_64.Sparse
meta import VerifiedGarbage.Proof.Mont.X86_64.SparseX
meta import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Mont.X86_64.WideOps
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnB
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# P-384's product modulo `n` as a function, on x86-64: verified

`p384n.mulContract` on x86-64, by register (`mulX64`), which `mulFnN6`
meets with or without BMI2 and ADX (`mulFnN6_x64`, from `mulFnN6_ok`: the
offsets `Fit`, below byte 3712, are apart from `n` and the function's
temporary area, bytes 4000 to 4095), constant time by taint tracking (only
the stack pointer, `ws` and the offsets' low halves are public, `o` kept in
`xmm6` meanwhile), and a state satisfying it (`mul_implies`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus p384n)

theorem p384n_m : p384n.m = n384 := by decide +kernel

theorem p384n_R : p384n.R = (2 ^ 64) ^ 6 :=
  (Nat.pow_mul 2 64 p384n.k).trans (congrArg (HPow.hPow (2 ^ 64)) (show p384n.k = 6 from rfl))

/-- The contract, from `mulFnN6_ok`. -/
theorem mulFnN6_x64 (adx : Bool) (s : State) (hs : (mulX64 p384n).pre s) :
    ∃ t s', Exec isa (mulFnN6 adx) s t s' ∧ abiPreserved s s' ∧ (mulX64 p384n).post s s' := by
  obtain ⟨⟨hrd, hwr, hret, hnw, ho, ha, hb⟩, hB⟩ := hs
  have hscr : Scr s (s.gpr .rdi) 8192 := ⟨rfl, by rw [hwr]; simp, hnw⟩
  simp only [Impl.Weierstrass.Mont.Fits, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes,
    p384n] at ho ha hb
  suffices hwp : WP isa (mulFnN6 adx) s fun s' => gprPreserved s s' ∧ (mulX64 p384n).post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by cases adx <;> decide +kernel) he hg, hp⟩
  simp only [argNum, numAt_eq] at hB
  have arg : ∀ x, x + 8 * 6 ≤ 4096 - 64 * 6 → ArgN6 8192 x := fun x hx =>
    ⟨.inl (by rw [fnTmp6_eq]; omega), by omega⟩
  rw [p384n_m] at hB
  refine WP.mono (mulFnN6_ok adx hscr (by decide) (arg _ ho) (arg _ ha) (arg _ hb) hB)
    fun s' ⟨hlt, heq, k, hmem⟩ => ?_
  refine ⟨⟨fun r hr => k.gpr r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩,
    by simp only [argNum, numAt_eq, p384n_m]; exact hlt,
    by simp only [argNum, numAt_eq, p384n_R, p384n_m]; exact heq, ?_⟩
  · refine Mem.readW_congr fun i hi => hmem _ (Or.inr ?_) (Or.inr ?_) <;>
    · have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      simp only [Region.Contains, Nat.not_le] at hx
      simp only [ofs, argOf]; omega
  · intro i hi hown ho'
    have e1 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
    have e2 : Impl.Weierstrass.Mont.ownAt p384n.k = 3712 := rfl
    have e4 : p384n.k = 6 := rfl
    rw [e1] at hi
    rw [e2] at hown
    rw [e4] at ho'
    have h64 : i < 2 ^ 64 := by omega
    refine hmem _ ?_ ?_
    · rw [ofs_off0 _ h64]; exact ho'
    · rw [ofs_off0 _ h64, fnTmp6_eq]; omega

theorem mulFnN6_ct (adx : Bool) : ConstantTime isa (mulX64 p384n).pre (mulX64 p384n).pub (mulFnN6 adx) := by
  cases adx
  · exact ct_zext (M := p384n) (fun _ h => h.1)
      (VG.Taint.constantTime (A := X86_64.taint) τ₁ (fun _ _ _ _ h => h) (by taint_decide))
  · exact ct_zext (M := p384n) (fun _ h => h.1)
      (VG.Taint.constantTime (A := X86_64.taint) τ₁ (fun _ _ _ _ h => h) (by taint_decide))

/-- `vg_p384_mul_mod_n` (`adx` false) and `vg_p384_mul_mod_n_adx` on x86-64. -/
theorem p384n_mul_verified (adx : Bool) : Verified X86_64.target (mulFnN6 adx) (p384n.mulContract X86_64.abi) :=
  Verified.of_correct (mulFnN6_x64 adx) (mulFnN6_ct adx) (mul_implies p384n (by decide) (by decide +kernel))

end VG.Proof.Weierstrass.X86_64.Mont
