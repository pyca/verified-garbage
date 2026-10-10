import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFn6
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnXVerified

/-!
# P-384's product modulo `p` as a function, on x86-64: verified

`p384p.mulContract` on x86-64, by register (`mulX64`), which `mulFn6`
meets with or without BMI2 and ADX (`mulFn6_x64`, from `mulFn6_ok`: the
offsets `Fit`, below byte 3712, are apart from the function's temporary area,
bytes 4048 to 4095), constant time by taint tracking (only the stack pointer,
`ws` and the offsets' low halves are public, `o` kept in `xmm6`
meanwhile, for a product), and a state satisfying it (`mul_implies`).
-/

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Spec.Weierstrass.Mont (numAt Keeps Modulus p384p)

theorem p384p_m : p384p.m = p384 := by decide +kernel

theorem p384p_R : p384p.R = (2 ^ 64) ^ 6 :=
  (Nat.pow_mul 2 64 p384p.k).trans (congrArg (HPow.hPow (2 ^ 64)) (show p384p.k = 6 from rfl))

/-- The contract, from `mulFn6_ok`. -/
theorem mulFn6_x64 (adx : Bool) (s : State) (hs : (mulX64 p384p).pre s) :
    ∃ t s', Exec isa (mulFn6 adx) s t s' ∧ abiPreserved s s' ∧ (mulX64 p384p).post s s' := by
  obtain ⟨⟨hrd, hwr, hret, hnw, ho, ha, hb⟩, hB⟩ := hs
  have hscr : Scr s (s.gpr .rdi) 8192 := ⟨rfl, by rw [hwr]; simp, hnw⟩
  simp only [Spec.Weierstrass.Mont.Fits, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes,
    p384p] at ho ha hb
  suffices hwp : WP isa (mulFn6 adx) s fun s' => gprPreserved s s' ∧ (mulX64 p384p).post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by cases adx <;> decide +kernel) he hg, hp⟩
  simp only [argNum, numAt_eq] at hB
  have arg : ∀ x, x + 8 * 6 ≤ 4096 - 64 * 6 → Arg6 8192 x := fun x hx =>
    ⟨.inl (by rw [fnTmp6_eq]; omega), by omega⟩
  refine WP.mono (mulFn6_ok adx hscr (by decide) p384p_m (arg _ ho) (arg _ ha) (arg _ hb) hB)
    fun s' ⟨hlt, heq, k, hmem⟩ => ?_
  refine ⟨⟨fun r hr => k.gpr r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩,
    by simp only [argNum, numAt_eq]; exact hlt, by simp only [argNum, numAt_eq, p384p_R]; exact heq, ?_⟩
  · refine Mem.readW_congr fun i hi => hmem _ (Or.inr ?_) (Or.inr ?_) <;>
    · have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      simp only [Region.Contains, Nat.not_le] at hx
      simp only [ofs, argOf]; omega
  · intro i hi hown ho'
    have e1 : Spec.Weierstrass.Mont.wsBytes = 8192 := rfl
    have e2 : Spec.Weierstrass.Mont.ownAt p384p.k = 3712 := rfl
    have e4 : p384p.k = 6 := rfl
    rw [e1] at hi
    rw [e2] at hown
    rw [e4] at ho'
    have h64 : i < 2 ^ 64 := by omega
    refine hmem _ ?_ ?_
    · rw [ofs_off0 _ h64]; exact ho'
    · rw [ofs_off0 _ h64, fnTmp6_eq]; omega

theorem mulFn6_ct (adx : Bool) : ConstantTime isa (mulX64 p384p).pre (mulX64 p384p).pub (mulFn6 adx) := by
  cases adx
  · exact ct_zext (M := p384p) (fun _ h => h.1)
      (VG.Taint.constantTime (A := X86_64.taint) τ₁ (fun _ _ _ _ h => h) (by taint_decide))
  · exact ct_zext (M := p384p) (fun _ h => h.1)
      (VG.Taint.constantTime (A := X86_64.taint) τ₁ (fun _ _ _ _ h => h) (by taint_decide))

/-- `vg_p384_mul_mod_p` (`adx` false) and `vg_p384_mul_mod_p_adx` on x86-64. -/
theorem p384p_mul_verified (adx : Bool) : Verified X86_64.target (mulFn6 adx) (p384p.mulContract X86_64.abi) :=
  Verified.of_correct (mulFn6_x64 adx) (mulFn6_ct adx) (mul_implies p384p (by decide) (by decide +kernel))

end VG.Proof.Weierstrass.X86_64.Mont
