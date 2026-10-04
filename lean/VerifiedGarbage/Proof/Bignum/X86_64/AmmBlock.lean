import VerifiedGarbage.Proof.Bignum.X86_64.AmmLane

/-!
# RSA with AVX512_IFMA on x86-64: a step on the machine

`ammStep_ok`: from a state with `StepIn`, the code of step `i` leaves in
role `k`'s lanes at step `i + 1` the limbs of `Amm52.step`, register 14
still zero, and changes nothing but the vector registers and `rax`.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 ammStep)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

theorem xi_xr : ∀ r < 16, xi (xr r) = r := by decide

theorem regOf_lt {p k i : Nat} (hp : p < 2) : regOf p k i < 10 := by unfold regOf; omega

theorem expReg_regOf {p kk i : Nat} (hp : p < 2) (hk : kk < 5) :
    expReg i (regOf p kk (i + 1)) = hT p kk i := by
  have hr := regOf_lt (k := kk) (i := i + 1) hp
  simp only [expReg, hr, ite_true]
  congr 1
  · unfold regOf; omega
  · unfold roleOf regOf; omega

/-- What a step keeps: everything but the vector registers and `rax`. -/
structure Keeps (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.mxcsr.trans h₁.mxcsr,
    ⟨h₂.flags.1.trans h₁.flags.1, h₂.flags.2.1.trans h₁.flags.2.1, h₂.flags.2.2.1.trans h₁.flags.2.2.1,
      h₂.flags.2.2.2.trans h₁.flags.2.2.2⟩⟩

theorem ammStep_ok {s : State} {i : Nat} (hi : i < 5) {L a m : Nat → Nat → Nat} {k b : Nat → Nat}
    (h : StepIn s i L a m k b) (hc : Ctx lim s) :
    WP isa (.block (ammStep i)) s fun s' =>
      (∀ p < 2, ∀ kk < 5, ∀ t < 4, qw s' (xr (regOf p kk (i + 1))) t =
        BitVec.ofNat 64 (step (ops a m k p) (L p) (b p) (kk + 5 * t))) ∧
      (∀ t < 4, qw s' .xmm14 t = 0) ∧ Keeps s s' := by
  obtain ⟨σ, e, hσ⟩ := run_ammStep hi
  refine WP.mono (run_ok hc e) fun s' hs => ⟨fun p hp kk hk t ht => ?_, fun t ht => ?_, ?_⟩
  · have hr := regOf_lt (k := kk) (i := i + 1) hp
    rw [hs.reg _ t ht, xi_xr _ (by omega), hσ _ (by omega), expReg_regOf hp hk]
    exact hT_eval h hp hk ht
  · rw [hs.reg _ t ht, show xi .xmm14 = 14 from rfl, hσ 14 (by decide)]
    simp only [expReg, show ¬ (14 : Nat) < 10 by decide, ite_false, show (14 : Nat) ≠ 10 by decide,
      show (14 : Nat) ≠ 11 by decide, show (14 : Nat) ≠ 12 by decide, show (14 : Nat) ≠ 13 by decide,
      show (14 : Nat) ≠ 15 by decide, A.eval]
    exact h.z t ht
  · exact ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩

end VG.Proof.Bignum.X86_64.AmmSym
