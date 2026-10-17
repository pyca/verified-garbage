module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawBody
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: the terminating rejection loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def DrawPost (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (s t : State) : Prop :=
  ∃ n, n ≤ bs.length ∧ DrawState p (off rp n) (used + n) (bs.drop n) t ∧
    (match Spec.Ffdh.drawWitness p.N bs with
      | none => word t.mem p.O (8 * oStatus) = 0
      | some (a, rest) => word t.mem p.O (8 * oStatus) = 1 ∧ rest = bs.drop n ∧
          wv t.mem p.I (slot p.w aXm) p.w = a) ∧
    t.zf = some false ∧ DrawSaved p s.mem t.mem ∧ DrawFrame p s.mem t.mem ∧ Keep mmRegs s t

private theorem draw_equation (p : WitnessParams) (bs : List Byte) :
    Spec.Ffdh.drawWitness p.N bs =
      if p.len ≤ bs.length then
        if 2 ≤ drawValue p bs ∧ drawValue p bs < p.N - 1
          then some (drawValue p bs, bs.drop p.len)
          else Spec.Ffdh.drawWitness p.N (bs.drop p.len)
      else none := by
  rw [VG.Proof.Ffdh.ParameterCandidate.drawWitness_eq (by
    rw [p.octets]; omega_using [p.width_bounds.2.2.1])]
  simp only [p.octets, p.predBits, drawValue]
  rfl

/-- Every retry consumes a positive number of bytes. Accepted witnesses,
exhaustion, and the exact consumed count agree with the octet-tape spec. -/
theorem drawWitness_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) : WP isa drawWitness s (DrawPost p rp used bs s) := by
  induction bs using (measure List.length).wf.induction generalizing rp used s with
  | h bs ih =>
    obtain ⟨trace, u, he, hstep, hs, hf, k⟩ := drawBody_ok h
    have hspec := draw_equation p bs
    by_cases havail : p.len ≤ bs.length
    · simp only [ite_eq_left havail] at hstep
      obtain ⟨hu, hx, hz, hstatus⟩ := hstep
      by_cases ha : 2 ≤ drawValue p bs ∧ drawValue p bs < p.N - 1
      · have hspec' : Spec.Ffdh.drawWitness p.N bs = some (drawValue p bs, bs.drop p.len) := by
          simpa only [ite_eq_left havail, ite_eq_left ha] using hspec
        have hzf : u.zf = some false := by simpa [ha] using hz
        refine ⟨_, u, Exec.loopExit he (by simp only [eval, hzf]), p.len, havail, hu, ?_, hzf, hs, hf, k⟩
        rw [hspec']
        exact ⟨hstatus, rfl, hx⟩
      · have hdrop : (bs.drop p.len).length < bs.length := by
          rw [List.length_drop]
          omega_using [havail, p.width_bounds.2.2.1]
        have hspec' : Spec.Ffdh.drawWitness p.N bs = Spec.Ffdh.drawWitness p.N (bs.drop p.len) := by
          simpa only [ite_eq_left havail, ite_eq_right ha] using hspec
        obtain ⟨trace', t, he', n, hn, ht, hr, hzt, hs', hf', k'⟩ := ih _ hdrop hu
        have hzf : isa.eval .e u = some true := by simp only [eval, hz, ha, decide_false, Bool.not_false]
        refine ⟨_, t, Exec.loopNext he hzf he', p.len + n, ?_, ?_, ?_, hzt, hs.trans hs', hf.trans hf',
          (k.trans k').mono (by decide)⟩
        · rw [List.length_drop] at hn
          omega_using [hn, havail]
        · simpa only [off_off, Nat.add_assoc, List.drop_drop] using ht
        · rw [hspec']
          simpa only [List.drop_drop] using hr
    · simp only [ite_eq_right havail] at hstep
      obtain ⟨hu, hz, hstatus⟩ := hstep
      have hspec' : Spec.Ffdh.drawWitness p.N bs = none := by simpa only [ite_eq_right havail] using hspec
      refine ⟨_, u, Exec.loopExit he (by simp only [eval, hz]), 0, by omega, ?_, ?_, hz, hs, hf, k⟩
      · simpa [off] using hu
      · rw [hspec']; exact hstatus

end VG.Proof.Ffdh.X86_64.ParameterCandidate
