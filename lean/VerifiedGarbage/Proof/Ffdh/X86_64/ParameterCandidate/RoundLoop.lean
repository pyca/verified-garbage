module

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundBody
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundRun
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: the uniform Miller–Rabin policy loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

def RoundsPost (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (n : Nat) (s t : State) : Prop :=
  ∃ consumed, consumed ≤ bs.length ∧ DrawState p (off rp consumed) (used + consumed) (bs.drop consumed) t ∧
    (match checkWitnesses p.N n bs with
      | none => word t.mem p.O (8 * oStatus) = 0
      | some (pass, rest) => word t.mem p.O (8 * oStatus) = BitVec.ofNat 64 (if pass then 1 else 2) ∧
          rest = bs.drop consumed) ∧
    RoundSaved p s.mem t.mem ∧ RoundFrame p (s.gpr .rsp) s.mem t.mem ∧ Keep mmRegs s t

/-- The counter advances only on accepted passing witnesses, and the first
composite witness or exhausted tape terminates the policy immediately. -/
theorem roundsLoop_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used i checks n : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hi : word s.mem p.O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hpos : 0 < n) (hcount : i + n = checks) (hc32 : checks < 2 ^ 31) :
    WP isa (.loop (roundBody M.mm K.run) .e) s (RoundsPost p rp used bs n s) := by
  induction n generalizing i rp used bs s with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, u, he, consumed, hcons, hu, hstatus, hindex, hrest, hz, hs, hf, k⟩ :=
      roundBody_ok M K h hroom hi hc (by omega_using [hcount, hc32]) hc32
    have hcu : word u.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks :=
      (hs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
    cases hdraw : Spec.Ffdh.drawWitness p.N bs with
    | none =>
      simp only [hdraw, Option.map_none, runStatus, runIndex] at hstatus hindex hz
      have hz' : isa.eval .e u = some false := by simpa [eval] using hz
      refine ⟨_, u, Exec.loopExit he hz', consumed, hcons, hu, ?_, hs, hf, k⟩
      simpa [checkWitnesses, hdraw] using hstatus
    | some ar =>
      obtain ⟨a, rest⟩ := ar
      have htail := hrest a rest hdraw
      simp only [hdraw, Option.map_some, runStatus, runIndex] at hstatus hindex hz
      by_cases hm : Spec.Ffdh.mrRound p.N a = true
      · simp only [hm, ↓reduceIte] at hstatus hindex hz
        by_cases hn : 0 < n
        · have hmore : i + 1 < checks := by omega_using [hcount, hn]
          have hstatus4 : passStatus i checks = 4 := by simp only [passStatus, ite_eq_left hmore]
          have hz' : isa.eval .e u = some true := by
            simpa only [eval, hstatus4, decide_true] using hz
          obtain ⟨trace', t, he', consumed', hcons', ht, hr, hs', hf', k'⟩ :=
            ih hu (hroom.after_draw k (by decide) consumed) hindex hcu hn (by omega_using [hcount])
          have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
          rw [hsp] at hf'
          refine ⟨_, t, Exec.loopNext he hz' he', consumed + consumed', ?_, ?_, ?_, hs.trans hs', hf.trans hf',
            (k.trans k').mono (by decide)⟩
          · rw [List.length_drop] at hcons'
            omega_using [hcons, hcons']
          · simpa only [off_off, Nat.add_assoc, List.drop_drop] using ht
          · have hcheck : checkWitnesses p.N (n + 1) bs = checkWitnesses p.N n (bs.drop consumed) := by
              simp [checkWitnesses, hdraw, hm, htail]
            rw [hcheck]
            simpa only [List.drop_drop] using hr
        · have hn0 : n = 0 := by omega
          subst hn0
          have hlast : ¬i + 1 < checks := by omega_using [hcount]
          have hstatus1 : passStatus i checks = 1 := by simp only [passStatus, ite_eq_right hlast]
          have hz' : isa.eval .e u = some false := by simpa [eval, hstatus1] using hz
          refine ⟨_, u, Exec.loopExit he hz', consumed, hcons, hu, ?_, hs, hf, k⟩
          have hcheck : checkWitnesses p.N 1 bs = some (true, rest) := by simp [checkWitnesses, hdraw, hm]
          rw [hcheck]
          exact ⟨by simpa only [hstatus1, ite_true] using hstatus, htail⟩
      · have hmf : Spec.Ffdh.mrRound p.N a = false := Bool.eq_false_iff.mpr hm
        simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hstatus hindex hz
        have hz' : isa.eval .e u = some false := by simpa [eval] using hz
        refine ⟨_, u, Exec.loopExit he hz', consumed, hcons, hu, ?_, hs, hf, k⟩
        have hcheck : checkWitnesses p.N (n + 1) bs = some (false, rest) := by simp [checkWitnesses, hdraw, hmf]
        rw [hcheck]
        exact ⟨hstatus, htail⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
