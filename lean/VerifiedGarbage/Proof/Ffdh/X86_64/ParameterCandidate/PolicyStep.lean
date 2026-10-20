module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundBodyCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundRun
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundBody

/-! # FFDH parameter generation on x86-64: public state after a policy iteration -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

def PolicyPublic.sample (d : PolicyPublic) : Option Nat := (Spec.Ffdh.drawWitness d.p.N d.bs).map Prod.fst

def PolicyAfter (d : PolicyPublic) (s : State) : Prop :=
  ∃ n, n ≤ d.bs.length ∧ DrawState d.p (off d.rp n) (d.used + n) (d.bs.drop n) s ∧
    word s.mem d.p.O (8 * oStatus) = BitVec.ofNat 64 (runStatus d.p d.i d.checks d.sample) ∧
    word s.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 (runIndex d.p d.i d.sample) ∧
    (∀ a rest, Spec.Ffdh.drawWitness d.p.N d.bs = some (a, rest) → rest = d.bs.drop n) ∧
    s.zf = some (decide (runStatus d.p d.i d.checks d.sample = 4)) ∧
    word s.mem d.p.O (8 * oChecks) = BitVec.ofNat 64 d.checks ∧ s.gpr .rsp = d.sp ∧
    s.wr = d.wr ∧ InnerKW d.p.O d.wr ∧ RoundRoom d.p (off d.rp n) (d.bs.drop n) s

theorem policy_after (M : Mont) (K : Kernel) (d : PolicyPublic) (s : State) (h : PolicyBefore d s) :
    WP isa (roundBody M.mm K.run) s (PolicyAfter d) := by
  obtain ⟨hd, hroom, hsp, hi, hc, hi32, hc32⟩ := h
  refine WP.mono (roundBody_ok M K hd.1 hroom hi hc hi32 hc32)
    fun t ⟨n, hn, ht, hs, hidx, hrest, hz, hsave, _, k⟩ => ?_
  exact ⟨n, hn, ht, hs, hidx, hrest, hz,
    (hsave _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc,
    (k.gpr (by decide)).trans hsp, k.2.2.trans hd.2.1, hd.2.2, hroom.after_draw k (by decide) n⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
