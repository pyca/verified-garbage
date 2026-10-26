module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundRun
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoop
public import Mathlib.Algebra.Group.Nat.Defs

/-! # FFDH parameter generation on x86-64: one complete uniform primality round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def RoundStep (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (i checks : Nat) (s t : State) : Prop :=
  let sample := (Spec.Ffdh.drawWitness p.N bs).map Prod.fst
  ∃ n, n ≤ bs.length ∧ DrawState p (off rp n) (used + n) (bs.drop n) t ∧
    word t.mem p.O (8 * oStatus) = BitVec.ofNat 64 (runStatus p i checks sample) ∧
    word t.mem p.O (8 * oIndex) = BitVec.ofNat 64 (runIndex p i sample) ∧
    (∀ a rest, Spec.Ffdh.drawWitness p.N bs = some (a, rest) → rest = bs.drop n) ∧
    t.zf = some (decide (runStatus p i checks sample = 4)) ∧
    RoundSaved p s.mem t.mem ∧ RoundFrame p (s.gpr .rsp) s.mem t.mem ∧ Keep mmRegs s t

theorem roundBody_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used i checks : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hi : word s.mem p.O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hi32 : i < 2 ^ 31) (hc32 : checks < 2 ^ 31) :
    WP isa (roundBody M.mm K.run) s (RoundStep p rp used bs i checks s) := by
  unfold roundBody
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (drawWitness_ok h) fun u ⟨n, hn, hu, hres, _, hs, hf, k⟩ => ?_)
  let sample := (Spec.Ffdh.drawWitness p.N bs).map Prod.fst
  have hsample : match sample with
      | none => word u.mem p.O (8 * oStatus) = 0
      | some a => word u.mem p.O (8 * oStatus) = 1 ∧ wv u.mem p.I (slot p.w aXm) p.w = a := by
    cases he : Spec.Ffdh.drawWitness p.N bs with
    | none => simpa only [sample, he, Option.map_none] using hres
    | some ar =>
      obtain ⟨a, rest⟩ := ar
      rw [he] at hres
      simp only [sample, he, Option.map_some]
      exact ⟨hres.1, hres.2.2⟩
  have hrest : ∀ a rest, Spec.Ffdh.drawWitness p.N bs = some (a, rest) → rest = bs.drop n := by
    intro a rest he
    rw [he] at hres
    exact hres.2.1
  have hiu : word u.mem p.O (8 * oIndex) = BitVec.ofNat 64 i :=
    (hs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi
  have hcu : word u.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks :=
    (hs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
  have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.seq (WP.mono (roundRun_ok M K hu (hroom.after_draw k (by decide) n) hiu hcu hi32 hc32 hsample)
    fun v ⟨hv, hstatus, hindex, hs', hf', kv⟩ => ?_)
  have houter : Scr v p.O 256 := by
    simpa [off] using hv.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  refine WP.mono (statusMore_ok hv.ready.good.scr p.space_bounds.2.1 houter hv.ready.good.rdi hv.link hstatus
    (by omega_using [runStatus_bound p i checks sample])) fun t ⟨hz, hm, kt⟩ => ?_
  refine ⟨n, hn, hv.same_mem hm kt ((kt.gpr (by decide)).trans hv.ready.good.rdi), ?_, ?_, hrest, hz,
    ?_, ?_, ((k.trans kv).trans kt).mono (by decide)⟩
  · rw [hm]; exact hstatus
  · rw [hm]; exact hindex
  · rw [hm]; exact hs.round.trans hs'
  · rw [hm]
    rw [hsp] at hf'
    exact hf.round.trans hf'

end VG.Proof.Ffdh.X86_64.ParameterCandidate
