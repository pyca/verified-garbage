module
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessRange
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont

/-! # FFDH parameter generation on x86-64: timing of the shared prepared round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.RsaKeyGen.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

structure RoundPublic where
  ws : Ws
  N : Nat
  a : Nat
  sp : Addr

def BeforeRound (p : RoundPublic) (s : State) : Prop :=
  ∃ mi, ModulusReady s p.ws.B p.ws.Z p.ws.w mi p.N ∧ MrDims p.ws.B p.ws.Z p.ws.w ∧
    slot p.ws.w 28 ≤ p.ws.Z ∧ Caller.Room s p.ws.B p.ws.Z ∧ s.gpr .rsp = p.sp ∧
    p.N % 2 = 1 ∧ 3 ≤ p.N ∧ wv s.mem p.ws.B (slot p.ws.w aXm) p.ws.w = p.a

private theorem beforeRound_good {p : RoundPublic} {s : State} (h : BeforeRound p s) : GoodW p.ws s := by
  obtain ⟨mi, hr, hd, _⟩ := h
  exact ⟨mi, hr.good, hd.z⟩

private theorem beforeRound_mont (M : Mont) (p : RoundPublic) (s : State) (h : BeforeRound p s) :
    WP isa (M.mm aXm aXm aR2) s (Caller.Before ⟨p.ws, p.sp⟩) := by
  obtain ⟨mi, hr, hd, hz, hroom, hsp, ho, h3, ha⟩ := h
  refine WP.mono (witnessMont_ok M hr hd ho (by omega) ha) fun t ⟨ht, hxm, _, k⟩ => ?_
  have hc : VG.Proof.RsaKeyGen.X86_64.MrCtx t p.ws.B p.ws.Z p.ws.w mi p.N
      (wv t.mem p.ws.B (slot p.ws.w aB) p.ws.w) := ⟨ht.good, ht.inv, ht.n, rfl, ht.r1, ht.rm1⟩
  have hst : t.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨mi, p.N, _, p.a, hc, ht.exponent, hd, hz,
    ⟨by rw [hst]; exact hroom.size, by rw [hst]; exact hroom.disjoint⟩,
    hst.trans hsp, ho, h3, hxm⟩

theorem witnessRound_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two BeforeRound) (witnessRound M.mm K.run) fun _ _ => True := by
  unfold witnessRound
  exact RelCT.seq
    (two_post (two_map RoundPublic.ws (fun _ _ h => beforeRound_good h)
      (M.ct (o := aXm) (a := aXm) (b := aR2) (by unfold MmUse; decide))) (beforeRound_mont M))
    (two_map (fun p : RoundPublic => (⟨p.ws, p.sp⟩ : Caller.Public)) (fun _ _ h => h) K.ct)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
