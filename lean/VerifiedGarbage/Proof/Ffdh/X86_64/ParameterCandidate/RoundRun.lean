module
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundStatus

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResult
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: run only an accepted witness -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def runStatus (p : WitnessParams) (i checks : Nat) : Option Nat → Nat
  | none => 0
  | some a => if Spec.Ffdh.mrRound p.N a then passStatus i checks else 2

def runIndex (p : WitnessParams) (i : Nat) : Option Nat → Nat
  | none => i
  | some a => if Spec.Ffdh.mrRound p.N a then i + 1 else i

theorem runStatus_bound (p : WitnessParams) (i checks : Nat) (sample : Option Nat) :
    runStatus p i checks sample ≤ 4 := by
  cases sample with
  | none => change 0 ≤ 4; omega
  | some a =>
    change (if Spec.Ffdh.mrRound p.N a then (if i + 1 < checks then 4 else 1) else 2) ≤ 4
    split
    · split <;> omega
    · omega

theorem roundRun_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used i checks : Nat} {sample : Option Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hi : word s.mem p.O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hi32 : i < 2 ^ 31) (hc32 : checks < 2 ^ 31)
    (hsample : match sample with
      | none => word s.mem p.O (8 * oStatus) = 0
      | some a => word s.mem p.O (8 * oStatus) = 1 ∧ wv s.mem p.I (slot p.w aXm) p.w = a) :
    WP isa (roundRun M.mm K.run) s fun t => DrawState p rp used bs t ∧
      word t.mem p.O (8 * oStatus) = BitVec.ofNat 64 (runStatus p i checks sample) ∧
      word t.mem p.O (8 * oIndex) = BitVec.ofNat 64 (runIndex p i sample) ∧
      RoundSaved p s.mem t.mem ∧ RoundFrame p (s.gpr .rsp) s.mem t.mem ∧ Keep mmRegs s t := by
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  unfold roundRun
  cases sample with
  | none =>
    refine WP.seq (WP.mono (statusTest_ok h.ready.good.scr p.space_bounds.2.1 houter h.ready.good.rdi
      h.link hsample (by decide : 0 < 2 ^ 64)) fun u ⟨hz, hm, k⟩ => ?_)
    have hu := h.same_mem hm k ((k.gpr (by decide)).trans h.ready.good.rdi)
    refine WP.ite true (by simp only [eval, hz, decide_true]) (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨hu, ?_, ?_, ?_, ?_, k.mono (by decide)⟩
    · rw [hm]; exact hsample
    · rw [hm]; exact hi
    · rw [hm]; exact RoundSaved.refl _ _
    · rw [hm]; exact RoundFrame.refl _ _ _
  | some a =>
    refine WP.seq (WP.mono (statusTest_ok h.ready.good.scr p.space_bounds.2.1 houter h.ready.good.rdi
      h.link hsample.1 (by decide : 1 < 2 ^ 64)) fun u ⟨hz, hm, k⟩ => ?_)
    have hu := h.same_mem hm k ((k.gpr (by decide)).trans h.ready.good.rdi)
    have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
    refine WP.ite false (by simp only [eval, hz, show ¬(1 : Nat) = 0 by decide, decide_false]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (witnessRound_state_ok M K (a := a) hu (hroom.congr hsp)
      (by rw [hm]; exact hsample.2)) fun v ⟨hv, hflag, hh, hf, kv⟩ => ?_)
    have hiv : word v.mem p.O (8 * oIndex) = BitVec.ofNat 64 i := by
      rw [hh _ (by decide), hm]; exact hi
    have hcv : word v.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks := by
      rw [hh _ (by decide), hm]; exact hc
    refine WP.mono (roundResult_ok hv hflag hiv hcv hi32 hc32) fun t ⟨ht, hstatus, hindex, hsaved, hframe, kt⟩ => ?_
    refine ⟨ht, hstatus, hindex, ?_, ?_, ((k.trans kv).trans kt).mono (by decide)⟩
    · intro j hj h12 h13 h14 h18 h19
      rw [hsaved j hj h12 h13 h14 h18 h19, hh j hj, hm]
    · simpa only [hm, hsp] using hf.trans hframe.round

end VG.Proof.Ffdh.X86_64.ParameterCandidate
