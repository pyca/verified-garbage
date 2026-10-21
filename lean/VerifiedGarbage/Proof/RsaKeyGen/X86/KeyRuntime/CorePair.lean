module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrepareTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Prepare
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Two secret factor pairs reach the retry comparison with the same public state -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

structure CoreStart (B : Addr) (Z n k e p q : Nat) (s : State) : Prop extends Preparation B Z n k e s where
  pValue : num s.mem B n aPa = p
  qValue : num s.mem B n aQa = q

structure ReadyPair (B : Addr) (Z n e p q p' q' : Nat) (s t : State) : Prop where
  left : Ws s B Z n 32
  right : Ws t B Z n 32
  agree : VG.X86.Taint.Agree runtimeTaint s t
  leftReady : KeyReady B n e p q s.mem
  rightReady : KeyReady B n e p' q' t.mem

theorem prepareReady_trace (B : Addr) (Z n k e p q p' q' : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
      VG.X86.Taint.Agree runtimeTaint s t)
      prepareLoaded (ReadyPair B Z n e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨Ps, Pt, agree⟩ := P
  obtain ⟨trace, finalAgree⟩ := prepareLoaded_trace B Z n k e width positive even
    _ _ _ _ _ _ ⟨Ps.toPreparation, Pt.toPreparation, agree⟩ A C
  obtain ⟨leftWs, _, leftReady, _⟩ := wp_result
    (prepareLoaded_ok Ps.workspace width positive even Ps.pBound Ps.qBound Ps.zero Ps.one
      (Ps.loaded.trans Ps.exponent.symm)) A
  obtain ⟨rightWs, _, rightReady, _⟩ := wp_result
    (prepareLoaded_ok Pt.workspace width positive even Pt.pBound Pt.qBound Pt.zero Pt.one
      (Pt.loaded.trans Pt.exponent.symm)) C
  rw [Ps.exponent, Ps.pValue, Ps.qValue] at leftReady
  rw [Pt.exponent, Pt.pValue, Pt.qValue] at rightReady
  exact ⟨trace, leftWs, rightWs, finalAgree, leftReady, rightReady⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
