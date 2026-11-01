module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialPair
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint two_map two_ite)
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)

structure PairData where
  dst : BitVec 32
  base : BitVec 32
  bytes : List Byte

structure PairTrialsStart (p : PairData × Nat) (s : State) : Prop where
  context : SieveContext p.1.dst p.1.base p.1.bytes.length s
  index : p.2<trialCount p.1.bytes.length
  cursor : s.gpr .r10=p.1.base+BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt ((p.1.bytes.length+7)/8) 34+4*p.2)
  bytes : Spec.Rsa.bytesAt s.mem (State.addr p.1.dst) p.1.bytes.length=p.1.bytes

private structure PrimeReady (p : PairData × Nat) (s : State) : Prop where
  start : PairTrialsStart p s
  prime : s.gpr .r7=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry p.2)

private def trialData (p : PairData × Nat) : TrialData :=
  ⟨p.1.dst,p.1.bytes.length,BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry p.2),p.1.bytes.reverse⟩

private theorem prime_trialState (p : PairData × Nat) (s : State) (h : PrimeReady p s) :
    TrialState (trialData p) s := by
  have buffers := trialBuffers_of_octets (prime:=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry p.2))
    h.start.context.read rfl h.start.bytes
  exact ⟨buffers.1,h.prime,buffers.2⟩

private theorem entry_ready (p : PairData × Nat) (s : State) (h : PairTrialsStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.pairEntry) s (PrimeReady p) := by
  refine WP.mono (pairEntry_ok h.context h.index h.cursor) ?_
  rintro t ⟨⟨prime,memory⟩,rest⟩
  exact ⟨⟨h.context.after_memory memory rest,h.index,(rest.gpr .r10 (by simp)).trans h.cursor,
    by rw [memory]; exact h.bytes⟩,prime⟩

private theorem pairEntry_taint : ∃ hint, (VG.Taint.check taint (Taint.ofRegs [.r10])
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.pairEntry) hint).isSome=true := ⟨_,by taint_decide⟩

theorem pairTrials_ct : RelCT isa (Two PairTrialsStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials (fun _ _ => True) := by
  obtain ⟨hint,checked⟩ := pairEntry_taint
  have entryTrace : RelCT isa (Two PairTrialsStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.pairEntry) (fun _ _ => True) := by
    refine two_taint [.r10] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.cursor.trans b.cursor.symm
  have entry : RelCT isa (Two PairTrialsStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.pairEntry) (Two PrimeReady) :=
    two_post entryTrace entry_ready
  have trials : RelCT isa (Two PrimeReady) VG.Impl.Ffdh.Arm.ParameterCandidate.trialPair
      (fun _ _ => True) :=
    (two_map trialData prime_trialState trialPair_ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact entry.seq trials

end VG.Proof.Ffdh.Arm.ParameterCandidate
