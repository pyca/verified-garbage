module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialSmall
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialOffset
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
  cursor : s.gpr .r10=p.1.base+BitVec.ofNat 32 (Spec.Rsa.Mont.arrAt ((p.1.bytes.length+7)/8) 34+4*p.2)
  bytes : Spec.Rsa.bytesAt s.mem (State.addr p.1.dst) p.1.bytes.length=p.1.bytes

private structure PrimeReady (p : PairData × Nat) (s : State) : Prop where
  start : PairTrialsStart p s
  prime : s.gpr .r7=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry p.2)

private structure PairDivided (p : PairData × Nat) (s : State) : Prop where
  start : PairTrialsStart p s
  zero : s.z=decide (Spec.Rsa.os2ip p.1.bytes%VG.Impl.RsaKeyGen.tabEntry p.2=0)

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
  have normalTrace : RelCT isa (Two PrimeReady) VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall
      (fun _ _ => True) :=
    (two_map trialData prime_trialState trialSmall_ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  have normal : RelCT isa (Two PrimeReady) VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall (Two PairDivided) := by
    refine two_post normalTrace ?_
    intro p s h
    have ctx := h.start.context
    refine WP.mono (trialSmall_ok s p.1.dst ctx.read.positive ctx.read.countFits ctx.read.bufferFits
      (by have := h.start.index; have := trialCount_bound p.1.bytes.length; omega : p.2<1024)
      h.prime (ctx.read.frame.read (by decide)) (ctx.read.frame.read (by decide))
      ctx.read.out ctx.read.width ctx.read.readable) ?_
    rintro t ⟨flag,memory,rest⟩
    refine ⟨⟨ctx.after_memory memory rest,h.start.index,
      (rest.gpr .r10 (by simp)).trans h.start.cursor,by rw [memory]; exact h.start.bytes⟩,?_⟩
    rwa [h.start.bytes] at flag
  have offset : RelCT isa (Two PrimeReady) VG.Impl.Ffdh.Arm.ParameterCandidate.trialOffset
      (fun _ _ => True) :=
    (two_map trialData prime_trialState trialOffset_ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  have branch : RelCT isa (Two PairDivided)
      (.ite .eq (.block []) (.seq (.block VG.Impl.Ffdh.Arm.ParameterCandidate.pairEntry)
        VG.Impl.Ffdh.Arm.ParameterCandidate.trialOffset)) (fun _ _ => True) := by
    refine two_ite ?_ (RelCT.block_nil (fun _ _ _ => trivial)) ?_
    · intro p s t a b
      change some s.z=some t.z
      rw [a.zero,b.zero]
    · exact (entry.seq offset).mono
        (fun _ _ ⟨p,a,b,sp⟩ => ⟨p,a.1.start,b.1.start,sp⟩) (fun _ _ _ => trivial)
  exact entry.seq (normal.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
