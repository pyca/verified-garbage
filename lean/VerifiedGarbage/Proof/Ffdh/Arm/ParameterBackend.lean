module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Ffdh.SievedCandidate
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePre
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateResult
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLimitedResult
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResult
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateCount
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessStep
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLocal
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateStart
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSat
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairInit
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTScreenedTests
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateQOdd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTQOdd
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream
import Mathlib.Data.Option.Basic
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateHalve
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! ### `Ffdh.Arm.ParameterCandidate.CTResidueLow`, which only this module used -/

section

/-! The generator-two low-octet prefilter reads one public candidate address. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

private def LowPointers (p : BitVec 32 × Nat) (s : State) : Prop :=
  s.gpr .r4 = p.1 ∧ s.gpr .r5 = BitVec.ofNat 32 p.2

private theorem residueLow_tail_taint : ∃ hint, (VG.Taint.check taint (Taint.ofRegs [.r4, .r5])
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow.drop 2)) hint).isSome = true := ⟨_, by taint_decide⟩

theorem residueLow_ct : RelCT isa (Two fun (p : BitVec 32 × Nat) s => ReadContext p.1 p.2 s)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow) (fun _ _ => True) := by
  have head : RelCT isa (Two fun (p : BitVec 32 × Nat) s => ReadContext p.1 p.2 s)
      (.block [.ldrSp .r4 4, .ldrSp .r5 12]) (Two LowPointers) :=
    two_post ((stackLoads_ct [(.r4, 4), (.r5, 12)]).mono
      (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      have out : s.mem.readW (State.addr (s.sp + 4#32)) 32 = p.1 := h.out
      have width : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 p.2 := h.width
      ffrun [LowPointers, h.frame.read (d := 4) (by decide), h.frame.read (d := 12) (by decide), out, width])
  obtain ⟨hint, checked⟩ := residueLow_tail_taint
  have tail : RelCT isa (Two LowPointers) (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow.drop 2))
      (fun _ _ => True) := by
    refine two_taint [.r4, .r5] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact a.1.trans b.1.symm
    · exact a.2.trans b.2.symm
  exact RelCT.block_append (head.seq tail)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CandidatePairMath`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

def candidateShapes (p : CandidateParams) : Bool :=
  (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) &&
    (Spec.Ffdh.primeShape ((p.candidate-1)/2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate-1)/2))

theorem candidateScreenP_shapes (p : CandidateParams) :
    candidateScreenP p = if candidateShapes p then candidateTests p p.length else candidateRejected p := by
  unfold candidateScreenP candidateScreenQ candidateShapes
  cases (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) <;>
    cases (Spec.Ffdh.primeShape ((p.candidate-1)/2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate-1)/2)) <;> rfl

theorem candidateScreenP_even (p : CandidateParams) (even : ((p.candidate-1)/2)%2=0) :
    candidateScreenP p=candidateRejected p := by
  rw [candidateScreenP_shapes]
  simp only [candidateShapes,even_primeShape even,Bool.false_and,Bool.and_false,Bool.false_eq_true,ite_false]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CandidatePair`, which only this module used -/

section

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PairSieve.lean`, which only this module imported.
section

/-! The paired RSA sieve implements both requested-width p/q screening policies. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem pairLoop_ok {s0 s : State} {dst base : BitVec 32} {n value : Nat}
    (start : PairInv s0 dst base n value 0 s) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep .ne) s (PairInv s0 dst base n value (trialCount n)) := by
  let inv := fun k t => ∃ i, i + k = (trialCount n) ∧ 0 < k ∧ PairInv s0 dst base n value i t
  refine WP.loop (M := isa) inv ?_ (trialCount n) s ⟨0, by omega, trialCount_positive n, start⟩
  intro k t h
  obtain ⟨i, hik, positive, state⟩ := h
  have progress := pairNext_progress (value:=value) (by omega : i < trialCount n)
  refine WP.mono (pairStep_ok state (by omega)) ?_
  rintro u ⟨next, flag⟩
  by_cases last : pairNext n value i = trialCount n
  · left
    refine ⟨?_, last ▸ next⟩
    change some (!u.z) = some false
    simp only [flag, last, decide_true, Bool.not_true]
  · right
    refine ⟨?_, trialCount n-pairNext n value i, by omega,
      pairNext n value i, by omega, by omega, next⟩
    change some (!u.z) = some true
    simp only [flag, last, decide_false, Bool.not_false]

theorem pairSieve_ok {s : State} {dst base : BitVec 32} {n : Nat} (h : SieveContext dst base n s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve s fun t =>
      SieveContext dst base n t ∧
      t.z = !(pairAny (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)) (trialCount n)) ∧
      Frame [sieveLocal s.sp] s.mem t.mem ∧ Rest sieveRegs s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (pairInit_ok h) ?_)
  intro u start
  refine WP.seq (WP.mono (pairLoop_ok start) ?_)
  intro v state
  refine WP.seq (WP.mono (sieveFinish_ok state.context.read.frame.space state.bad) ?_)
  rintro t ⟨⟨flag, memory⟩, rest⟩
  refine WP.block_nil ⟨state.context.after_memory memory rest, flag, ?_,
    state.rest.trans (rest.mono (by simp [sieveRegs]))⟩
  rw [memory]
  exact state.changed

theorem pair_shape_ok {s : State} {dst base : BitVec 32} {n : Nat} (h : SieveContext dst base n s)
    {bits : Nat} (width : n=(bits+7)/8)
    (largeP : 8161<Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n))
    (largeQ : 8161<(Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)-1)/2)
    (oddP : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)%2=1)
    (oddQ : ((Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)-1)/2)%2=1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve s fun t =>
      SieveContext dst base n t ∧
      t.z=((Spec.Ffdh.primeShape (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)) &&
        !Spec.RsaKeyGen.obviouslyComposite bits (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n))) &&
        (Spec.Ffdh.primeShape ((Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)-1)/2) &&
          !Spec.RsaKeyGen.obviouslyComposite bits ((Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)-1)/2))) ∧
      Frame [sieveLocal s.sp] s.mem t.mem ∧ Rest sieveRegs s t := by
  refine WP.mono (pairSieve_ok h) ?_
  rintro t ⟨ctx,flag,changed,rest⟩
  have shape := pair_shape (bits:=bits) largeP largeQ oddP oddQ
  rw [width] at flag shape
  rw [shape] at flag
  simpa only [width] using And.intro ctx (And.intro flag (And.intro changed rest))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidatePair_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (table : TableData p.base p.length s.mem)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate)
    (oddQ : ((p.candidate-1)/2)%2=1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve s fun t =>
      CandidateContext p consumed t ∧ TableData p.base p.length t.mem ∧
      t.z=((Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) &&
        (Spec.Ffdh.primeShape ((p.candidate-1)/2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate-1)/2))) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length ∧
      Frame [⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (pair_shape_ok (h.sieve_context table) (bits:=p.bits) rfl
    (by rw [number]; exact p.sieve_large.1) (by rw [number]; exact p.sieve_large.2)
    (by rw [number]; exact p.candidate_odd) (by rw [number]; exact oddQ)) ?_
  rintro t ⟨ctx, flag, changed, rest⟩
  rw [number] at flag
  have frame : Frame [⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem := changed
  refine ⟨h.after_aux (by decide : 44 ≤ 64) (by decide : 64 + 4 ≤ 68) frame rest,
    ctx.table, flag, ?_, frame, rest.mono (by simp [sieveRegs, roundClobbers])⟩
  refine rsa_bytes_frame frame (by have := p.length_bounds; omega_using [this]) ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
  exact h.stackOutput.symm.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTPairTrials`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CTTrialPair`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CTTrialPairLoop`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.PairTrialLoopWord`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.PairTrialWord`, which only this module used -/

section

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Bignum.Arm.TrialDivision16
open VG.Impl.Ffdh.Arm.ParameterCandidate

private theorem trialPairRedcWord_ok (s : State) :
    WP isa (.block trialPairRedc) s fun t =>
      (t.gpr .r8 = redcWord (s.gpr .r7) (s.gpr .r8) (s.gpr .r4) (s.gpr .r3) ∧ t.mem = s.mem) ∧
      Rest [.r8, .r7, .r6] s t := by
  unfold trialPairRedc VG.Impl.Bignum.Arm.TrialDivision16.redcAt
  refine wp_dp (op2_reg _ _) fun u1 v1 => wp_mul fun u2 v2 => wp_mov (op2_lsl (by decide)) fun u3 v3 =>
    wp_mov (op2_lsr (by decide)) fun u4 v4 => wp_mul fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 =>
      wp_mov (op2_lsr (by decide)) fun t v7 => WP.block_nil ?_
  refine ⟨⟨?_, by rw [v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩,
    (v1.rest (by simp)).trans ((v2.rest (by simp)).trans ((v3.rest (by simp)).trans
      ((v4.rest (by simp)).trans ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans (v7.rest (by simp)))))))⟩
  rw [v7.gpr, v6.gpr, dpVal, v5.gpr, v4.gpr, v3.gpr, v2.gpr, v1.gpr, dpVal,
    v5.other .r7 (by decide), v4.other .r7 (by decide),
    v3.other .r7 (by decide), v2.other .r7 (by decide), v1.gpr, dpVal,
    v4.other .r3 (by decide), v3.other .r3 (by decide), v2.other .r3 (by decide), v1.other .r3 (by decide),
    v1.other .r4 (by decide)]
  rfl


theorem trialPairStepWord_ok (s : State) {n : Nat} (positive : 0<n) (fits : n<2^32)
    (count : s.gpr .r1=BitVec.ofNat 32 n)
    (readLow : InRegions (s.rd++s.wr) (State.addr (s.gpr .r0-1)) 1)
    (readHigh : 1<n → InRegions (s.rd++s.wr) (State.addr (s.gpr .r0-2)) 1) :
    WP isa trialPairStep s fun t =>
      t.gpr .r2=redcWord (trialDigitWord s.mem (s.gpr .r0) n) (s.gpr .r2) (s.gpr .r4) (s.gpr .r3) ∧
      t.gpr .r8=redcWord (trialDigitWord s.mem (s.gpr .r0) n) (s.gpr .r8) (s.gpr .r4) (s.gpr .r3) ∧
      t.gpr .r0=s.gpr .r0-BitVec.ofNat 32 (min 2 n) ∧
      t.gpr .r1=BitVec.ofNat 32 (n-min 2 n) ∧ t.z=decide (n≤2) ∧ t.mem=s.mem ∧
      Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s t := by
  unfold trialPairStep
  refine WP.seq (WP.mono (trialDigit_ok s positive fits count readLow readHigh) ?_)
  rintro u ⟨⟨ptr,cnt,word,mem⟩,rest⟩
  simp only [List.cons_append,List.nil_append]
  refine wp_mov (op2_reg _ _) fun v save => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (redcWord_ok v) ?_
  rintro x ⟨⟨a,memX⟩,keepX⟩
  rw [WP.block_append_iff]
  refine WP.mono (trialPairRedcWord_ok x) ?_
  rintro y ⟨⟨b,memY⟩,keepY⟩
  refine wp_cmp (op2_imm (by decide)) fun t flags zero => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [flags.gpr,keepY.gpr .r2 (by simp),a,save.other .r5 (by decide),word,
      save.other .r2 (by decide),rest.gpr .r2 (by simp),
      save.other .r4 (by decide),rest.gpr .r4 (by simp),save.other .r3 (by decide),rest.gpr .r3 (by simp)]
    rfl
  · rw [flags.gpr,b,keepX.gpr .r7 (by simp),save.gpr,word,
      keepX.gpr .r8 (by simp),save.other .r8 (by decide),rest.gpr .r8 (by simp),
      keepX.gpr .r4 (by simp),save.other .r4 (by decide),rest.gpr .r4 (by simp),
      keepX.gpr .r3 (by simp),save.other .r3 (by decide),rest.gpr .r3 (by simp)]
    rfl
  · rw [flags.gpr,keepY.gpr .r0 (by simp),keepX.gpr .r0 (by simp),save.other .r0 (by decide),ptr]
  · rw [flags.gpr,keepY.gpr .r1 (by simp),keepX.gpr .r1 (by simp),save.other .r1 (by decide),cnt]
  · rw [zero,keepY.gpr .r1 (by simp),keepX.gpr .r1 (by simp),save.other .r1 (by decide),cnt]
    change (BitVec.ofNat 32 (n-min 2 n)-0#32==0#32)=_
    rw [BitVec.sub_zero]
    change (BitVec.ofNat 32 (n-min 2 n)==(0 : BitVec 32))=_
    rw [ofNat_beq_zero (by omega_using [fits] : n-min 2 n<2^32)]
    exact decide_eq_decide.mpr (by omega_using [])
  · rw [flags.mem,memY,memX,save.mem,mem]
  · exact (rest.mono (by simp)).trans ((save.rest (by simp)).trans ((keepX.mono (by simp)).trans
      ((keepY.mono (by simp)).trans (flags.rest _))))


end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairLoopWord_ok (s : State) {n : Nat} (positive : 0<n) (fits : n<2^32)
    (count : s.gpr .r1=BitVec.ofNat 32 n) (readable : TrialReadable s (s.gpr .r0) n) :
    WP isa (.loop trialPairStep .ne) s fun t =>
      t.gpr .r2=trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) ∧
      t.gpr .r8=trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r8) ∧
      t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s t := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    obtain ⟨tr,u,run,valA,valB,ptr,cnt,flag,memory,rest⟩ :=
      trialPairStepWord_ok s positive fits count (readable.low positive) (fun h => readable.high h)
    have recurrenceA : trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2)=
        trialWordResult u.mem (u.gpr .r0) (u.gpr .r3) (u.gpr .r4) (n-min 2 n) (u.gpr .r2) := by
      rw [trialWordResult,dite_eq_right (by omega_using [positive])]
      rw [memory,ptr,valA,rest.gpr .r3 (by simp),rest.gpr .r4 (by simp)]
    have recurrenceB : trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r8)=
        trialWordResult u.mem (u.gpr .r0) (u.gpr .r3) (u.gpr .r4) (n-min 2 n) (u.gpr .r8) := by
      rw [trialWordResult,dite_eq_right (by omega_using [positive])]
      rw [memory,ptr,valB,rest.gpr .r3 (by simp),rest.gpr .r4 (by simp)]
    by_cases last : n≤2
    · have zero : n-min 2 n=0 := by omega_using [last]
      have resultA : u.gpr .r2=trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) := by
        rw [recurrenceA,zero,trialWordResult,dite_eq_left rfl]
      have resultB : u.gpr .r8=trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r8) := by
        rw [recurrenceB,zero,trialWordResult,dite_eq_left rfl]
      exact ⟨_,u,.loopExit run (by change some (!u.z)=some false;rw [flag,decide_eq_true last];rfl),
        resultA,resultB,memory,rest⟩
    · have smaller : n-min 2 n<n := by omega_using [positive]
      have readU : TrialReadable u (u.gpr .r0) (n-min 2 n) := by
        rw [ptr]
        exact readable.advance rest (Nat.min_le_right 2 n)
      obtain ⟨trT,t,runT,resultA,resultB,memoryT,restT⟩ := ih _ smaller u (by omega_using [last]) (by omega_using [fits]) cnt readU
      exact ⟨_,t,.loopNext run (by change some (!u.z)=some true;rw [flag,decide_eq_false last];rfl) runT,
        resultA.trans recurrenceA.symm,resultB.trans recurrenceB.symm,memoryT.trans memory,rest.trans restT⟩


end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! One public byte-count trace computes both exact sieve accumulators. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

structure TrialPairLoopPair (s t : State) : Prop extends TrialLoopPair s t where
  offset : s.gpr .r8=t.gpr .r8

private theorem trialPairLoop_taint : ∃ hint, (VG.Taint.check taint (Taint.ofRegs [.r0,.r1])
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairStep .ne) hint).isSome=true := ⟨_,by taint_decide⟩

theorem trialPairLoop_ct : RelCT isa TrialPairLoopPair
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairStep .ne)
    (fun s t => s.gpr .r2=t.gpr .r2 ∧ s.gpr .r3=t.gpr .r3 ∧ s.gpr .r8=t.gpr .r8) := by
  obtain ⟨hint,checked⟩ := trialPairLoop_taint
  have trace : RelCT isa TrialPairLoopPair
      (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairStep .ne) (fun _ _ => True) := by
    refine RelCT.taint (A:=taint) (Taint.ofRegs [.r0,.r1]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro reg hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.pointer
    · exact h.count
  intro s t trS trT u v h runS runT
  have countS : s.gpr .r1=BitVec.ofNat 32 (s.gpr .r1).toNat := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have countT : t.gpr .r1=BitVec.ofNat 32 (s.gpr .r1).toNat := h.count.symm.trans countS
  obtain ⟨_,u',execS,valueAS,valueBS,_,restS⟩ :=
    trialPairLoopWord_ok s h.positive (s.gpr .r1).isLt countS h.readLeft
  obtain ⟨_,v',execT,valueAT,valueBT,_,restT⟩ :=
    trialPairLoopWord_ok t h.positive (s.gpr .r1).isLt countT h.readRight
  obtain ⟨_,rfl⟩ := Exec.det runS execS
  obtain ⟨_,rfl⟩ := Exec.det runT execT
  refine ⟨(trace _ _ _ _ _ _ h runS runT).1,?_,?_,?_⟩
  · rw [valueAS,valueAT,←h.pointer,←h.acc,←h.divisor,←h.inverse]
    exact trialWordResult_congr _ h.bytes
  · exact (restS.gpr .r3 (by simp)).trans (h.divisor.trans (restT.gpr .r3 (by simp)).symm)
  · rw [valueBS,valueBT,←h.pointer,←h.offset,←h.divisor,←h.inverse]
    exact trialWordResult_congr _ h.bytes

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Both divisibility decisions depend only on the public candidate bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

private structure PairOriginalReady (p : TrialData) (s : State) : Prop where
  input : TrialState p s
  pointer : s.gpr .r0=p.dst+BitVec.ofNat 32 p.n
  count : s.gpr .r1=BitVec.ofNat 32 p.n
  acc : s.gpr .r2=0
  divisor : s.gpr .r3=p.prime
  inverse : s.gpr .r4=VG.Proof.RsaKeyGen.ninv p.prime

private structure PairReady (p : TrialData) (s : State) : Prop extends PairOriginalReady p s where
  offset : s.gpr .r8=p.prime-1

private theorem start_ready (p : TrialData) (s : State) (h : TrialState p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) s (PairOriginalReady p) := by
  refine WP.mono (trialStart_ok s p.dst p.n (h.1.frame.read (by decide)) (h.1.frame.read (by decide))
    (h.1.frame.saved 4 (by decide)) (h.1.frame.saved 12 (by decide))) ?_
  rintro t ⟨⟨ptr,count,acc,prime,inverse,memory⟩,rest⟩
  rw [h.2.1] at prime inverse
  exact ⟨⟨h.1.after_memory memory rest,(rest.gpr .r7 (by simp)).trans h.2.1,
    by rw [memory];exact h.2.2⟩,ptr,count,acc,prime,inverse⟩

private theorem init_ready (p : TrialData) (s : State) (h : PairOriginalReady p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairInit) s (PairReady p) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairInit
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t upd => WP.block_nil ?_
  have rest := upd.rest (by simp : Reg.r8∈[.r8])
  refine ⟨⟨⟨h.input.1.after_memory upd.mem rest,(rest.gpr .r7 (by simp)).trans h.input.2.1,
    by rw [upd.mem];exact h.input.2.2⟩,
    (rest.gpr .r0 (by simp)).trans h.pointer,(rest.gpr .r1 (by simp)).trans h.count,
    (rest.gpr .r2 (by simp)).trans h.acc,(rest.gpr .r3 (by simp)).trans h.divisor,
    (rest.gpr .r4 (by simp)).trans h.inverse⟩,?_⟩
  rw [upd.gpr,VG.Proof.X25519.Arm.dpVal,h.divisor]

private theorem ready_pair {s t : State} (h : Two PairReady s t) : TrialPairLoopPair s t := by
  obtain ⟨p,a,b,_⟩ := h
  have countNat : (s.gpr .r1).toNat=p.n := by
    rw [a.count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt a.input.1.countFits]
  refine ⟨⟨a.pointer.trans b.pointer.symm,a.count.trans b.count.symm,a.acc.trans b.acc.symm,
    a.divisor.trans b.divisor.symm,a.inverse.trans b.inverse.symm,?_,?_,?_,?_⟩,
    a.offset.trans b.offset.symm⟩
  · rw [countNat];exact a.input.1.positive
  · rw [countNat,a.pointer];exact a.input.1.readable
  · rw [countNat,b.pointer];exact b.input.1.readable
  · rw [countNat,a.pointer]
    intro i hi
    exact (a.input.2.2 i hi).trans (b.input.2.2 i hi).symm

private theorem pairFlag_taint : ∃ hint, (VG.Taint.check taint (Taint.ofRegs [.r2,.r3,.r8])
    VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairFlag hint).isSome=true := ⟨_,by taint_decide⟩

theorem trialPair_ct : RelCT isa (Two TrialState)
    VG.Impl.Ffdh.Arm.ParameterCandidate.trialPair (fun _ _ => True) := by
  have start : RelCT isa (Two TrialState) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart)
      (Two PairOriginalReady) :=
    two_post (trialStart_ct.mono (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)) start_ready
  have initial : RelCT isa (Two PairOriginalReady) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairInit)
      (Two PairReady) :=
    two_post ((VG.Proof.Bignum.Arm.stackOnly_ct _ (by decide)).mono
      (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)) init_ready
  have loop := trialPairLoop_ct.mono (fun _ _ h => ready_pair h) (fun _ _ h => h)
  obtain ⟨hint,checked⟩ := pairFlag_taint
  have flag : RelCT isa (fun s t => s.gpr .r2=t.gpr .r2 ∧ s.gpr .r3=t.gpr .r3 ∧ s.gpr .r8=t.gpr .r8)
      VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairFlag (fun _ _ => True) := by
    refine RelCT.taint (A:=taint) (Taint.ofRegs [.r2,.r3,.r8]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro reg hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  exact start.seq (initial.seq (loop.seq flag))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

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

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CandidateEntered`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CandidateSpec`, which only this module used -/

section

/-! The native controller's Boolean result is exactly the already merged candidate specification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Ffdh.ParameterCandidate

def candidateAsSpec (p : CandidateParams) (answer : Option (Bool × List Byte)) : Option (Option Nat × List Byte) :=
  answer.map (fun (pass, tail) => (if pass then some p.candidate else none, tail))

theorem candidateScreen_spec (p : CandidateParams) (enough : p.length ≤ p.bytes.length) :
    candidateAsSpec p (candidateScreen p) = Spec.Ffdh.sievedParameterCandidate p.bits p.generator p.bytes := by
  unfold Spec.Ffdh.sievedParameterCandidate
  rw [draw_of_le (len := (p.bits + 7) / 8) enough]
  simp only [bind, Option.bind_some]
  change candidateAsSpec p (candidateScreen p) =
    (if !(Spec.Ffdh.generationShape p.bits p.generator p.candidate && Spec.Ffdh.primeShape p.candidate &&
      Spec.Ffdh.primeShape ((p.candidate - 1) / 2) &&
      !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate &&
      !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate - 1) / 2)) then some (none, p.bytes.drop p.length) else do
      let (pass, tail) ← Spec.Ffdh.screenedParameterWitnesses p.candidate ((p.candidate - 1) / 2) (p.bytes.drop p.length)
      pure (if pass then some p.candidate else none, tail))
  have reorder (a b c d e : Bool) : (a && b && c && d && e) = (a && (b && d) && (c && e)) := by
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
  rw [reorder]
  have halfBits : Spec.RsaKeyGen.bitLength ((p.candidate - 1) / 2) = p.bits - 1 :=
    VG.Proof.Ffdh.ParameterCandidate.half_bitLength (bits := p.bits)
      (by have := p.minBits; omega_using [this]) (Spec.Rsa.os2ip (p.bytes.take p.length))
  unfold candidateScreen candidateScreenP candidateScreenQ
  by_cases gen : Spec.Ffdh.generationShape p.bits p.generator p.candidate = true
  · by_cases pp : (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) = true
    · by_cases qp : (Spec.Ffdh.primeShape ((p.candidate - 1) / 2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate - 1) / 2)) = true
      · simp only [gen, pp, qp, Bool.true_and, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
        rw [← screenedChecks_eq ((Bool.and_eq_true _ _).mp pp).1 ((Bool.and_eq_true _ _).mp qp).1]
        unfold screenedChecks
        rw [p.candidate_bits, halfBits]
        unfold candidateTests screenedTests continueWitnesses witnessRemaining
        simp only [limitedPhase, limitedChecks, candidatePhase, phaseBits, Bool.false_eq_true, ite_false,
          ite_true, Nat.sub_zero]
        cases first : checkWitnesses p.candidate 1 (p.bytes.drop p.length) with
        | none => rfl
        | some pair =>
          obtain ⟨pass, tail⟩ := pair
          cases pass with
          | false => rfl
          | true =>
            dsimp only [bind, Option.bind_some, Bool.not_true, Bool.false_eq_true, ite_false]
            cases q : checkWitnesses ((p.candidate - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) tail with
            | none => rfl
            | some pair =>
              obtain ⟨pass, rest⟩ := pair
              cases pass with
              | false => rfl
              | true =>
                dsimp only [bind, Option.bind_some, Bool.not_true, Bool.false_eq_true, ite_false]
                cases checkWitnesses p.candidate (Spec.Ffdh.primeChecks p.bits - 1) rest with
                | none => rfl
                | some pair => obtain ⟨pass, tail⟩ := pair; rfl
      · have nq : (Spec.Ffdh.primeShape ((p.candidate - 1) / 2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate - 1) / 2)) = false := Bool.eq_false_iff.mpr qp
        simp [gen, pp, nq, candidateAsSpec, candidateRejected]
    · have np : (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) = false := Bool.eq_false_iff.mpr pp
      simp [gen, np, candidateAsSpec, candidateRejected]
  · have ng : Spec.Ffdh.generationShape p.bits p.generator p.candidate = false := Bool.eq_false_iff.mpr gen
    simp [ng, candidateAsSpec, candidateRejected]

def candidateAnswer (p : CandidateParams) : Option (Bool × List Byte) :=
  if p.length ≤ p.bytes.length then candidateScreen p else none

theorem candidateAnswer_spec (p : CandidateParams) :
    candidateAsSpec p (candidateAnswer p) = Spec.Ffdh.sievedParameterCandidate p.bits p.generator p.bytes := by
  by_cases enough : p.length ≤ p.bytes.length
  · rw [candidateAnswer, ite_eq_left enough]
    exact candidateScreen_spec p enough
  · rw [candidateAnswer, ite_eq_right enough]
    unfold Spec.Ffdh.sievedParameterCandidate
    have short : p.bytes.length < (p.bits + 7) / 8 := by change p.bytes.length < p.length; omega_using [enough]
    rw [draw_of_short short]
    rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.ScreenedTests`, which only this module used -/

section

/-! Screen p once before completing q and the remaining p witnesses. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/LimitedFinal.lean`, which only this module imported.
section

/-! Restore p, complete its remaining witnesses, and return the candidate result. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem limitedFinal_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.limitedFinal (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s
      (CandidateReturn p (witnessRemaining (limitedPhase p false) used 0) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.limitedFinal VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateShape_ok h enough) ?_)
  rintro u ⟨ctx, _, number, changed, rest⟩
  refine WP.seq (WP.mono (limitedTest_ok b v ctx number p.candidate_odd) ?_)
  rintro w ⟨next, ctxW, _, status, suffix, bytes, changedW, restW⟩
  refine WP.seq (WP.mono (candidateResult_ok ctxW status suffix (by
    intro _ _
    rw [bytes]
    exact number)) ?_)
  intro t returned
  refine WP.block_nil ?_
  have returnedU := returned.trans_pre (candidate_phase_frame (p := p) (q := false) changedW) restW (fun _ h => h)
  exact returnedU.trans_pre (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/ScreenedAfterQ.lean`, which only this module imported.
section

/-! Complete q and then the remaining p witnesses, or return an early rejection. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem screenedAfterQ_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2)
    (odd : ((p.candidate - 1) / 2) % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.afterScreenedQ (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s
      (CandidateReturn p (screenedQTests p used) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.afterScreenedQ VG.Impl.Ffdh.Arm.ParameterCandidate.limitedFinal VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateTest_ok b v (q := true) h number odd) ?_)
  rintro u ⟨next, ctx, _, status, suffix, _, changed, rest⟩
  let answer := witnessRemaining (candidatePhase p true) used 0
  have bound : witnessResultStatus (witnessRemaining (candidatePhase p true) used 0) ≤ 2 :=
    witnessResultStatus_bound _
  refine WP.seq (WP.mono (cmpStatus_ok _ 1 (by omega) (by decide) status) ?_)
  rintro w ⟨⟨zero, memory⟩, restW⟩
  have ctxW := ctx.after_memory memory restW
  have statusW : w.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus answer) :=
    (restW.gpr .r3 (by simp)).trans status
  by_cases go : witnessResultStatus answer = 1
  · refine WP.seq (WP.ite true (by change some w.z = some true; rw [zero, decide_eq_true go]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (limitedFinal_ok b v ctxW enough) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [← screenedQTests_go p used next go suffix] at returned
    have returnedU := returned.trans_pre (by rw [memory]; exact Frame.refl _ _) restW (by simp)
    exact returnedU.trans_pre (candidate_phase_frame changed) rest (fun _ h => h)
  · refine WP.seq (WP.ite false (by change some w.z = some false; rw [zero, decide_eq_false go]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateResult_ok ctxW statusW suffix (by
      intro tail accepted
      exact False.elim (go (by rw [accepted]; rfl)))) ?_
    intro t returned
    refine WP.block_nil ?_
    change CandidateReturn p (witnessRemaining (candidatePhase p true) used 0) w t at returned
    rw [← screenedQTests_stop p used go] at returned
    have returnedU := returned.trans_pre (by rw [memory]; exact Frame.refl _ _) restW (by simp)
    exact returnedU.trans_pre (candidate_phase_frame changed) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/ScreenedQ.lean`, which only this module imported.
section

/-! Reconstruct q after p's early witness without requiring the no-longer-needed sieve table. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem screenedQ_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate)
    (odd : ((p.candidate - 1) / 2) % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s
      (CandidateReturn p (screenedQTests p used) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ
  refine WP.seq (WP.mono (candidateHalveValue_ok h number) ?_)
  rintro u ⟨context, value, _, changed, rest⟩
  refine WP.mono (screenedAfterQ_ok b v context enough value odd) ?_
  intro t returned
  exact returned.trans_pre (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem screenedTests_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length)
    (odd : ((p.candidate - 1) / 2) % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedTests (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s
      (CandidateReturn p (screenedTests p used) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenedTests VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateShape_ok h enough) ?_)
  rintro shaped ⟨shapeCtx, _, shapeNumber, shapeChanged, shapeRest⟩
  refine WP.seq (WP.mono (limitedTest_ok b v (first := true) shapeCtx shapeNumber p.candidate_odd) ?_)
  rintro u ⟨next, ctx, _, status, suffix, sameBytes, changed, rest⟩
  let answer := witnessRemaining (limitedPhase p true) used 0
  have bound : witnessResultStatus (witnessRemaining (limitedPhase p true) used 0) ≤ 2 :=
    witnessResultStatus_bound _
  refine WP.seq (WP.mono (cmpStatus_ok _ 1 (by omega_using [bound]) (by decide) status) ?_)
  rintro w ⟨⟨zero, memory⟩, restW⟩
  have ctxW := ctx.after_memory memory restW
  have statusW : w.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus answer) :=
    (restW.gpr .r3 (by simp)).trans status
  by_cases go : witnessResultStatus answer = 1
  · refine WP.seq (WP.ite true (by change some w.z = some true; rw [zero, decide_eq_true go]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (screenedQ_ok b v ctxW enough (by rw [memory, sameBytes]; exact shapeNumber) odd) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [← screenedTests_go p used next go suffix] at returned
    have returnedU := returned.trans_pre (by rw [memory]; exact Frame.refl _ _) restW (by simp)
    exact (returnedU.trans_pre (candidate_phase_frame (p := p) (q := false) changed) rest (fun _ h => h)).trans_pre
      (shapeChanged.mono (by simp [candidateRegions])) shapeRest (fun _ h => h)
  · refine WP.seq (WP.ite false (by change some w.z = some false; rw [zero, decide_eq_false go]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateResult_ok ctxW statusW suffix (by
      intro tail accepted
      exact False.elim (go (by rw [accepted]; rfl)))) ?_
    intro t returned
    refine WP.block_nil ?_
    change CandidateReturn p (witnessRemaining (limitedPhase p true) used 0) w t at returned
    rw [← screenedTests_stop p used go] at returned
    have returnedU := returned.trans_pre (by rw [memory]; exact Frame.refl _ _) restW (by simp)
    exact (returnedU.trans_pre (candidate_phase_frame (p := p) (q := false) changed) rest (fun _ h => h)).trans_pre
      (shapeChanged.mono (by simp [candidateRegions])) shapeRest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CandidateLocalFrame`, which only this module used -/

section

/-! Each candidate-local store fits the controller's explicitly permitted state range. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont

theorem candidate_local_frame {s t : State} {p : CandidateParams} {consumed d : Nat}
    (h : CandidateContext p consumed s) (lower : 40 ≤ d) (upper : d + 4 ≤ 68)
    (changed : Frame [⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩] s.mem t.mem) :
    Frame (candidateRegions p s.sp) s.mem t.mem := by
  refine changed.sub ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  refine ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [candidateRegions], ?_⟩
  rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [upper, this]), VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
  exact Offset.sub _ lower (by omega_using [upper])

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Complete candidate execution after reserving the common AAPCS frame. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateScreenPair.lean`, which only this module imported.
section

/-! Initialize the RSA table once and screen both moduli at each prime. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateScreenPair_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateContext p p.length s) (enough : p.length ≤ p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate)
    (oddQ : ((p.candidate-1)/2)%2=1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s
      (CandidateReturn p (candidateScreenP p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateTable_ok h) ?_)
  rintro u ⟨ctx, table, changed, rest⟩
  have bytes := rsa_bytes_frame (src := State.addr p.out) (k := p.length) changed (by have := p.length_bounds; omega) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact p.outputScratch)
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length) = p.candidate := by
    rw [bytes]
    exact number
  refine WP.seq (WP.mono (candidatePair_ok ctx table numberU oddQ) ?_)
  rintro w ⟨ctxW, tableW, flag, bytesW, changedW, restW⟩
  change w.z=candidateShapes p at flag
  have numberW : Spec.Rsa.os2ip (Spec.Rsa.bytesAt w.mem (State.addr p.out) p.length) = p.candidate := by
    rw [bytesW]
    exact numberU
  by_cases prime : candidateShapes p = true
  · refine WP.seq (WP.ite true (by change some w.z = some true; rw [flag, prime]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (screenedTests_ok b v ctxW enough oddQ) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_shapes, prime]
    exact (returned.trans_pre (candidate_local_frame ctx (by decide) (by decide) changedW) restW (fun _ h => h)).trans_pre
      (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)
  · have composite : candidateShapes p = false := Bool.eq_false_iff.mpr prime
    refine WP.seq (WP.ite false (by change some w.z = some false; rw [flag, composite]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctxW) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_shapes, composite]
    exact (returned.trans_pre (candidate_local_frame ctx (by decide) (by decide) changedW) restW (fun _ h => h)).trans_pre
      (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateScreenP.lean`, which only this module imported.
section

/-! Reject even q before the paired RSA sieve and witness controller. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateScreenP_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateContext p p.length s) (enough : p.length≤p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s
      (CandidateReturn p (candidateScreenP p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenP VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateQOdd_ok h number) ?_)
  rintro u ⟨ctx,flag,memory,rest⟩
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length)=p.candidate := by
    rw [memory]
    exact number
  by_cases oddQ : ((p.candidate-1)/2)%2=1
  · refine WP.seq (WP.ite true (by change some u.z=some true; rw [flag,decide_eq_true oddQ]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateScreenPair_ok b v ctx enough numberU oddQ) ?_
    intro t returned
    refine WP.block_nil ?_
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (fun _ h => h)
  · refine WP.seq (WP.ite false (by change some u.z=some false; rw [flag,decide_eq_false oddQ]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_even p (by omega)]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateMain.lean`, which only this module imported.
section

/-! The entire candidate body: shape, residue, two sieves, and q/p Miller–Rabin. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateMain_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.main (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s (CandidateReturn p (candidateScreen p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.main VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateCount_ok h enough) ?_)
  rintro u ⟨ctxU, changedU, restU⟩
  refine WP.seq (WP.mono (candidateShape_ok ctxU enough) ?_)
  rintro w ⟨ctxW, _, numberW, changedW, restW⟩
  refine WP.seq (WP.mono (candidateResidue_ok ctxW numberW) ?_)
  rintro a ⟨ctxA, flag, memoryA, restA⟩
  have numberA : Spec.Rsa.os2ip (Spec.Rsa.bytesAt a.mem (State.addr p.out) p.length) = p.candidate := by
    rw [memoryA]
    exact numberW
  by_cases shape : Spec.Ffdh.generationShape p.bits p.generator p.candidate = true
  · refine WP.seq (WP.ite true (by change some a.z = some true; rw [flag, shape]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateScreenP_ok b v ctxA enough numberA) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreen, shape]
    exact ((returned.trans_pre (by rw [memoryA]; exact Frame.refl _ _) restA (fun _ h => h)).trans_pre
      (changedW.mono (by simp [candidateRegions])) restW (fun _ h => h)).trans_pre
      (candidate_local_frame h (by decide) (by decide) changedU) restU (fun _ h => h)
  · have badShape : Spec.Ffdh.generationShape p.bits p.generator p.candidate = false := Bool.eq_false_iff.mpr shape
    refine WP.seq (WP.ite false (by change some a.z = some false; rw [flag, badShape]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctxA) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreen, badShape]
    exact ((returned.trans_pre (by rw [memoryA]; exact Frame.refl _ _) restA (fun _ h => h)).trans_pre
      (changedW.mono (by simp [candidateRegions])) restW (fun _ h => h)).trans_pre
      (candidate_local_frame h (by decide) (by decide) changedU) restU (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateGuard.lean`, which only this module imported.
section

/-! Complete candidate control flow, including the short initial entropy tape. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateGuard_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)]) s
      (CandidateReturn p (candidateAnswer p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (initialRoom_ok h.saved.space p.tapeCount
    (by have := p.length_bounds; omega) (h.saved.saved 20 (by decide)) (h.saved.saved 12 (by decide))) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases enough : p.length ≤ p.bytes.length
  · refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false (by omega)]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateMain_ok b v ctx enough) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateAnswer, ite_eq_left enough]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (by simp [roundClobbers])
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true (by omega)]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateNone_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateAnswer, ite_eq_right enough]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (by simp [roundClobbers])

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def candidateEnteredRegions (p : CandidateParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.out, p.length⟩, ⟨State.addr p.usedPtr, 8⟩, ⟨State.addr p.base, 8 * p.capacity⟩,
    ⟨State.addr sp, 72⟩, FrameStack.belowA sp 56]

def candidatePost (p : CandidateParams) (m : Mem) (r : BitVec 32) : Prop :=
  r = BitVec.ofNat 32 (witnessResultStatus (candidateAnswer p)) ∧
  Spec.Rsa.wordsAt m (State.addr p.usedPtr) 1 =
    [BitVec.ofNat 64 (match candidateAnswer p with | none => 0 | some (_, rest) => p.bytes.length - rest.length)] ∧
  Spec.Rsa.bytesAt m (State.addr p.out) p.length =
    (match candidateAnswer p with | some (true, _) => Spec.Rsa.i2osp p.candidate p.length | _ => List.replicate p.length 0)

theorem candidateEntered_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateStart p s) (incoming : CandidateIncoming p s)
    (out : s.gpr .r0 = p.out) (width : s.gpr .r1 = BitVec.ofNat 32 p.length)
    (used : s.gpr .r2 = p.usedPtr) (bits : s.gpr .r3 = BitVec.ofNat 32 p.bits) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.entry,
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)]) s
      (fun t => Frame (candidateEnteredRegions p s.sp) s.mem t.mem ∧ candidatePost p t.mem (t.gpr .r0)) := by
  change WP isa (.seq (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) _) s _
  rw [WP.seq_iff]
  refine WP.mono (candidateEntry_ok h.locals incoming out width used bits) ?_
  rintro u ⟨saved, changed, rest⟩
  refine WP.mono (candidateGuard_ok b v (h.after_entry saved changed rest)) ?_
  rintro t ⟨status, count, bytes, frame, _⟩
  rw [rest.sp] at frame
  have bodyFrame : Frame (candidateEnteredRegions p s.sp) u.mem t.mem := by
    refine frame.sub ?_
    intro r hr
    simp only [candidateReturnRegions, candidateRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [candidateEnteredRegions], fun _ h => h⟩
    · exact ⟨_, by simp [candidateEnteredRegions], fun _ h => h⟩
    · exact ⟨_, by simp [candidateEnteredRegions], fun _ h => h⟩
    · exact ⟨_, by simp [candidateEnteredRegions], fun _ h => h⟩
    · refine ⟨⟨State.addr s.sp, 72⟩, by simp [candidateEnteredRegions], ?_⟩
      rw [VG.Arm.addr_add (by have := h.locals.nowrap; omega_using [this])]
      exact Offset.sub_base _ (by decide : 40 + 28 ≤ 72)
  exact ⟨(changed.mono (by simp [candidateEnteredRegions])).trans bodyFrame, status, count, bytes⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CandidateFn`, which only this module used -/

section

/-! Preserve the AAPCS callee-saved registers around complete candidate generation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure CandidateFnInput (p : CandidateParams) (s : State) : Prop where
  stackFits : 184 ≤ s.sp.toNat
  start : CandidateStart p (entered s)
  incoming : CandidateIncoming p (entered s)
  out : (entered s).gpr .r0 = p.out
  width : (entered s).gpr .r1 = BitVec.ofNat 32 p.length
  used : (entered s).gpr .r2 = p.usedPtr
  bits : (entered s).gpr .r3 = BitVec.ofNat 32 p.bits
  saved : ∀ r ∈ candidateEnteredRegions p (entered s).sp,
    (⟨State.addr (VG.Proof.Bignum.Arm.pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem candidateFn_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : CandidateParams} (h : CandidateFnInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.code (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s fun t =>
      abiPreserved s t ∧ candidatePost p t.mem (t.gpr .r0) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.code
  refine framed_of_separate _ s (by have := h.stackFits; omega_using [this])
    (candidateEnteredRegions p (entered s).sp) (candidatePost p) h.saved
    (candidateEntered_ok b v h.start h.incoming h.out h.width h.used h.bits) (hQ := ?_)
  intro m₁ m₂ status hf ⟨st, used, out⟩
  have sep : ∀ R ∈ [(⟨State.addr p.out, p.length⟩ : Region), ⟨State.addr p.usedPtr, 8⟩], ∀ r ∈ released s,
      R.Disjoint r := by
    intro R hR r hr
    simp only [released, List.mem_cons, List.not_mem_nil, or_false] at hr hR
    rcases hR with rfl | rfl <;> rcases hr with rfl | rfl
    · exact (h.saved _ (by simp [candidateEnteredRegions])).symm
    · exact h.start.stackOutput.symm
    · exact (h.saved _ (by simp [candidateEnteredRegions])).symm
    · exact h.start.stackUsed.symm
  refine ⟨st, Eq.trans ?_ used, Eq.trans (VG.Proof.Bignum.Arm.rsa_bytes_frame hf
    (by have := p.outputFits; simp only [CandidateParams.length]; omega_using [this]) (sep _ (by simp))) out⟩
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro j hj
  have bound : j < 1 := List.mem_range.mp hj
  exact hf.readW (r := ⟨State.addr p.usedPtr, 8⟩) (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound]))
    (sep _ (by simp)) (by decide)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CandidateInput`, which only this module used -/

section

/-! The public signature supplies all permissions, incoming words and 184 bytes of stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem candidateInput {s : State} {p : CandidateParams}
    (pre : (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre s) (args : CandidateAbi p s) :
    CandidateFnInput p s := by
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, _, _, _, _, _, _, stackOut, stackUsed, stackTape, stackScratch, stackArgs,
    _, _, _, _, _, _, _, _, _⟩ := pre
  have widthNat : (s.gpr .r1).toNat = p.length := by
    rw [args.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.length_bounds; omega_using [this])]
  have tapeNat : (stackArg s 2).toNat = p.bytes.length := by
    rw [args.tapeLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.tapeCount]
  have capacityNat : (stackArg s 4).toNat = p.capacity := by
    rw [args.capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.capacity_fits]
  rw [args.out, args.used, args.base, widthNat, capacityNat, Nat.mul_comm p.capacity 8] at wr
  rw [args.tape, tapeNat] at rd
  rw [args.out, widthNat] at stackOut
  rw [args.used] at stackUsed
  rw [args.tape, tapeNat] at stackTape
  rw [args.base, capacityNat, Nat.mul_comm p.capacity 8] at stackScratch
  have reserved : s.sp.setWidth 64 - 184#64 = State.addr (s.sp - 184#32) := (FrameStack.addr_sub' stackFit).symm
  rw [reserved] at stackOut stackUsed stackTape stackScratch stackArgs
  have fit128 : 128 ≤ s.sp.toNat := by omega_using [stackFit]
  have sub128 := FrameStack.belowA_sub (sp := s.sp) (a := 128) (b := 184) (by decide) stackFit
  have localsSub : (⟨State.addr (entered s).sp, 72⟩ : Region).Sub (FrameStack.belowA s.sp 184) :=
    fun x hx => sub128 x (locals_sub_reserved s fit128 x hx)
  have savedSub : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Sub (FrameStack.belowA s.sp 184) :=
    fun x hx => sub128 x (saved_sub_reserved s fit128 x hx)
  have belowSub : (FrameStack.belowA (entered s).sp 56).Sub (FrameStack.belowA s.sp 184) := by
    rw [entered_sp]
    exact FrameStack.belowA_inner (by decide) stackFit
  have workspace : Workspace s p.base (8 * p.capacity) := ⟨p.scratchFits, by rw [wr]; simp [State.addr]⟩
  have tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.tape) p.bytes.length :=
    ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have start : CandidateStart p (entered s) := by
    refine ⟨⟨?_, List.mem_cons_self⟩, entered_workspace workspace, ?_, ?_, entered_read tapeRead, ?_, ?_,
      stackOut.sub_left localsSub, stackUsed.sub_left localsSub, stackScratch.sub_left localsSub, stackTape.sub_left localsSub,
      stackOut.sub_left belowSub, stackUsed.sub_left belowSub, stackScratch.sub_left belowSub, stackTape.sub_left belowSub⟩
    · rw [entered_nat s fit128]; have := s.sp.isLt; omega_using []
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
    · refine (rsa_bytes_frame (entered_frame s fit128) (by have := p.tapeCount; omega_using [tapeNat]) ?_).trans args.bytes
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact stackTape.symm.sub_right savedSub
    · rw [entered_nat s fit128]; omega_using [stackFit]
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 5) : stackArgAddr s i = off (State.addr s.sp) (4 * i) := VG.Arm.addr_add (by omega_using [argFit, hi])
  have argSub (i : Nat) (hi : i < 5) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 20⟩ := by
    rw [argStart, argAddr i hi]
    exact Offset.sub_base _ (by omega_using [hi])
  have incoming (i : Nat) (hi : i < 5) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s fit128 (by omega_using [argFit, hi])
      ⟨⟨stackArgAddr s 0, 20⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
      ((stackArgs.sub_left sub128).sub_right (argSub i hi)) rfl
  have nativeIncoming : CandidateIncoming p (entered s) := by
    refine ⟨?_⟩
    intro i hi
    have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [hi]
    rcases choices with rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [candidateIncomingValue]
    · rw [← args.generator]; exact incoming 0 (by decide)
    · rw [← args.tape]; exact incoming 1 (by decide)
    · rw [← args.tapeLength]; exact incoming 2 (by decide)
    · rw [← args.base]; exact incoming 3 (by decide)
    · rw [← args.capacity]; exact incoming 4 (by decide)
  refine ⟨stackFit, start, nativeIncoming, args.out, args.width, args.used, args.bits, ?_⟩
  intro r hr
  simp only [candidateEnteredRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact stackOut.sub_left savedSub
  · exact stackUsed.sub_left savedSub
  · exact stackScratch.sub_left savedSub
  · exact saved_separate_locals s fit128
  · have shift : (pcPushed s).sp = (entered s).sp + 72#32 := (BitVec.sub_add_cancel _ _).symm
    have room : (entered s).sp.toNat + 72 < 2 ^ 32 := by rw [entered_nat s fit128]; have := s.sp.isLt; omega_using []
    rw [shift, VG.Arm.addr_add room, FrameStack.belowA, FrameStack.addr_sub' start.stackBelow]
    exact (Offset.disjoint_below_above _ (m := 56) (a := 72) (l := 56) (by decide)).symm

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Bignum.OctetsValue`, which only this module used -/

section

/-! A fixed-width big-endian encoding is determined by its integer value. -/

@[expose] public section
namespace VG.Proof.Bignum
open VG

theorem bytesAt_eq_of_value {m : Mem} {base : Addr} {n : Nat} {xs : List Byte}
    (length : xs.length = n)
    (value : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m base n) = Spec.Rsa.os2ip xs) :
    Spec.Rsa.bytesAt m base n = xs := by
  have encoded := (VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt m base n)).symm
  rw [bytesAt_length, value, ← length] at encoded
  simpa only [length] using encoded.trans (VG.Proof.Rsa.i2osp_os2ip xs)

end VG.Proof.Bignum

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTCandidateFinish`, which only this module used -/

section

/-! Candidate returns use public output addresses and width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch

def CandidateContextStart (p : CandidatePoint) (s : State) : Prop := CandidateContext p.params p.used s

theorem candidateRejected_ct : RelCT isa (Two CandidateContextStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected (fun _ _ => True) :=
  two_map (fun p => (⟨p.params.out, p.params.usedPtr, p.params.length⟩ : ResultData))
    (fun p _ h => ⟨p.used, h.result_context⟩) finRejected_ct

theorem candidateNone_ct : RelCT isa (Two CandidateContextStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (fun _ _ => True) :=
  two_map (fun p => (⟨p.params.out, p.params.usedPtr, p.params.length⟩ : ResultData))
    (fun p _ h => ⟨p.used, h.result_context⟩) finNone_ct

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTPairStep`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_ite)

private def PairDone (p : PairData × Nat) (s : State) : Prop :=
  s.z=(Spec.Rsa.os2ip p.1.bytes%VG.Impl.RsaKeyGen.tabEntry p.2==0 ||
    (VG.Impl.RsaKeyGen.tabEntry p.2-1+Spec.Rsa.os2ip p.1.bytes)%VG.Impl.RsaKeyGen.tabEntry p.2==0)

theorem pairActiveStep_ct : RelCT isa (Two PairTrialsStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.pairActiveStep (fun _ _ => True) := by
  have trials : RelCT isa (Two PairTrialsStart) VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials (Two PairDone) :=
    two_post pairTrials_ct (fun p s h => by
      refine WP.mono (pairTrials_ok h.context h.index h.cursor (by rw [h.bytes])) ?_
      rintro t ⟨flag,_,_⟩
      exact flag)
  have flag : RelCT isa (Two PairDone) VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFlag (fun s t => s.sp=t.sp) :=
    sieveFlag_ct.mono (fun _ _ ⟨_,a,b,sp⟩ => ⟨sp,a.trans b.symm⟩) (fun _ _ h => h)
  have count : RelCT isa (fun s t => s.sp=t.sp)
      (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance ++ VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount))
      (fun s t => s.sp=t.sp) := stackOnly_ct _ rfl
  exact trials.seq (flag.seq (count.seq (RelCT.block_nil (fun _ _ _ => trivial))))

structure PairStepStart (p : PairData × Nat) (s : State) : Prop where
  trials : PairTrialsStart p s
  bad : s.mem.readW (State.addr (s.sp+64#32)) 32 = if pairAny (Spec.Rsa.os2ip p.1.bytes) p.2 then 1 else 0

private def PairGuarded (p : PairData × Nat) (s : State) : Prop :=
  PairStepStart p s ∧ s.z = !pairAny (Spec.Rsa.os2ip p.1.bytes) p.2

theorem pairStep_ct : RelCT isa (Two PairStepStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep (fun _ _ => True) := by
  have guardTrace : RelCT isa (Two PairStepStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish) (fun _ _ => True) :=
    (stackOnly_ct _ rfl).mono (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)
  have guard : RelCT isa (Two PairStepStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish) (Two PairGuarded) := by
    refine two_post guardTrace ?_
    intro p s h
    refine WP.mono (sieveFinish_ok h.trials.context.read.frame.space h.bad) ?_
    rintro t ⟨⟨flag,memory⟩,rest⟩
    refine ⟨⟨⟨h.trials.context.after_memory memory rest,h.trials.index,?_,?_⟩,?_⟩,flag⟩
    · rw [rest.gpr .r10 (by simp)]; exact h.trials.cursor
    · rw [memory]; exact h.trials.bytes
    · rw [memory,rest.sp]; exact h.bad
  refine guard.seq (two_ite ?_ ?_ ?_)
  · intro p s t h k
    change some s.z=some t.z
    rw [h.2,k.2]
  · exact pairActiveStep_ct.mono
      (fun _ _ ⟨p,a,b,sp⟩ => ⟨p,a.1.1.trials,b.1.1.trials,sp⟩) (fun _ _ h => h)
  · exact (stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.sieveSkip rfl).mono
      (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! A verified parameter candidate supplied to the native retry/refill controller. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTTable.lean`, which only this module imported.
section

/-! The native RSA sieve table is written at the same public scratch offsets in both runs. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

def TableStart (p : CandidateParams × Nat) (s : State) : Prop := CandidateContext p.1 p.2 s
private def TablePointer (p : CandidateParams × Nat) (s : State) : Prop :=
  s.gpr .r11 = p.1.base + BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt p.1.words 34)

theorem tableWrite_ct : RelCT isa (Two TableStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) (fun _ _ => True) := by
  have pointer : RelCT isa (Two TableStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer) (Two TablePointer) :=
    two_post ((stackOnly_ct _ (by decide)).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (tablePointer_ok s p.1.base p.1.length p.1.length_bounds.2
        (by simpa only [BitVec.add_zero] using h.saved.read (d := 0) (by decide)) (h.saved.read (by decide))
        (by simpa only [BitVec.add_zero, candidateValues] using h.saved.saved 0 (by decide)) (h.saved.saved 12 (by decide))) ?_
      rintro t ⟨⟨ptr, _⟩, _⟩
      exact ptr)
  obtain ⟨hint, checked⟩ := tableWrites_taint
  have writes : RelCT isa (Two TablePointer) (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrites 1024))
      (fun _ _ => True) := by
    refine two_taint [.r11] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  exact RelCT.block_append (pointer.seq writes)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTPairLoop.lean`, which only this module imported.
section

/-! The RSA sieve loop has a public trace, including its public rejection flags. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Bignum
open VG.Proof.Ffdh.Arm.KeySearch (Two)

def PairCTState (p : PairData × Nat) (s : State) : Prop :=
  ∃ original, PairInv original p.1.dst p.1.base p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2 s

private theorem PairCTState.step_start {p : PairData × Nat} {s : State}
    (h : PairCTState p s) (more : p.2 < (trialCount p.1.bytes.length)) : PairStepStart p s := by
  obtain ⟨original, inv⟩ := h
  exact ⟨⟨inv.context, more, inv.cursor, bytesAt_eq_of_value rfl inv.candidate⟩, inv.bad⟩

private theorem pairStep_fixed (p : PairData × Nat) (more : p.2 < (trialCount p.1.bytes.length)) :
    RelCT isa (fun s t => PairCTState p s ∧ PairCTState p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep
      (fun s t => PairCTState (p.1, (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)) s ∧ PairCTState (p.1, (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)) t ∧
        s.z = decide ((pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)) ∧ t.z = decide ((pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)) ∧ s.sp = t.sp) := by
  intro s t trS trT u v h runS runT
  have leak := (pairStep_ct _ _ _ _ _ _ ⟨p, h.1.step_start more, h.2.1.step_start more, h.2.2⟩ runS runT).1
  obtain ⟨originalS, invS⟩ := h.1
  obtain ⟨originalT, invT⟩ := h.2.1
  obtain ⟨_, u', execS, nextS, zeroS⟩ := pairStep_ok invS more
  obtain ⟨_, v', execT, nextT, zeroT⟩ := pairStep_ok invT more
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, ⟨originalS, nextS⟩, ⟨originalT, nextT⟩, zeroS, zeroT,
    (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def PairLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : PairData × Nat, p.2 < (trialCount p.1.bytes.length) ∧ (trialCount p.1.bytes.length) - p.2 ≤ remaining ∧ PairCTState p s ∧ PairCTState p t ∧ s.sp = t.sp

theorem pairLoop_ct : RelCT isa (Two fun (p : PairData) s => PairCTState (p, 0) s)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep .ne) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (PairLoopPair n) VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep
      (fun u v => isa.eval .ne u = isa.eval .ne v ∧
        (isa.eval .ne u = some false → True) ∧
        (isa.eval .ne u = some true → ∃ m, m < n ∧ PairLoopPair m u v)) := by
    intro n s t trS trT u v h runS runT
    obtain ⟨p, more, remaining, left, right, sp⟩ := h
    have progress := pairNext_progress (value:=Spec.Rsa.os2ip p.1.bytes) more
    obtain ⟨leak, stateU, stateV, zeroU, zeroV, spUV⟩ := pairStep_fixed p more _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zeroU, zeroV]
    · intro go
      change some (!u.z) = some true at go
      have next : (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) < (trialCount p.1.bytes.length) := by
        by_cases last : (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)
        · rw [zeroU, decide_eq_true last] at go
          cases go
        · omega
      exact ⟨(trialCount p.1.bytes.length) - ((pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)), by omega, (p.1, (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)), next, by exact Nat.le_refl _, stateU, stateV, spUV⟩
  exact (RelCT.loop PairLoopPair step 1024).mono
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨(p, 0), trialCount_positive _, by change trialCount p.bytes.length - 0 ≤ 1024; have := trialCount_bound p.bytes.length; omega, left, right, sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTPairSieve.lean`, which only this module imported.
section

/-! Complete small-prime screening leaks only the public candidate and workspace layout. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

def PairPublic (p : PairData) (s : State) : Prop :=
  SieveContext p.dst p.base p.bytes.length s ∧ Spec.Rsa.bytesAt s.mem (State.addr p.dst) p.bytes.length = p.bytes

private theorem sieveInit_ct : RelCT isa (fun s t => s.sp = t.sp)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit (fun s t => s.sp = t.sp) := by
  have tail : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitTail)
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitRegisters (by decide)).seq (save_ct .r1 64))
  exact (stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer (by decide)).seq tail

theorem pairSieve_ct : RelCT isa (Two PairPublic) VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve (fun _ _ => True) := by
  have init : RelCT isa (Two PairPublic) VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit
      (Two fun p s => PairCTState (p, 0) s) :=
    two_post (sieveInit_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (pairInit_ok h.1) ?_
      intro t inv
      rw [h.2] at inv
      exact ⟨s, inv⟩)
  have finish : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish)
      (fun _ _ => True) := (stackOnly_ct _ rfl).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact init.seq ((relCT_keep_sp pairLoop_ct (fun _ _ ⟨_, _, _, sp⟩ => sp)).seq
    (finish.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidatePair.lean`, which only this module imported.
section

/-! Reuse the paired sieve timing proof without allocating a separate q buffer. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure CandidatePairStart (p : CandidatePoint) (s : State) : Prop where
  context : CandidateContext p.params p.used s
  table : TableData p.params.base p.params.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = p.params.candidate
  oddQ : ((p.params.candidate-1)/2)%2=1

structure CandidatePaired (p : CandidatePoint) (s : State) : Prop where
  start : CandidatePairStart p s
  zero : s.z=candidateShapes p.params

theorem candidatePaired_ok (p : CandidatePoint) (s : State) (h : CandidatePairStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve s (CandidatePaired p) := by
  refine WP.mono (candidatePair_ok h.context h.table h.number h.oddQ) ?_
  rintro t ⟨ctx, table, zero, bytes, _, _⟩
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, h.oddQ⟩, zero⟩

theorem candidatePair_ct : RelCT isa (Two (CandidatePairStart))
    VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve (Two (CandidatePaired)) := by
  refine two_post ?_ (candidatePaired_ok)
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  let xs := Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length
  have length : xs.length = p.params.length := VG.Proof.Bignum.bytesAt_length _ _ _
  have same : Spec.Rsa.bytesAt t.mem (State.addr p.params.out) p.params.length = xs :=
    VG.Proof.Bignum.bytesAt_eq_of_value length (right.number.trans left.number.symm)
  have leftPublic : PairPublic ⟨p.params.out, p.params.base, xs⟩ s := by
    change SieveContext p.params.out p.params.base xs.length s ∧ _
    rw [length]
    exact ⟨left.context.sieve_context left.table, rfl⟩
  have rightPublic : PairPublic ⟨p.params.out, p.params.base, xs⟩ t := by
    change SieveContext p.params.out p.params.base xs.length t ∧ _
    rw [length]
    exact ⟨right.context.sieve_context right.table, same⟩
  exact pairSieve_ct _ _ _ _ _ _ ⟨_, leftPublic, rightPublic, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateScreenPair.lean`, which only this module imported.
section

/-! The paired screening stage depends only on public candidate data. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenPairStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length ≤ p.bytes.length
  oddQ : ((p.candidate-1)/2)%2=1
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate

private def PSieveStart (p : CandidateParams) (s : State) : Prop :=
  CandidatePairStart ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private def PSieveEnd (p : CandidateParams) (s : State) : Prop :=
  CandidatePaired ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private theorem pTable_ok (p : CandidateParams) (s : State) (h : ScreenPairStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) s (PSieveStart p) := by
  refine WP.mono (candidateTable_ok h.context) ?_
  rintro t ⟨ctx, table, changed, _⟩
  have bytes := rsa_bytes_frame (src := State.addr p.out) (k := p.length) changed (by have := p.length_bounds; omega) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact p.outputScratch)
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, h.oddQ⟩, h.enough⟩

theorem candidateScreenPair_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two ScreenPairStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have table : RelCT isa (Two ScreenPairStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite)
      (Two PSieveStart) :=
    two_post (two_map (fun p => (p, p.length)) (fun _ _ h => h.context) tableWrite_ct) pTable_ok
  have sieve : RelCT isa (Two PSieveStart) VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve (Two PSieveEnd) :=
    two_post ((two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1)
      (candidatePair_ct)).mono (fun _ _ h => h) (fun _ _ _ => trivial))
      (fun _ _ h => WP.mono (candidatePaired_ok _ _ h.1) (fun _ post => ⟨post, h.2⟩))
  have branch : RelCT isa (Two PSieveEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.1.zero, right.1.zero]
    · exact two_map (fun p => (⟨p,p.length⟩ : CandidatePoint))
        (fun _ _ h => ⟨h.1.1.start.context,h.1.2,h.1.1.start.oddQ⟩) (screenedTests_ct b v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.1.start.context) candidateRejected_ct
  exact table.seq (sieve.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateScreenP.lean`, which only this module imported.
section

/-! Reject even q before the paired RSA trial sieve and shared witness controller. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenPStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length≤p.bytes.length
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate

private structure QOddChecked (p : CandidateParams) (s : State) : Prop where
  start : ScreenPStart p s
  zero : s.z=decide (((p.candidate-1)/2)%2=1)

private theorem qOdd_checked (p : CandidateParams) (s : State) (h : ScreenPStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) s (QOddChecked p) := by
  refine WP.mono (candidateQOdd_ok h.context h.number) ?_
  rintro t ⟨ctx,zero,memory,_⟩
  exact ⟨⟨ctx,h.enough,by rw [memory]; exact h.number⟩,zero⟩

theorem candidateScreenP_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two ScreenPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have guard : RelCT isa (Two ScreenPStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) (Two QOddChecked) :=
    two_post ((two_map (fun p => (p.out,p.length)) (fun _ _ h => h.context.read_context) qOdd_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) qOdd_checked
  have branch : RelCT isa (Two QOddChecked)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite ?_ ?_ ?_
    · intro p s t a b
      change some s.z=some t.z
      rw [a.zero,b.zero]
    · refine two_map id ?_ (candidateScreenPair_ct b v)
      intro p s h
      refine ⟨h.1.start.context,h.1.start.enough,?_,h.1.start.number⟩
      apply of_decide_eq_true
      have go : some s.z=some true := h.2
      exact h.1.zero.symm.trans (Option.some.inj go)
    · exact two_map (fun p => (⟨p,p.length⟩ : CandidatePoint))
        (fun _ _ h => h.1.start.context) candidateRejected_ct
  exact guard.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidatePost.lean`, which only this module imported.
section

/-! Translate native status, output and entropy count to the public FFDH contract. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

theorem candidatePost_spec {p : CandidateParams} {m : Mem} {r : BitVec 32} (post : candidatePost p m r) :
    let res := Spec.Ffdh.sievedParameterCandidate p.bits p.generator p.bytes
    r.toNat = Proof.Ffdh.candidateStatus res ∧
    Spec.Rsa.bytesAt m (State.addr p.out) p.length =
      (match res with | some (some n, _) => Spec.Rsa.i2osp n p.length | _ => List.replicate p.length 0) ∧
    Spec.Rsa.wordsAt m (State.addr p.usedPtr) 1 =
      [BitVec.ofNat 64 (match res with | some (_, tail) => p.bytes.length - tail.length | none => 0)] := by
  obtain ⟨status, count, bytes⟩ := post
  dsimp only
  rw [← candidateAnswer_spec p]
  cases answer : candidateAnswer p with
  | none =>
    rw [answer] at status count bytes
    exact ⟨by rw [status]; rfl, bytes, count⟩
  | some pair =>
    obtain ⟨pass, tail⟩ := pair
    rw [answer] at status count bytes
    cases pass <;> exact ⟨by rw [status]; rfl, bytes, count⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateCorrect.lean`, which only this module imported.
section

/-! The complete ARMv7 candidate callable satisfies the existing shared FFDH contract. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_correct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) (s : State)
    (pre : (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.ParameterCandidate.code (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s tr t ∧
      abiPreserved s t ∧ (Proof.Ffdh.sievedParameterCandidateContract abi 184).post s t := by
  obtain ⟨p, args⟩ := candidatePublic s pre
  obtain ⟨tr, t, run, preserved, post⟩ := candidateFn_ok b v (candidateInput pre args)
  refine ⟨tr, t, run, preserved, ?_⟩
  have result := candidatePost_spec post
  have widthNat : (s.gpr .r1).toNat = p.length := by
    rw [args.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.length_bounds; omega)]
  have bitsNat : (s.gpr .r3).toNat = p.bits := by
    rw [args.bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.maxBits; omega)]
  have generatorNat : (stackArg s 0).toNat = p.generator := by
    rw [args.generator, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases p.generatorAllowed with eq | eq <;> omega)]
  have tapeNat : (stackArg s 2).toNat = p.bytes.length := by
    rw [args.tapeLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.tapeCount]
  have bytes := args.bytes
  simp only [State.addr] at bytes result
  sig_post [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [args.out, args.used, args.tape, widthNat, bitsNat, generatorNat, tapeNat, bytes]
  exact result

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTResidue2.lean`, which only this module imported.
section

/-! Generator-two filtering branches only on its public low candidate octet. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_map two_ite)

def Residue2Start (p : TrialData) (s : State) : Prop := TrialBuffers p s ∧ p.prime = 3#32

private def Residue2Low (p : TrialData) (s : State) : Prop := Residue2Start p s ∧
  s.z = decide ((p.values[0]?.getD 0).toNat % 8 = 3)

theorem residue2_ct : RelCT isa (Two Residue2Start) VG.Impl.Ffdh.Arm.ParameterCandidate.residue2 (fun _ _ => True) := by
  have lowTrace : RelCT isa (Two Residue2Start) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow)
      (fun _ _ => True) :=
    two_map (fun p : TrialData => (p.dst, p.n)) (fun _ _ h => h.1.1) residueLow_ct
  have low : RelCT isa (Two Residue2Start) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow) (Two Residue2Low) :=
    two_post lowTrace (fun p s h => by
      refine WP.mono (residueLow_ok s p.dst p.n (h.1.1.frame.read (by decide)) (h.1.1.frame.read (by decide))
        h.1.1.out h.1.1.width (h.1.1.readable.low h.1.1.positive)) ?_
      rintro t ⟨⟨flag, memory⟩, rest⟩
      have last : s.mem (State.addr (p.dst + BitVec.ofNat 32 p.n - 1)) = p.values[0]?.getD 0 := h.1.2 0 h.1.1.positive
      rw [last] at flag
      exact ⟨⟨⟨h.1.1.after_memory memory rest, by rw [memory]; exact h.1.2⟩, h.2⟩, flag⟩)
  have branch : RelCT isa (Two Residue2Low)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime 3 [2, 5]) (.block [])) (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · exact (residuePrime_ct 3 [2, 5] (by decide) residue2Equals_taint).mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p, a.1.1, b.1.1, sp⟩) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ _ => trivial)
  exact low.seq branch

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTResidue.lean`, which only this module imported.
section

/-! Complete generator dispatch and congruence filtering depend only on public inputs. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_map two_ite)

def ResiduePublic (p : TrialData × Nat) (s : State) : Prop :=
  TrialBuffers p.1 s ∧ (p.2 = 2 ∨ p.2 = 5) ∧
    s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 p.2

private def ResidueReady (p : TrialData × Nat) (s : State) : Prop :=
  ResiduePublic p s ∧ s.z = decide (p.2 = 2)

private def residueTrial (p : TrialData × Nat) (prime : BitVec 32) : TrialData := { p.1 with prime := prime }

theorem residue_ct : RelCT isa (Two ResiduePublic) VG.Impl.Ffdh.Arm.ParameterCandidate.residue (fun _ _ => True) := by
  have head : RelCT isa (Two ResiduePublic) (.block [.ldrSp .r1 28, .cmp .r1 (.imm 2)]) (Two ResidueReady) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (residueHead_ok h.1.1 (by rcases h.2.1 with eq | eq <;> omega) h.2.2) ?_
      rintro t ⟨⟨flag, memory⟩, rest⟩
      exact ⟨⟨⟨h.1.1.after_memory memory rest, by rw [memory]; exact h.1.2⟩, h.2.1,
        by rw [memory, rest.sp]; exact h.2.2⟩, flag⟩)
  have branch : RelCT isa (Two ResidueReady)
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.residue2 VG.Impl.Ffdh.Arm.ParameterCandidate.residue5) (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · refine two_map (fun p => residueTrial p 3#32) ?_ residue2_ct
      intro p s h
      exact ⟨h.1.1.1, rfl⟩
    · have five := residuePrime_ct 5 [2, 3, 7, 8] (by decide) residue5Equals_taint
      refine two_map (fun p => residueTrial p 5#32) ?_ five
      intro p s h
      exact ⟨h.1.1.1, rfl⟩
  exact head.seq branch

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateResidue.lean`, which only this module imported.
section

/-! Equal public candidate values give identical generator-residue traces. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)

theorem candidateResidue_ct : RelCT isa (Two ScreenPStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.residue (fun _ _ => True) := by
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  let xs := Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length
  have length : xs.length = p.length := VG.Proof.Bignum.bytesAt_length _ _ _
  have same : Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = xs :=
    VG.Proof.Bignum.bytesAt_eq_of_value length (right.number.trans left.number.symm)
  have buffersL := trialBuffers_of_octets (xs := xs) (prime := 0#32) left.context.read_context length rfl
  have buffersR := trialBuffers_of_octets (xs := xs) (prime := 0#32) right.context.read_context length same
  have genL : s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 p.generator := by
    simpa only [candidateValues] using left.context.saved.saved 28 (by simp [candidateSlots])
  have genR : t.mem.readW (State.addr (t.sp + 28#32)) 32 = BitVec.ofNat 32 p.generator := by
    simpa only [candidateValues] using right.context.saved.saved 28 (by simp [candidateSlots])
  exact residue_ct _ _ _ _ _ _ ⟨(⟨p.out, p.length, 0#32, xs.reverse⟩, p.generator), ⟨buffersL, p.generatorAllowed, genL⟩,
    ⟨buffersR, p.generatorAllowed, genR⟩, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateTestP.lean`, which only this module imported.
section

/-! Restore and test p using the public original entropy prefix. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidateTestPStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateContext p.params p.used s ∧ p.params.length ≤ p.params.bytes.length

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateMain.lean`, which only this module imported.
section

/-! Complete native candidate controller timing from public entropy and buffer descriptors. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def CountedStart (p : CandidateParams) (s : State) : Prop :=
  CandidateContext p p.length s ∧ p.length ≤ p.bytes.length

private structure CandidateResidueEnd (p : CandidateParams) (s : State) : Prop where
  start : ScreenPStart p s
  zero : s.z = Spec.Ffdh.generationShape p.bits p.generator p.candidate

private theorem candidateResidueEnd_ok (p : CandidateParams) (s : State) (h : ScreenPStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue s (CandidateResidueEnd p) := by
  refine WP.mono (candidateResidue_ok h.context h.number) ?_
  rintro t ⟨ctx, zero, mem, _⟩
  exact ⟨⟨ctx, h.enough, by rw [mem]; exact h.number⟩, zero⟩

theorem candidateMain_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two CandidateTestPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.main (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  have countTrace : RelCT isa (fun s t => s.sp = t.sp)
      (.block (([.ldrSp .r1 12] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 40))
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct [.ldrSp .r1 12] rfl).seq (save_ct .r1 40))
  have count : RelCT isa (Two CandidateTestPStart)
      (.block (([.ldrSp .r1 12] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 40)) (Two CountedStart) :=
    (two_post (countTrace.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
      (fun p _ h => WP.mono (candidateCount_ok h.1 h.2) (fun _ ⟨ctx, _, _⟩ => (show CountedStart p.params _ from ⟨ctx, h.2⟩)))).mono
      (fun _ _ h => h) (fun _ _ ⟨p, left, right, sp⟩ => ⟨p.params, left, right, sp⟩)
  have shapeTrace : RelCT isa (Two CountedStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (fun _ _ => True) :=
    two_map (fun p => (⟨p.out, p.tape, p.bytes.take p.length, p.bits⟩ : ShapeData)) (fun _ _ h => h.1.shape_context h.2) shapeP_ct
  have shape : RelCT isa (Two CountedStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (Two ScreenPStart) :=
    two_post shapeTrace (fun _ _ h => WP.mono (candidateShape_ok h.1 h.2) (fun _ ⟨ctx, _, number, _, _⟩ => ⟨ctx, h.2, number⟩))
  have residue : RelCT isa (Two ScreenPStart) VG.Impl.Ffdh.Arm.ParameterCandidate.residue (Two CandidateResidueEnd) :=
    two_post candidateResidue_ct candidateResidueEnd_ok
  have branch : RelCT isa (Two CandidateResidueEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact two_map id (fun _ _ h => h.1.start) (candidateScreenP_ct b v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.start.context) candidateRejected_ct
  exact count.seq (shape.seq (residue.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateGuard.lean`, which only this module imported.
section

/-! Short entropy returns and the full native candidate body share the public tape-length guard. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def CandidateRoomEnd (p : CandidatePoint) (s : State) : Prop :=
  CandidateContextStart p s ∧ s.z = decide (p.params.bytes.length < p.params.length)

private theorem candidateRoomEnd_ok (p : CandidatePoint) (s : State) (h : CandidateContextStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) s (CandidateRoomEnd p) := by
  refine WP.mono (initialRoom_ok h.saved.space p.params.tapeCount
    (by have := p.params.length_bounds; omega) (h.saved.saved 20 (by decide)) (h.saved.saved 12 (by decide))) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.after_memory mem rest, zero⟩

theorem candidateGuard_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two CandidateContextStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)])
    (fun _ _ => True) := by
  have room : RelCT isa (Two CandidateContextStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) (Two CandidateRoomEnd) :=
    two_post (initialRoom_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) candidateRoomEnd_ok
  have branch : RelCT isa (Two CandidateRoomEnd)
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code))
      (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.2, right.2]
    · exact two_map id (fun _ _ h => h.1.1) candidateNone_ct
    · refine two_map id ?_ (candidateMain_ct b v)
      intro p s h
      have enough : p.params.length ≤ p.params.bytes.length := by
        have go := h.2
        change some s.z = some false at go
        rw [h.1.2] at go
        have := of_decide_eq_false (Option.some.inj go)
        omega
      exact ⟨h.1.1, enough⟩
  exact room.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTEntry.lean`, which only this module imported.
section

/-! The complete native candidate entry has a fixed stack-address trace. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm

private def entryStores : List (Reg × Nat) := [(.r0, 4), (.r0, 8), (.r1, 12), (.r2, 32), (.r3, 24)]
private def entryCopies : List (Nat × Nat) := [(128, 28), (132, 16), (136, 20), (140, 0), (144, 36)]

theorem candidateEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) (fun s t => s.sp = t.sp) := by
  have zero : RelCT isa LocalAddress (.block [.mov .r0 (.imm 0), .str .r0 .r12 40]) LocalAddress :=
    RelCT.block_append (localZero_ct.seq (storeLocal_ct .r0 40))
  have tail : RelCT isa LocalAddress (.block
      ((entryStores.map fun p => Instr.str p.1 .r12 p.2) ++
        (entryCopies.flatMap fun p => [Instr.ldrSp .r0 p.1, Instr.str .r0 .r12 p.2]) ++
        [.mov .r0 (.imm 0), .str .r0 .r12 40])) LocalAddress :=
    RelCT.block_append ((RelCT.block_append ((localStores_ct entryStores).seq (localCopies_ct entryCopies))).seq zero)
  change RelCT isa _ (.block ([.addSp .r12 0] ++ _)) _
  exact RelCT.block_append (stackAddr_ct.seq (tail.mono (fun _ _ h => h) (fun _ _ h => h.2)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateEntered.lean`, which only this module imported.
section

/-! Native entry snapshots the public candidate arguments before the complete controller. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure CandidateEntryStart (p : CandidateParams) (s : State) : Prop where
  start : CandidateStart p s
  incoming : CandidateIncoming p s
  out : s.gpr .r0 = p.out
  width : s.gpr .r1 = BitVec.ofNat 32 p.length
  used : s.gpr .r2 = p.usedPtr
  bits : s.gpr .r3 = BitVec.ofNat 32 p.bits

private theorem candidateEntryStart_ok (p : CandidateParams) (s : State) (h : CandidateEntryStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) s (CandidateContextStart ⟨p, 0⟩) := by
  refine WP.mono (candidateEntry_ok h.start.locals h.incoming h.out h.width h.used h.bits) ?_
  rintro t ⟨saved, changed, rest⟩
  exact h.start.after_entry saved changed rest

theorem candidateEntered_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two CandidateEntryStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.entry,
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)])
    (fun _ _ => True) :=
  (two_post (candidateEntry_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) candidateEntryStart_ok).seq
    ((candidateGuard_ct b v).mono (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨p, 0⟩, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateFn.lean`, which only this module imported.
section

/-! The common AAPCS frame preserves the full candidate's public timing policy. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateFn_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : RelCT isa (Two CandidateFnInput)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.code (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) (fun _ _ => True) := by
  refine framed_ct (fun _ _ ⟨_, left, right, _⟩ => ⟨by have := left.stackFits; omega, by have := right.stackFits; omega⟩)
    (fun _ _ ⟨_, _, _, sp⟩ => sp) ?_
  refine (candidateEntered_ct b v).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s, t, ⟨p, left, right, sp⟩, rfl, rfl⟩
  exact ⟨p, ⟨left.start, left.incoming, left.out, left.width, left.used, left.bits⟩,
    ⟨right.start, right.incoming, right.out, right.width, right.used, right.bits⟩,
    by change s.sp - 56#32 - 72#32 = t.sp - 56#32 - 72#32; rw [sp]⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateContractCT.lean`, which only this module imported.
section

/-! The native candidate satisfies the public shared FFDH timing contract. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_contract_ct (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) : ConstantTime isa (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre
    (Proof.Ffdh.sievedParameterCandidateContract abi 184).pub (VG.Impl.Ffdh.Arm.ParameterCandidate.code (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) := by
  intro s t trS trT u z hs ht hp runS runT
  obtain ⟨p, args⟩ := candidatePublic s hs
  sig_pub [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have argsT : CandidateAbi p t := {
    out := p0.symm.trans args.out
    width := p1.symm.trans args.width
    used := p2.symm.trans args.used
    bits := p3.symm.trans args.bits
    generator := p4.symm.trans args.generator
    tape := p5.symm.trans args.tape
    tapeLength := p6.symm.trans args.tapeLength
    base := p7.symm.trans args.base
    capacity := p8.symm.trans args.capacity
    bytes := by
      rw [← p5, ← p6, args.tape, args.tapeLength] at byteEq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.tapeCount] at byteEq
      exact byteEq.symm.trans args.bytes }
  exact ((candidateFn_ct b v) _ _ _ _ _ _ ⟨p, candidateInput hs args, candidateInput ht argsT, sp⟩ runS runT).1

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Verified.lean`, which only this module imported.
section

/-! Complete native ARMv7 parameter candidates satisfy the shared public API. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_verified (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) :
    Verified target (VG.Impl.Ffdh.Arm.ParameterCandidate.code (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)
      (Proof.Ffdh.sievedParameterCandidateContract abi 184) :=
  ⟨candidate_correct b v, candidate_contract_ct b v, candidate_sat⟩

/-- The candidate with the product's rewriting of its callers. -/
theorem called_verified (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) :
    Verified target (b.caller.code (VG.Impl.Ffdh.Arm.ParameterCandidate.code
      (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code))
      (Proof.Ffdh.sievedParameterCandidateContract abi 184) :=
  b.caller.verified (candidate_verified b v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/StackPieces.lean`, which only this module imported.
section

/-! Fixed candidate operations do not allocate additional stack frames. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Impl.Ffdh.Arm.ParameterCandidate

theorem shapeP_stack : FrameStack.armStack shapeP = 0 := by decide +kernel
theorem residue_stack : FrameStack.armStack residue = 0 := by decide +kernel
theorem pairSieve_stack : FrameStack.armStack pairSieve = 0 := by decide +kernel
theorem halveQ_stack : FrameStack.armStack halveQ = 0 := by decide +kernel
theorem finNone_stack : FrameStack.armStack finNone = 0 := by decide +kernel
theorem finRejected_stack : FrameStack.armStack finRejected = 0 := by decide +kernel
theorem result_stack : FrameStack.armStack result = 0 := by decide +kernel
theorem drawRange_stack : FrameStack.armStack drawRange = 0 := by decide +kernel
theorem onPass_stack : FrameStack.armStack onPass = 0 := by decide +kernel

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Stack.lean`, which only this module imported.
section

/-! The candidate frame and shared round require at most 184 bytes of stack. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

private theorem op_stack (b : VG.Proof.Bignum.Arm.MontBackend) (o a c : Nat) :
    FrameStack.armStack (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul o a c) = FrameStack.armStack b.mul + 8 := by
  simp only [VG.Impl.Bignum.Arm.MontCall.op, FrameStack.armStack, Nat.max_zero, Nat.zero_max]

private theorem phasePrepared_stack (b : VG.Proof.Bignum.Arm.MontBackend) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared
      (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) = FrameStack.armStack b.mul + 8 := by
  have prepareZero : FrameStack.armStack VG.Impl.Bignum.Arm.PublicFn.prepare = 0 := rfl
  have importZero : FrameStack.armStack VG.Impl.Bignum.Arm.importModulus = 0 := rfl
  have inverseZero : FrameStack.armStack VG.Impl.Bignum.Arm.precomputeInverse = 0 := rfl
  have initZero : FrameStack.armStack VG.Impl.Bignum.Arm.r2Init = 0 := rfl
  have normalizedZero : FrameStack.armStack VG.Impl.Bignum.Arm.NormalizedR2.init = 0 := rfl
  have doubleZero : FrameStack.armStack VG.Impl.Bignum.Arm.doubleLoop = 0 := rfl
  have oneZero : FrameStack.armStack (VG.Impl.Bignum.Arm.smallConst 1 1) = 0 := rfl
  have keyZero : FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.montKeySetup = 0 := rfl
  have expZero : FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.expSetup = 0 := rfl
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared, VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep,
    VG.Impl.Ffdh.Arm.ParameterCandidate.seqs, VG.Impl.Ffdh.Arm.CandidatePrepare.code,
    VG.Impl.Ffdh.Arm.SharedPrepare.code, VG.Impl.Ffdh.Arm.NormalizedPrepare.code,
    VG.Impl.Bignum.Arm.SharedPrecompute.precompute, VG.Impl.Bignum.Arm.NormalizedPrecompute.precompute,
    VG.Impl.Bignum.Arm.SharedR2.r2, VG.Impl.Bignum.Arm.NormalizedR2.r2, VG.Impl.Bignum.Arm.SharedR2.squares,
    FrameStack.armStack, op_stack, prepareZero, importZero, inverseZero, initZero, normalizedZero,
    doubleZero, oneZero, keyZero, expZero, Nat.max_self, Nat.max_zero, Nat.zero_max]

private theorem candidate_code_stack (b : VG.Proof.Bignum.Arm.MontBackend) (name : String) (body : Prog isa) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.code
      (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) name body) =
      max (FrameStack.armStack b.mul + 8) (FrameStack.armStack body) + 128 := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.code, VG.Impl.Ffdh.Arm.framed,
    VG.Impl.Ffdh.Arm.ParameterCandidate.main, VG.Impl.Ffdh.Arm.ParameterCandidate.screenP,
    VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair, VG.Impl.Ffdh.Arm.ParameterCandidate.tests,
    VG.Impl.Ffdh.Arm.ParameterCandidate.screenedTests, VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ,
    VG.Impl.Ffdh.Arm.ParameterCandidate.afterScreenedQ, VG.Impl.Ffdh.Arm.ParameterCandidate.limitedFinal,
    VG.Impl.Ffdh.Arm.ParameterCandidate.test, VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited,
    VG.Impl.Ffdh.Arm.ParameterCandidate.phaseRun, VG.Impl.Ffdh.Arm.ParameterCandidate.millerRabin,
    VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep, VG.Impl.Ffdh.Arm.ParameterCandidate.draw,
    VG.Impl.Ffdh.Arm.ParameterCandidate.round, VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel,
    VG.Impl.Ffdh.Arm.ParameterCandidate.seqs, FrameStack.armStack, List.length_cons, List.length_nil,
    phasePrepared_stack, op_stack, shapeP_stack, residue_stack, pairSieve_stack, halveQ_stack,
    finNone_stack, finRejected_stack, result_stack, drawRange_stack, onPass_stack,
    Nat.max_self, Nat.max_zero, Nat.zero_max, Nat.reduceAdd, Nat.reduceMul]
  omega

theorem candidate_stack (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.code
      (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) ≤ 184 := by
  rw [candidate_code_stack]
  have := v.stack
  have := b.stackOk
  omega

theorem called_stack (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) :
    FrameStack.armStack (b.caller.code (VG.Impl.Ffdh.Arm.ParameterCandidate.code
      (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)) ≤ 184 :=
  (b.caller.stack_le _).trans (candidate_stack b v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

structure ParameterBackend where
  candidate : Prog isa
  candidate_verified : Verified target candidate (Proof.Ffdh.sievedParameterCandidateContract abi 184)
  candidateStack : FrameStack.armStack candidate ≤ 184
  suffix : String
  features : List String

def ParameterBackend.candidateName (b : ParameterBackend) : String :=
  "vg_ffdh_parameter_candidate_sieved" ++ b.suffix

/-- The candidate over the shared product `b`, which calls the round `v`. -/
def parameterBackend (v : VG.Proof.MillerRabin.Arm.RoundImpl) (b : VG.Proof.Bignum.Arm.MontBackend) :
    ParameterBackend := by
  exact {
    candidate := b.caller.code (VG.Impl.Ffdh.Arm.ParameterCandidate.code
      (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code)
    candidate_verified := by exact ParameterCandidate.called_verified b v
    candidateStack := by exact ParameterCandidate.called_stack b v
    suffix := b.suffix
    features := b.features }

/-- The rounds the candidate over `b` is emitted with: the first of `rounds`
whose CPU features are all among `b`'s, so that the candidate needs no
feature beyond those of its product. -/
def roundsFor (b : VG.Proof.Bignum.Arm.MontBackend) (rounds : List VG.Proof.MillerRabin.Arm.RoundImpl) :
    List VG.Proof.MillerRabin.Arm.RoundImpl :=
  (rounds.filter fun v => v.features.all fun f => b.features.contains f).take 1

end VG.Proof.Ffdh.Arm
