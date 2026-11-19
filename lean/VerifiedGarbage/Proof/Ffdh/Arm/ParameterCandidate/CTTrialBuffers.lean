module

public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Impl.Bignum.Arm.TrialDivision16

/-! ### `Ffdh.Arm.ParameterCandidate.CTResiduePrime`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CTTrialSmall`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CTTrialLoop`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.TrialWordCongr`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.TrialLoopWord`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.TrialStepWord`, which this module and modules that import it used -/

section

/-! The exact accumulator, needed to relate public trial-division branch decisions. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/TrialDivision16Value.lean`, which only this module imported.
section

/-! Exact public-value propagation through the RSA/FFDH small-prime reducer. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TrialDivision16
open VG VG.Arm VG.Proof.X25519.Arm

def redcWord (digit acc inverse divisor : BitVec 32) : BitVec 32 :=
  (((((digit + acc) * inverse) <<< 16) >>> 16) * divisor + (digit + acc)) >>> 16

theorem redcWord_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.Arm.TrialDivision16.redc) s fun t =>
      (t.gpr .r2 = redcWord (s.gpr .r5) (s.gpr .r2) (s.gpr .r4) (s.gpr .r3) ∧ t.mem = s.mem) ∧
      Rest [.r2, .r5, .r6] s t := by
  unfold VG.Impl.Bignum.Arm.TrialDivision16.redc VG.Impl.Bignum.Arm.TrialDivision16.redcAt
  refine wp_dp (op2_reg _ _) fun u1 v1 => wp_mul fun u2 v2 => wp_mov (op2_lsl (by decide)) fun u3 v3 =>
    wp_mov (op2_lsr (by decide)) fun u4 v4 => wp_mul fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 =>
      wp_mov (op2_lsr (by decide)) fun t v7 => WP.block_nil ?_
  refine ⟨⟨?_, by rw [v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩,
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans ((v6.rest (by decide)).trans (v7.rest (by decide)))))))⟩
  rw [v7.gpr, v6.gpr, dpVal, v5.gpr, v4.gpr, v3.gpr, v2.gpr, v1.gpr, dpVal,
    v5.other .r5 (by decide), v4.other .r5 (by decide),
    v3.other .r5 (by decide), v2.other .r5 (by decide), v1.gpr, dpVal,
    v4.other .r3 (by decide), v3.other .r3 (by decide), v2.other .r3 (by decide), v1.other .r3 (by decide),
    v1.other .r4 (by decide)]
  rfl

end VG.Proof.Bignum.Arm.TrialDivision16
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm.TrialDivision16

def trialDigitWord (m : Mem) (endPtr : BitVec 32) (n : Nat) : BitVec 32 :=
  (m (State.addr (endPtr - 1))).setWidth 32 |||
    (if n = 1 then (0 : BitVec 32) else (m (State.addr (endPtr - 2))).setWidth 32 <<< 8)

theorem trialStepWord_ok (s : State) {n : Nat} (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n)
    (readLow : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 1)) 1)
    (readHigh : 1 < n → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 2)) 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep s fun t =>
      t.gpr .r2 = redcWord (trialDigitWord s.mem (s.gpr .r0) n) (s.gpr .r2) (s.gpr .r4) (s.gpr .r3) ∧
      t.gpr .r0 = s.gpr .r0 - BitVec.ofNat 32 (min 2 n) ∧
      t.gpr .r1 = BitVec.ofNat 32 (n - min 2 n) ∧ t.z = decide (n ≤ 2) ∧ t.mem = s.mem ∧
      Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep
  refine WP.seq (WP.mono (trialDigit_ok s positive fits count readLow readHigh) ?_)
  rintro u ⟨⟨ptr, cnt, word, mem⟩, rest⟩
  rw [WP.block_append_iff]
  refine WP.mono (redcWord_ok u) ?_
  rintro v ⟨⟨acc, memory⟩, kept⟩
  refine wp_cmp (op2_imm (by decide)) fun t flags zero => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, flags.mem.trans (memory.trans mem),
    (rest.mono (by simp)).trans ((kept.mono (by simp)).trans (flags.rest _))⟩
  · rw [flags.gpr, acc, word, rest.gpr .r2 (by simp), rest.gpr .r4 (by simp), rest.gpr .r3 (by simp)]
    rfl
  · rw [flags.gpr, kept.gpr .r0 (by simp), ptr]
  · rw [flags.gpr, kept.gpr .r1 (by simp), cnt]
  · rw [zero, kept.gpr .r1 (by simp), cnt]
    change (BitVec.ofNat 32 (n - min 2 n) - 0#32 == 0#32) = _
    rw [BitVec.sub_zero]
    change (BitVec.ofNat 32 (n - min 2 n) == (0 : BitVec 32)) = _
    rw [ofNat_beq_zero (by omega_using [fits] : n - min 2 n < 2 ^ 32)]
    exact decide_eq_decide.mpr (by omega_using [])

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Exact accumulator propagation through every native small-prime digit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm.TrialDivision16

def trialWordResult (m : Mem) (endPtr divisor inverse : BitVec 32) (n : Nat) (acc : BitVec 32) : BitVec 32 :=
  if _empty : n = 0 then acc else
    trialWordResult m (endPtr - BitVec.ofNat 32 (min 2 n)) divisor inverse (n - min 2 n)
      (redcWord (trialDigitWord m endPtr n) acc inverse divisor)
termination_by n
decreasing_by omega_using [_empty]

theorem trialLoopWord_ok (s : State) {n : Nat} (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n) (readable : TrialReadable s (s.gpr .r0) n) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) s fun t =>
      t.gpr .r2 = trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    obtain ⟨tr, u, run, value, ptr, cnt, flag, memory, rest⟩ :=
      trialStepWord_ok s positive fits count (readable.low positive) (fun h => readable.high h)
    have recurrence : trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) =
        trialWordResult u.mem (u.gpr .r0) (u.gpr .r3) (u.gpr .r4) (n - min 2 n) (u.gpr .r2) := by
      rw [trialWordResult, dite_eq_right (by omega_using [positive])]
      rw [memory, ptr, value, rest.gpr .r3 (by simp), rest.gpr .r4 (by simp)]
    by_cases last : n ≤ 2
    · have zero : n - min 2 n = 0 := by omega_using [last]
      have result : u.gpr .r2 = trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) := by
        rw [recurrence, zero, trialWordResult, dite_eq_left rfl]
      exact ⟨_, u, .loopExit run (by change some (!u.z) = some false; rw [flag, decide_eq_true last]; rfl), result, memory, rest⟩
    · have smaller : n - min 2 n < n := by omega_using [positive]
      have readU : TrialReadable u (u.gpr .r0) (n - min 2 n) := by
        rw [ptr]
        exact readable.advance rest (Nat.min_le_right 2 n)
      obtain ⟨trT, t, runT, resultT, memoryT, restT⟩ := ih _ smaller u (by omega_using [last]) (by omega_using [fits]) cnt readU
      exact ⟨_, t, .loopNext run (by change some (!u.z) = some true; rw [flag, decide_eq_false last]; rfl) runT,
        resultT.trans recurrence.symm, memoryT.trans memory, rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! The exact reducer result depends only on its public candidate octets and arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm.TrialDivision16

theorem trialWordResult_step (m : Mem) (endPtr divisor inverse : BitVec 32) {n : Nat} (positive : 0 < n)
    (acc : BitVec 32) :
    trialWordResult m endPtr divisor inverse n acc =
      trialWordResult m (endPtr - BitVec.ofNat 32 (min 2 n)) divisor inverse (n - min 2 n)
        (redcWord (trialDigitWord m endPtr n) acc inverse divisor) := by
  rw [trialWordResult, dite_eq_right (by omega_using [positive])]

theorem trialWordResult_congr {m m' : Mem} {endPtr divisor inverse : BitVec 32} {n : Nat} (acc : BitVec 32)
    (bytes : ∀ i < n, m (State.addr (endPtr - BitVec.ofNat 32 (i + 1))) =
      m' (State.addr (endPtr - BitVec.ofNat 32 (i + 1)))) :
    trialWordResult m endPtr divisor inverse n acc = trialWordResult m' endPtr divisor inverse n acc := by
  induction n using Nat.strongRecOn generalizing endPtr acc with
  | ind n ih =>
    by_cases empty : n = 0
    · subst n
      rw [trialWordResult, dite_eq_left rfl, trialWordResult, dite_eq_left rfl]
    · have positive : 0 < n := by omega_using [empty]
      have low : m (State.addr (endPtr - 1)) = m' (State.addr (endPtr - 1)) := bytes 0 positive
      have digit : trialDigitWord m endPtr n = trialDigitWord m' endPtr n := by
        unfold trialDigitWord
        rw [low]
        by_cases one : n = 1
        · rw [ite_eq_left one, ite_eq_left one]
        · rw [ite_eq_right one, ite_eq_right one]
          have high : m (State.addr (endPtr - 2)) = m' (State.addr (endPtr - 2)) := bytes 1 (by omega_using [empty, one])
          rw [high]
      rw [trialWordResult_step m _ _ _ positive acc, trialWordResult_step m' _ _ _ positive acc, digit]
      refine ih _ (by omega_using [empty]) _ ?_
      intro i hi
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      have offset : min 2 n + (i + 1) = min 2 n + i + 1 := by omega_using []
      rw [offset]
      exact bytes _ (by omega_using [hi])

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Trial division has a public byte-count trace and retains an equal public accumulator. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

structure TrialLoopPair (s t : State) : Prop where
  pointer : s.gpr .r0 = t.gpr .r0
  count : s.gpr .r1 = t.gpr .r1
  acc : s.gpr .r2 = t.gpr .r2
  divisor : s.gpr .r3 = t.gpr .r3
  inverse : s.gpr .r4 = t.gpr .r4
  positive : 0 < (s.gpr .r1).toNat
  readLeft : TrialReadable s (s.gpr .r0) (s.gpr .r1).toNat
  readRight : TrialReadable t (t.gpr .r0) (s.gpr .r1).toNat
  bytes : ∀ i < (s.gpr .r1).toNat,
    s.mem (State.addr (s.gpr .r0 - BitVec.ofNat 32 (i + 1))) =
      t.mem (State.addr (s.gpr .r0 - BitVec.ofNat 32 (i + 1)))

theorem trialLoop_ct : RelCT isa TrialLoopPair
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) (fun s t => s.gpr .r2 = t.gpr .r2) := by
  obtain ⟨hint, checked⟩ := trialLoop_taint
  have trace : RelCT isa TrialLoopPair (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) (fun _ _ => True) := by
    refine RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.pointer
    · exact h.count
  intro s t trS trT u v h runS runT
  have countS : s.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have countT : t.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := h.count.symm.trans countS
  obtain ⟨_, u', execS, valueS, _, _⟩ := trialLoopWord_ok s h.positive (s.gpr .r1).isLt countS h.readLeft
  obtain ⟨_, v', execT, valueT, _, _⟩ := trialLoopWord_ok t h.positive (s.gpr .r1).isLt countT h.readRight
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  refine ⟨(trace _ _ _ _ _ _ h runS runT).1, ?_⟩
  change u.gpr .r2 = v.gpr .r2
  rw [valueS, valueT]
  rw [← h.pointer, ← h.acc, ← h.divisor, ← h.inverse]
  exact trialWordResult_congr _ h.bytes

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Complete small-prime reduction, with the branch accumulator determined by public octets. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

structure TrialData where
  dst : BitVec 32
  n : Nat
  prime : BitVec 32
  values : List Byte

def TrialState (p : TrialData) (s : State) : Prop :=
  ReadContext p.dst p.n s ∧ s.gpr .r7 = p.prime ∧
  ∀ i < p.n, s.mem (State.addr (p.dst + BitVec.ofNat 32 p.n - BitVec.ofNat 32 (i + 1))) = p.values[i]?.getD 0

private def TrialReady (p : TrialData) (s : State) : Prop :=
  TrialState p s ∧ s.gpr .r0 = p.dst + BitVec.ofNat 32 p.n ∧ s.gpr .r1 = BitVec.ofNat 32 p.n ∧
  s.gpr .r2 = 0 ∧ s.gpr .r3 = p.prime ∧ s.gpr .r4 = VG.Proof.RsaKeyGen.ninv p.prime

private theorem trialStart_ready (p : TrialData) (s : State) (h : TrialState p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) s (TrialReady p) := by
  refine WP.mono (trialStart_ok s p.dst p.n (h.1.frame.read (by decide)) (h.1.frame.read (by decide))
    (h.1.frame.saved 4 (by decide)) (h.1.frame.saved 12 (by decide))) ?_
  rintro t ⟨⟨ptr, count, acc, prime, inverse, memory⟩, rest⟩
  rw [h.2.1] at prime inverse
  exact ⟨⟨h.1.after_memory memory rest, (rest.gpr .r7 (by simp)).trans h.2.1,
    by rw [memory]; exact h.2.2⟩, ptr, count, acc, prime, inverse⟩

private theorem trialReady_pair {s t : State} (h : Two TrialReady s t) : TrialLoopPair s t := by
  obtain ⟨p, a, b, _⟩ := h
  have countNat : (s.gpr .r1).toNat = p.n := by
    rw [a.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.1.1.countFits]
  refine ⟨a.2.1.trans b.2.1.symm, a.2.2.1.trans b.2.2.1.symm,
    a.2.2.2.1.trans b.2.2.2.1.symm, a.2.2.2.2.1.trans b.2.2.2.2.1.symm,
    a.2.2.2.2.2.trans b.2.2.2.2.2.symm, ?_, ?_, ?_, ?_⟩
  · rw [countNat]; exact a.1.1.positive
  · rw [countNat, a.2.1]; exact a.1.1.readable
  · rw [countNat, b.2.1]; exact b.1.1.readable
  · rw [countNat, a.2.1]
    intro i hi
    exact (a.1.2.2 i hi).trans (b.1.2.2 i hi).symm

theorem trialSmall_ct : RelCT isa (Two TrialState)
    VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall (fun s t => s.gpr .r2 = t.gpr .r2) := by
  have start : RelCT isa (Two TrialState) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) (Two TrialReady) :=
    two_post (trialStart_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) trialStart_ready
  have loop := trialLoop_ct.mono (fun _ _ h => trialReady_pair h) (fun _ _ h => h)
  obtain ⟨hint, checked⟩ := trialFlag_taint
  have flag : RelCT isa (fun s t => s.gpr .r2 = t.gpr .r2)
      VG.Impl.Ffdh.Arm.ParameterCandidate.trialFlag (fun _ _ => True) := by
    refine RelCT.taint (A := taint) (Taint.ofRegs [.r2]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h
  have keep : RelCT isa (fun s t => s.gpr .r2 = t.gpr .r2)
      VG.Impl.Ffdh.Arm.ParameterCandidate.trialFlag (fun s t => s.gpr .r2 = t.gpr .r2) := by
    intro s t trS trT u v h runS runT
    obtain ⟨_, u', execS, _, _, restS⟩ := trialFlag_ok s
    obtain ⟨_, v', execT, _, _, restT⟩ := trialFlag_ok t
    obtain ⟨_, rfl⟩ := Exec.det runS execS
    obtain ⟨_, rfl⟩ := Exec.det runT execT
    exact ⟨(flag _ _ _ _ _ _ h runS runT).1,
      (restS.gpr .r2 (by simp)).trans (h.trans (restT.gpr .r2 (by simp)).symm)⟩
  exact start.seq (loop.seq (keep.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Public generator congruences reuse the same native RSA small-prime reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

def TrialBuffers (p : TrialData) (s : State) : Prop :=
  ReadContext p.dst p.n s ∧
  ∀ i < p.n, s.mem (State.addr (p.dst + BitVec.ofNat 32 p.n - BitVec.ofNat 32 (i + 1))) = p.values[i]?.getD 0

theorem residuePrime_ct (prime : Nat) (values : List Nat) (enc : encodable (BitVec.ofNat 32 prime) = true)
    (cert : CandidateCert [.r2] (VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals values)) :
    RelCT isa (Two fun p s => TrialBuffers p s ∧ p.prime = BitVec.ofNat 32 prime)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime prime values) (fun _ _ => True) := by
  have load : RelCT isa (Two fun p s => TrialBuffers p s ∧ p.prime = BitVec.ofNat 32 prime)
      (.block [.mov .r7 (.imm (BitVec.ofNat 32 prime))]) (Two TrialState) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine wp_mov (op2_imm enc) fun t moved => WP.block_nil ?_
      have rest := moved.rest (by simp : Reg.r7 ∈ [Reg.r7])
      exact ⟨h.1.1.after_memory moved.mem rest, moved.gpr.trans h.2.symm,
        by rw [moved.mem]; exact h.1.2⟩)
  obtain ⟨hint, checked⟩ := cert
  have test : RelCT isa (fun s t => s.gpr .r2 = t.gpr .r2)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals values) (fun _ _ => True) := by
    refine RelCT.taint (A := taint) (Taint.ofRegs [.r2]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h
  exact load.seq (trialSmall_ct.seq (test.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Convert public big-endian candidate octets to the shared reducer's backward reads. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

theorem trialBuffers_of_octets {s : State} {dst prime : BitVec 32} {n : Nat} {xs : List Byte}
    (h : ReadContext dst n s) (length : xs.length = n)
    (bytes : Spec.Rsa.bytesAt s.mem (State.addr dst) n = xs) :
    TrialBuffers ⟨dst, n, prime, xs.reverse⟩ s := by
  refine ⟨h, ?_⟩
  intro i hi
  change i < n at hi
  change s.mem (State.addr (dst + BitVec.ofNat 32 n - BitVec.ofNat 32 (i + 1))) = xs.reverse[i]?.getD 0
  rw [List.getElem?_reverse (by omega_using [length, hi]), length]
  have index : n - 1 - i = n - (i + 1) := by omega_using []
  rw [index, VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega_using [hi]),
    VG.Arm.addr_add (by have := h.bufferFits; omega_using [this])]
  have value := congrArg (fun bs : List Byte => bs[n - (i + 1)]?.getD 0) bytes
  simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega_using [hi] : n - (i + 1) < n),
    Option.map_some, Option.getD_some] using value

end VG.Proof.Ffdh.Arm.ParameterCandidate
