module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResultContext
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ClearOutput
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishHead
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status

/-! ### `Ffdh.Arm.ParameterCandidate.Finish`, which only this module used -/

section

/-! Final candidate returns preserve an accepted p and clear every failed output. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/FinishWord.lean`, which only this module imported.
section

/-! Return the candidate status and write a complete u64 entropy count. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem finish_ok (s : State) (usedPtr : BitVec 32) (status count : Nat)
    (statusBound : status ≤ 2) (countBound : count < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 32#32)) 4)
    (pointer : s.mem.readW (State.addr (s.sp + 32#32)) 32 = usedPtr)
    (output : OutputBuffer usedPtr 8 s) (value : s.gpr .r3 = BitVec.ofNat 32 count) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 status ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 count] ∧
      Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2] s t := by
  have write0 : InRegions s.wr (State.addr usedPtr) 4 := by
    simpa only [BitVec.add_zero] using
      CallLay.inRegions_sub output.writable (off := 0) (by decide : 0 + 4 ≤ 8) (by decide)
  have write4 : InRegions s.wr (off (State.addr usedPtr) 4) 4 :=
    CallLay.inRegions_sub output.writable (by decide : 4 + 4 ≤ 8) (by decide)
  have addr4 : State.addr (usedPtr + 4#32) = off (State.addr usedPtr) 4 :=
    VG.Arm.addr_add (by have := output.fits; omega)
  have enc : encodable (BitVec.ofNat 32 status) = true := encodable_byte (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : status < 2 ^ 32)]
    omega)
  have run : WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 status ∧
        t.mem = (s.mem.writeW (State.addr usedPtr) (BitVec.ofNat 32 count)).writeW
          (off (State.addr usedPtr) 4) (0 : BitVec 32)) ∧ Rest [.r0, .r1, .r2] s t := by
    refine withRest_all [.r0, .r1, .r2] ?_ (by rfl) (by rfl)
    unfold VG.Impl.Ffdh.Arm.ParameterCandidate.finish
    ffrun [BitVec.add_zero, read, pointer, write0, write4, addr4, value, enc]
  refine WP.mono run ?_
  rintro t ⟨⟨result, memory⟩, rest⟩
  refine ⟨result, ?_, ?_, rest⟩
  · rw [memory]
    exact VG.Proof.Ffdh.Arm.KeySearch.usedMem_words s.mem usedPtr count countBound
  · rw [memory]
    exact VG.Proof.Ffdh.Arm.KeySearch.usedMem_frame s.mem usedPtr (BitVec.ofNat 32 count)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem bytes_after_used {s t : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) (changed : Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n :=
  rsa_bytes_frame changed (by have := h.countFits; omega_using [this]) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.outputUsed)

private theorem finishConsumed_ok {s : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (h : ResultContext dst usedPtr n consumed s) (bound : status ≤ 2) :
    WP isa (.block (([.ldrSp .r3 40] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 status ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 consumed] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n ∧
      Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3] s t := by
  have saved : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 consumed := by
    simpa only [resultValues] using h.saved.saved 40 (by simp [resultSlots])
  rw [WP.block_append_iff]
  refine wp_loadStack (a := State.addr (s.sp + 40#32)) (by decide) rfl
    (h.saved.read (by decide)) fun u loaded => WP.block_nil ?_
  have memory := loaded.mem
  have rest : Rest [.r3] s u := loaded.rest (by simp)
  have ctx := h.after_memory memory rest
  have pointer : u.mem.readW (State.addr (u.sp + 32#32)) 32 = usedPtr := by
    simpa only [resultValues] using ctx.saved.saved 32 (by simp [resultSlots])
  refine WP.mono (finish_ok u usedPtr status consumed bound h.consumedFits
    (ctx.saved.read (by decide)) pointer ctx.used (loaded.gpr.trans saved)) ?_
  rintro t ⟨result, words, changed, restT⟩
  rw [memory] at changed
  exact ⟨result, words, bytes_after_used h changed, changed,
    (rest.mono (by simp)).trans (restT.mono (by simp))⟩

theorem finAccepted_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 1 ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 consumed] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n ∧
      Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  refine WP.mono (finishConsumed_ok h (status := 1) (by decide)) ?_
  rintro t ⟨result, words, bytes, changed, rest⟩
  exact ⟨result, words, bytes, changed.mono (by simp), rest.mono (by simp)⟩

theorem finRejected_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 2 ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 consumed] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected, WP.seq_iff]
  refine WP.mono (clearOutput_ok h) ?_
  rintro u ⟨ctx, cleared, changed, rest⟩
  refine WP.mono (finishConsumed_ok ctx (status := 2) (by decide)) ?_
  rintro t ⟨result, words, bytes, changedT, restT⟩
  exact ⟨result, words, bytes.trans cleared,
    (changed.mono (by simp)).trans (changedT.mono (by simp)),
    (rest.mono (by simp)).trans (restT.mono (by simp))⟩

private theorem finishZero_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa (.block (([.mov .r3 (.imm 0)] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.finish 0)) s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 0 ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 0] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.bytesAt s.mem (State.addr dst) n ∧
      Frame [⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3] s t := by
  rw [WP.block_append_iff]
  refine wp_mov (op2_imm (v := (0 : BitVec 32)) (by decide)) fun u moved => WP.block_nil ?_
  have rest : Rest [.r3] s u := moved.rest (by simp)
  have ctx := h.after_memory moved.mem rest
  have pointer : u.mem.readW (State.addr (u.sp + 32#32)) 32 = usedPtr := by
    simpa only [resultValues] using ctx.saved.saved 32 (by simp [resultSlots])
  refine WP.mono (finish_ok u usedPtr 0 0 (by decide) (by decide)
    (ctx.saved.read (by decide)) pointer ctx.used moved.gpr) ?_
  rintro t ⟨result, words, changed, restT⟩
  rw [moved.mem] at changed
  exact ⟨result, words, bytes_after_used h changed, changed,
    (rest.mono (by simp)).trans (restT.mono (by simp))⟩

theorem finNone_ok {s : State} {dst usedPtr : BitVec 32} {n consumed : Nat}
    (h : ResultContext dst usedPtr n consumed s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finNone s fun t =>
      t.gpr .r0 = BitVec.ofNat 32 0 ∧
      Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 0] ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.finNone, WP.seq_iff]
  refine WP.mono (clearOutput_ok h) ?_
  rintro u ⟨ctx, cleared, changed, rest⟩
  refine WP.mono (finishZero_ok ctx) ?_
  rintro t ⟨result, words, bytes, changedT, restT⟩
  exact ⟨result, words, bytes.trans cleared,
    (changed.mono (by simp)).trans (changedT.mono (by simp)),
    (rest.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Candidate returns use the exact tape suffix, encoded p, and API status. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Result.lean`, which only this module imported.
section

/-! Interpret the native phase status as the candidate API's output and count. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

def ResultPost (s : State) (dst usedPtr : BitVec 32) (n consumed status : Nat) (t : State) : Prop :=
  t.gpr .r0 = BitVec.ofNat 32 status ∧
  Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 (if status = 0 then 0 else consumed)] ∧
  Spec.Rsa.bytesAt t.mem (State.addr dst) n =
    (if status = 1 then Spec.Rsa.bytesAt s.mem (State.addr dst) n else List.replicate n 0) ∧
  Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t

private theorem ResultPost.trans_pre {s u t : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (post : ResultPost u dst usedPtr n consumed status t) (memory : u.mem = s.mem) (rest : Rest [] s u) :
    ResultPost s dst usedPtr n consumed status t := by
  obtain ⟨result, words, bytes, changed, kept⟩ := post
  refine ⟨result, words, ?_, ?_, (rest.mono (by simp)).trans kept⟩
  · simpa only [memory] using bytes
  · simpa only [memory] using changed

private theorem resultTail_ok {s : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (h : ResultContext dst usedPtr n consumed s) (bound : status ≤ 2) (nonzero : status ≠ 0)
    (word : s.gpr .r3 = BitVec.ofNat 32 status) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block [.cmp .r3 (.imm 1)], .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected]) s (ResultPost s dst usedPtr n consumed status) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (cmpStatus_ok status 1 (by omega) (by decide) word) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases one : status = 1
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true one]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (finAccepted_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [one]
    exact (show ResultPost u dst usedPtr n consumed 1 t from returned).trans_pre memory rest
  · have two : status = 2 := by omega
    refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false one]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (finRejected_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [two]
    exact (show ResultPost u dst usedPtr n consumed 2 t from returned).trans_pre memory rest

theorem result_ok {s : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (h : ResultContext dst usedPtr n consumed s) (bound : status ≤ 2)
    (word : s.gpr .r3 = BitVec.ofNat 32 status) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.result s (ResultPost s dst usedPtr n consumed status) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.result VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (cmpStatus_ok status 0 (by omega) (by decide) word) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases none : status = 0
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true none]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (finNone_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [none]
    exact (show ResultPost u dst usedPtr n consumed 0 t from returned).trans_pre memory rest
  · refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false none]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (resultTail_ok ctx bound none ((rest.gpr .r3 (by simp)).trans word)) ?_
    intro t returned
    refine WP.block_nil ?_
    exact returned.trans_pre memory rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

def candidateReturnRegions (p : CandidateParams) (sp : BitVec 32) : List Region :=
  ⟨State.addr p.usedPtr, 8⟩ :: candidateRegions p sp

def CandidateReturn (p : CandidateParams) (answer : Option (Bool × List Byte)) (s t : State) : Prop :=
  t.gpr .r0 = BitVec.ofNat 32 (witnessResultStatus answer) ∧
  Spec.Rsa.wordsAt t.mem (State.addr p.usedPtr) 1 =
    [BitVec.ofNat 64 (match answer with | none => 0 | some (_, rest) => p.bytes.length - rest.length)] ∧
  Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length =
    (match answer with | some (true, _) => Spec.Rsa.i2osp p.candidate p.length | _ => List.replicate p.length 0) ∧
  Frame (candidateReturnRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t

theorem witnessResultStatus_bound (answer : Option (Bool × List Byte)) : witnessResultStatus answer ≤ 2 := by
  cases answer with
  | none => decide
  | some pair => obtain ⟨pass, rest⟩ := pair; cases pass <;> simp only [witnessResultStatus] <;> omega_using []

theorem CandidateReturn.trans_pre {s u t : State} {p : CandidateParams} {answer : Option (Bool × List Byte)}
    {rs : List Reg} (post : CandidateReturn p answer u t)
    (changed : Frame (candidateRegions p s.sp) s.mem u.mem) (rest : Rest rs s u)
    (clobbers : ∀ r ∈ rs, r ∈ roundClobbers) : CandidateReturn p answer s t := by
  obtain ⟨status, count, bytes, frame, restT⟩ := post
  rw [rest.sp] at frame
  exact ⟨status, count, bytes, (changed.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans frame,
    (rest.mono clobbers).trans restT⟩

private theorem candidateReturn_of_result {s : State} {p : CandidateParams} {used : Nat} {answer : Option (Bool × List Byte)}
    (h : CandidateContext p used s)
    (suffix : ∀ pass rest, answer = some (pass, rest) → rest = p.bytes.drop used)
    (number : ∀ rest, answer = some (true, rest) →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    ∀ t, ResultPost s p.out p.usedPtr p.length used (witnessResultStatus answer) t → CandidateReturn p answer s t := by
  rintro t ⟨result, words, bytes, changed, rest⟩
  refine ⟨result, ?_, ?_, changed.mono (by simp [candidateReturnRegions, candidateRegions]),
    rest.mono (by simp [roundClobbers])⟩
  · cases ha : answer with
    | none => simpa [ha, witnessResultStatus] using words
    | some pair =>
      obtain ⟨pass, tail⟩ := pair
      have tailEq := suffix pass tail ha
      change Spec.Rsa.wordsAt t.mem (State.addr p.usedPtr) 1 = [BitVec.ofNat 64 (p.bytes.length - tail.length)]
      rw [tailEq, List.length_drop]
      have usedEq : p.bytes.length - (p.bytes.length - used) = used := by have := h.consumedBound; omega_using [this]
      rw [usedEq]
      cases pass <;> simpa [ha, witnessResultStatus] using words
  · cases ha : answer with
    | none => simpa [ha, witnessResultStatus] using bytes
    | some pair =>
      obtain ⟨pass, tail⟩ := pair
      cases pass with
      | false => simpa [ha, witnessResultStatus] using bytes
      | true =>
        have encoded := (VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)).symm
        have size : (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length).length = p.length := by simp [Spec.Rsa.bytesAt]
        rw [size, number tail ha] at encoded
        exact (show Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length =
          Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length from by simpa [ha, witnessResultStatus] using bytes).trans encoded

theorem candidateResult_ok {s : State} {p : CandidateParams} {used : Nat} {answer : Option (Bool × List Byte)}
    (h : CandidateContext p used s)
    (status : s.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus answer))
    (suffix : ∀ pass rest, answer = some (pass, rest) → rest = p.bytes.drop used)
    (number : ∀ rest, answer = some (true, rest) →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.result s (CandidateReturn p answer s) :=
  WP.mono (result_ok h.result_context (witnessResultStatus_bound answer) status)
    (candidateReturn_of_result h suffix number)

theorem candidateRejected_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected s
      (CandidateReturn p (some (false, p.bytes.drop used)) s) := by
  refine WP.mono (finRejected_ok h.result_context) ?_
  intro t returned
  exact candidateReturn_of_result h (by intro pass tail eq; cases eq; rfl)
    (by intro tail eq; cases eq) t returned

theorem candidateNone_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finNone s (CandidateReturn p none s) := by
  refine WP.mono (finNone_ok h.result_context) ?_
  intro t returned
  exact candidateReturn_of_result h (by intro pass tail eq; cases eq)
    (by intro tail eq; cases eq) t returned

end VG.Proof.Ffdh.Arm.ParameterCandidate
