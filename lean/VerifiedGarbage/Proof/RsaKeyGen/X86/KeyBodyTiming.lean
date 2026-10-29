module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBody
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.Framework.X86.RelCT

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpCode
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExportState
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEntry
import VerifiedGarbage.Proof.Framework.KernelRfl
/-! # The complete native key body obeys the shared public exponent and retry leak -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyClearExport.lean`, which only this module imported.
section

/-! # Clear the output-mask zero array independently of inverse scratch contents -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Impl.Mont.X86.Dynamic

theorem clearExport_ok {E : Environment} {s : State} (h : Input E s) (bit : slot s.mem E.base kOk ≤ 1) :
    WP isa (zerosW (VG.Impl.Rsa.X86.Keys.slot E.n aZero) (E.n + 2)) s fun t =>
      ExportState E t ∧ Keeps [.eax, .ebp, .edx] s t := by
  have fits := h.ws.arr_fit (j := aZero) (by decide)
  refine WP.mono (zerosW_ok h.ws.workspace (by omega) fits) fun t ⟨O, zero, K⟩ => ?_
  change Outside E.base (arr E.n aZero) (S E.n) s.mem t.mem at O
  change val32 t.mem E.base (arr E.n aZero) (E.n + 2) = 0 at zero
  have clear : Keep E.base E.n [aZero] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O) (by unfold S; omega) (by simp)
  have header : ∀ d, d + 4 ≤ hdr → slot t.mem E.base d = slot s.mem E.base d :=
    fun d hd => clear.slot hd (by simp)
  have input : Input E t := h.keep (h.ws.rest K) K (by
    intro d hd
    apply BitVec.eq_of_toNat_eq
    exact header d (by unfold hdr; omega))
  have lowZero : num t.mem E.base E.n aZero = 0 := by
    have H := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := E.n) (by omega)
    simpa only [Nat.mul_zero, Nat.add_zero] using H
  exact ⟨⟨input, lowZero, by rw [header kOk (by decide)]; exact bit⟩, K⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyExportTiming.lean`, which only this module imported.
section

/-! # All seven masked key outputs have a public address trace -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Impl.Mont.X86.Dynamic

structure ExportPair (E : Environment) (s t : State) : Prop where
  left : ExportState E s
  right : ExportState E t
  stack : s.gpr .esp = t.gpr .esp
  agree : VG.X86.Taint.Agree (workspaceTaint true) s t

theorem ExportPair.output {E : Environment} {s t : State} (P : ExportPair E s t) : OutputPair E s t :=
  ⟨⟨P.left.input, P.right.input, P.stack⟩, P.agree, P.left.bit, P.right.bit⟩

theorem clearExport_trace (E : Environment) :
    RelCT isa (OutputPair E) (zerosW (VG.Impl.Rsa.X86.Keys.slot E.n aZero) (E.n + 2)) (ExportPair E) := by
  intro s t tr ur u v P A C
  have checked : KeyPublic (zerosW (VG.Impl.Rsa.X86.Keys.slot E.n aZero) (E.n + 2)) :=
    ⟨zerosHint true, zerosTaint true, zeros_check true _ _, rfl⟩
  obtain ⟨trace, agree⟩ := key_public_trace checked _ _ _ _ _ _ P.2.1 A C
  obtain ⟨leftState, leftKeeps⟩ := wp_result (clearExport_ok P.1.left P.2.2.1) A
  obtain ⟨rightState, rightKeeps⟩ := wp_result (clearExport_ok P.1.right P.2.2.2) C
  refine ⟨trace, leftState, rightState, ?_, agree⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.1.stack

theorem writePort_pair_trace (E : Environment) (i : Nat) (hi : i < 7) :
    RelCT isa (ExportPair E) (writePort E.n i) (ExportPair E) := by
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := writePort_trace E i hi _ _ _ _ _ _ P.output A C
  obtain ⟨leftState, leftKeeps⟩ := wp_result (P.left.port_ok hi) A
  obtain ⟨rightState, rightKeeps⟩ := wp_result (P.right.port_ok hi) C
  refine ⟨trace, leftState, rightState, ?_, agree⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.stack

theorem writePorts_trace (E : Environment) (i count : Nat) (bound : i + count ≤ 7) :
    RelCT isa (ExportPair E) (writePorts E.n i count) (ExportPair E) := by
  induction count generalizing i with
  | zero => exact RelCT.block_nil (fun _ _ P => P)
  | succ count ih =>
    exact RelCT.seq (writePort_pair_trace E i (by omega)) (ih (i + 1) (by omega))

theorem writeOutputs_trace (E : Environment) :
    RelCT isa (OutputPair E) (writeOutputs E.n) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold writeOutputs seqs
  apply RelCT.seq (clearExport_trace E)
  apply RelCT.seq (writePorts_trace E 0 7 (by decide))
  have checked : KeyPublic (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc kStatus))]) :=
    ⟨.block [], workspaceTaint true, rfl, rfl⟩
  exact (key_public_trace checked).mono (fun _ _ P => P.agree) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeySizedTiming.lean`, which only this module imported.
section

/-! # Complete native key assembly is constant time modulo its public exponent and retry result -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key

theorem sized_trace (E : Environment) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (SizedStart E e p q p' q') (sized E.n) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold sized seqs
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.assoc
  exact RelCT.seq (inputReady_trace E e p q p' q')
    (RelCT.seq (deriveOutput_trace E e p q p' q' release) (writeOutputs_trace E))

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyDispatchTiming.lean`, which only this module imported.
section

/-! # Public native key width dispatch retains all secret input snapshots -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.Candidate
open VG.Impl.RsaKeyGen.X86.Key

theorem SizedStart.keepFlags {E : Environment} {e p q p' q' : Nat} {s t u v : State}
    (P : SizedStart E e p q p' q' s t) (U : Fupd s u) (V : Fupd t v) : SizedStart E e p q p' q' u v := by
  have left := P.inputs.left.keep (P.inputs.left.ws.rest (U.keeps [])) (U.keeps [])
    (by intro d hd; rw [U.mem])
  have right := P.inputs.right.keep (P.inputs.right.ws.rest (V.keeps [])) (V.keeps [])
    (by intro d hd; rw [V.mem])
  refine ⟨⟨left, right, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [U.gpr, V.gpr]
    exact P.inputs.stack
  · rw [U.mem]
    exact P.leftExponent
  · rw [V.mem]
    exact P.rightExponent
  · rw [U.mem]
    exact P.leftP
  · rw [U.mem]
    exact P.leftQ
  · rw [V.mem]
    exact P.rightP
  · rw [V.mem]
    exact P.rightQ

theorem dispatch_trace (E : Environment) (e p q p' q' w : Nat) (width : E.n = 4 * w) (small : w < 2 ^ 32)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ()))
    (choices : List Nat) (member : w ∈ choices) (bounded : ∀ v ∈ choices, v < 2 ^ 32) :
    RelCT isa (WithValue (SizedStart E e p q p' q') (BitVec.ofNat 32 w)) (dispatch choices) (fun _ _ => True) := by
  induction choices with
  | nil => cases member
  | cons v rest ih =>
    unfold dispatch
    have compare := compare_value_trace (P := SizedStart E e p q p' q') (BitVec.ofNat 32 w) (BitVec.ofNat 32 v)
      (fun _ _ _ _ P U V => P.keepFlags U V)
    rw [width_comparison small (bounded v List.mem_cons_self)] at compare
    by_cases same : w = v
    · rw [decide_eq_true same] at compare
      refine RelCT.seq compare (branch_true ?_)
      rw [← same, ← width]
      exact (sized_trace E e p q p' q' release).mono (fun _ _ P => P.1) (fun _ _ _ => trivial)
    · rw [decide_eq_false same] at compare
      exact RelCT.seq compare (branch_false (ih (List.mem_cons.mp member |>.resolve_left same)
        (fun j hj => bounded j (List.mem_cons_of_mem _ hj))))

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyWidthTiming.lean`, which only this module imported.
section

/-! # The public modulus byte count becomes the native key width -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Candidate
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.Key

theorem widthArgs_ok {E : Environment} {s : State} (h : Input E s) :
    WP isa (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) s fun t =>
      Input E t ∧ t.mem = s.mem ∧ t.gpr .eax = BitVec.ofNat 32 (E.primeLength / 8) ∧ Keeps [.eax] s t := by
  have valid := h.valid.length
  have dimensions := h.valid.widths
  have lengthBound : 2 * E.primeLength < 2 ^ 32 := by omega
  have widthBound : E.primeLength / 8 < 2 ^ 32 := by omega
  have head := h.ws.hdr_le
  refine wp_movS (readSrc_sc h.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.hdr at head; omega))
    fun a A _ => wp_shr (by decide) fun t T _ => WP.block_nil ?_
  have memory := T.mem.trans A.mem
  have K : Keeps [.eax] s t := A.keeps.trans T.keeps
  refine ⟨h.keep (h.ws.rest K) K (by intro d hd; rw [memory]), memory, ?_, K⟩
  rw [T.gpr, A.gpr, h.arguments 1 (by decide)]
  change BitVec.ofNat 32 (2 * E.primeLength) >>> 4 = BitVec.ofNat 32 (E.primeLength / 8)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt lengthBound, Nat.mod_eq_of_lt widthBound]
  change (2 * E.primeLength) / 16 = E.primeLength / 8
  omega

theorem widthArgs_trace (E : Environment) (e p q p' q' : Nat) :
    RelCT isa (SizedStart E e p q p' q') (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4])
      (WithValue (SizedStart E e p q p' q') (BitVec.ofNat 32 (E.primeLength / 8))) := by
  intro s t tr ur u v P A C
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    checkedBlockInvariant rfl rfl
  obtain ⟨leftInput, leftMem, leftValue, leftKeeps⟩ := wp_result (widthArgs_ok P.inputs.left) A
  obtain ⟨rightInput, rightMem, rightValue, rightKeeps⟩ := wp_result (widthArgs_ok P.inputs.right) C
  refine ⟨(raw _ _ _ _ _ _ P.inputs.agree A C).1, ?_, leftValue, rightValue⟩
  refine ⟨⟨leftInput, rightInput, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact P.inputs.stack
  · rw [leftMem]
    exact P.leftExponent
  · rw [rightMem]
    exact P.rightExponent
  · rw [leftMem]
    exact P.leftP
  · rw [leftMem]
    exact P.leftQ
  · rw [rightMem]
    exact P.rightP
  · rw [rightMem]
    exact P.rightQ

theorem front_trace (E : Environment) (v : E.Valid) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (SizedStart E e p q p' q')
      (.seq (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) (dispatch widths)) (fun _ _ => True) := by
  have lengths := v.length
  have width : E.n = 4 * (E.primeLength / 8) := by
    unfold Environment.n
    obtain ⟨_, _, _⟩ := lengths
    omega
  have bounds : 4 ≤ E.primeLength / 8 ∧ E.primeLength / 8 ≤ 64 := by
    obtain ⟨_, _, _⟩ := lengths
    omega
  apply RelCT.seq (widthArgs_trace E e p q p' q')
  apply dispatch_trace E e p q p' q' (E.primeLength / 8) width (by omega) release widths
  · exact List.mem_map.mpr ⟨E.primeLength / 8 - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    omega

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyEntryTiming.lean`, which only this module imported.
section

/-! # Copying the eighteen native key arguments has a public address trace -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateArgs

def EntryPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Entry base size p inputs s ∧ Entry base size p inputs t

theorem pointer_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (S : Entry base size p inputs s) :
    WP isa (.block [.mov .edi (.mem (arg 16))]) s fun t => t.gpr .edi = inputs 16 ∧ Keeps [.edi] s t := by
  refine wp_movS (S.read 16 (by decide)) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem pointer_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) (.block [.mov .edi (.mem (arg 16))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  intro s t tr ur u v ⟨S, T⟩ A C
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (arg 16))])
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  have start : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact S.sp.trans T.sp.symm)
  obtain ⟨leftValue, leftKeeps⟩ := wp_result (pointer_ok S) A
  obtain ⟨rightValue, rightKeeps⟩ := wp_result (pointer_ok T) C
  refine ⟨(raw _ _ _ _ _ _ start A C).1, agree_regs ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact S.sp.trans T.sp.symm
  · exact leftValue.trans rightValue.symm

theorem enter_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) VG.Impl.RsaKeyGen.X86.Key.enter (fun _ _ => True) := by
  have copied : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (copies 18) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ H => H)
      (hc := VG.Taint.hintOf taint (τr [.esp, .edi]) (copies 18))
    kernel_rfl
  exact RelCT.seq pointer_trace copied

end VG.Proof.RsaKeyGen.X86.KeyArgs
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure BodyPair (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop where
  left : EntryInput E sp s
  right : EntryInput E sp t
  leftExponent : inputExponent E s.mem = e
  rightExponent : inputExponent E t.mem = e
  leftP : inputPrime E s.mem 2 = p
  leftQ : inputPrime E s.mem 3 = q
  rightP : inputPrime E t.mem 2 = p'
  rightQ : inputPrime E t.mem 3 = q'

theorem enterInput_trace (E : Environment) (v : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.enter (SizedStart E e p q p' q') := by
  intro s t tr ur u z P A C
  have trace := (KeyArgs.enter_trace _ _ _ _ _ _ ⟨P.left.arguments, P.right.arguments⟩ A C).1
  obtain ⟨leftInput, leftFrame, leftKeeps⟩ := wp_result (enter_input_ok v P.left) A
  obtain ⟨rightInput, rightFrame, rightKeeps⟩ := wp_result (enter_input_ok v P.right) C
  refine ⟨trace, ⟨⟨leftInput, rightInput, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact P.left.arguments.sp.trans P.right.arguments.sp.symm
  · unfold inputExponent
    rw [leftInput.exponent_preserved leftFrame]
    exact P.leftExponent
  · unfold inputExponent
    rw [rightInput.exponent_preserved rightFrame]
    exact P.rightExponent
  · unfold inputPrime
    rw [leftInput.output_preserved (by decide : 2 < 7) leftFrame]
    exact P.leftP
  · unfold inputPrime
    rw [leftInput.output_preserved (by decide : 3 < 7) leftFrame]
    exact P.leftQ
  · unfold inputPrime
    rw [rightInput.output_preserved (by decide : 2 < 7) rightFrame]
    exact P.rightP
  · unfold inputPrime
    rw [rightInput.output_preserved (by decide : 3 < 7) rightFrame]
    exact P.rightQ

theorem body_trace (E : Environment) (v : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.body (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u z P A C
  have raw : RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.body (fun _ _ => True) :=
    RelCT.seq (enterInput_trace E v sp e p q p' q') (front_trace E v e p q p' q' release)
  refine ⟨(raw _ _ _ _ _ _ P A C).1, agree_regs ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [Exec.gpr KeyNoSp.body_noSp A, Exec.gpr KeyNoSp.body_noSp C]
  exact P.left.arguments.sp.trans P.right.arguments.sp.symm

end VG.Proof.RsaKeyGen.X86.Key
