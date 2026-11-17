module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRt
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClear
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `RsaKeyGen.X86.CandidateClearInput`, which this module and modules that import it used -/

section

/-! # Clearing the output retains every input needed by the candidate body -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateClear.lean`, which only this module imported.
section

/-! # Output clearing is complete even when candidate entropy is exhausted -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateClear
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

theorem code_ok {s : State} {base : Addr} {size len : Nat} {out : BitVec 32}
    (S : Scr s base size) (header : 8 ≤ size) (positive : 0 < len) (lengthBound : len < 2 ^ 32)
    (outEq : s.mem.readW (off base 0) 32 = out)
    (lenEq : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 len)
    (fit : out.toNat + len ≤ 2 ^ 32) (write : InRegions s.wr (out.setWidth 64) len) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateClear.code s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = List.replicate len 0 ∧
      t.gpr .eax = 0#32 ∧ Outside (out.setWidth 64) 0 len s.mem t.mem ∧
      Keeps [.esi, .ecx, .eax] s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateClear.code VG.Impl.RsaKeyGen.X86.CandidateClear.args
  refine WP.seq (wp_movS (readSrc_sc S (d := 0) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 4) (by omega)) fun b B _ =>
    wp_movS rfl fun c C _ => WP.block_nil ?_)
  have K : Keeps [.esi, .ecx, .eax] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok positive lengthBound fit
    (by rw [C.other .esi (by decide), B.other .esi (by decide), A.gpr, outEq])
    (by rw [C.other .ecx (by decide), B.gpr, A.mem, lenEq]) C.gpr ?_) fun t ⟨V, Z, O, T⟩ => ?_
  · intro i index
    rw [K.2.2]
    obtain ⟨r, mem, contains⟩ := write
    exact ⟨r, mem, contains.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · exact ⟨V, Z, M ▸ O, K.trans (T.mono (by decide))⟩

end VG.Proof.RsaKeyGen.X86.CandidateClear
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem clear_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateClear.code s fun t =>
      Input E eBytes pBytes entropy t ∧
      Spec.Rsa.bytesAt t.mem (E.out.setWidth 64) E.length = List.replicate E.length 0 ∧
      MutableFrame E s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have lengthPositive : 0 < E.length := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega_using [this]
  have lengthBound : E.length < 2 ^ 32 := CandidateGeometry.native_length_bound v.length
  refine WP.mono_syms (CandidateClear.code_ok I.scratch (by omega_using [space]) lengthPositive lengthBound I.out_eq
    (I.header 1 (by decide)) v.outFit I.outWrite) fun t ⟨zeros, _, O, K⟩ syms => ?_
  have F : Frame [E.outRegion] s.mem t.mem := by
    simpa only [Environment.outRegion, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame O (by omega_using [lengthBound])
  have M : MutableFrame E s.mem t.mem :=
    F.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_append_left _ List.mem_cons_self)
  have readHeader (d : Nat) (fit : d + 4 ≤ E.size) : t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    F.readW (r := E.workspaceRegion) (Offset.contains_base _ fit (by have := I.scratch.nowrap; omega_using [fit, this]))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.outWorkspace.symm) (by decide)
  refine ⟨I.keepMutable v K (by decide) (by decide) M ?_ ?_ (by rw [syms]), zeros, M, K⟩
  · intro i index
    exact (readHeader _ (by omega_using [space, index])).trans (I.header i index)
  · exact (readHeader 44 (by omega_using [space])).trans I.usedPointer

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.CandidateEntry`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateArgContext`, which only this module used -/

section

/-! # Workspace header writes leave every original candidate argument readable -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

def argsRegion (p : BitVec 32) : Region := ⟨(p + 20#32).setWidth 64, 44⟩

structure Context (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base size
  header : 48 ≤ size
  sp : s.gpr .esp = p
  fit : p.toNat + 64 ≤ 2 ^ 32
  separate : (argsRegion p).Disjoint ⟨base, size⟩
  read : ∀ i < 11, readSrc s (.mem (arg i)) = some (inputs i)

theorem Context.address {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {i : Nat} (index : i < 11) :
    s.ea (arg i) = off (argsRegion p).base (4 * i) := by
  change addr (s.gpr .esp) (20 + 4 * i) = _
  rw [C.sp, addr_eq (by have := C.fit; omega_using [index, this])]
  have start : (p + 20#32).setWidth 64 = off (p.setWidth 64) 20 := addr_eq (by have := C.fit; omega_using [this])
  change off (p.setWidth 64) (20 + 4 * i) = off ((p + 20#32).setWidth 64) (4 * i)
  rw [start]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

theorem Context.keep {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s t : State}
    (C : Context base size p inputs s) (K : Keeps [.eax] s t) (F : Frame [⟨base, size⟩] s.mem t.mem) :
    Context base size p inputs t := by
  have spT : t.gpr .esp = p := (K.1 .esp (by decide)).trans C.sp
  have C0 : Context base size p inputs t := by
    refine ⟨C.scratch.of_keeps K (by decide), C.header, spT, C.fit, C.separate, ?_⟩
    intro i index
    have eaT : t.ea (arg i) = s.ea (arg i) := by
      change addr (t.gpr .esp) _ = addr (s.gpr .esp) _
      rw [K.1 .esp (by decide)]
    have memory : t.mem.readW (s.ea (arg i)) 32 = s.mem.readW (s.ea (arg i)) 32 := by
      rw [C.address index]
      exact F.readW (r := argsRegion p)
        (Offset.contains_base _ (by change 4 * i + 4 ≤ 44; omega_using [index]) (by omega_using [index] : 4 * i < 2 ^ 64))
        (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact C.separate) (by decide)
    have same : readSrc t (.mem (arg i)) = readSrc s (.mem (arg i)) := by
      show t.load32 (t.ea (arg i)) = s.load32 (s.ea (arg i))
      simp only [State.load32, eaT, K.2.1, K.2.2, memory]
    exact same.trans (C.read i index)
  exact C0

end VG.Proof.RsaKeyGen.X86.CandidateArgs

end

end

/-! # The cdecl candidate entry establishes its workspace from argument nine -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateArgs.lean`, which only this module imported.
section

/-! # Native argument copying retains the used-output pointer through every round -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

theorem copy_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {i : Nat} (index : i < 11) :
    WP isa (.block (copy i)) s fun t =>
      Context base size p inputs t ∧ t.mem.readW (off base (4 * i)) 32 = inputs i ∧
      Outside base (4 * i) 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold copy
  refine wp_movS (C.read i index) fun a A _ => ?_
  have Sa := C.scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by have := C.header; omega)) (Sa.write (by have := C.header; omega)) fun t T => WP.block_nil ?_
  have O : Outside base (4 * i) 4 s.mem t.mem := by
    rw [T.mem, A.mem]
    exact writeW32_outside _ _ _ (by omega)
  have K := A.keeps.widen (T.keeps [])
  have F : Frame [⟨base, size⟩] s.mem t.mem := VG.Proof.MillerRabin.X86.workspaceGlobalFrame (g := ⟨base, size, 0⟩) (rs := [(4 * i, 4)])
    (Outs.of_outside O (List.mem_singleton_self _))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change 4 * i + 4 ≤ size; have := C.header; omega)
  exact ⟨C.keep K F, by rw [T.mem, Mem.readW_writeW_self32, A.gpr], O, K⟩

theorem copies_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {n : Nat} (bound : n ≤ 11) :
    WP isa (copies n) s fun t =>
      Context base size p inputs t ∧ (∀ i < n, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      Outside base 0 (4 * n) s.mem t.mem ∧ Keeps [.eax] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨C, by intro i index; omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | succ n ih =>
    change WP isa (.seq (copies n) (.block (copy n))) s _
    refine WP.seq (WP.mono (ih C (by omega)) fun a ⟨A, valuesA, Oa, Ka⟩ => ?_)
    refine WP.mono (copy_ok A (by omega)) fun t ⟨T, valueT, Ot, Kt⟩ => ?_
    refine ⟨T, ?_, ?_, Ka.trans Kt⟩
    · intro i index
      by_cases last : i = n
      · subst i; exact valueT
      · have same := BitVec.eq_of_toNat_eq (Ot.w32 (d := 4 * i) (by omega) (by omega))
        exact same.trans (valuesA i (by omega))
    · exact (Oa.mono (by decide) (by omega)).trans (Ot.mono (by omega) (by omega))

theorem code_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) :
    WP isa code s fun t =>
      Context base size p inputs t ∧ (∀ i < 11, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      t.mem.readW (off base 44) 32 = inputs 2 ∧ Outside base 0 48 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold code
  refine WP.seq (WP.mono (copies_ok C (by decide : 11 ≤ 11)) fun a ⟨A, valuesA, Oa, Ka⟩ => ?_)
  unfold saveUsed
  refine wp_movS (readSrc_sc A.scratch (d := 8) (by have := C.header; omega)) fun b B _ => ?_
  have Kb := Ka.trans B.keeps
  have Sb := C.scratch.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (by have := C.header; omega)) (Sb.write (by have := C.header; omega)) fun t T => WP.block_nil ?_
  have Ot : Outside base 44 4 a.mem t.mem := by
    rw [T.mem, B.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Kbt := B.keeps.widen (T.keeps [])
  have F : Frame [⟨base, size⟩] a.mem t.mem := VG.Proof.MillerRabin.X86.workspaceGlobalFrame (g := ⟨base, size, 0⟩) (rs := [(44, 4)])
    (Outs.of_outside Ot (List.mem_singleton_self _))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact C.header)
  refine ⟨A.keep Kbt F, ?_, ?_, (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)), Ka.trans Kbt⟩
  · intro i index
    exact (BitVec.eq_of_toNat_eq (Ot.w32 (d := 4 * i) (Or.inl (by omega)) (by omega))).trans (valuesA i index)
  · rw [T.mem, Mem.readW_writeW_self32, B.gpr]
    exact valuesA 2 (by decide)

end VG.Proof.RsaKeyGen.X86.CandidateArgs
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.RsaKeyGen.X86.CandidateArgs

structure Entry (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s : State) : Prop where
  workspace : Ws s base size
  header : 48 ≤ size
  pointer : (inputs 9).setWidth 64 = base
  stack : StkOk p base size
  sp : s.gpr .esp = p
  fit : p.toNat + 64 ≤ 2 ^ 32
  separate : (argsRegion p).Disjoint ⟨base, size⟩
  read : ∀ i < 11, readSrc s (.mem (arg i)) = some (inputs i)

theorem enter_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (E : Entry base size p inputs s) :
    WP isa enter s fun t =>
      Context base size p inputs t ∧ (∀ i < 11, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      t.mem.readW (off base 44) 32 = inputs 2 ∧ Outside base 0 48 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  unfold enter
  refine WP.seq (wp_movS (E.read 9 (by decide)) fun a A _ => WP.block_nil ?_)
  have Sa : Scr a base size := by
    refine ⟨?_, ?_, E.workspace.nowrap, ?_⟩
    · rw [A.gpr]; exact E.pointer
    · rw [A.keeps.2.2]; exact E.workspace.wr
    · rw [A.other .esp (by decide), E.sp]; exact E.stack
  have C : Context base size p inputs a := by
    refine ⟨Sa, E.header, (A.other .esp (by decide)).trans E.sp, E.fit, E.separate, ?_⟩
    intro i index
    have address : a.ea (arg i) = s.ea (arg i) := by
      change addr (a.gpr .esp) _ = addr (s.gpr .esp) _
      rw [A.other .esp (by decide)]
    have same : readSrc a (.mem (arg i)) = readSrc s (.mem (arg i)) := by
      show a.load32 (a.ea (arg i)) = s.load32 (s.ea (arg i))
      simp only [State.load32, address, A.keeps.2.1, A.keeps.2.2, A.mem]
    exact same.trans (E.read i index)
  refine WP.mono (code_ok C) fun t ⟨T, values, usedPtr, O, K⟩ => ?_
  rw [A.mem] at O
  exact ⟨T, values, usedPtr, O, (A.keeps.mono (by decide)).widen K⟩

end VG.Proof.RsaKeyGen.X86.CandidateArgs

end

end

/-! ### `RsaKeyGen.X86.CandidateResultSpec`, which only this module used -/

section

/-! # Native candidate results agree with the shared candidate operation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

def StepOutputs (E : Environment) (entropy : List Byte)
    (result : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand)) (s : State) : Prop :=
  match result with
  | none => Outputs E 0 0 (List.replicate E.length 0) s
  | some (.prime c, rest) => Outputs E 1 (entropy.length - rest.length) (Spec.Rsa.i2osp c E.length) s
  | some (.close, rest) => Outputs E 2 (entropy.length - rest.length) (List.replicate E.length 0) s
  | some (.rejected, rest) => Outputs E 3 (entropy.length - rest.length) (List.replicate E.length 0) s

theorem filtered_outputs_eq {E : Environment} (e : Nat) (p : Option Nat) (entropy : List Byte)
    (enough : E.length ≤ entropy.length) (s : State) :
    FilteredOutputs E e p entropy s ↔ StepOutputs E entropy
      (VG.Proof.RsaKeyGen.afterDraw (8 * E.length) e p (candidateValue E entropy) (entropy.drop E.length)) s := by
  have count : entropy.length - (entropy.length - E.length) = E.length := by omega_using [enough]
  unfold FilteredOutputs SieveOutputs ExponentOutputs VG.Proof.RsaKeyGen.afterDraw
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) p (candidateValue E entropy)
  · cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
    · by_cases gcd : Nat.gcd (candidateValue E entropy - 1) e = 1
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_iff_eq, gcd]
        unfold PrimalityOutputs
        cases test : Spec.RsaKeyGen.primalityTest (candidateValue E entropy) (entropy.drop E.length) with
        | none => rfl
        | some pr => obtain ⟨prime, rest⟩ := pr; cases prime <;> rfl
      · simp [gcd, StepOutputs, count]
    · simp [StepOutputs, count]
  · simp [StepOutputs, count]

theorem candidate_outputs_eq {E : Environment} (v : E.Valid) (eBytes pBytes entropy : List Byte)
    (enough : E.length ≤ entropy.length) (s : State) :
    FilteredOutputs E (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy s ↔
      StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) s := by
  unfold Spec.RsaKeyGen.candidateOp
  rw [VG.Proof.RsaKeyGen.candidateStep_eq E.length _ _ _ (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega_using [this])]
  rw [VG.Proof.RsaKeyGen.ite_t enough]
  simpa only [candidateValue, VG.Proof.RsaKeyGen.seg, List.drop_zero] using
    filtered_outputs_eq (E := E) (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy enough s

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Native argument entry and the complete candidate body satisfy the shared operation -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateAvailable.lean`, which only this module imported.
section

/-! # The candidate drawn and filtered at its run-time width, then tested -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Outputs.keepFlags {E : Environment} {status count : Nat} {bytes : List Byte} {s t : State}
    (O : Outputs E status count bytes s) (F : Fupd s t) : Outputs E status count bytes t := by
  unfold Outputs at O ⊢
  rw [F.gpr, F.mem]
  exact O

theorem available_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round) s fun t =>
      FilteredOutputs E (Spec.Rsa.os2ip eBytes) (Spec.RsaKeyGen.otherPrime pBytes) entropy t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.available
  refine WP.seq (WP.mono (front_rt_ok v I zeros enough) fun d ⟨front, Fd, Kd⟩ => ?_)
  refine WP.seq (wp_cmpS rfl fun e Ee Z => WP.block_nil ?_)
  have Fe : MutableFrame E s.mem e.mem := by rw [Ee.mem]; exact Fd
  have Ke : Keeps WitnessStep.clob s e := Kd.widen (Ee.keeps [])
  unfold FrontOutputs at front
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)
  · rw [close] at front
    simp only [Bool.false_eq_true, ↓reduceIte] at front
    cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E entropy)
    · rw [composite] at front
      simp only [Bool.false_eq_true, ↓reduceIte] at front
      obtain ⟨De, four⟩ := front
      refine WP.ite true (by change e.zf = _; rw [Z, four]; rfl) (fun _ => ?_) (fun bad => nomatch bad)
      have Dd := De.keepMem v Ee.mem (Ee.keeps []) (by decide) (by decide) Ee.syms
      refine WP.mono (exponent_result_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Dd enough)
        fun t ⟨output, Ft, Kt⟩ => ?_
      exact ⟨by simpa only [FilteredOutputs, SieveOutputs, close, composite, Bool.false_eq_true, ↓reduceIte]
        using output, Fe.trans Ft, Ke.trans Kt⟩
    · rw [composite] at front
      simp only [↓reduceIte] at front
      refine WP.ite false (by change e.zf = _; rw [Z, front.1]; rfl) (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.block_nil ⟨?_, Fe, Ke⟩
      simpa only [FilteredOutputs, SieveOutputs, close, composite, Bool.false_eq_true, ↓reduceIte] using
        front.keepFlags Ee
  · rw [close] at front
    simp only [↓reduceIte] at front
    refine WP.ite false (by change e.zf = _; rw [Z, front.1]; rfl) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.block_nil ⟨?_, Fe, Ke⟩
    simpa only [FilteredOutputs, close, ↓reduceIte] using front.keepFlags Ee

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateNoEntropy.lean`, which only this module imported.
section

/-! # Exhaustion before drawing a candidate returns zero status and zero consumption -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem no_entropy_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateFinish.none s fun t =>
      Outputs E 0 0 (List.replicate E.length 0) t ∧ MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.mono (CandidateFinish.none_ok I.scratch (by have H : 256 ≤ E.size := v.geometry.headerFit; omega)
    I.usedWrite I.usedPointer) fun t ⟨statusEq, memory, O, K⟩ => ?_
  refine ⟨⟨statusEq, ?_, ?_⟩, used_frame O, K.mono (by unfold WitnessStep.clob; decide)⟩
  · exact (VG.Proof.Bignum.scratch_bytes O (by have := v.outFit; omega) v.outUsed).trans zeros
  · rw [memory, Mem.readW_writeW_self64]

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFront.lean`, which only this module imported.
section

/-! # Clearing, the public entropy guard, and width dispatch implement the candidate operation -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem front_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) :
    WP isa (.seq VG.Impl.RsaKeyGen.X86.Candidate.clear
      (.seq (.block [.mov .eax (.mem (sc 32)), .alu .cmp .eax (.mem (sc 4))])
        (.ite .b VG.Impl.RsaKeyGen.X86.CandidateFinish.none
          (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round)))) s fun t =>
      StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have lengthBound : E.length < 2 ^ 32 := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  refine WP.seq (WP.mono (clear_ok v I) fun a ⟨Ia, zeros, F, K⟩ => ?_)
  refine WP.seq (wp_movS (readSrc_sc Ia.scratch (d := 32) (by omega)) fun b B _ =>
    WP.mono (cmp_src_cf (readSrc_sc (Ia.scratch.of_keeps B.keeps (by decide)) (d := 4) (by omega)))
      fun d ⟨C, carry⟩ => ?_)
  have M : d.mem = a.mem := C.mem.trans B.mem
  have Ka : Keeps [.eax] a d := B.keeps.widen (C.keeps [])
  have Id := Ia.keepMem v M Ka (by decide) (by decide) (C.syms.trans B.syms)
  have zd : Spec.Rsa.bytesAt d.mem (E.out.setWidth 64) E.length = List.replicate E.length 0 := by rw [M]; exact zeros
  have Fd : MutableFrame E s.mem d.mem := by rw [M]; exact F
  have Kd : Keeps WitnessStep.clob s d := (K.mono (by unfold WitnessStep.clob; decide)).trans (Ka.mono (by unfold WitnessStep.clob; decide))
  have condition : isa.eval .b d = some (decide (E.randLength < E.length)) := by
    change d.cf = _
    rw [carry, B.gpr, B.mem, Ia.header 8 (by decide), Ia.header 1 (by decide)]
    change some (decide ((BitVec.ofNat 32 E.randLength).toNat < (BitVec.ofNat 32 E.length).toNat)) = _
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.randLengthFit, Nat.mod_eq_of_lt lengthBound]
  by_cases enough : E.length ≤ E.randLength
  · refine WP.ite false (by rw [condition, decide_eq_false (by omega)]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (available_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Id zd enough)
      fun t ⟨output, Ft, Kt⟩ => ?_
    exact ⟨(candidate_outputs_eq v eBytes pBytes entropy (by rw [Id.memory.entropyLength]; exact enough) t).mp output,
      Fd.trans Ft, Kd.trans Kt⟩
  · refine WP.ite true (by rw [condition, decide_eq_true (by omega)]) (fun _ => ?_) (fun bad => nomatch bad)
    refine WP.mono (no_entropy_ok v Id zd) fun t ⟨output, Ft, Kt⟩ => ?_
    have exhausted : ¬ E.length ≤ entropy.length := by rw [Id.memory.entropyLength]; exact enough
    have spec : Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy = none := by
      unfold Spec.RsaKeyGen.candidateOp
      rw [VG.Proof.RsaKeyGen.candidateStep_eq E.length _ _ _ (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega),
        VG.Proof.RsaKeyGen.ite_f exhausted]
    exact ⟨by rw [spec]; exact output, Fd.trans Ft, Kd.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

structure EntryInput (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop where
  arguments : CandidateArgs.Entry E.base E.size E.p E.argument s
  outWrite : InRegions s.wr (E.out.setWidth 64) E.length
  usedWrite : VG.Proof.Mont.X86.Rt.Ws s (E.used.setWidth 64) 8
  memory : MemoryFacts E eBytes pBytes entropy s

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem enter_input_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : EntryInput E eBytes pBytes entropy s) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateArgs.enter s fun t =>
      Input E eBytes pBytes entropy t ∧ WorkFrame E s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  refine WP.mono_syms (CandidateArgs.enter_ok I.arguments) fun t ⟨C, header, used, O, K⟩ syms => ?_
  have F : Frame [E.workspaceRegion] s.mem t.mem :=
    workspaceGlobalFrame (g := E.geometry) (Outs.of_outside O List.mem_cons_self)
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change 0 + 48 ≤ E.size; have := v.geometry.headerFit; change 256 ≤ E.size at this; omega_using [this])
  have frame : WorkFrame E s.mem t.mem := F.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)
  exact ⟨⟨C.scratch, C.sp, header, used, by rw [K.2.2]; exact I.outWrite,
    I.usedWrite.of_keeps K, I.memory.keep v K frame (by rw [syms])⟩, frame, K⟩

theorem body_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : EntryInput E eBytes pBytes entropy s) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) s fun t =>
      StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps bodyClob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.body
  refine WP.seq (WP.mono (enter_input_ok v I) fun a ⟨Ia, F, K⟩ => ?_)
  refine WP.mono (front_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Ia)
    fun t ⟨output, Ft, Kt⟩ => ?_
  exact ⟨output, F.mutable.trans Ft, (K.mono (by unfold bodyClob; decide)).trans
    (Kt.mono (by unfold WitnessStep.clob bodyClob; decide))⟩

end VG.Proof.RsaKeyGen.X86.Candidate
