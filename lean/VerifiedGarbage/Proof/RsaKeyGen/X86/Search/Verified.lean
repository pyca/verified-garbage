module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CT
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePreparedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpLoop
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClear
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Code
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultTiming
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStackUse
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRt
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop

/-! ### `RsaKeyGen.X86.CandidateABIValid`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.CandidateBody`, which the modules that import this one used -/

section

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

end

end

/-! ### `RsaKeyGen.X86.CandidateABIRegions`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateABIGeometry`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateABITable`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateABISeparate`, which this module and modules that import it used -/

section

/-! # The candidate signature separates every writable buffer from live inputs and the call frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

def inputRegions (E : Environment) : List Region := [E.exponentRegion, E.otherRegion, E.randRegion]
def reservedRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 152#64, 152⟩

structure CallSeparation (s : State) : Prop where
  outUsed : (callEnvironment s).outRegion.Disjoint (callEnvironment s).usedRegion
  outWorkspace : (callEnvironment s).outRegion.Disjoint (callEnvironment s).workspaceRegion
  usedWorkspace : (callEnvironment s).usedRegion.Disjoint (callEnvironment s).workspaceRegion
  argsWorkspace : (⟨argAddr s 0, 44⟩ : Region).Disjoint (callEnvironment s).workspaceRegion
  readWrite : ∀ r ∈ inputRegions (callEnvironment s), ∀ R ∈ (callEnvironment s).writeRegions, r.Disjoint R
  stackFar : ∀ r ∈ (callEnvironment s).writeRegions ++ inputRegions (callEnvironment s), r.Disjoint (reservedRegion s)
  returnFar : ∀ r ∈ (callEnvironment s).writeRegions, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r
  tableHeld : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts,
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
    t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s)

theorem call_separation {s : State} (h : contract.pre s) : CallSeparation s := by
  sig_pre [contract, Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    packed_length, stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  all_goals dsimp only [callEnvironment, inputRegions, reservedRegion, Environment.outRegion,
    Environment.usedRegion, Environment.workspaceRegion, Environment.exponentRegion, Environment.otherRegion,
    Environment.randRegion, Environment.base, Environment.size, Environment.writeRegions,
    VG.Impl.RsaKeyGen.TrialTable32.consts]
  all_goals try simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, forall_eq_or_imp, forall_eq]
  all_goals repeat' apply And.intro
  all_goals simp only [Nat.mul_comm] at *
  all_goals first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # The shared signature supplies the native sieve table as a readable immutable object -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont

theorem table_regions (s : State) :
    Abi.constRegions (fun n => (s.syms n).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts = [(callEnvironment s).tableRegion] := by
  rw [VG.Impl.RsaKeyGen.TrialTable32.consts, Abi.constRegions_cons, Abi.constRegions_nil, packed_length]
  rfl

theorem CallLayout.readRegions {s : State} (A : CallLayout s) : s.rd = (callEnvironment s).readRegions := by
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, A.rdPrefix, A.rdTable, table_regions]
  rfl

theorem CallSeparation.tableProperties {s : State} (A : CallSeparation s) :
    (callEnvironment s).tableRegion.base.toNat + 8192 ≤ 2 ^ 32 ∧
    (∀ r ∈ s.wr, (callEnvironment s).tableRegion.Disjoint r) ∧
    (callEnvironment s).tableRegion.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧
    (callEnvironment s).tableRegion.Disjoint (reservedRegion s) := by
  have member : (callEnvironment s).tableRegion ∈ Abi.constRegions (fun n => (s.syms n).setWidth 64)
      VG.Impl.RsaKeyGen.TrialTable32.consts := by rw [table_regions]; exact List.mem_cons_self
  exact A.tableFar _ member

private theorem held_word {m : Mem} {f : String → Addr} {tables : List (String × List (BitVec 64))}
    {name : String} {words : List (BitVec 64)} (H : Abi.constsHeld m f tables)
    (member : (name, words) ∈ tables) {i : Nat} (bound : i < words.length) :
    m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words[i] := by
  rw [H (name, words) member i bound, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]

theorem CallSeparation.tableWords {s : State} (A : CallSeparation s) (i : Nat) (index : i < 1024) :
    s.mem.readW (off ((callEnvironment s).table.setWidth 64) (8 * i)) 64 =
      BitVec.ofNat 64 (VG.Impl.RsaKeyGen.TrialTable32.entry i) := by
  have bound : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by rw [packed_length]; exact index
  have member : (VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed) ∈
      VG.Impl.RsaKeyGen.TrialTable32.consts := List.mem_cons_self
  have held := held_word A.tableHeld member bound
  exact held.trans (VG.Proof.RsaKeyGen.TrialTable32.packed_entry index)

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Signature separation yields the exact native candidate frame bounds -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

private theorem disjoint_bounds {a b : Addr} {n k : Nat}
    (_an : a.toNat + n ≤ 2 ^ 64) (_bk : b.toNat + k ≤ 2 ^ 64) (np : 0 < n) (kp : 0 < k)
    (D : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  by_contra bad
  have overlap : a.toNat < b.toNat + k ∧ b.toNat < a.toNat + n := by omega_using [bad]
  by_cases order : a.toNat ≤ b.toNat
  · apply D b
    · change (b - a).toNat + 1 ≤ n
      rw [BitVec.toNat_sub]
      omega_using [bad, order]
    · change (b - b).toNat + 1 ≤ k
      rw [BitVec.sub_self]; change 0 + 1 ≤ k; omega_using [kp]
  · apply D a
    · change (a - a).toNat + 1 ≤ n
      rw [BitVec.sub_self]; change 0 + 1 ≤ n; omega_using [np]
    · change (a - b).toNat + 1 ≤ k
      rw [BitVec.toNat_sub]
      omega_using [bad, order]

theorem CallLayout.privateNat {s : State} (A : CallLayout s) :
    (callEnvironment s).p.toNat = (s.gpr .esp).toNat - 16 := sub_toNat (by have := A.low; omega_using [this])

theorem CallLayout.reservedNat {s : State} (A : CallLayout s) :
    (reservedRegion s).base.toNat = (s.gpr .esp).toNat - 152 := by
  change ((s.gpr .esp).setWidth 64 - 152#64).toNat = _
  rw [← Taint.sub_setWidth A.low, BitVec.toNat_setWidth, sub_toNat A.low,
    Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])]

theorem CallLayout.workspaceStack {s : State} (A : CallLayout s) (Z : CallSizes s) (D : CallSeparation s) :
    (callEnvironment s).p.toNat ≤ (callEnvironment s).base.toNat ∨
    (callEnvironment s).base.toNat + (callEnvironment s).size + 136 ≤ (callEnvironment s).p.toNat := by
  have g := CandidateGeometry.geometry_valid (workspace := (callEnvironment s).base) Z.length Z.capacity
  have nonempty : 0 < (callEnvironment s).size := by
    have := g.headerFit
    change 256 ≤ 8 * (arg s 10).toNat at this
    change 0 < 8 * (arg s 10).toNat
    omega_using [this]
  have far := D.stackFar (callEnvironment s).workspaceRegion (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have fit : (callEnvironment s).base.toNat + (callEnvironment s).size ≤ 2 ^ 32 := by
    change ((arg s 9).setWidth 64).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 9).isLt (by decide))]
    exact A.workspaceFit
  have rn : ((s.gpr .esp).setWidth 64 - 152#64).toNat = (s.gpr .esp).toNat - 152 := A.reservedNat
  have bounds := disjoint_bounds (Nat.le_trans fit (by decide)) (n := (callEnvironment s).size) (k := 152)
    (by rw [rn]; have := A.low; have := (s.gpr .esp).isLt; omega_using []) nonempty (by decide) far
  rw [rn] at bounds
  rw [A.privateNat]
  have low := A.low
  change (callEnvironment s).base.toNat + (callEnvironment s).size ≤ (s.gpr .esp).toNat - 152 ∨
    (s.gpr .esp).toNat - 152 + 152 ≤ (callEnvironment s).base.toNat at bounds
  omega_using [nonempty, bounds]

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # The ABI's reserved stack contains both candidate frames and the saved registers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem CallLayout.writeMember {s : State} (A : CallLayout s) {r : Region}
    (mem : r ∈ (callEnvironment s).writeRegions) : r ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_left _ mem

theorem CallSeparation.stackAll {s : State} (_A : CallLayout s) (D : CallSeparation s) :
    ∀ r ∈ (callEnvironment s).writeRegions ++ (callEnvironment s).readRegions, r.Disjoint (reservedRegion s) := by
  intro r mem
  rcases List.mem_append.mp mem with mem | mem
  · exact D.stackFar r (List.mem_append_left _ mem)
  · change r ∈ inputRegions (callEnvironment s) ++ [(callEnvironment s).tableRegion] at mem
    rcases List.mem_append.mp mem with mem | mem
    · exact D.stackFar r (List.mem_append_right _ mem)
    · obtain rfl := List.mem_singleton.mp mem
      exact D.tableProperties.2.2.2

theorem CallSeparation.readWriteAll {s : State} (A : CallLayout s) (D : CallSeparation s) :
    ∀ r ∈ (callEnvironment s).readRegions, ∀ R ∈ (callEnvironment s).writeRegions, r.Disjoint R := by
  intro r mem R write
  change r ∈ inputRegions (callEnvironment s) ++ [(callEnvironment s).tableRegion] at mem
  rcases List.mem_append.mp mem with mem | mem
  · exact D.readWrite r mem R write
  · obtain rfl := List.mem_singleton.mp mem
    exact D.tableProperties.2.1 R (A.writeMember write)

theorem CallLayout.savedSub {s : State} (A : CallLayout s) :
    (⟨(callEnvironment s).p.setWidth 64, 16⟩ : Region).Sub (reservedRegion s) := by
  have reserved : reservedRegion s = below (s.gpr .esp) 152 := by
    unfold reservedRegion below
    rw [Taint.sub_setWidth A.low]
  rw [reserved]
  exact below_sub (by decide) A.low

theorem CallLayout.bodyStackSub {s : State} (A : CallLayout s) :
    (below (callEnvironment s).p 136).Sub (reservedRegion s) := by
  have reserved : reservedRegion s = below (s.gpr .esp) 152 := by
    unfold reservedRegion below
    rw [Taint.sub_setWidth A.low]
  rw [reserved]
  exact below_inner (by decide) A.low

theorem call_args_address (s : State) : ((callEnvironment s).p + 20#32).setWidth 64 = argAddr s 0 := by
  change ((s.gpr .esp - 16#32 + 20#32).setWidth 64) = ((s.gpr .esp + 4#32).setWidth 64)
  congr 1
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Every state admitted by the shared candidate contract satisfies its native geometry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem call_valid {s : State} (h : contract.pre s) : (callEnvironment s).Valid := by
  have A := call_layout h
  have Z := call_sizes h
  have D := call_separation h
  refine ⟨Z.length, Z.exponentLength, Z.otherLength, Z.capacity,
    A.workspaceFit, A.outFit, A.usedFit, A.exponentFit, A.otherFit, A.randFit, (arg s 8).isLt,
    ?_, ?_, ?_, A.workspaceStack Z D, ?_, ?_, D.outUsed, D.outWorkspace, D.usedWorkspace,
    D.readWriteAll A, ?_⟩
  · have fit := D.tableProperties.1
    change ((s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64).toNat + 8192 ≤ 2 ^ 32 at fit
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (s.syms _).isLt (by decide))] at fit
    exact fit
  · rw [A.privateNat]
    have := A.low
    omega_using [this]
  · rw [A.privateNat]
    have := A.low
    have := A.argsFit
    omega_using [this]
  · intro r mem
    exact (D.stackAll A r mem).sub_right A.savedSub
  · rw [call_args_address]
    exact D.argsWorkspace
  · intro r mem
    exact (D.stackAll A r mem).sub_right A.bodyStackSub

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.CandidateVerified`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.CandidateSatisfiable`, which only this module used -/

section

/-! # A concrete native caller satisfies the candidate contract and its static table -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 32
  | 2 => 0x2000
  | 3 => 0x3000
  | 4 => 3
  | 5 => 0x4000
  | 6 => 0
  | 7 => 0x5000
  | 8 => 0
  | 9 => 0x10000
  | _ => 544

def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 44 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x3000, 3⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 4352⟩, ⟨0x20004, 44⟩]
  syms _ := 0x30000

theorem sat_arguments (i : Nat) (index : i < 11) : arg satState i = satArgument i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega_using [index]
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, packed_length]

theorem sat_table : Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by rw [packed_length]; decide
  have small : i < 1024 := by simpa only [packed_length] using index
  have ix : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by rw [packed_length]; exact small
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  have held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i ix
  refine Eq.trans (Mem.readW_congr (m := satMemory) (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_) held
  intro j bound
  have index := small
  have address : ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat =
      65532 + 8 * i + j := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [small, bound]
  change (if _ then _ else _) = _
  apply ite_eq_right
  intro inside
  exfalso
  apply (show ¬ ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 44 from by
    change ¬ ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 44
    rw [address]
    omega_using []) inside

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts,
    stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_arguments 8 (by decide),
    sat_arguments 9 (by decide), sat_arguments 10 (by decide)]
  simp only [packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.RsaKeyGen.primeLenValid; decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.CandidateABIMemory`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.CandidateABIArgs`, which only this module used -/

section

/-! # The outer register push preserves all eleven cdecl arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem call_argument (s : State) (i : Nat) (index : i < 11) : (callEnvironment s).argument i = arg s i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega_using [index]
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Environment.argument, callEnvironment, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem CallLayout.argumentOffset {s : State} (A : CallLayout s) {i : Nat} (index : i < 11) :
    argAddr s i = off (argAddr s 0) (4 * i) := by
  have fit := A.argsFit
  change addr (s.gpr .esp) (4 + 4 * i) = off (addr (s.gpr .esp) 4) (4 * i)
  rw [addr_eq (by omega_using [index, fit]), addr_eq (by omega_using [fit])]
  exact (Offset.add_add _ _ _).symm

theorem CallLayout.pushedArgument {s : State} (A : CallLayout s) {i : Nat} (index : i < 11) :
    readSrc (Compact.entered s) (.mem (VG.Impl.RsaKeyGen.X86.CandidateArgs.arg i)) = some (arg s i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have separate : (⟨argAddr s 0, 44⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 44⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by have := A.argsFit; omega_using [this])]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (⟨argAddr s 0, 44⟩ : Region).Contains (argAddr s i) 4 := by
    rw [A.argumentOffset index]
    exact Offset.contains_base _ (by omega_using [index]) (by omega_using [index])
  have word := F.readW (w := 32) contains (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact separate) (by decide)
  change (Compact.entered s).load32 ((Compact.entered s).ea (VG.Impl.Mont.X86.Compact.arg i)) = _
  rw [Compact.argument_address]
  have access : InRegions ((Compact.entered s).rd ++ (Compact.entered s).wr) (argAddr s i) 4 := by
    change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (argAddr s i) 4
    refine ⟨⟨argAddr s 0, 44⟩, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), contains⟩
    rw [A.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [State.load32, ite_eq_left access]
  exact congrArg some word

theorem entry_arguments {s : State} (h : contract.pre s) :
    CandidateArgs.Entry (callEnvironment s).base (callEnvironment s).size (callEnvironment s).p
      (callEnvironment s).argument (Compact.entered s) := by
  have A := call_layout h
  have v := call_valid h
  have space : 256 ≤ (callEnvironment s).size := v.geometry.headerFit
  refine ⟨⟨?_, ?_⟩, by omega_using [space], rfl, ?_, ?_, v.argsFit, v.argsFar, ?_⟩
  · change (callEnvironment s).workspaceRegion ∈ below (s.gpr .esp) 16 :: s.wr
    exact List.mem_cons_of_mem _ (A.writeMember (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · change ((arg s 9).setWidth 64).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 9).isLt (by decide))]
    exact A.workspaceFit
  · refine ⟨by have := v.low; omega_using [this], ?_⟩
    rcases v.workspaceStack with left | right
    · exact Or.inl left
    · exact Or.inr (by omega_using [right])
  · rw [Compact.entered, pushed_esp]
    rfl
  · intro i index
    rw [call_argument s i index]
    exact A.pushedArgument index

end VG.Proof.RsaKeyGen.X86.Candidate

end

end


/-! # Saving registers retains the contract's original input snapshots and static table -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def callEBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
def callPBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat
def callEntropy (s : State) : List Byte := Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat

theorem call_memory {s : State} (h : contract.pre s) :
    MemoryFacts (callEnvironment s) (callEBytes s) (callPBytes s) (callEntropy s) s := by
  have A := call_layout h
  have D := call_separation h
  have read (r : Region) (mem : r ∈ (callEnvironment s).readRegions) : InRegions (s.rd ++ s.wr) r.base r.len :=
    ⟨r, List.mem_append_left _ (by rw [A.readRegions]; exact mem), Region.contains_self _ _⟩
  refine ⟨read (callEnvironment s).exponentRegion List.mem_cons_self, read (callEnvironment s).otherRegion (List.mem_cons_of_mem _ List.mem_cons_self),
    read (callEnvironment s).randRegion (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    read (callEnvironment s).tableRegion (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),
    rfl, rfl, rfl, D.tableWords, rfl⟩

theorem entry_memory {s : State} (h : contract.pre s) :
    MemoryFacts (callEnvironment s) (callEBytes s) (callPBytes s) (callEntropy s) (Compact.entered s) := by
  have A := call_layout h
  have v := call_valid h
  have M := call_memory h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  have F : Frame [(⟨(callEnvironment s).p.setWidth 64, 16⟩ : Region)] s.mem (Compact.entered s).mem :=
    pushed_frame (rs := Compact.savedRegisters) (by decide) fit
  have read {a : Addr} {n : Nat} (R : InRegions (s.rd ++ s.wr) a n) :
      InRegions ((Compact.entered s).rd ++ (Compact.entered s).wr) a n := by
    obtain ⟨r, mem, contains⟩ := R
    refine ⟨r, ?_, contains⟩
    change r ∈ s.rd ++ (below (s.gpr .esp) 16 :: s.wr)
    exact (List.mem_append.mp mem).elim (List.mem_append_left _) (fun member => List.mem_append_right _ (List.mem_cons_of_mem _ member))
  have bytes (r : Region) (mem : r ∈ (callEnvironment s).readRegions) :
      Spec.Rsa.bytesAt (Compact.entered s).mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len :=
    VG.Proof.RsaKeyGen.frame_bytesAt F (by
      intro R member; obtain rfl := List.mem_singleton.mp member
      exact v.savedFar r (List.mem_append_right _ mem)) (v.readFit mem)
  refine ⟨read M.exponentRead, read M.otherRead, read M.randRead, read M.tableRead,
    bytes (callEnvironment s).exponentRegion List.mem_cons_self, bytes (callEnvironment s).otherRegion (List.mem_cons_of_mem _ List.mem_cons_self),
    bytes (callEnvironment s).randRegion (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), ?_, rfl⟩
  intro i index
  have tableMem : (callEnvironment s).tableRegion ∈ (callEnvironment s).readRegions :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have same := F.readW (r := (callEnvironment s).tableRegion) (w := 64)
    (a := off ((callEnvironment s).table.setWidth 64) (8 * i))
    (Offset.contains_base _ (by change 8 * i + 8 ≤ 8192; omega_using [index]) (by omega_using [index]))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.savedFar _ (List.mem_append_right _ tableMem)) (by decide)
  exact same.trans (M.table i index)

theorem entry_input {s : State} (h : contract.pre s) :
    EntryInput (callEnvironment s) (callEBytes s) (callPBytes s) (callEntropy s) (Compact.entered s) := by
  have A := call_layout h
  have v := call_valid h
  refine ⟨entry_arguments h, ?_, ?_, entry_memory h⟩
  · change InRegions (below (s.gpr .esp) 16 :: s.wr) (callEnvironment s).outRegion.base (callEnvironment s).outRegion.len
    exact ⟨_, List.mem_cons_of_mem _ (A.writeMember List.mem_cons_self), Region.contains_self _ _⟩
  · refine ⟨?_, ?_⟩
    · change (callEnvironment s).usedRegion ∈ below (s.gpr .esp) 16 :: s.wr
      exact List.mem_cons_of_mem _ (A.writeMember (List.mem_cons_of_mem _ List.mem_cons_self))
    · change ((arg s 2).setWidth 64).toNat + 8 ≤ 2 ^ 32
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 2).isLt (by decide))]
      exact v.usedFit

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.CandidateScheduleContinue`, which only this module used -/

section

/-! # Equal declared schedules determine coprimality and prepared-result shape -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.Proof.RsaKeyGen

theorem schedule_gcd_eq {E : Environment} {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : schedule E eBytes pBytes rBytes = schedule E eBytes qBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (rComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = false)
    (sComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = false) :
    decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) =
      decide (Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) := by
  have H := congrArg Sched.gbad same
  rw [schedule_exponent rClose rComposite, schedule_exponent sClose sComposite] at H
  have equal := congrArg Bool.not H
  simp only [Bool.not_not] at equal
  apply Bool.eq_iff_iff.mpr
  have iff := Bool.eq_iff_iff.mp equal
  simpa only [beq_iff_eq, decide_eq_true_eq] using iff

theorem schedule_shape_eq {E : Environment} {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : schedule E eBytes pBytes rBytes = schedule E eBytes qBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false)
    (rComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = false)
    (sComposite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = false)
    (good : Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) :
    shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length)) := by
  have gcdEq := schedule_gcd_eq same rClose sClose rComposite sComposite
  have goodRight : Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1 :=
    of_decide_eq_true (gcdEq.symm.trans (decide_eq_true good))
  have H := congrArg Sched.mr same
  rw [schedule_mr rClose rComposite good, schedule_mr sClose sComposite goodRight] at H
  exact H

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Native candidate generation has complete correctness, timing, and satisfiability certificates -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateSaved.lean`, which only this module imported.
section

/-! # Candidate workspace writes and nested frames retain the saved cdecl registers -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem saved_stack_far {E : Environment} (v : E.Valid) :
    (⟨E.p.setWidth 64, 16⟩ : Region).Disjoint (below E.p 136) := by
  unfold below
  rw [Taint.sub_setWidth v.low]
  exact Offset.base_disjoint_below _ (by decide)

theorem saved_read {E : Environment} (v : E.Valid) {s t : State}
    (fit : 16 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (F : MutableFrame E (Compact.entered s).mem t.mem) {i : Nat} (index : i < 4) :
    t.mem.readW (addr E.p (4 * i)) 32 = s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  have pFit : E.p.toNat + 16 ≤ 2 ^ 32 := by
    rw [← sp, Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat fit]
    have := (s.gpr .esp).isLt
    omega
  have same := F.readW (r := (⟨E.p.setWidth 64, 16⟩ : Region)) (a := addr E.p (4 * i)) (w := 32)
    (by rw [addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega)) (by
      intro r mem
      rcases List.mem_append.mp mem with mem | mem
      · exact (v.savedFar r (List.mem_append_left _ mem)).symm
      · obtain rfl := List.mem_singleton.mp mem
        exact saved_stack_far v) (by decide)
  have word := pushed_word (rs := Compact.savedRegisters) (by decide) fit index
  change (Compact.entered s).mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 = _ at word
  rw [sp] at word
  exact same.trans word

theorem return_read {E : Environment} (_v : E.Valid) {s t : State}
    (fit : 152 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (returnFar : ∀ r ∈ E.writeRegions, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r)
    (F : MutableFrame E (Compact.entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have outside : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 152) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  have inner : (below E.p 136).Sub (below (s.gpr .esp) 152) := by
    rw [← sp, Compact.entered, pushed_esp]
    exact below_inner (by decide) fit
  have same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4) (by
    intro r mem
    rcases List.mem_append.mp mem with mem | mem
    · exact returnFar r mem
    · obtain rfl := List.mem_singleton.mp mem
      exact outside.sub_right inner) (by decide)
  have pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) (by change 16 ≤ _; omega)
  exact same.trans (pushed.readW (Region.contains_self _ _) (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem
    exact outside.sub_right (below_sub (by decide) fit)) (by decide))

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFrameResult.lean`, which only this module imported.
section

/-! # The complete candidate restores the native calling convention after every result -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem StepOutputs.keep {E : Environment} {entropy : List Byte}
    {result : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand)} {s t : State}
    (R : StepOutputs E entropy result s) (eax : t.gpr .eax = s.gpr .eax) (mem : t.mem = s.mem) :
    StepOutputs E entropy result t := by
  cases result with
  | none => simpa only [StepOutputs, Outputs, eax, mem] using R
  | some pr =>
    obtain ⟨candidate, rest⟩ := pr
    cases candidate <;> simpa only [StepOutputs, Outputs, eax, mem] using R

/-- The outputs, whatever the bytes outside `out` and `used` are. -/
theorem StepOutputs.frame {E : Environment} {entropy : List Byte}
    {result : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand)} {s t : State}
    (R : StepOutputs E entropy result s) (eax : t.gpr .eax = s.gpr .eax) {rs : List Region}
    (F : Frame rs s.mem t.mem) (dOut : ∀ q ∈ rs, E.outRegion.Disjoint q)
    (dUsed : ∀ q ∈ rs, E.usedRegion.Disjoint q) (fit : E.length < 2 ^ 64) :
    StepOutputs E entropy result t := by
  have hb : Spec.Rsa.bytesAt t.mem (E.out.setWidth 64) E.length =
      Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length :=
    VG.Proof.Rsa.rsa_bytes_frame F fit dOut
  have hw : t.mem.readW (E.used.setWidth 64) 64 = s.mem.readW (E.used.setWidth 64) 64 :=
    F.readW (r := E.usedRegion) (Region.contains_self _ _) dUsed (by decide)
  cases result with
  | none => simpa only [StepOutputs, Outputs, eax, hb, hw] using R
  | some pr =>
    obtain ⟨candidate, rest⟩ := pr
    cases candidate <;> simpa only [StepOutputs, Outputs, eax, hb, hw] using R

theorem framed_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : EntryInput E eBytes pBytes entropy (Compact.entered s))
    (fit : 152 ≤ (s.gpr .esp).toNat)
    (returnFar : ∀ r ∈ E.writeRegions, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r) :
    WP isa (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) s fun t =>
      abiPreserved s t ∧ StepOutputs E entropy (Spec.RsaKeyGen.candidateOp E.length eBytes pBytes entropy) t := by
  have savedFit : 16 ≤ (s.gpr .esp).toNat := by omega
  have entrySp := I.arguments.sp
  have inner : NoSp (.seq (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (.block Compact.restoreRegs)) :=
    CandidateNoSp.sequence (CandidateNoSp.body montNoSp roundNoSp montName roundName) (NoSp.of_all (by rfl))
  have region : below (s.gpr .esp) (4 * VG.Proof.Mont.X86.Compact.savedRegisters.length) = ⟨E.p.setWidth 64, 16⟩ := by
    rw [← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
    rfl
  unfold VG.Impl.RsaKeyGen.X86.Candidate.code
  refine WP.frameLocal (rs := VG.Proof.Mont.X86.Compact.savedRegisters) (by decide) (by decide) (by decide) savedFit inner
    (fun t m _ ⟨abi, R⟩ fl => ⟨VG.Proof.Mont.X86.Compact.abi_frame savedFit abi fl,
      R.frame rfl fl
        (fun q hq => by rw [List.mem_singleton.mp hq, region]; exact v.savedFar _ (by simp [Environment.writeRegions]))
        (fun q hq => by rw [List.mem_singleton.mp hq, region]; exact v.savedFar _ (by simp [Environment.writeRegions]))
        (by have := v.outFit; omega)⟩) ?_
  refine WP.seq (WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v I)
    fun t ⟨R, F, K⟩ => ?_)
  have sp : t.gpr .esp = E.p := (K.1 .esp (by unfold bodyClob; decide)).trans entrySp
  have pFit : E.p.toNat + 16 ≤ 2 ^ 32 := by
    rw [← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat savedFit]
    have := (s.gpr .esp).isLt
    omega
  have read (i : Nat) (index : i < 4) : readSrc t (.mem (at_ .esp (4 * i))) = some
      (s.gpr (VG.Proof.Mont.X86.Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp]
      change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (addr E.p (4 * i)) 4
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      have region : below (s.gpr .esp) 16 = ⟨E.p.setWidth 64, 16⟩ := by
        rw [← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
        rfl
      rw [region, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, saved_read v savedFit entrySp F index]
  refine WP.mono (VG.Proof.Mont.X86.Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, mem, keep⟩
  have sp' : u.gpr .esp = E.p := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show VG.Proof.Mont.X86.Compact.savedRegisters.length = 4 from rfl,
        VG.Proof.Mont.X86.Compact.popped_four_value, sp', mem]
      exact saved_read v savedFit entrySp F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', ← entrySp, VG.Proof.Mont.X86.Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]
    exact return_read v fit entrySp returnFar F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, mem]

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateCorrect.lean`, which only this module imported.
section

/-! # The complete native candidate satisfies the shared RSA generation contract -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem correct {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) s trace t ∧
      abiPreserved s t ∧ contract.post s t := by
  have A := call_layout h
  have D := call_separation h
  obtain ⟨trace, t, run, preserved, R⟩ := framed_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    (call_valid h) (entry_input h) A.low D.returnFar
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  have entropyLength : (callEntropy s).length = (arg s 8).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  change StepOutputs (callEnvironment s) (callEntropy s)
    (Spec.RsaKeyGen.candidateOp (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s)) t at R
  cases result : Spec.RsaKeyGen.candidateOp (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s) with
  | none =>
    rw [result] at R
    dsimp only [callEBytes, callPBytes, callEntropy] at result
    rw [result]
    obtain ⟨status, bytes, used⟩ := R
    refine ⟨by rw [status]; rfl, bytes, ?_⟩
    simpa only [callEnvironment, Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.map_append, List.map_nil,
      List.map_cons, List.nil_append, Nat.mul_zero, BitVec.add_zero] using congrArg (fun x => [x]) used
  | some pr =>
    obtain ⟨candidate, rest⟩ := pr
    rw [result] at R
    cases candidate
    all_goals dsimp only [StepOutputs, Outputs] at R
    all_goals obtain ⟨status, bytes, used⟩ := R
    all_goals rw [entropyLength] at used
    all_goals dsimp only [callEBytes, callPBytes, callEntropy] at result
    all_goals rw [result]
    all_goals refine ⟨by rw [status]; rfl, bytes, ?_⟩
    all_goals simpa only [callEnvironment, Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.map_append, List.map_nil,
      List.map_cons, List.nil_append, Nat.mul_zero, BitVec.add_zero] using congrArg (fun x => [x]) used

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidatePublic.lean`, which only this module imported.
section

/-! # The shared contract publishes arguments, table address, exponent bytes, and only its declared candidate leak -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.RsaKeyGen

structure PublicInputs (s t : State) : Prop where
  stack : s.gpr .esp = t.gpr .esp
  arguments : ∀ i < 11, arg s i = arg t i
  tables : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol
  observations : (callEBytes s).map (·.toNat) ++
      Spec.RsaKeyGen.candidateLeak (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s) =
    (callEBytes t).map (·.toNat) ++
      Spec.RsaKeyGen.candidateLeak (arg t 1).toNat (callEBytes t) (callPBytes t) (callEntropy t)

theorem public_inputs {s t : State} (H : contract.pub s t) : PublicInputs s t := by
  sig_pub [contract, Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  sig_split H
  refine ⟨by with_reducible assumption, ?_, by with_reducible assumption, by dsimp only [callEBytes, callPBytes, callEntropy]; with_reducible assumption⟩
  intro i index
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem PublicInputs.table {s t : State} (P : PublicInputs s t) :
    s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol := by
  exact P.tables

theorem PublicInputs.environment {s t : State} (P : PublicInputs s t) : callEnvironment s = callEnvironment t := by
  simp only [callEnvironment, P.arguments 0 (by decide), P.arguments 1 (by decide), P.arguments 2 (by decide),
    P.arguments 3 (by decide), P.arguments 4 (by decide), P.arguments 5 (by decide), P.arguments 6 (by decide),
    P.arguments 7 (by decide), P.arguments 8 (by decide), P.arguments 9 (by decide), P.arguments 10 (by decide),
    P.stack, P.table]

theorem PublicInputs.exponent {s t : State} (P : PublicInputs s t) : callEBytes s = callEBytes t := by
  have lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    simp only [List.length_map, callEBytes, VG.Proof.Bignum.bytesAt_length, P.arguments 4 (by decide)]
  exact map_toNat_inj (List.append_inj P.observations lengths).1

theorem PublicInputs.leak {s t : State} (P : PublicInputs s t) :
    SameLeak (callEnvironment s) (callEBytes s) (callPBytes s) (callPBytes t) (callEntropy s) (callEntropy t) := by
  have lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    simp only [List.length_map, callEBytes, VG.Proof.Bignum.bytesAt_length, P.arguments 4 (by decide)]
  have L := (List.append_inj P.observations lengths).2
  rw [← P.arguments 1 (by decide), ← P.exponent] at L
  exact L

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateAvailableTiming.lean`, which only this module imported.
section

/-! # The candidate's front and its continuation hide the entropy -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

theorem four_comparison (x : BitVec 32) : (x - 4 == 0#32) = decide (x = 4) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

theorem FrontPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : FrontPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    FrontPair E eBytes pBytes qBytes rBytes sBytes u z := by
  rcases P with ⟨same, other⟩ | ⟨S, T, D, rest⟩
  · exact Or.inl ⟨by rw [U.gpr, Z.gpr]; exact same, by rw [U.gpr]; exact other⟩
  · exact Or.inr ⟨by rw [U.gpr]; exact S, by rw [Z.gpr]; exact T, D.keepFlags v U Z, rest⟩

/-- `eax = 4` decides the continuation in both runs alike. -/
theorem continue_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (FrontPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq (.block [.alu .cmp .eax (.imm 4)])
        (.ite .e (VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck montName mont roundName round) (.block [])))
      (fun _ _ => True) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block [.alu .cmp .eax (.imm 4)])
      (VG.X86.Taint.Agree (τr [])) := checkedBlockInvariant rfl rfl
  have cmp : RelCT isa (FrontPair E eBytes pBytes qBytes rBytes sBytes) (.block [.alu .cmp .eax (.imm 4)])
      (fun u z => FrontPair E eBytes pBytes qBytes rBytes sBytes u z ∧
        isa.eval .e u = some (decide (u.gpr .eax = 4)) ∧ isa.eval .e z = some (decide (z.gpr .eax = 4))) := by
    intro s t tr ur u z P A B
    obtain ⟨U, ZU⟩ := wp_result (compare_value_ok (s := s) 4) A
    obtain ⟨Z, ZZ⟩ := wp_result (compare_value_ok (s := t) 4) B
    refine ⟨(raw _ _ _ _ _ _ (agree_regs (by intro r mem; cases mem)) A B).1, P.keepFlags v U Z, ?_, ?_⟩
    · rw [ZU, U.gpr, four_comparison]
    · rw [ZZ, Z.gpr, four_comparison]
  refine RelCT.seq cmp (VG.RelCT.ite ?_ ?_ ?_)
  · rintro u z ⟨P, CU, CZ⟩
    rw [CU, CZ]
    rcases P with ⟨same, _⟩ | ⟨S, T, _⟩
    · rw [same]
    · rw [S, T]
  · rintro s t tr ur u z ⟨⟨P, CU, _⟩, yes⟩ A B
    rw [CU] at yes
    have four : s.gpr .eax = 4 := of_decide_eq_true (Option.some.inj yes)
    rcases P with ⟨_, other⟩ | ⟨_, _, D, rClose, sClose, rComposite, sComposite⟩
    · exact absurd four other
    have schedules := schedule_eq v length rEnough leak
    exact exponent_stage_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough
      (schedule_gcd_eq schedules rClose sClose rComposite sComposite)
      (schedule_shape_eq schedules rClose sClose rComposite sComposite) _ _ _ _ _ _ D A B
  · have empty : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block []) (VG.X86.Taint.Agree (τr [])) :=
      checkedBlockInvariant rfl rfl
    exact empty.mono (fun _ _ _ => agree_regs (by intro r mem; cases mem)) (fun _ _ _ => trivial)

theorem available_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.available
  exact RelCT.seq (front_rt_trace v length rEnough enough leak)
    (continue_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length rEnough enough leak)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateClearTiming.lean`, which only this module imported.
section

/-! # Clearing leaks only the public output address and length -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateClear
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateClear

theorem args_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (header : 8 ≤ size) :
    WP isa (.block args) s fun t =>
      t.gpr .esi = s.mem.readW (off base 0) 32 ∧ t.gpr .ecx = s.mem.readW (off base 4) 32 := by
  unfold args
  refine wp_movS (readSrc_sc S (d := 0) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 4) (by omega)) fun b B _ =>
    wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.other .esi (by decide), B.other .esi (by decide), A.gpr],
    by rw [T.other .ecx (by decide), B.gpr, A.mem]⟩

def InputPair (base : Addr) (size : Nat) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧
    s.mem.readW (off base 0) 32 = t.mem.readW (off base 0) 32 ∧
    s.mem.readW (off base 4) 32 = t.mem.readW (off base 4) 32

theorem args_trace {base : Addr} {size : Nat} (header : 8 ≤ size) :
    RelCT isa (InputPair base size) (.block args) (VG.X86.Taint.Agree (τr [.esi, .ecx])) := by
  intro s t tr ur u z ⟨S, T, outEq, lenEq⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block args)
      (VG.X86.Taint.Agree (τr [.edi])) := checkedBlockInvariant rfl rfl
  have A : VG.X86.Taint.Agree (τr [.edi]) s t := by
    apply agree_regs
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  have trace := (raw _ _ _ _ _ _ A E G).1
  obtain ⟨outU, lenU⟩ := wp_result (args_ok S header) E
  obtain ⟨outZ, lenZ⟩ := wp_result (args_ok T header) G
  refine ⟨trace, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · rw [outU, outZ]; exact outEq
  · rw [lenU, lenZ]; exact lenEq

theorem code_trace {base : Addr} {size : Nat} (header : 8 ≤ size) :
    RelCT isa (InputPair base size) code (fun _ _ => True) := by
  unfold code
  refine RelCT.seq (args_trace header) ?_
  apply RelCT.taint (A := taint) (τr [.esi, .ecx]) (fun _ _ H => H)
    (hc := VG.Taint.hintOf taint (τr [.esi, .ecx]) (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne))
  rfl

end VG.Proof.RsaKeyGen.X86.CandidateClear
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFrontTiming.lean`, which only this module imported.
section

/-! # The candidate's output clearing and entropy guard have a public trace -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen
open VG.Impl.Mont.X86

theorem clear_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (InputPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.Candidate.clear
      (ClearedPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have raw := CandidateClear.code_trace (base := E.base) (size := E.size)
    (by have H : 256 ≤ E.size := v.geometry.headerFit; omega)
  have trace := (raw _ _ _ _ _ _ ⟨P.left.scratch, P.right.scratch,
    P.left.out_eq.trans P.right.out_eq.symm, (P.left.header 1 (by decide)).trans (P.right.header 1 (by decide)).symm⟩ A B).1
  obtain ⟨IU, zerosU, _, _⟩ := wp_result (clear_ok v P.left) A
  obtain ⟨IZ, zerosZ, _, _⟩ := wp_result (clear_ok v P.right) B
  exact ⟨trace, ⟨IU, IZ⟩, zerosU, zerosZ⟩

def guardArgs : List Instr := [.mov .eax (.mem (sc 32)), .alu .cmp .eax (.mem (sc 4))]

theorem guardArgs_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : WP isa (.block guardArgs) s fun t =>
      isa.eval .b t = some (decide (E.randLength < E.length)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.syms = s.syms := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have lengthBound : E.length < 2 ^ 32 := by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega
  unfold guardArgs
  refine wp_movS (readSrc_sc I.scratch (d := 32) (by omega)) fun a A _ =>
    WP.mono (cmp_src_cf (readSrc_sc (I.scratch.of_keeps A.keeps (by decide)) (d := 4) (by omega))) fun t ⟨T, CF⟩ => ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.widen (T.keeps []), T.syms.trans A.syms⟩
  change t.cf = _
  rw [CF, A.gpr, A.mem, I.header 8 (by decide), I.header 1 (by decide)]
  change some (decide ((BitVec.ofNat 32 E.randLength).toNat < (BitVec.ofNat 32 E.length).toNat)) = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.randLengthFit, Nat.mod_eq_of_lt lengthBound]

theorem guardArgs_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes) (.block guardArgs)
      (WithCondition (ClearedPair E eBytes pBytes qBytes rBytes sBytes) .b (decide (E.randLength < E.length))) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block guardArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  obtain ⟨flagU, memU, KU, symU⟩ := wp_result (guardArgs_ok v P.left) A
  obtain ⟨flagZ, memZ, KZ, symZ⟩ := wp_result (guardArgs_ok v P.right) B
  exact ⟨(raw _ _ _ _ _ _ P.toInputPair.agree A B).1,
    P.keepMem v memU memZ KU KZ (by decide) (by decide) symU symZ, flagU, flagZ⟩

theorem front_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (rLength : rBytes.length = E.randLength) (sLength : sBytes.length = E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (InputPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq VG.Impl.RsaKeyGen.X86.Candidate.clear (.seq (.block guardArgs)
        (.ite .b VG.Impl.RsaKeyGen.X86.CandidateFinish.none
          (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round)))) (fun _ _ => True) := by
  refine RelCT.seq (clear_pair_trace v) (RelCT.seq (guardArgs_trace v) ?_)
  by_cases enough : E.length ≤ E.randLength
  · have condition : decide (E.randLength < E.length) = false := decide_eq_false (by omega)
    rw [condition]
    exact branch_false (available_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      (rLength.trans sLength.symm) (by rw [rLength]; exact enough) enough leak)
  · have condition : decide (E.randLength < E.length) = true := decide_eq_true (by omega)
    rw [condition]
    apply branch_true
    exact (CandidateFinish.none_trace (base := E.base) (size := E.size)
      (by have H : 256 ≤ E.size := v.geometry.headerFit; omega)).mono (fun _ _ P =>
        ⟨P.left.scratch, P.right.scratch, P.left.usedPointer.trans P.right.usedPointer.symm⟩) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateEntryTiming.lean`, which only this module imported.
section

/-! # Argument entry leaks only the public cdecl arguments and workspace address -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateArgs

def EntryPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Entry base size p inputs s ∧ Entry base size p inputs t

theorem pointer_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (S : Entry base size p inputs s) :
    WP isa (.block [.mov .edi (.mem (arg 9))]) s fun t => t.gpr .edi = inputs 9 ∧ Keeps [.edi] s t := by
  refine wp_movS (S.read 9 (by decide)) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem pointer_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) (.block [.mov .edi (.mem (arg 9))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (arg 9))])
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  have A : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.sp.trans T.sp.symm)
  obtain ⟨ptrU, Ku⟩ := wp_result (pointer_ok S) E
  obtain ⟨ptrZ, Kz⟩ := wp_result (pointer_ok T) G
  refine ⟨(raw _ _ _ _ _ _ A E G).1, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · rw [Ku.1 .esp (by decide), Kz.1 .esp (by decide)]; exact S.sp.trans T.sp.symm
  · exact ptrU.trans ptrZ.symm

def InitializedPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Context base size p inputs s ∧ Context base size p inputs t ∧
    (∀ i < 11, s.mem.readW (off base (4 * i)) 32 = inputs i ∧ t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
    s.mem.readW (off base 44) 32 = inputs 2 ∧ t.mem.readW (off base 44) 32 = inputs 2

theorem enter_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) enter (InitializedPair base size p inputs) := by
  have copied : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) code (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ H => H)
      (hc := VG.Taint.hintOf taint (τr [.esp, .edi]) code)
    kernel_rfl
  have raw : RelCT isa (EntryPair base size p inputs) enter (fun _ _ => True) := RelCT.seq pointer_trace copied
  intro s t tr ur u z ⟨S, T⟩ E G
  obtain ⟨Cu, valuesU, usedU, _, _⟩ := wp_result (enter_ok S) E
  obtain ⟨Cz, valuesZ, usedZ, _, _⟩ := wp_result (enter_ok T) G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1, Cu, Cz, fun i index => ⟨valuesU i index, valuesZ i index⟩, usedU, usedZ⟩

end VG.Proof.RsaKeyGen.X86.CandidateArgs
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateBodyTiming.lean`, which only this module imported.
section

/-! # Native argument entry and the complete candidate body obey the declared leak -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure BodyPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop where
  left : EntryInput E eBytes pBytes rBytes s
  right : EntryInput E eBytes qBytes sBytes t

theorem enter_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.CandidateArgs.enter
      (InputPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have trace := (CandidateArgs.enter_trace _ _ _ _ _ _ ⟨P.left.arguments, P.right.arguments⟩ A B).1
  obtain ⟨IU, _, _⟩ := wp_result (enter_input_ok v P.left) A
  obtain ⟨IZ, _, _⟩ := wp_result (enter_input_ok v P.right) B
  exact ⟨trace, IU, IZ⟩

theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (BodyPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.body montName mont roundName round) (fun _ _ => True) :=
    RelCT.seq (enter_pair_trace v) (front_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      P.left.memory.entropyLength P.right.memory.entropyLength leak)
  refine ⟨(raw _ _ _ _ _ _ P A B).1, agree_regs ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  rw [Exec.gpr (CandidateNoSp.body montNoSp roundNoSp montName roundName) A,
    Exec.gpr (CandidateNoSp.body montNoSp roundNoSp montName roundName) B]
  exact P.left.arguments.sp.trans P.right.arguments.sp.symm

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateFrameTiming.lean`, which only this module imported.
section

/-! # Saving and restoring cdecl registers preserves candidate trace equivalence -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def FramedPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop :=
  BodyPair E eBytes pBytes qBytes rBytes sBytes (Compact.entered s) (Compact.entered t) ∧ s.gpr .esp = t.gpr .esp

theorem framed_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (FramedPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) (fun _ _ => True) := by
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.Mont.X86.Compact.restoreRegs)
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  unfold VG.Impl.RsaKeyGen.X86.Candidate.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := VG.X86.Taint.Agree (τr [.esp])) (fun _ _ P => P.2)
  exact (RelCT.seq (body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v leak) restore).mono
    (by rintro _ _ ⟨s, t, P, rfl, rfl⟩; exact P.1) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateConstantTime.lean`, which only this module imported.
section

/-! # Native candidate generation is constant time under exactly the shared contract's declared leak -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem constantTime {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) :
    ConstantTime isa contract.pre contract.pub (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) := by
  apply RelCT.constantTime
  intro s t tr ur u z ⟨HS, HT, HP⟩ A B
  have P := public_inputs HP
  have I := entry_input HS
  have J := entry_input HT
  rw [← P.environment, ← P.exponent] at J
  exact framed_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
    (call_valid HS) P.leak _ _ _ _ _ _ ⟨⟨I, J⟩, P.stack⟩ A B

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem verified {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) :
    Verified target (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) contract :=
  ⟨correct montVerified montNoSp montStack roundVerified roundNoSp roundStack,
    constantTime montVerified montNoSp montStack roundVerified roundNoSp roundStack, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.CandidateSafety`, which only this module used -/

section

/-! # Registration checks the complete native candidate's stack-pointer discipline -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem code_sp {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round).allInstrs (fun i => !isa.writesSp i) = true := by
  have equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  rw [equal]
  exact CandidateNoSp.checked (CandidateNoSp.code Hm Hr montName roundName)

end VG.Proof.RsaKeyGen.X86.Candidate

end

end


/-! # The verified prime search (i686)

For any candidate within 152 bytes of stack (`search_verified_of`), and for
the candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/X86/RsaKeyGen.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Impl.RsaKeyGen.X86.Search
open VG.Proof.MillerRabin.X86 (RoundImpl montName montCode compact_noSp compact_stack)

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 32
  | 2 => 0x2000
  | 3 => 0x3000
  | 4 => 1
  | 5 => 0x3100
  | 6 => 0
  | 7 => 0x4000
  | 8 => 0
  | 9 => 0x10000
  | 10 => 544
  | _ => 0x6000

/-- The arguments; a state with no candidates left, the width 32 and the
budget `32769 · 32 = 0x100020`; RSA's table at `0x30000`. -/
def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 48 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else if a = 0x6008 then 0x20
  else if a = 0x6010 then 0x20
  else if a = 0x6012 then 0x10
  else constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x3000, 1⟩, ⟨0x3100, 0⟩, ⟨0x4000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 8⟩, ⟨0x10000, 4352⟩, ⟨0x6000, 32⟩, ⟨0x20004, 48⟩]
  syms _ := 0x30000

theorem sat_arguments (i : Nat) (index : i < 12) : arg satState i = satArgument i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by
    omega_using [index]
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

theorem sat_table : Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
  have small : i < 1024 := by simpa only [VG.Proof.RsaKeyGen.X86.Candidate.packed_length] using index
  have ix : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; exact small
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  have held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i ix
  refine Eq.trans (Mem.readW_congr (m := satMemory) (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_)
    held
  intro j bound
  have address : ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat =
      65532 + 8 * i + j := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [small, bound]
  have far : ∀ c : Addr, c.toNat < 0x10000 →
      0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j ≠ c := by
    intro c hc e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega_using [small, bound, hc, this]
  change (if _ then _ else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun inside => by
      change ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 48 at inside
      rw [address] at inside; omega_using [inside]),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6008 (by decide))),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6010 (by decide))),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6012 (by decide)))]

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, Proof.RsaKeyGen.primeSearchContract, Proof.RsaKeyGen.primeSearchSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_arguments 8 (by decide),
    sat_arguments 9 (by decide), sat_arguments 10 (by decide), sat_arguments 11 (by decide)]
  simp only [packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)
    | (unfold Spec.RsaKeyGen.primeLenValid; decide +kernel)
    | decide +kernel
    | rfl

theorem search_verified_of (c : Cand) : Verified target (code c.call) contract :=
  ⟨correct c, constantTime c, satisfiable⟩

/-- `vg_rsa_keygen_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_rsa_keygen_candidate" ++ v.suffix
  code := Impl.RsaKeyGen.X86.Candidate.code montName montCode v.name v.code
  verified := Proof.RsaKeyGen.X86.Candidate.verified Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack
    v.verified v.noSp v.stack
  noSp := CandidateNoSp.code compact_noSp v.noSp montName v.name
  stack := CandidateStackUse.code compact_stack v.stack montName v.name

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) : Verified target (searchCode v) contract :=
  search_verified_of (Cand.ofRound v)

/-- No instruction of the search, its candidate's included, writes `esp`. -/
theorem search_all (v : RoundImpl) : (searchCode v).all (fun i => !isa.writesSp i) = true := by
  have h := Proof.RsaKeyGen.X86.Candidate.code_sp compact_noSp v.noSp montName v.name
  refine Code.all_of_allInstrs ?_
  simp only [searchCode, Cand.ofRound, Cand.call, code, body, iteration, candidateStep, candidateRun,
    Impl.RsaKeyGen.X86.Search.classify, reject, short, exhausted, zeroOut, Code.allInstrs, h]
  rfl

end VG.Proof.RsaKeyGen.X86.Search
