module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBody
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Contract

/-! ### `RsaKeyGen.X86.KeyEncodedResult`, which this module and modules that import it used -/

section

/-! # The native seven-port result is the shared encoded key operation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def encodedOperation (E : Environment) (m : Mem) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  Proof.RsaKeyGen.keyOp E.primeLength
    (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len)
    (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len)
    (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)

def EncodedResult (E : Environment) (m : Mem) (t : State) : Prop :=
  let result := encodedOperation E m
  let outs := (List.range 7).map E.outputRegion
  (t.gpr .eax).toNat = Proof.RsaKeyGen.keyStatus result ∧
    match result with
    | .inl (.ok ys) => outs.map (fun r => Spec.Rsa.bytesAt t.mem r.base r.len) = ys
    | _ => ∀ r ∈ outs, Spec.Rsa.bytesAt t.mem r.base r.len = List.replicate r.len 0

theorem BodyOutcome.encoded {E : Environment} {m : Mem} {t : State} (v : E.Valid) (R : BodyOutcome E m t) :
    EncodedResult E m t := by
  have widths := v.widths
  have bits : 16 * E.primeLength = 32 * E.n := by omega_using [widths]
  unfold BodyOutcome WrittenCore at R
  rw [show E.outputs.n = E.n from rfl] at R
  unfold EncodedResult encodedOperation Proof.RsaKeyGen.keyOp
  rw [bits]
  cases code : Spec.RsaKeyGen.keyFromPrimes (32 * E.n)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) with
  | inr u =>
    cases u
    rw [code] at R
    refine ⟨R.1, ?_⟩
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have bound := List.mem_range.mp hi
    simpa only [v.outputRegion bound, v.outputLength bound, Environment.outputRegion] using R.2 i bound
  | inl result =>
    cases result with
    | error failure =>
      rw [code] at R
      refine ⟨R.1, ?_⟩
      intro r hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hi
      simpa only [v.outputRegion bound, v.outputLength bound, Environment.outputRegion] using R.2 i bound
    | ok key =>
      rw [code] at R
      refine ⟨R.1, ?_⟩
      have values : ∀ i < 7, Spec.Rsa.bytesAt t.mem (E.outputRegion i).base (E.outputRegion i).len =
          Spec.Rsa.i2osp (keyField key i) (E.outputLength i) := by
        intro i hi
        simpa only [v.outputRegion hi, v.outputLength hi] using R.2 i hi
      have joined : ((List.range 7).map E.outputRegion).map (fun r => Spec.Rsa.bytesAt t.mem r.base r.len) =
          (List.range 7).map (fun i => Spec.Rsa.i2osp (keyField key i) (E.outputLength i)) := by
        rw [List.map_map]
        exact List.map_congr_left fun i hi => values i (List.mem_range.mp hi)
      exact joined

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyFramed`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeySaved`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyCallArgs`, which this module and modules that import it used -/

section

/-! # The native register push retains all eighteen cdecl key arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem CallLayout.workspaceMember {s : State} (A : CallLayout s) : callWorkspace s ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_right _ List.mem_cons_self

theorem CallLayout.argumentMember {s : State} (A : CallLayout s) : callArguments s ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem CallLayout.outputMember {s : State} (A : CallLayout s) {i : Nat} (hi : i < 7) : callOutput s i ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem CallLayout.argumentOffset {s : State} (A : CallLayout s) {i : Nat} (hi : i < 18) :
    argAddr s i = off (argAddr s 0) (4 * i) := by
  have fit := A.argsFit
  change addr (s.gpr .esp) (4 + 4 * i) = off (addr (s.gpr .esp) 4) (4 * i)
  rw [addr_eq (by omega_using [hi, fit]), addr_eq (by omega_using [fit])]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

theorem CallLayout.pushedArgument {s : State} (A : CallLayout s) {i : Nat} (hi : i < 18) :
    readSrc (Compact.entered s) (.mem (VG.Impl.RsaKeyGen.X86.CandidateArgs.arg i)) = some (arg s i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have separate : (callArguments s).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 72⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by have := A.argsFit; omega_using [this])]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (callArguments s).Contains (argAddr s i) 4 := by
    rw [A.argumentOffset hi]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  have word := F.readW contains (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide : 32 / 8 < 2 ^ 64)
  change (Compact.entered s).load32 ((Compact.entered s).ea (VG.Impl.Mont.X86.Compact.arg i)) = _
  rw [Compact.argument_address]
  have access : InRegions ((Compact.entered s).rd ++ (Compact.entered s).wr) (argAddr s i) 4 := by
    refine ⟨callArguments s, List.mem_append_right _ (List.mem_cons_of_mem _ A.argumentMember), contains⟩
  rw [State.load32, ite_eq_left access]
  exact congrArg some word

theorem call_args_region (s : State) : KeyArgs.argsRegion (callSp s) = callArguments s := by
  unfold KeyArgs.argsRegion callArguments
  congr 1
  change ((s.gpr .esp - 16#32 + 20#32).setWidth 64) = ((s.gpr .esp + 4#32).setWidth 64)
  congr 1
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem entry_arguments {s : State} (h : contract.pre s) :
    KeyArgs.Entry (callEnvironment s).base (callEnvironment s).size (callSp s)
      (callEnvironment s).argument (Compact.entered s) := by
  have A := call_layout h
  have D := call_separation h
  have Z := call_sizes h
  have v := call_valid h
  have bank := v.bankFit
  have head : 72 ≤ (callEnvironment s).size := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at bank
    omega_using [bank]
  refine ⟨⟨?_, ?_⟩, head, rfl, workspace_stack h, ?_, ?_, ?_, ?_, workspace_deep h⟩
  · exact List.mem_cons_of_mem _ A.workspaceMember
  · change ((arg s 16).setWidth 64).toNat + 8 * (arg s 17).toNat ≤ 2 ^ 32
    rw [VG.BitVec.toNat_setWidth_32_64]
    exact A.workspaceFit
  · rw [Compact.entered, pushed_esp]
    rfl
  · rw [A.privateNat]
    have := A.low
    have := A.argsFit
    omega_using [this]
  · rw [call_args_region]
    exact D.argsWorkspace
  · intro i hi
    rw [Z.argument hi]
    exact A.pushedArgument hi

theorem entry_input {s : State} (h : contract.pre s) :
    EntryInput (callEnvironment s) (callSp s) (Compact.entered s) := by
  have A := call_layout h
  have Z := call_sizes h
  refine ⟨entry_arguments h, ?_, ?_, ?_⟩
  · intro i hi
    rw [Z.outputRegion hi]
    exact ⟨callOutput s i, List.mem_cons_of_mem _ (A.outputMember hi), Region.contains_self _ _⟩
  · refine ⟨callExponent s, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    change callExponent s ∈ s.rd
    rw [A.rd]
    exact List.mem_singleton_self _
  · intro i hi
    rw [call_args_region, Z.outputRegion hi]
    exact (call_separation h).argsOutput i hi

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Native key writes preserve the saved cdecl registers and return address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem call_writes {s : State} (h : contract.pre s) :
    (callEnvironment s).outputs.writes = callWorkspace s :: callOutputs s := by
  have v := call_valid h
  have Z := call_sizes h
  change callWorkspace s :: (List.range 7).map (callEnvironment s).outputs.region =
    callWorkspace s :: (List.range 7).map (callOutput s)
  congr 1
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  rw [v.outputRegion bound, Z.outputRegion bound]

theorem writes_reserved {s : State} (h : contract.pre s) :
    ∀ r ∈ (callEnvironment s).outputs.writes, r.Disjoint (reservedRegion s) := by
  have D := call_separation h
  rw [call_writes h]
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.stackWorkspace
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact D.stackOutput i (List.mem_range.mp hi)

theorem writes_return {s : State} (h : contract.pre s) :
    ∀ r ∈ (callEnvironment s).outputs.writes, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
  have D := call_separation h
  rw [call_writes h]
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.returnWorkspace
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact D.returnOutput i (List.mem_range.mp hi)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Callable native key assembly restores all cdecl registers and the return address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86

theorem BodyOutcome.keep {E : Environment} {m : Mem} {s t : State} (R : BodyOutcome E m s)
    (eax : t.gpr .eax = s.gpr .eax) (memory : t.mem = s.mem) : BodyOutcome E m t := by
  simpa only [BodyOutcome, WrittenCore, eax, memory] using R

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The callable key operation uses the caller's original encoded inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem pushed_bytes {s : State} (h : contract.pre s) {r : Region}
    (far : r.Disjoint (reservedRegion s)) (size : r.len < 2 ^ 64) :
    Spec.Rsa.bytesAt (Compact.entered s).mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len := by
  have A := call_layout h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  apply VG.Proof.Rsa.rsa_bytes_frame F size
  intro R hr
  obtain rfl := List.mem_singleton.mp hr
  exact far.sub_right A.savedSub

end VG.Proof.RsaKeyGen.X86.Key
