module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

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
