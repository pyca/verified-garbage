module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABISeparate
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Sig

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
