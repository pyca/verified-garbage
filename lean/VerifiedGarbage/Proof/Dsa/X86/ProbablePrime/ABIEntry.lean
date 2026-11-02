module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABI
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The precondition gives a valid environment and the body's entry state -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.ProbablePrime

theorem packed_length : VG.Impl.RsaKeyGen.TrialTable32.packed.length = 1024 := by
  simp only [VG.Impl.RsaKeyGen.TrialTable32.packed, List.length_map, List.length_range]

theorem table_regions (s : State) :
    Abi.constRegions (fun n => (s.syms n).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts = [tableRegionOf s] := by
  rw [VG.Impl.RsaKeyGen.TrialTable32.consts, Abi.constRegions_cons, Abi.constRegions_nil, packed_length]
  rfl

theorem CallFacts.table {bits : Nat} {s : State} (F : CallFacts bits s) :
    (tableRegionOf s).base.toNat + 8192 ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, (tableRegionOf s).Disjoint r) ∧
    (tableRegionOf s).Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ (tableRegionOf s).Disjoint (reservedRegion s) :=
  F.tableFar _ (by rw [table_regions]; exact List.mem_cons_self)

theorem CallFacts.rd {bits : Nat} {s : State} (F : CallFacts bits s) :
    s.rd = [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, tableRegionOf s] := by
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, F.rdPrefix, F.rdTable, table_regions]
  rfl

private theorem held_word {m : Mem} {f : String → Addr} {tables : List (String × List (BitVec 64))}
    {name : String} {words : List (BitVec 64)} (H : Abi.constsHeld m f tables)
    (member : (name, words) ∈ tables) {i : Nat} (bound : i < words.length) :
    m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words[i] := by
  rw [H (name, words) member i bound, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]

theorem CallFacts.tableWords {bits : Nat} {s : State} (F : CallFacts bits s) (i : Nat) (index : i < 1024) :
    s.mem.readW (off ((s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64) (8 * i)) 64 =
      BitVec.ofNat 64 (VG.Impl.RsaKeyGen.TrialTable32.entry i) := by
  have bound : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by rw [packed_length]; exact index
  have member : (VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed) ∈
      VG.Impl.RsaKeyGen.TrialTable32.consts := List.mem_cons_self
  exact (held_word F.tableHeld member bound).trans (VG.Proof.RsaKeyGen.TrialTable32.packed_entry index)

private theorem disjoint_bounds {a b : Addr} {n k : Nat}
    (_an : a.toNat + n ≤ 2 ^ 64) (_bk : b.toNat + k ≤ 2 ^ 64) (np : 0 < n) (kp : 0 < k)
    (D : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  by_contra bad
  have overlap : a.toNat < b.toNat + k ∧ b.toNat < a.toNat + n := by omega
  by_cases order : a.toNat ≤ b.toNat
  · apply D b
    · change (b - a).toNat + 1 ≤ n
      rw [BitVec.toNat_sub]
      omega
    · change (b - b).toNat + 1 ≤ k
      rw [BitVec.sub_self]; change 0 + 1 ≤ k; omega
  · apply D a
    · change (a - a).toNat + 1 ≤ n
      rw [BitVec.sub_self]; change 0 + 1 ≤ n; omega
    · change (a - b).toNat + 1 ≤ k
      rw [BitVec.toNat_sub]
      omega

theorem CallFacts.reserved {bits : Nat} {s : State} (F : CallFacts bits s) :
    reservedRegion s = below (s.gpr .esp) 152 := by
  unfold reservedRegion below
  rw [Taint.sub_setWidth F.low]

theorem CallFacts.pNat {bits : Nat} {s : State} (F : CallFacts bits s) :
    (callEnvironment bits s).p.toNat = (s.gpr .esp).toNat - 16 := sub_toNat (by have := F.low; omega)

theorem CallFacts.workspaceRegion {bits : Nat} {s : State} (_ : CallFacts bits s) :
    (callEnvironment bits s).workspaceRegion = ⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩ := by
  change (⟨(arg s 0).setWidth 64, 8 * (arg s 1).toNat⟩ : Region) = _
  rw [Nat.mul_comm]

theorem CallFacts.savedSub {bits : Nat} {s : State} (F : CallFacts bits s) :
    (⟨(callEnvironment bits s).p.setWidth 64, 16⟩ : Region).Sub (reservedRegion s) := by
  rw [F.reserved]
  exact below_sub (by decide) F.low

theorem CallFacts.bodyStackSub {bits : Nat} {s : State} (F : CallFacts bits s) :
    (below (callEnvironment bits s).p 136).Sub (reservedRegion s) := by
  rw [F.reserved]
  exact below_inner (by decide) F.low

theorem call_args_address (bits : Nat) (s : State) :
    ((callEnvironment bits s).p + 20#32).setWidth 64 = argAddr s 0 := by
  change ((s.gpr .esp - 16#32 + 20#32).setWidth 64) = ((s.gpr .esp + 4#32).setWidth 64)
  congr 1
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem CallFacts.stackAll {bits : Nat} {s : State} (F : CallFacts bits s) :
    ∀ r ∈ [(callEnvironment bits s).workspaceRegion, (callEnvironment bits s).randRegion,
      (callEnvironment bits s).usedRegion, (callEnvironment bits s).tableRegion], r.Disjoint (reservedRegion s) := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · rw [F.workspaceRegion]; exact F.stackWs.symm
  · exact F.stackRand.symm
  · exact F.stackUsed.symm
  · exact F.table.2.2.2

theorem CallFacts.valid {bits : Nat} {s : State} (F : CallFacts bits s) (b : Bits bits) :
    (callEnvironment bits s).Valid := by
  have low := F.low
  have pNat := F.pNat
  have wsFit := F.wsFit
  have workspaceNat : (callEnvironment bits s).base.toNat = (arg s 0).toNat := by
    change ((arg s 0).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide))]
  refine ⟨b, ?_, ?_, F.randFit, (arg s 3).isLt, F.usedFit, ?_, by omega, by have := F.argsFit; omega, ?_,
    ?_, ?_, F.randUsed, ?_, ?_, F.table.2.1 _ (by rw [F.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩
  · have := F.room
    change scratchBytes (width bits) + bits / 8 ≤ 8 * (arg s 1).toNat
    exact this
  · change (arg s 0).toNat + 8 * (arg s 1).toNat ≤ 2 ^ 32
    omega
  · have fit := F.table.1
    change ((s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64).toNat + 8192 ≤ 2 ^ 32 at fit
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (s.syms _).isLt (by decide))] at fit
    exact fit
  · have nonempty : 0 < (callEnvironment bits s).size := by
      have := F.room
      change 0 < 8 * (arg s 1).toNat
      unfold scratchBytes VG.Impl.Bignum.X86.PublicContext.slot VG.Impl.Bignum.hdrBytes at this
      omega
    have far := F.stackAll _ List.mem_cons_self
    have rn : (reservedRegion s).base.toNat = (s.gpr .esp).toNat - 152 := by
      rw [F.reserved]
      change ((s.gpr .esp - BitVec.ofNat 32 152).setWidth 64).toNat = _
      rw [BitVec.toNat_setWidth, sub_toNat low, Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]
    have bounds := disjoint_bounds (a := (callEnvironment bits s).base) (n := (callEnvironment bits s).size)
      (b := (reservedRegion s).base) (k := 152)
      (by rw [workspaceNat]; change (arg s 0).toNat + 8 * (arg s 1).toNat ≤ 2 ^ 64; omega)
      (by rw [rn]; have := (s.gpr .esp).isLt; omega) nonempty (by decide) far
    rw [rn, workspaceNat] at bounds
    rw [pNat, workspaceNat]
    change (arg s 0).toNat + 8 * (arg s 1).toNat ≤ (s.gpr .esp).toNat - 152 ∨
      (s.gpr .esp).toNat - 152 + 152 ≤ (arg s 0).toNat at bounds
    change (s.gpr .esp).toNat - 16 ≤ (arg s 0).toNat ∨ (arg s 0).toNat + 8 * (arg s 1).toNat + 136 ≤
      (s.gpr .esp).toNat - 16
    omega
  · rw [call_args_address, F.workspaceRegion]; exact F.wsArgs.symm
  · rw [F.workspaceRegion]; exact F.wsRand.symm
  · rw [F.workspaceRegion]; exact F.wsUsed.symm
  · rw [F.workspaceRegion]; exact F.table.2.1 _ (by rw [F.wr]; exact List.mem_cons_self)
  · intro r mem
    exact (F.stackAll r mem).sub_right F.savedSub
  · intro r mem
    exact (F.stackAll r mem).sub_right F.bodyStackSub

theorem candidateAt_eq (bits : Nat) (s : State) (m : Mem) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) m ((arg s 0).setWidth 64) =
      (callEnvironment bits s).candidate m := rfl

theorem CallFacts.pushedArgument {bits : Nat} {s : State} (F : CallFacts bits s) {i : Nat} (index : i < 5) :
    readSrc (Compact.entered s) (.mem (VG.Impl.Mont.X86.Compact.arg i)) = some (arg s i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := F.low; omega
  have argsFit := F.argsFit
  have P := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have offset : argAddr s i = off (argAddr s 0) (4 * i) := by
    change addr (s.gpr .esp) (4 + 4 * i) = off (addr (s.gpr .esp) 4) (4 * i)
    rw [addr_eq (by omega), addr_eq (by omega)]
    exact (Offset.add_add _ _ _).symm
  have separate : (⟨argAddr s 0, 20⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 20⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by omega)]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s i) 4 := by
    rw [offset]
    exact Offset.contains_base _ (by omega) (by omega)
  have word := P.readW (w := 32) contains (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact separate)
    (by decide)
  change (Compact.entered s).load32 ((Compact.entered s).ea (VG.Impl.Mont.X86.Compact.arg i)) = _
  rw [Compact.argument_address]
  have access : InRegions ((Compact.entered s).rd ++ (Compact.entered s).wr) (argAddr s i) 4 := by
    change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (argAddr s i) 4
    refine ⟨⟨argAddr s 0, 20⟩, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), contains⟩
    rw [F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [State.load32, ite_eq_left access]
  exact congrArg some word

theorem CallFacts.entry {bits : Nat} {s : State} (F : CallFacts bits s) (b : Bits bits) :
    EntryInput (callEnvironment bits s) ((callEnvironment bits s).candidate s.mem) (callEntropy s)
      (Compact.entered s) := by
  have v := F.valid b
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := F.low; omega
  have P : Frame [⟨(callEnvironment bits s).p.setWidth 64, 16⟩] s.mem (Compact.entered s).mem :=
    pushed_frame (rs := Compact.savedRegisters) (by decide) fit
  have far (r : Region) (mem : r ∈ [(callEnvironment bits s).workspaceRegion, (callEnvironment bits s).randRegion,
      (callEnvironment bits s).usedRegion, (callEnvironment bits s).tableRegion]) :
      ∀ R ∈ [(⟨(callEnvironment bits s).p.setWidth 64, 16⟩ : Region)], r.Disjoint R := by
    intro R member
    obtain rfl := List.mem_singleton.mp member
    exact v.savedFar r mem
  have wsIn : (callEnvironment bits s).workspaceRegion ∈ s.wr := by
    rw [F.workspaceRegion, F.wr]; exact List.mem_cons_self
  refine ⟨⟨List.mem_cons_of_mem _ wsIn, by rw [v.baseNat]; exact v.workspaceFit⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩⟩
  · rw [Compact.entered, pushed_esp]; rfl
  · intro i index
    rw [F.pushedArgument index]
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Environment.argument, callEnvironment, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · refine ⟨List.mem_cons_of_mem _ ?_, ?_⟩
    · rw [F.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · have := F.usedFit
      change ((arg s 4).setWidth 64).toNat + 8 ≤ _
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide))]
      omega
  · refine ⟨(callEnvironment bits s).randRegion, ?_, Region.contains_self _ _⟩
    change _ ∈ s.rd ++ (below (s.gpr .esp) 16 :: s.wr)
    rw [F.rd]; exact List.mem_append_left _ List.mem_cons_self
  · change Spec.Rsa.bytesAt (Compact.entered s).mem _ _ = Spec.Rsa.bytesAt s.mem _ _
    exact VG.Proof.RsaKeyGen.frame_bytesAt P (far _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (by have := (arg s 3).isLt; change (arg s 3).toNat ≤ 2 ^ 64; omega)
  · refine ⟨(callEnvironment bits s).tableRegion, ?_, Region.contains_self _ _⟩
    change _ ∈ s.rd ++ (below (s.gpr .esp) 16 :: s.wr)
    rw [F.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro i index
    have member : (callEnvironment bits s).tableRegion ∈ [(callEnvironment bits s).workspaceRegion,
        (callEnvironment bits s).randRegion, (callEnvironment bits s).usedRegion, (callEnvironment bits s).tableRegion] :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [P.readW (r := (callEnvironment bits s).tableRegion)
      (Offset.contains_base _ (by change 8 * i + 8 ≤ 8192; omega) (by omega)) (far _ member) (by decide)]
    exact F.tableWords i index
  · unfold Environment.candidate
    have room := v.room
    have wsFit := v.workspaceFit
    have inner : (⟨off (callEnvironment bits s).base (callEnvironment bits s).scratch,
        (callEnvironment bits s).bits / 8⟩ : Region).Sub
        (callEnvironment bits s).workspaceRegion := Offset.sub_base (callEnvironment bits s).base room
    rw [VG.Proof.RsaKeyGen.frame_bytesAt P (fun R member => (far _ List.mem_cons_self R member).sub_left inner)
      (by omega)]

end VG.Proof.Dsa.X86.ProbablePrime
