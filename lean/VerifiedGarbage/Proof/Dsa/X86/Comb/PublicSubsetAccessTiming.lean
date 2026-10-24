module

import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSelectTiming

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicColumnTiming
import VerifiedGarbage.Proof.Mont.X86.CombSubsetControl
import VerifiedGarbage.Proof.Mont.X86.CombAccess
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import Init.Prelude
public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! The subset builder preserves its public indices across each table lookup. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure SubsetIndex (base : Addr) (size a lo idx : Nat) (s : State) : Prop where
  scr : Scr s base size
  count : s.gpr .esi=BitVec.ofNat 32 a
  low : w32 s.mem base 28=lo
  index : w32 s.mem base 4=idx

theorem subsetIndex_agree {base : Addr} {size a lo idx : Nat} {s t : State}
    (S : SubsetIndex base size a lo idx s) (T : SubsetIndex base size a lo idx t) :
    VG.X86.Taint.Agree columnIndex s t := by
  apply agree_regs (rs := [.edi,.esi])
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
  · exact S.count.trans T.count.symm

theorem subsetSelect_relCT {n e : Nat} (h : Supported n e) (base : Addr) (a lo idx o : Nat)
    (hi : idx<32) (ho : o=5 ∨ o=6) :
    RelCT isa (fun s t => SubsetIndex base (layout n e).size a lo idx s ∧ SubsetIndex base (layout n e).size a lo idx t)
      (VG.Impl.Mont.X86.Comb.publicSelect n (context n+16*n) (slot n o))
      (fun s t => SubsetIndex base (layout n e).size a lo idx s ∧ SubsetIndex base (layout n e).size a lo idx t) := by
  have L := table_layout h
  have shape : 32≤slot n o ∧ slot n o+8*n≤context n ∧ slot n o+8*n≤(layout n e).size ∧ 32≤(layout n e).size := by
    rcases ho with rfl|rfl <;>
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have step {s : State} (S : SubsetIndex base (layout n e).size a lo idx s) :
      WP isa (VG.Impl.Mont.X86.Comb.publicSelect n (context n+16*n) (slot n o)) s
        (SubsetIndex base (layout n e).size a lo idx) := by
    have ent := L.entry hi
    refine WP.mono (VG.Proof.Mont.X86.Comb.publicSelect_ok S.scr L.positive (by omega)
      (by rw [S.index]; exact Nat.le_trans ent.2 L.bound) shape.2.2.1 (.inl (by unfold entry; omega))) fun t ⟨O,_,K⟩ => ?_
    exact ⟨S.scr.of_keeps K (by decide),(K.1 .esi (by decide)).trans S.count,
      (O.w32 (by omega) (by decide)).trans S.low,(O.w32 (by omega) (by decide)).trans S.index⟩
  intro s t tr ur sf tf ⟨S,T⟩ E F
  have CT := publicSelect_relCT base (layout n e).size n (context n+16*n) (slot n o) (by omega)
  exact ⟨(CT _ _ _ _ _ _ ⟨S.scr,T.scr,S.index.trans T.index.symm⟩ E F).1,
    wp_result (step S) E,wp_result (step T) F⟩

theorem subsetLow_relCT (base : Addr) (size a lo idx : Nat) (hz : 32≤size) :
    RelCT isa (fun s t => SubsetIndex base size a lo idx s ∧ SubsetIndex base size a lo idx t)
      VG.Impl.Mont.X86.Comb.subsetLow
      (fun s t => SubsetIndex base size a lo lo s ∧ SubsetIndex base size a lo lo t) := by
  have CT : RelCT isa (VG.X86.Taint.Agree columnIndex) VG.Impl.Mont.X86.Comb.subsetLow
      (VG.X86.Taint.Agree columnIndex) := checkedProgramChange (hint := .block []) rfl rfl
  have step {s : State} (S : SubsetIndex base size a lo idx s) :
      WP isa VG.Impl.Mont.X86.Comb.subsetLow s (SubsetIndex base size a lo lo) := by
    refine WP.mono (VG.Proof.Mont.X86.Comb.subsetLow_ok S.scr hz) fun t ⟨O,V,K⟩ => ?_
    exact ⟨S.scr.of_keeps K (by decide),(K.1 .esi (by decide)).trans S.count,
      (O.w32 (by decide) (by decide)).trans S.low,V.trans S.low⟩
  intro s t tr ur sf tf ⟨S,T⟩ E F
  exact ⟨(CT _ _ _ _ _ _ (subsetIndex_agree S T) E F).1,wp_result (step S) E,wp_result (step T) F⟩

end VG.Proof.Dsa.X86.Comb
