module

import VerifiedGarbage.Proof.Mont.X86.PublicWord

import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Impl.Mont.X86.CombTable
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.Slots
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! A direct lookup's trace depends only on its public index and workspace address. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

 def loadedIndex : VG.X86.Taint.T := { regs := .ofList [.edi,.eax], flags := false }
 def copyPointers : VG.X86.Taint.T := { regs := .ofList [.edi,.ecx,.ebp,.ebx], flags := false }

def WordPair (base : Addr) (size : Nat) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧ w32 s.mem base 4=w32 t.mem base 4

theorem loadWord_relCT (base : Addr) (size o : Nat) (hz : o+4≤size) :
    RelCT isa (fun (s t : State) => Scr s base size ∧ Scr t base size ∧ w32 s.mem base o=w32 t.mem base o)
      (.block [.mov .eax (.mem (sc o))]) (VG.X86.Taint.Agree loadedIndex) :=
  VG.Proof.Mont.X86.Dynamic.publicWord_relCT base size o hz

theorem loadIndex_relCT (base : Addr) (size : Nat) (hz : 8≤size) :
    RelCT isa (WordPair base size) (.block [.mov .eax (.mem (sc 4))]) (VG.X86.Taint.Agree loadedIndex) :=
  loadWord_relCT base size 4 hz

def copyAfterRead (n tab : Nat) : List Instr :=
  [.mov .edx (VG.Impl.Mont.X86.Comb.imm (8*n)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .add .eax (VG.Impl.Mont.X86.Comb.imm tab),
    .mov .ecx (.reg .eax), .mov .ebp (.reg .edi), .mov .ebx (VG.Impl.Mont.X86.Comb.imm (2*n))]

theorem copyAfterRead_relCT (n tab : Nat) :
    RelCT isa (VG.X86.Taint.Agree loadedIndex) (.block (copyAfterRead n tab)) (VG.X86.Taint.Agree copyPointers) := by
  exact erased_relCT (.block (copyAfterRead n tab)) (.block (copyAfterRead 1 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by taint_decide)

theorem copyLoop_relCT (dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree copyPointers)
      (VG.Impl.Mont.X86.Comb.copyLoop (at_ .ecx 0) (at_ .ebp dst))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  exact erased_relCT _ (VG.Impl.Mont.X86.Comb.copyLoop (at_ .ecx 0) (at_ .ebp 0))
    (VG.Taint.hintOf taint copyPointers (VG.Impl.Mont.X86.Comb.copyLoop (at_ .ecx 0) (at_ .ebp 0)))
    (by kernel_rfl) (by kernel_rfl) (by decide) (by taint_decide)

theorem publicSelect_relCT (base : Addr) (size n tab dst : Nat) (hz : 8≤size) :
    RelCT isa (WordPair base size) (VG.Impl.Mont.X86.Comb.publicSelect n tab dst)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Mont.X86.Comb.publicSelect VG.Impl.Mont.X86.Comb.copySetup
  change RelCT isa (WordPair base size)
    (.seq (.block ([.mov .eax (.mem (sc 4))] ++ copyAfterRead n tab))
      (VG.Impl.Mont.X86.Comb.copyLoop (at_ .ecx 0) (at_ .ebp dst))) _
  exact RelCT.seq (RelCT.block_append (RelCT.seq (loadIndex_relCT base size hz) (copyAfterRead_relCT n tab)))
    (copyLoop_relCT dst)

end VG.Proof.Dsa.X86.Comb
