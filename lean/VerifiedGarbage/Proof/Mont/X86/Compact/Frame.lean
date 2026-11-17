module

import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `Mont.X86.Compact.Restore`, which this module and modules that import it used -/

section

/-! # The compact multiplication's register-saving frame -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86

theorem restore_ok {s : State} {edi esi ebp : BitVec 32}
    (readEdi : readSrc s (.mem (at_ .esp 0)) = some edi)
    (readEsi : readSrc s (.mem (at_ .esp 4)) = some esi)
    (readEbp : readSrc s (.mem (at_ .esp 8)) = some ebp) :
    WP isa (.block Compact.restoreRegs) s fun t =>
      t.gpr .edi = edi ∧ t.gpr .esi = esi ∧ t.gpr .ebp = ebp ∧
      t.mem = s.mem ∧ Keeps [.edi, .esi, .ebp] s t := by
  unfold Compact.restoreRegs
  refine wp_movS readEdi fun a A _ => ?_
  have readEsiA : readSrc a (.mem (at_ .esp 4)) = some esi := by
    rw [VG.Proof.Mont.X86.Dynamic.readSrc_upd A (by decide)]; exact readEsi
  refine wp_movS readEsiA fun b B _ => ?_
  have readEbpB : readSrc b (.mem (at_ .esp 8)) = some ebp := by
    rw [VG.Proof.Mont.X86.Dynamic.readSrc_upd B (by decide),
      VG.Proof.Mont.X86.Dynamic.readSrc_upd A (by decide)]; exact readEbp
  refine wp_movS readEbpB fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, T.gpr, T.mem.trans (B.mem.trans A.mem), ?_⟩
  · rw [T.other .edi (by decide), B.other .edi (by decide), A.gpr]
  · rw [T.other .esi (by decide), B.gpr]
  · exact ((A.keeps.mono (by decide)).widen B.keeps).widen T.keeps

end VG.Proof.Mont.X86.Compact

end

end

/-! # A complete callable compact multiplication restores the i686 ABI -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

def savedRegisters : List Reg := [.ebx, .ebp, .esi, .edi]
def entered (s : State) : State := pushed savedRegisters s

theorem popped_four_value (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW ((s.gpr .esp + 12).setWidth 64) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

/-- The calling convention's words, whatever the bytes of the push below
`esp` are and the unknowns. -/
theorem abi_frame {s t : State} {m : Mem} {u : Nat → BitVec 32} (hn : 16 ≤ (s.gpr .esp).toNat)
    (h : abiPreserved s t) (fl : Frame [below (s.gpr .esp) (4 * savedRegisters.length)] t.mem m) :
    abiPreserved s { t with mem := m, unknowns := u } := by
  refine ⟨h.1, ?_⟩
  show m.readW _ _ = _
  rw [fl.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    show Region.Disjoint _ ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩
    rw [Taint.sub_setWidth hn]
    exact (Offset.below_disjoint _ (by have := (s.gpr .esp).isLt; omega)).symm) (by decide)]
  exact h.2

end VG.Proof.Mont.X86.Compact
