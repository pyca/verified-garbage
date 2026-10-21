module

public import VerifiedGarbage.Impl.Mont.X86.Compact
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The compact multiplication's register-saving frame -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86

theorem inner_noSp : NoSp (.seq Compact.core (.block Compact.restoreRegs)) :=
  .of_all (by decide +kernel)

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
