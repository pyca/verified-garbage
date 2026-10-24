module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Entry
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Scan
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Table

/-! Complete read-only recognition after saving the two public arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

def recognizeCode : Prog isa := .seq (.block entry) (scan groups 0)
def allClobbers : List Reg := .r9 :: clobbers

structure Result (s t : State) : Prop where
  value : t.gpr .rax = BitVec.ofNat 64
    (recognizeList groups (s.gpr .rdx).toNat (CheckDomain.cdDom s))
  context : Context (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rdx).toNat (CheckDomain.cdDom s) t
  mem : t.mem = entryMem s
  keep : Keep allClobbers s t
  mxcsr : t.mxcsr = s.mxcsr

theorem recognize_ok {s : State} (g : Geometry s) : WP isa recognizeCode s (Result s) := by
  have core : WP isa recognizeCode s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (recognizeList groups (s.gpr .rdx).toNat (CheckDomain.cdDom s)) ∧
      Context (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rdx).toNat (CheckDomain.cdDom s) t ∧
      t.mem = entryMem s ∧ Keep allClobbers s t := by
    rw [recognizeCode, WP.seq_iff]
    refine WP.mono_syms (entry_ok g) ?_
    rintro u ⟨base, memU, restU⟩ symU
    have contextU := entry_context g base memU restU
    have frame : Frame [⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩] s.mem u.mem := by
      rw [memU]; exact entryMem_frame g
    have tableU := consts_table_after g.consts frame restU g.writable
    rw [← symU] at tableU
    have ptr : u.syms tableSym + BitVec.ofNat 64 0 = u.syms tableSym := BitVec.add_zero _
    rw [← ptr] at tableU
    refine WP.mono (scan_ok groups 0 u contextU rfl tableU
      (by simpa only [Nat.zero_add, tableBytes] using
        (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length))) ?_
    rintro t ⟨value, memT, restT⟩
    refine ⟨value, contextU.after memT restT, memT.trans memU,
      (restU.trans restT).mono ?_⟩
    intro r hr
    simp only [allClobbers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact hr
  refine WP.mono_mx (c := recognizeCode) (by decide +kernel) core ?_
  rintro t ⟨value, context, mem, rest⟩ mxcsr
  exact ⟨value, context, mem, rest, mxcsr⟩

end VG.Proof.Ffdh.X86_64.VettedValidation
