module

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Scan
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Table
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Geometry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.State

/-! ### `Ffdh.X86_64.VettedValidation.Recognize`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.VettedValidation.Entry`, which this module and modules that import it used -/

section

/-! Saving public arguments writes only the existing scratch buffer. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

def entryMem (s : State) : Mem :=
  (s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 128) (s.gpr .rsi)).writeW
    (s.gpr .rcx + BitVec.ofNat 64 136) (s.gpr .rdx)

theorem entry_ok {s : State} (g : Geometry s) :
    WP isa (.block entry) s fun t =>
      t.gpr .r9 = s.gpr .rcx ∧ t.mem = entryMem s ∧ Keep [.r9] s t := by
  have first : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 128) 8 :=
    g.scratch.region (by have := g.room; omega_using [this]) (by decide)
  have second : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 136) 8 :=
    g.scratch.region (by have := g.room; omega_using [this]) (by decide)
  refine WP.mono (WP.keep [.r9] (Q := fun t =>
    t.gpr .r9 = s.gpr .rcx ∧ t.mem = entryMem s) ?_ rfl) ?_
  · xrun [entry, entryMem, first, second]
  · rintro t ⟨⟨base, mem⟩, rest⟩
    exact ⟨base, mem, rest⟩

theorem entryMem_frame {s : State} (g : Geometry s) :
    Frame [⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩] s.mem (entryMem s) := by
  unfold entryMem
  exact ((Frame.refl _ _).writeW List.mem_cons_self (s.gpr .rsi)
    (Offset.contains_base _ (by have := g.room; omega_using [this]) (by decide))).writeW
      List.mem_cons_self (s.gpr .rdx)
        (Offset.contains_base _ (by have := g.room; omega_using [this]) (by decide))

theorem entryMem_saved (s : State) :
    (entryMem s).readW (s.gpr .rcx + BitVec.ofNat 64 128) 64 = s.gpr .rsi ∧
    (entryMem s).readW (s.gpr .rcx + BitVec.ofNat 64 136) 64 = s.gpr .rdx := by
  constructor
  · rw [entryMem, Mem.readW_writeW_sep
      (Offset.sep _ (d := 128) (n := 8) (e := 136) (k := 8)
        (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _

theorem entry_context {s t : State} (g : Geometry s)
    (base : t.gpr .r9 = s.gpr .rcx) (mem : t.mem = entryMem s) (rest : Keep [.r9] s t) :
    Context (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rdx).toNat (CheckDomain.cdDom s) t := by
  have length : (CheckDomain.cdDom s).length = (s.gpr .rsi).toNat := by
    simp only [CheckDomain.cdDom, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have frame := entryMem_frame g
  have same := entryMem_saved s
  have read (d : Nat) (fit : d + 8 ≤ (s.gpr .r8).toNat * 8) :
      InRegions (t.rd ++ t.wr) (s.gpr .rcx + BitVec.ofNat 64 d) 8 := by
    rw [rest.2.1, rest.2.2]
    obtain ⟨r, member, contains⟩ := g.scratch.region fit (by decide)
    exact ⟨r, List.mem_append_right _ member, contains⟩
  refine ⟨base, rest.gpr (by decide), ?_, ?_, read 128 (by have := g.room; omega_using [this]),
    read 136 (by have := g.room; omega_using [this]), ?_, ?_, by rw [length]; exact g.shape, g.lower, g.upper⟩
  · rw [mem, same.1, length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [mem, same.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [rest.2.1, rest.2.2, length]
    exact g.read
  · rw [mem, length, VG.Proof.Rsa.rsa_bytes_frame frame
      (by have := (s.gpr .rsi).isLt; omega_using [])
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact g.separate)]

end VG.Proof.Ffdh.X86_64.VettedValidation

end

end

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

end

end

/-! A miss restores all original general-validator arguments without changing memory. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

structure Restored (s t : State) : Prop where
  args : t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8
  mem : t.mem = entryMem s
  keep : Keep allClobbers s t
  mxcsr : t.mxcsr = s.mxcsr

theorem restore_ok {s t : State} (h : Result s t) :
    WP isa (.block restore) t (Restored s) := by
  have length : t.mem.readW (s.gpr .rcx + BitVec.ofNat 64 128) 64 = s.gpr .rsi := by
    rw [h.mem, (entryMem_saved s).1]
  have width : t.mem.readW (s.gpr .rcx + BitVec.ofNat 64 136) 64 = s.gpr .rdx := by
    rw [h.mem, (entryMem_saved s).2]
  refine WP.mono_mx (by decide +kernel)
    (WP.keep [.rsi, .rdx, .rcx] (Q := fun u =>
      (u.gpr .rsi = s.gpr .rsi ∧ u.gpr .rdx = s.gpr .rdx ∧
        u.gpr .rcx = s.gpr .rcx) ∧ u.mem = t.mem) ?_ rfl) ?_
  · xrun [restore, h.context.baseReg, h.context.readLength, h.context.readWidth, length, width]
  · rintro u ⟨⟨⟨len, key, base⟩, mem⟩, rest⟩ mxcsr
    have total : Keep allClobbers s u := (h.keep.trans rest).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)
    exact ⟨⟨total.gpr (by decide), len, key, base, total.gpr (by decide)⟩,
      mem.trans h.mem, total, mxcsr.trans h.mxcsr⟩

theorem Restored.pre {s t : State} (h : Restored s t) (hs : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi 8).pre (plain t) := by
  have old := (pre_plain hs).1
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi,
    argRegs, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at old ⊢
  simpa only [plain, stripConsts, State.withRegions, h.args.1, h.args.2.1,
    h.args.2.2.1, h.args.2.2.2.1, h.args.2.2.2.2, h.keep.2.1, h.keep.2.2,
    h.keep.gpr (r := .rsp) (by decide)] using old

theorem Restored.domain {s t : State} (h : Restored s t) (g : Geometry s) :
    CheckDomain.cdDom t = CheckDomain.cdDom s := by
  unfold CheckDomain.cdDom
  rw [h.args.1, h.args.2.1, h.mem]
  exact VG.Proof.Rsa.rsa_bytes_frame (entryMem_frame g)
    (by have := (s.gpr .rsi).isLt; omega_using [])
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact g.separate)

theorem Restored.abi {s t : State} (h : Restored s t) (g : Geometry s) : abiPreserved s t := by
  refine ⟨fun r hr => h.keep.gpr (by revert r; decide), ?_, ?_⟩
  · rw [h.mem]
    exact (entryMem_frame g).readW (Region.contains_self _ _)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact g.returnSeparate) (by decide)
  · rw [h.mxcsr]

end VG.Proof.Ffdh.X86_64.VettedValidation
