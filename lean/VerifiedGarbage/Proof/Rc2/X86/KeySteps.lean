module

public import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Rc2.X86.PiLookup
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rc2.Select32

@[expose] public section

section

/-! # Correctness of baseline x86 RC2 lookup steps -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

/-- A register-only block preserves memory, regions, and other GPRs. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

/-- PITABLE[EAX & 255] into EAX (`piLookupSse_ok`), keeping memory; the 16
bytes at EDI pass the lanes through. -/
theorem piLookup_ok (s : State) (lanes : InRegions s.wr ((s.gpr .edi).setWidth 64) 16) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .eax = (Spec.Rc2.pi ((s.gpr .eax).setWidth 8)).setWidth 32 ∧
      Keep [.eax, .ebx, .edx] s s') := by
  have hw : InRegions s.wr (addr (s.gpr .edi) 0) 16 := by
    rw [show addr (s.gpr .edi) 0 = (s.gpr .edi).setWidth 64 by
      simp only [addr, BitVec.add_zero]]
    exact lanes
  refine WP.mono (piLookupSse_ok s hw) fun t ⟨h1, hg, hm, hrd, hwr⟩ => ⟨h1, ⟨fun r hr => ?_, hm, hrd, hwr⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact hg r hr.1 hr.2.1 hr.2.2

end VG.Proof.Rc2.X86

end

/-! # Individual X86 RC2 key-expansion steps -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

def addr32 (x : BitVec 32) : Addr := x.setWidth 64

theorem addr_add {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    addr32 (x + BitVec.ofNat 32 k) = addr32 x + BitVec.ofNat 64 k :=
  VG.X86.addr_eq h

def keyTemps : List Reg := [.eax, .ecx, .ebx, .edx]

/-- The public zero flag controls the key-expansion loops. -/
def zeroFlag (s : State) : Option Bool := s.zf

theorem eval_zero (s : State) : eval .e s = zeroFlag s := rfl

theorem eval_nonzero (s : State) :
    eval .ne s = (zeroFlag s).map (!·) := rfl

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp + s.gpr .ecx)) 1)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      zeroFlag s' = some ((s.gpr .ecx + 1 - s.gpr .esi) == 0) ∧
      Keep keyTemps
        {s with mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx)) (s.mem (addr32 (s.gpr .ebp + s.gpr .ecx)))} s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, copyKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, Reg8.reg, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8, State.store8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readable, writable]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags,  reduceCtorEq, ite_false, ite_true]
  · simp only [zeroFlag, zf_arithFlags, zf_setReg]
  · constructor
    · intro r hr
      have h8 : r ≠ .eax := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .ecx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags,  h8, h23, h9, ite_false]
    · simp only [ mem_setReg, mem_arithFlags,
        BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
    · rfl
    · rfl

theorem fillInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi))) 1) :
    ∃ s', runBlock isa fillInput s = some s' ∧
      s'.gpr .eax = (s.mem (addr32 (s.gpr .edi + s.gpr .ecx - 1))).setWidth 32 +
        (s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi)))).setWidth 32 ∧
      Keep [.eax, .ebx, .edx] s s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, fillInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readLo, readHi]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .eax := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .ebx := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags, h8, h3, h5, ite_false]
    · rfl
    · rfl
    · rfl

theorem fillOutput_ok (s : State)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa fillFinish s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      zeroFlag s' = some ((s.gpr .ecx + 1 - 128) == 0) ∧
      Keep keyTemps {s with mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx)) ((s.gpr .eax).setWidth 8)} s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, fillFinish, storeKey, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, Reg8.reg, execAlu, readSrc, Option.bind_some, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, writable]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags,  reduceCtorEq, ite_true, ite_false]
  · simp only [zeroFlag, zf_arithFlags, zf_setReg]
  · constructor
    · intro r hr
      have h23 : r ≠ .ecx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags,  h23, h9, ite_false]
    · simp only [mem_arithFlags, mem_setReg]
    · rfl
    · rfl

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa reduceInput s = some s' ∧
      s'.gpr .eax = (s.mem (addr32 (s.gpr .edi + s.gpr .ecx))).setWidth 32 &&& s.gpr .ebx ∧
      Keep [.eax, .edx] s s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, reduceInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readable]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .eax := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags, h8, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem storeByte_ok (s : State)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa storeKey s = some s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Keep [.edx] {s with mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx)) ((s.gpr .eax).setWidth 8)} s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [storeKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, Reg8.reg, execAlu, readSrc, Option.bind_some, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, writable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · rfl
  · constructor
    · intro r hr
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem descendInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi))) 1) :
    ∃ s', runBlock isa descendInput s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx - 1 ∧
      s'.gpr .eax = (s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1))).setWidth 32 ^^^
        (s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi)))).setWidth 32 ∧
      Keep [.eax, .ecx, .ebx, .edx] s s' := by
  simp only [addr32] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [descendInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .eax := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .ecx := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .ebx := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags, h8, h23, h3, h5, ite_false]
    · rfl
    · rfl
    · rfl

theorem cmpZero_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .ecx (.imm 0)] s = some s' ∧
      zeroFlag s' = some (s.gpr .ecx == 0) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · change some ((s.gpr .ecx - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end VG.Proof.Rc2.X86
