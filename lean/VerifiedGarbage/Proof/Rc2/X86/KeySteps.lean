import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
import VerifiedGarbage.Proof.Rc2.Expansion
import VerifiedGarbage.Impl.Rc2.X86.Lookup
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd

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

theorem index_imm (i : Nat) (hi : i < 256) :
    BitVec.ofNat 32 i = (BitVec.ofNat 8 i).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

theorem mask_neg (x : BitVec 32) : (x ^^^ 0xffffffff) + 1 = 0 - x := by
  change (x ^^^ BitVec.allOnes 32) + 1#32 = 0#32 - x
  rw [BitVec.xor_allOnes, ← BitVec.neg_eq_not_add, BitVec.zero_sub]

theorem piStep_ok (s : State) (x : Byte) (hx : s.gpr .eax = x.setWidth 32)
    (i : Nat) (hi : i < 256) :
    ∃ s', runBlock isa (piStep i) s = some s' ∧
      s'.gpr .ebx = s.gpr .ebx |||
        (if x.toNat = i then (Spec.Rc2.piTable.getD i 0).setWidth 32 else 0) ∧
      Keep [.ebx, .edx] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, piStep, selectMask, rr, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift,
      readSrc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      ]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rw [hx, index_imm i hi, mask_neg]
    change s.gpr .ebx |||
      ((0 - (((x.setWidth 32 ^^^ (BitVec.ofNat 8 i).setWidth 32) - 1) >>> 31)) &&&
        (Spec.Rc2.piTable.getD i 0).setWidth 32) = _
    rw [Word32.selectMask_eq]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.allOnes_and]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem piSteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 256)
    (s : State) (x : Byte) (hx : s.gpr .eax = x.setWidth 32) :
    WP isa (.block (is.flatMap piStep)) s (fun s' =>
      s'.gpr .ebx = s.gpr .ebx |||
        (if x.toNat ∈ is then (Spec.Rc2.piTable.getD x.toNat 0).setWidth 32 else 0) ∧
      Keep [.ebx, .edx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := piStep_ok s x hx i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .eax (by decide)).trans hx
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem piStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .eax (.imm 255), imm .ebx 0] s = some s' ∧
      s'.gpr .eax = ((s.gpr .eax).setWidth 8).setWidth 32 ∧ s'.gpr .ebx = 0 ∧
      Keep [.eax, .ebx, .edx] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact Word32.maskByte _
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _

theorem piLookup_ok (s : State) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .eax = (Spec.Rc2.pi ((s.gpr .eax).setWidth 8)).setWidth 32 ∧
      Keep [.eax, .ebx, .edx] s s') := by
  rw [piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := piStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piSteps_ok (List.range 256) (fun i hi => List.mem_range.mp hi)
    s₁ ((s.gpr .eax).setWidth 8) input₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .ebx = (Spec.Rc2.pi ((s.gpr .eax).setWidth 8)).setWidth 32 := by
    rw [h₂.1, zero₁]
    simp only [List.mem_range]
    rw [ite_eq_left ((s.gpr .eax).setWidth 8).isLt]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .eax (s₂.gpr .ebx), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.eax, .ebx, .edx] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _

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
