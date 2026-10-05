import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Impl.Rc2.X86.Lookup
import VerifiedGarbage.Proof.Rc2.Word32
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Rc2.PiLit

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Save`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.KeySteps`. -/
section

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
    (h : VG.Proof.Rc2.X86.Keep rs s s') (h' : VG.Proof.Rc2.X86.Keep rs s' s'') : VG.Proof.Rc2.X86.Keep rs s s'' :=
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
      VG.Proof.Rc2.X86.Keep [.ebx, .edx] s s' := by
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
    rw [hx, VG.Proof.Rc2.X86.index_imm i hi, VG.Proof.Rc2.X86.mask_neg]
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
      VG.Proof.Rc2.X86.Keep [.ebx, .edx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.piStep_ok s x hx i (hi i (by simp))
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

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Rc2.X86.Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Rc2.X86.Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem piStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .eax (.imm 255), imm .ebx 0] s = some s' ∧
      s'.gpr .eax = ((s.gpr .eax).setWidth 8).setWidth 32 ∧ s'.gpr .ebx = 0 ∧
      VG.Proof.Rc2.X86.Keep [.eax, .ebx, .edx] s s' := by
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
      VG.Proof.Rc2.X86.Keep [.eax, .ebx, .edx] s s') := by
  rw [piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := VG.Proof.Rc2.X86.piStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.piSteps_ok (List.range 256) (fun i hi => List.mem_range.mp hi)
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
    · have k₂ : VG.Proof.Rc2.X86.Keep [.eax, .ebx, .edx] s₁ s₂ := h₂.2.weaken (by
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
    VG.Proof.Rc2.X86.addr32 (x + BitVec.ofNat 32 k) = VG.Proof.Rc2.X86.addr32 x + BitVec.ofNat 64 k :=
  VG.X86.addr_eq h

def keyTemps : List Reg := [.eax, .ecx, .ebx, .edx]

/-- The public zero flag controls the key-expansion loops. -/
def zeroFlag (s : State) : Option Bool := s.zf

theorem eval_zero (s : State) : eval .e s = VG.Proof.Rc2.X86.zeroFlag s := rfl

theorem eval_nonzero (s : State) :
    eval .ne s = (VG.Proof.Rc2.X86.zeroFlag s).map (!·) := rfl

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .ebp + s.gpr .ecx)) 1)
    (writable : InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      VG.Proof.Rc2.X86.zeroFlag s' = some ((s.gpr .ecx + 1 - s.gpr .esi) == 0) ∧
      VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps
        {s with mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .ebp + s.gpr .ecx)))} s' := by
  simp only [VG.Proof.Rc2.X86.addr32] at *
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, copyKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, Reg8.reg, execAlu, readSrc, Option.bind_some, Option.map_some, State.load8, State.store8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, readable, writable]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags,  reduceCtorEq, ite_false, ite_true]
  · simp only [VG.Proof.Rc2.X86.zeroFlag, zf_arithFlags, zf_setReg]
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
    (readLo : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi))) 1) :
    ∃ s', runBlock isa fillInput s = some s' ∧
      s'.gpr .eax = (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx - 1))).setWidth 32 +
        (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi)))).setWidth 32 ∧
      VG.Proof.Rc2.X86.Keep [.eax, .ebx, .edx] s s' := by
  simp only [VG.Proof.Rc2.X86.addr32] at *
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
    (writable : InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa fillFinish s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      VG.Proof.Rc2.X86.zeroFlag s' = some ((s.gpr .ecx + 1 - 128) == 0) ∧
      VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps {s with mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) ((s.gpr .eax).setWidth 8)} s' := by
  simp only [VG.Proof.Rc2.X86.addr32] at *
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, fillFinish, storeKey, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, rr, memOp, State.ea, Reg8.reg, execAlu, readSrc, Option.bind_some, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, writable]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags,  reduceCtorEq, ite_true, ite_false]
  · simp only [VG.Proof.Rc2.X86.zeroFlag, zf_arithFlags, zf_setReg]
  · constructor
    · intro r hr
      have h23 : r ≠ .ecx := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .edx := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, gpr_arithFlags,  h23, h9, ite_false]
    · simp only [mem_arithFlags, mem_setReg]
    · rfl
    · rfl

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa reduceInput s = some s' ∧
      s'.gpr .eax = (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx))).setWidth 32 &&& s.gpr .ebx ∧
      VG.Proof.Rc2.X86.Keep [.eax, .edx] s s' := by
  simp only [VG.Proof.Rc2.X86.addr32] at *
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
    (writable : InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    ∃ s', runBlock isa storeKey s = some s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      VG.Proof.Rc2.X86.Keep [.edx] {s with mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) ((s.gpr .eax).setWidth 8)} s' := by
  simp only [VG.Proof.Rc2.X86.addr32] at *
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
    (readLo : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi))) 1) :
    ∃ s', runBlock isa descendInput s = some s' ∧
      s'.gpr .ecx = s.gpr .ecx - 1 ∧
      s'.gpr .eax = (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1))).setWidth 32 ^^^
        (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi)))).setWidth 32 ∧
      VG.Proof.Rc2.X86.Keep [.eax, .ecx, .ebx, .edx] s s' := by
  simp only [VG.Proof.Rc2.X86.addr32] at *
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
      VG.Proof.Rc2.X86.zeroFlag s' = some (s.gpr .ecx == 0) ∧ VG.Proof.Rc2.X86.Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · change some ((s.gpr .ecx - 0) == 0) = _
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end VG.Proof.Rc2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.KeyLoop`. -/
section

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem fillKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi))) 1)
    (writable : InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block fillKey) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      VG.Proof.Rc2.X86.zeroFlag s' = some ((s.gpr .ecx + 1 - 128) == 0) ∧
      VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps {s with
        mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx))
          (Spec.Rc2.pi (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx - 1)) +
          s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi)))))} s') := by
  rw [fillKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.fillInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.piLookup_ok s₁)
  intro s₂ h₂
  have k₁ : VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h <;> subst r <;> decide)
  have k₂ : VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .edi (by decide)
  have index := (keep₁.reg .ecx (by decide)).trans rfl
  have index₂ : s₂.gpr .ecx = s.gpr .ecx := (h₂.2.reg .ecx (by decide)).trans index
  have write₂ : InRegions s₂.wr (VG.Proof.Rc2.X86.addr32 (s₂.gpr .edi + s₂.gpr .ecx)) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := VG.Proof.Rc2.X86.fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem piStore_ok (s : State) (writable : InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block (piLookup ++ storeKey)) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx ∧
      VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps {s with
        mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) (Spec.Rc2.pi ((s.gpr .eax).setWidth 8))} s') := by
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.piLookup_ok s)
  intro s₁ h₁
  have ptr := h₁.2.reg .edi (by decide)
  have index := h₁.2.reg .ecx (by decide)
  have valid : InRegions s₁.wr (VG.Proof.Rc2.X86.addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  obtain ⟨s₂, run₂, index₂, keep₂⟩ := VG.Proof.Rc2.X86.storeByte_ok s₁ valid
  refine WP.of_runBlock ⟨s₂, run₂, index₂.trans index, ?_⟩
  constructor
  · intro r hr
    rw [keep₂.reg r (by intro hm; simp only [List.mem_singleton] at hm; subst r; exact hr (by decide))]
    exact h₁.2.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h <;> subst r <;> decide))
  · rw [keep₂.mem, h₁.2.mem, ptr, index, h₁.1]
    simp
  · exact keep₂.rd.trans h₁.2.rd
  · exact keep₂.wr.trans h₁.2.wr

theorem reduceKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) 1)
    (writable : InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block reduceKey) s (fun s' => s'.gpr .ecx = s.gpr .ecx ∧
      VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps {s with
        mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx))
          (Spec.Rc2.pi (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + s.gpr .ecx)) &&& (s.gpr .ebx).setWidth 8))} s') := by
  rw [reduceKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.reduceInput_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .edi (by decide)
  have index := keep₁.reg .ecx (by decide)
  have valid : InRegions s₁.wr (VG.Proof.Rc2.X86.addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (VG.Proof.Rc2.X86.piStore_ok s₁ valid)
  intro s₂ h₂
  refine ⟨h₂.1.trans index, ?_⟩
  constructor
  · intro r hr
    exact (h₂.2.reg r hr).trans (keep₁.reg r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h <;> subst r <;> exact hr (by decide)))
  · rw [h₂.2.mem, keep₁.mem, ptr, index, out₁]
    simp
  · exact h₂.2.rd.trans keep₁.rd
  · exact h₂.2.wr.trans keep₁.wr

theorem descendKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi))) 1)
    (writable : InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1))) 1) :
    WP isa (.block descendKey) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx - 1 ∧ VG.Proof.Rc2.X86.zeroFlag s' = some ((s.gpr .ecx - 1) == 0) ∧
      VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps {s with
        mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1)))
          (Spec.Rc2.pi (s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) ^^^
            s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi)))))} s') := by
  rw [descendKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.descendInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .edi (by decide)
  have valid : InRegions s₁.wr (VG.Proof.Rc2.X86.addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  rw [← List.append_assoc, WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.piStore_ok s₁ valid)
  intro s₂ h₂
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := VG.Proof.Rc2.X86.cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .ecx (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by simp)).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)


end VG.Proof.Rc2.X86

end

/-! # A bounded loop rule and frame invariant for key expansion -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem forwardLoop (body : Prog isa) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ VG.Proof.Rc2.X86.zeroFlag s' = some (decide (i + 1 = stop))))
    (i : Nat) (hi : i < stop) (s : State) (hs : I i s) :
    WP isa (.loop body .ne) s (I stop) := by
  let Inv (n : Nat) (s : State) := ∃ i, i < stop ∧ stop - i = n ∧ I i s
  refine WP.loop (M := isa) Inv ?_ (stop - i) s ⟨i, hi, rfl, hs⟩
  intro n s ⟨j, hj, hn, hI⟩
  apply WP.mono (step j hj s hI)
  intro s' h'
  by_cases he : j + 1 = stop
  · left
    constructor
    · simp only [VG.Proof.Rc2.X86.eval_nonzero, h'.2, he, decide_true, Option.map_some, Bool.not_true]
    · rw [he] at h'
      exact h'.1
  · right
    constructor
    · simp only [VG.Proof.Rc2.X86.eval_nonzero, h'.2, he, decide_false, Option.map_some, Bool.not_false]
    · exact ⟨stop - (j + 1), by omega, j + 1, by omega, rfl, h'.1⟩

/-- Across a key-expansion loop only the four temporaries and the schedule
buffer change. The key, scratch saves, and return address are separate. -/
structure KeyFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ VG.Proof.Rc2.X86.keyTemps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨VG.Proof.Rc2.X86.addr32 (s₀.gpr .edi), 128⟩] s₀.mem s.mem

theorem KeyFrame.refl (s : State) : VG.Proof.Rc2.X86.KeyFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem KeyFrame.trans {s₀ s₁ s₂ : State} (h₁ : VG.Proof.Rc2.X86.KeyFrame s₀ s₁) (h₂ : VG.Proof.Rc2.X86.KeyFrame s₁ s₂) :
    VG.Proof.Rc2.X86.KeyFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .edi (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem KeyFrame.step {s₀ s s' : State} (h : VG.Proof.Rc2.X86.KeyFrame s₀ s) (i : Nat) (hi : i < 128)
    (b : Byte) (keep : VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps {s with mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s₀.gpr .edi) + BitVec.ofNat 64 i) b} s') : VG.Proof.Rc2.X86.KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]
  exact h.mem.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

theorem KeyFrame.keep {s₀ s s' : State} (h : VG.Proof.Rc2.X86.KeyFrame s₀ s) (keep : VG.Proof.Rc2.X86.Keep VG.Proof.Rc2.X86.keyTemps s s') :
    VG.Proof.Rc2.X86.KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]; exact h.mem

theorem counter_add (i : Nat) : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
  rw [BitVec.ofNat_add]
  rfl

theorem counter_eq (i n : Nat) (hi : i < 2 ^ 32) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 i - BitVec.ofNat 32 n) == 0#32) = decide (i = n) := by
  have he : (BitVec.ofNat 32 i - BitVec.ofNat 32 n = 0#32) ↔ i = n := by bv_omega
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using he

theorem counter_sub (i : Nat) (hi : 1 ≤ i) :
    BitVec.ofNat 32 i - 1 = BitVec.ofNat 32 (i - 1) :=
  Offset.ofNat_sub_ofNat hi

end VG.Proof.Rc2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Save`. -/
section

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem exec_load (s : State) (t n : Reg) (off : Nat)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.mov t (.mem (memOp n off))) s =
      some (s.setReg t (s.mem.readW (VG.Proof.Rc2.X86.addr32 (s.gpr n) + BitVec.ofNat 64 off) 32)) := by
  change (State.load32 s (VG.Proof.Rc2.X86.addr32 (s.gpr n + BitVec.ofNat 32 off))).map (s.setReg t) = _
  rw [VG.Proof.Rc2.X86.addr_add fit]
  simp only [State.load32, h, ite_true, Option.map_some]

theorem exec_store (s : State) (t n : Reg) (off : Nat)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.store (memOp n off) t) s =
      some {s with mem := s.mem.writeW (VG.Proof.Rc2.X86.addr32 (s.gpr n) + BitVec.ofNat 64 off) (s.gpr t)} := by
  change State.store32 s (VG.Proof.Rc2.X86.addr32 (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t) = _
  rw [VG.Proof.Rc2.X86.addr_add fit]
  simp only [State.store32, h, ite_true]

end VG.Proof.Rc2.X86

end

/-! # Saving and restoring RC2's callee-saved registers in scratch -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

def saveMem (m : Mem) (p : Addr) (v : Nat → BitVec 32) (n : Nat) : Mem :=
  (List.range n).foldl (fun m i => m.writeW (p + BitVec.ofNat 64 (4 * i)) (v i)) m

theorem saveMem_succ (m : Mem) (p : Addr) (v : Nat → BitVec 32) (n : Nat) :
    VG.Proof.Rc2.X86.saveMem m p v (n + 1) = (VG.Proof.Rc2.X86.saveMem m p v n).writeW (p + BitVec.ofNat 64 (4 * n)) (v n) := by
  simp only [VG.Proof.Rc2.X86.saveMem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem saveMem_read (m : Mem) (p : Addr) (v : Nat → BitVec 32) (n : Nat) (hn : n ≤ 64)
    (i : Nat) (hi : i < n) : (VG.Proof.Rc2.X86.saveMem m p v n).readW (p + BitVec.ofNat 64 (4 * i)) 32 = v i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [VG.Proof.Rc2.X86.saveMem_succ]
    by_cases he : i = n
    · subst i; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem saveMem_frame (m : Mem) (p : Addr) (v : Nat → BitVec 32) (n : Nat) (hn : n ≤ 64) :
    Frame [⟨p, 4 * n⟩] m (VG.Proof.Rc2.X86.saveMem m p v n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    rw [VG.Proof.Rc2.X86.saveMem_succ]
    have prev : Frame [⟨p, 4 * (n + 1)⟩] m (VG.Proof.Rc2.X86.saveMem m p v n) := by
      apply (ih (by omega)).sub
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      refine ⟨⟨p, 4 * (n + 1)⟩, List.mem_cons_self, ?_⟩
      intro x hx
      change (x - p).toNat + 1 ≤ 4 * n at hx
      change (x - p).toNat + 1 ≤ 4 * (n + 1)
      omega
    exact prev.writeW List.mem_cons_self _ (Offset.contains_base p (by omega) (by omega))

def saveCode (base : Reg) (regs : Nat → Reg) (n : Nat) : List Instr :=
  (List.range n).map fun i => .store (memOp base (4 * i)) (regs i)

theorem saveCode_ok (s : State) (base : Reg) (regs : Nat → Reg) (n : Nat) (hn : n ≤ 64)
    (fit : (s.gpr base).toNat + 256 ≤ 2 ^ 32)
    (writable : ∀ i < n, InRegions s.wr (VG.Proof.Rc2.X86.addr32 (s.gpr base) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (VG.Proof.Rc2.X86.saveCode base regs n)) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.Proof.Rc2.X86.saveMem s.mem (VG.Proof.Rc2.X86.addr32 (s.gpr base)) (fun i => s.gpr (regs i)) n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [VG.Proof.Rc2.X86.saveCode, List.range_succ, List.map_append, List.map_cons, List.map_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega) (fun i hi => writable i (by omega)))
    intro s₁ h₁
    have valid := writable n (by omega)
    have valid₁ : InRegions s₁.wr (VG.Proof.Rc2.X86.addr32 (s₁.gpr base) + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [h₁.1, h₁.2.2.1]; exact valid
    have fit₁ : (s₁.gpr base).toNat + 256 ≤ 2 ^ 32 := by rw [h₁.1]; exact fit
    refine WP.of_runBlock ⟨{s₁ with mem := s₁.mem.writeW (VG.Proof.Rc2.X86.addr32 (s₁.gpr base) + BitVec.ofNat 64 (4 * n)) (s₁.gpr (regs n))}, ?_, ?_⟩
    · simp only [runBlock_cons, VG.Proof.Rc2.X86.exec_store _ _ _ (4 * n) (by omega) valid₁,
        runStep_some, runBlock_nil]
    · exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, by rw [h₁.2.2.2, h₁.1, VG.Proof.Rc2.X86.saveMem_succ]⟩

def restoreCode (base : Reg) (regs : Nat → Reg) (is : List Nat) : List Instr :=
  is.map fun i => .mov (regs i) (.mem (memOp base (4 * i)))

theorem restoreCode_ok (s : State) (base : Reg) (regs : Nat → Reg) (is : List Nat)
    (values : Reg → BitVec 32) (fit : (s.gpr base).toNat + 256 ≤ 2 ^ 32) (bounds : ∀ i ∈ is, i < 64)
    (separate : ∀ i ∈ is, regs i ≠ base)
    (readable : ∀ i ∈ is, InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.addr32 (s.gpr base) + BitVec.ofNat 64 (4 * i)) 4)
    (stored : ∀ i ∈ is, s.mem.readW (VG.Proof.Rc2.X86.addr32 (s.gpr base) + BitVec.ofNat 64 (4 * i)) 32 = values (regs i)) :
    WP isa (.block (VG.Proof.Rc2.X86.restoreCode base regs is)) s (fun s' =>
      (∀ r ∈ is.map regs, s'.gpr r = values r) ∧ VG.Proof.Rc2.X86.Keep (is.map regs) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    change WP isa (.block (([.mov (regs i) (.mem (memOp base (4 * i)))] : List Instr) ++ VG.Proof.Rc2.X86.restoreCode base regs is)) s _
    rw [WP.block_append_iff]
    let s₁ := s.setReg (regs i) (values (regs i))
    have hi : i ∈ i :: is := List.mem_cons_self
    refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
    · have bound := bounds i hi
      simp only [runBlock_cons, VG.Proof.Rc2.X86.exec_load _ _ _ (4 * i) (by omega) (readable i hi),
        runStep_some, runBlock_nil, stored i hi]
      rfl
    have keep₁ : VG.Proof.Rc2.X86.Keep [regs i] s s₁ := by
      constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        exact gpr_setReg_of_ne _ _ hr
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _
    have ptr₁ := keep₁.reg base (by
      simp only [List.mem_singleton]; exact Ne.symm (separate i hi))
    have read₁ : ∀ j ∈ is,
        InRegions (s₁.rd ++ s₁.wr) (VG.Proof.Rc2.X86.addr32 (s₁.gpr base) + BitVec.ofNat 64 (4 * j)) 4 := by
      rw [keep₁.rd, keep₁.wr, ptr₁]
      exact fun j hj => readable j (List.mem_cons_of_mem _ hj)
    have stored₁ : ∀ j ∈ is,
        s₁.mem.readW (VG.Proof.Rc2.X86.addr32 (s₁.gpr base) + BitVec.ofNat 64 (4 * j)) 32 = values (regs j) := by
      rw [keep₁.mem, ptr₁]
      exact fun j hj => stored j (List.mem_cons_of_mem _ hj)
    apply WP.mono (ih s₁ (by rw [ptr₁]; exact fit) (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) (fun j hj => separate j (List.mem_cons_of_mem _ hj)) read₁ stored₁)
    intro s₂ h₂
    constructor
    · intro r hr
      simp only [List.map_cons, List.mem_cons] at hr
      by_cases hm : r ∈ is.map regs
      · exact h₂.1 r hm
      · have he := hr.resolve_right hm
        subst r
        rw [h₂.2.reg _ hm]
        exact gpr_setReg_self _ _ _
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_singleton] at hr
        subst r; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hr

theorem saveMem_frame_le (m : Mem) (p : Addr) (v : Nat → BitVec 32)
    (n capacity : Nat) (hn : n ≤ capacity) (hc : capacity ≤ 64) :
    Frame [⟨p, 4 * capacity⟩] m (VG.Proof.Rc2.X86.saveMem m p v n) := by
  apply (VG.Proof.Rc2.X86.saveMem_frame m p v n (by omega)).sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  refine ⟨⟨p, 4 * capacity⟩, List.mem_cons_self, ?_⟩
  intro x hx
  change (x - p).toNat + 1 ≤ 4 * n at hx
  change (x - p).toNat + 1 ≤ 4 * capacity
  omega

end VG.Proof.Rc2.X86

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.KeyIO`. -/
section

section

/-! # Public effective-key mask selection -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

theorem cmpMask_ok (s : State) (i : Nat) (_hi : i < 7) :
    ∃ s', runBlock isa [.alu .cmp .edx (.imm (BitVec.ofNat 32 (i + 1)))] s = some s' ∧
      zeroFlag s' = some (s.gpr .edx == BitVec.ofNat 32 (i + 1)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · change some ((s.gpr .edx - BitVec.ofNat 32 (i + 1)) == 0) = _
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem setMask_ok (s : State) (i : Nat) (_hi : i < 7) :
    ∃ s', runBlock isa [imm .ebx (2 ^ (i + 1) - 1)] s = some s' ∧
      s'.gpr .ebx = BitVec.ofNat 32 (2 ^ (i + 1) - 1) ∧ Keep [.ebx] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, exec]
    rfl, ?_⟩
  constructor
  · rfl
  · exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; exact hr), rfl, rfl, rfl⟩

theorem maskBranch_ok (s : State) (i : Nat) (hi : i < 7) :
    WP isa (.seq (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 (i + 1)))])
      (.ite .e (.block [imm .ebx (2 ^ (i + 1) - 1)]) (.block []))) s (fun s' =>
        s'.gpr .ebx = (if s.gpr .edx = BitVec.ofNat 32 (i + 1)
          then BitVec.ofNat 32 (2 ^ (i + 1) - 1) else s.gpr .ebx) ∧ Keep [.ebx] s s') := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpMask_ok s i hi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.ite (s.gpr .edx == BitVec.ofNat 32 (i + 1)) (by exact flag₁)
  · intro he
    have eq := beq_iff_eq.mp he
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := setMask_ok s₁ i hi
    apply WP.of_runBlock
    refine ⟨s₂, run₂, ?_, ?_⟩
    · rw [ite_eq_left eq]; exact out₂
    · exact (keep₁.weaken (by simp)).trans keep₂
  · intro he
    have ne : s.gpr .edx ≠ BitVec.ofNat 32 (i + 1) := by simpa using he
    apply WP.block_nil
    refine ⟨?_, keep₁.weaken (by simp)⟩
    rw [ite_eq_right ne]
    exact keep₁.reg .ebx (by simp)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.seq a b) c) s Q ↔ WP isa (.seq a (.seq b c)) s Q := by
  constructor
  · intro h
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)
  · intro h
    exact WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))

theorem maskBranches_ok (is : List Nat) (hi : ∀ i ∈ is, i < 7)
    (s : State) (k : Nat) (hk : k < 8) (index : s.gpr .edx = BitVec.ofNat 32 k) :
    WP isa (is.foldr (fun i rest =>
      .seq (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .e (.block [imm .ebx (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))
      s (fun s' => s'.gpr .ebx = (if k ∈ is.map (· + 1) then
        BitVec.ofNat 32 (2 ^ k - 1) else s.gpr .ebx) ∧ Keep [.ebx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.foldr_cons, ← seq_assoc]
    apply WP.seq
    apply WP.mono (maskBranch_ok s i (hi i List.mem_cons_self))
    intro s₁ h₁
    have index₁ := (h₁.2.reg .edx (by decide)).trans index
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ index₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₂.1, h₁.1, index]
    have eq : BitVec.ofNat 32 k = BitVec.ofNat 32 (i + 1) ↔ k = i + 1 := by
      have bound := hi i List.mem_cons_self
      bv_omega
    simp only [eq, List.map_cons, List.mem_cons]
    by_cases he : k = i + 1
    · subst k; simp
    · by_cases hm : k ∈ is.map (· + 1) <;> simp [he, hm]

theorem maskStart_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .esp + 12)) 4) :
    ∃ s', runBlock isa [.mov .edx (.mem (memOp .esp 12)), .alu .and .edx (.imm 7), imm .ebx 255] s = some s' ∧
      s'.gpr .edx = s.mem.readW (addr32 (s.gpr .esp + 12)) 32 &&& 7 ∧
      s'.gpr .ebx = 255 ∧ Keep [.ebx, .edx] s s' := by
  simp only [addr32, BitVec.ofNat_eq_ofNat] at *
  refine ⟨_, by
    simp only [↓reduceIte, imm, memOp, State.ea, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32, Option.bind_some,
      Option.map_some, gpr_setReg, readable]
    rfl, ?_⟩
  refine ⟨?_, rfl, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem maskCode_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .esp + 12)) 4)
    (input : s.mem.readW (addr32 (s.gpr .esp + 12)) 32 = BitVec.ofNat 32 bits) :
    WP isa maskCode s (fun s' =>
      (s'.gpr .ebx).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))) ∧
      Keep [.ebx, .edx] s s') := by
  rw [maskCode]
  apply WP.seq
  obtain ⟨s₁, run₁, index₁, mask₁, keep₁⟩ := maskStart_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have index : s₁.gpr .edx = BitVec.ofNat 32 (bits % 8) := by
    rw [index₁, input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    change bits % 2 ^ 32 &&& (2 ^ 3 - 1) = bits % 8 % 2 ^ 32
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  apply WP.mono (maskBranches_ok (List.range 7) (by simp)
    s₁ (bits % 8) (Nat.mod_lt _ (by decide)) index)
  intro s₂ h₂
  refine ⟨?_, keep₁.trans (h₂.2.weaken (by simp))⟩
  rw [h₂.1, mask₁]
  have exponent : 8 + bits - 8 * ((bits + 7) / 8) = if bits % 8 = 0 then 8 else bits % 8 := by
    split <;> omega
  rw [exponent]
  have fact : ∀ r < 8,
      ((if r ∈ (List.range 7).map (· + 1) then BitVec.ofNat 32 (2 ^ r - 1)
        else 255).setWidth 8) = BitVec.ofNat 8 (255 % 2 ^ (if r = 0 then 8 else r)) := by decide
  exact fact _ (Nat.mod_lt _ (by decide))

end VG.Proof.Rc2.X86

end

section

section

/-! # The descending effective-key reduction loop -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem descendLoop_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 < 128)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 t8) (start : s.gpr .ecx = BitVec.ofNat 32 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (addr32 (s.gpr .edi)) l 128) :
    WP isa (.loop (.block descendKey) .ne) s (fun s' =>
      s'.gpr .ecx = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (addr32 (s.gpr .edi)) (descend l t8 (128 - t8)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .ecx = BitVec.ofNat 32 (128 - t8 - j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (addr32 (s.gpr .edi)) (descend l t8 j) 128
  have finish : I (128 - t8) = (fun s' => s'.gpr .ecx = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (addr32 (s.gpr .edi)) (descend l t8 (128 - t8)) 128) := by
    funext s'
    simp only [I, Nat.sub_self]
    rfl
  rw [← finish]
  apply forwardLoop (.block descendKey) I (128 - t8) _ 0 (by omega) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .edi (by decide)
  have len₁ := (frame₁.reg .esi (by decide)).trans len
  have indexNew : s₁.gpr .ecx - 1 = BitVec.ofNat 32 (127 - t8 - j) := by
    rw [index₁, counter_sub _ (show 1 ≤ 128 - t8 - j by omega)]
    congr 1; omega
  have loAddr : addr32 (s₁.gpr .edi + (s₁.gpr .ecx - 1) + 1) =
      addr32 (s.gpr .edi) + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [outPtr, indexNew, BitVec.add_assoc, counter_add]
    exact addr_add (by omega)
  have hiAddr : addr32 (s₁.gpr .edi + (s₁.gpr .ecx - 1 + s₁.gpr .esi)) =
      addr32 (s.gpr .edi) + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [outPtr, indexNew, len₁, ← BitVec.ofNat_add]
    exact addr_add (by omega)
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (addr32 (s₁.gpr .edi + (s₁.gpr .ecx - 1))) 1 := by
    rw [frame₁.wr, outPtr, indexNew, addr_add (by omega)]
    exact writable _ (by omega)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .edi + (s₁.gpr .ecx - 1) + 1)) 1 := by
    rw [loAddr]; exact read₁ _ (by omega)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .edi + (s₁.gpr .ecx - 1 + s₁.gpr .esi))) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega)
  apply WP.mono (descendKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((descend l t8 j).getD (127 - t8 - j + 1) 0 ^^^
    (descend l t8 j).getD (127 - t8 - j + t8) 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (addr32 (s.gpr .edi) + BitVec.ofNat 64 (127 - t8 - j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega), prefix₁ _ (by omega), outPtr, indexNew, addr_add (by omega)] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (127 - t8 - j) (by omega) b keep₂, ?_⟩
    · rw [h₂.1]
      change s₁.gpr .ecx - 1 = _
      rw [indexNew]
      congr 1; omega
    · rw [keep₂.mem, descend_succ]
      exact prefix₁.write (by decide) (by omega) b
  · rw [h₂.2.1]
    change some ((s₁.gpr .ecx - 1) == 0#32) = _
    rw [indexNew]
    have he : 127 - t8 - j = 0 ↔ j + 1 = 128 - t8 := by omega
    have eqZero := counter_eq (127 - t8 - j) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    rw [eqZero]
    simp only [he]

end VG.Proof.Rc2.X86

end

section

/-! # Forward expansion to 128 bytes -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem fillLoop_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length < 128)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 key.length) (start : s.gpr .ecx = BitVec.ofNat 32 key.length)
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (addr32 (s.gpr .edi)) (fill key 0) key.length) :
    WP isa (.loop (.block fillKey) .ne) s (fun s' =>
      s'.gpr .ecx = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill key (128 - key.length)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .ecx = BitVec.ofNat 32 (key.length + j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill key j) (key.length + j)
  have finish : I (128 - key.length) = (fun s' => s'.gpr .ecx = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill key (128 - key.length)) 128) := by
    funext s'
    simp only [I, Nat.add_sub_of_le (Nat.le_of_lt ht')]
    rfl
  rw [← finish]
  apply forwardLoop (.block fillKey) I (128 - key.length) _ 0 (by omega) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .edi (by decide)
  have len₁ := (frame₁.reg .esi (by decide)).trans len
  have loAddr : addr32 (s₁.gpr .edi + s₁.gpr .ecx - 1) =
      addr32 (s.gpr .edi) + BitVec.ofNat 64 (key.length + j - 1) := by
    rw [outPtr, index₁, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, counter_sub _ (by omega)]
    exact addr_add (by omega)
  have hiAddr : addr32 (s₁.gpr .edi + (s₁.gpr .ecx - s₁.gpr .esi)) =
      addr32 (s.gpr .edi) + BitVec.ofNat 64 j := by
    rw [outPtr, index₁, len₁, Offset.ofNat_sub_ofNat (by omega), Nat.add_sub_cancel_left]
    exact addr_add (by omega)
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [frame₁.wr, outPtr, index₁, addr_add (by omega)]
    exact writable _ (by omega)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .edi + s₁.gpr .ecx - 1)) 1 := by
    rw [loAddr]; exact read₁ _ (by omega)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .edi + (s₁.gpr .ecx - s₁.gpr .esi))) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega)
  apply WP.mono (fillKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((fill key j).getD (key.length + j - 1) 0 + (fill key j).getD j 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (addr32 (s.gpr .edi) + BitVec.ofNat 64 (key.length + j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega), prefix₁ _ (by omega), outPtr, index₁, addr_add (by omega)] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (key.length + j) (by omega) b keep₂, ?_⟩
    · rw [h₂.1, index₁, counter_add, Nat.add_assoc]
    · rw [keep₂.mem, fill_succ]
      have h := prefix₁.extend (show key.length + j < 128 by omega) b
      simpa only [fillStep, Nat.add_sub_cancel_left, Nat.add_assoc] using h
  · rw [h₂.2.1, index₁, counter_add]
    have he : key.length + j + 1 = 128 ↔ j + 1 = 128 - key.length := by omega
    change some ((BitVec.ofNat 32 (key.length + j + 1) - BitVec.ofNat 32 128) == 0#32) = _
    rw [counter_eq _ _ (by omega) (by decide)]
    simp only [he]

end VG.Proof.Rc2.X86

end

section

/-! # The key-copy loop -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem copyLoop_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (keyFit : (s.gpr .ebp).toNat + t ≤ 2 ^ 32)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 t) (zero : s.gpr .ecx = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (addr32 (s.gpr .ebp)) t).Disjoint ⟨addr32 (s.gpr .edi), 128⟩) :
    WP isa (.loop (.block copyKey) .ne) s (fun s' =>
      s'.gpr .ecx = BitVec.ofNat 32 t ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill (Spec.Rc2.bytesAt s.mem (addr32 (s.gpr .ebp)) t) 0) t) := by
  let key := Spec.Rc2.bytesAt s.mem (addr32 (s.gpr .ebp)) t
  let I (i : Nat) (s' : State) := s'.gpr .ecx = BitVec.ofNat 32 i ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill key 0) i
  apply forwardLoop (.block copyKey) I t _ 0 (by omega) s
    ⟨zero, KeyFrame.refl s, fun i hi => by omega⟩
  intro i hi s₁ ⟨index₁, frame₁, prefix₁⟩
  have keyPtr := frame₁.reg .ebp (by decide)
  have outPtr := frame₁.reg .edi (by decide)
  have len₁ := (frame₁.reg .esi (by decide)).trans len
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .ebp + s₁.gpr .ecx)) 1 := by
    rw [frame₁.rd, frame₁.wr, keyPtr, index₁, addr_add (by omega)]
    exact readable i hi
  have write₁ : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [frame₁.wr, outPtr, index₁, addr_add (by omega)]
    exact writable i (by omega)
  have byte₁ : s₁.mem (addr32 (s₁.gpr .ebp + s₁.gpr .ecx)) = key.getD i 0 := by
    rw [keyPtr, index₁, addr_add (by omega), bytesAt_getD _ _ _ _ hi]
    exact frame₁.mem.bytes (by simpa using sep) (by change t ≤ 2 ^ 64; omega) hi
  obtain ⟨s₂, run₂, index₂, flag₂, keep₂⟩ := copyKey_ok s₁ read₁ write₁
  have keep₂' : Keep keyTemps
      {s₁ with mem := s₁.mem.writeW (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) (key.getD i 0)} s₂ := by
    rw [byte₁] at keep₂
    simpa only [outPtr, index₁, addr_add (by omega : (s.gpr .edi).toNat + i < 2 ^ 32)] using keep₂
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · refine ⟨?_, frame₁.step i (by omega) _ keep₂', ?_⟩
    · rw [index₂, index₁, counter_add]
    · rw [keep₂'.mem]
      have prefix₂ := prefix₁.extend (show i < 128 by omega) (key.getD i 0)
      rw [initial_set key i] at prefix₂
      exact prefix₂
  · rw [flag₂, index₁, len₁, counter_add]
    exact congrArg some (counter_eq (i + 1) t (by omega) (by omega))

end VG.Proof.Rc2.X86

end

/-! # Key-expansion control and register setup -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

theorem cmp128_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .ecx (.imm 128)] s = some s' ∧
      zeroFlag s' = some ((s.gpr .ecx - 128) == 0) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · rfl
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem maybeFill_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length ≤ 128)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 key.length) (start : s.gpr .ecx = BitVec.ofNat 32 key.length)
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (addr32 (s.gpr .edi)) (fill key 0) key.length) :
    WP isa (.seq (.block [.alu .cmp .ecx (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block []))) s (fun s' =>
        s'.gpr .ecx = 128 ∧ KeyFrame s s' ∧
        BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill key (128 - key.length)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmp128_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (key.length = 128)) := by
    rw [flag₁, start]
    exact congrArg some (counter_eq _ _ (by omega) (by decide))
  have ptr₁ := keep₁.reg .edi (by simp)
  by_cases he : key.length = 128
  · apply WP.ite false (by simp only [eval_nonzero, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨?_, frame₁, ?_⟩
      · rw [keep₁.reg .ecx (by simp), start, he]; rfl
      · rw [keep₁.mem]
        simpa only [he, Nat.sub_self] using initialPrefix
  · apply WP.ite true (by simp only [eval_nonzero, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (addr32 (s₁.gpr .edi)) (fill key 0) key.length := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (fillLoop_ok s₁ key ht (by omega) (by rw [ptr₁]; exact outFit)
        ((keep₁.reg .esi (by simp)).trans len) ((keep₁.reg .ecx (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨h₂.1, frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

theorem setReduction_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .esp + 12)) 4)
    (input : s.mem.readW (addr32 (s.gpr .esp + 12)) 32 = BitVec.ofNat 32 bits) :
    ∃ s', runBlock isa reduceSetup s = some s' ∧
      s'.gpr .esi = BitVec.ofNat 32 ((bits + 7) / 8) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (128 - (bits + 7) / 8) ∧ Keep [.esi, .ecx] s s' := by
  simp only [addr32, BitVec.ofNat_eq_ofNat] at *
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, reduceSetup, imm, memOp, State.ea, BitVec.ofNat_eq_ofNat, runBlock_cons,
      runStep_some, exec, execAlu, execShift, readSrc, State.load32, Option.bind_some,
      Option.map_some, gpr_setReg, readable]
    rfl, ?_⟩
  have t8 : (s.mem.readW (addr32 (s.gpr .esp + 12)) 32 + 7#32) >>> 3 = BitVec.ofNat 32 ((bits + 7) / 8) := by
    change (s.mem.readW (BitVec.setWidth 64 (s.gpr .esp + 12#32)) 32 + 7#32) >>> 3 = _
    rw [input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    exact t8
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    change 128#32 - (s.mem.readW (addr32 (s.gpr .esp + 12)) 32 + 7#32) >>> 3 = _
    rw [t8]
    exact Offset.ofNat_sub_ofNat (by omega)
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem maybeDescend_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 ≤ 128)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 t8) (start : s.gpr .ecx = BitVec.ofNat 32 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (addr32 (s.gpr .edi)) l 128) :
    WP isa (.seq (.block [.alu .cmp .ecx (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block []))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (addr32 (s.gpr .edi)) (descend l t8 (128 - t8)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpZero_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (t8 = 128)) := by
    rw [flag₁, start]
    have eqZero := counter_eq (128 - t8) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 32 (128 - t8) == 0#32) = _
    rw [eqZero]
    have he : 128 - t8 = 0 ↔ t8 = 128 := by omega
    simp only [he]
  have ptr₁ := keep₁.reg .edi (by simp)
  by_cases he : t8 = 128
  · apply WP.ite false (by simp only [eval_nonzero, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨frame₁, ?_⟩
      rw [keep₁.mem, he]
      exact initialPrefix
  · apply WP.ite true (by simp only [eval_nonzero, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (addr32 (s₁.gpr .edi)) l 128 := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (descendLoop_ok s₁ l t8 ht (by omega) (by rw [ptr₁]; exact outFit)
        ((keep₁.reg .esi (by simp)).trans len) ((keep₁.reg .ecx (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

end VG.Proof.Rc2.X86

end

section

/-! # Composing the RC2 key-expansion stages -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def coreRegs : List Reg := [.esp, .edi]

structure CoreFrame (s₀ s : State) : Prop where
  reg : ∀ r ∈ coreRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨addr32 (s₀.gpr .edi), 128⟩] s₀.mem s.mem

theorem CoreFrame.of_keep {s s' : State} {rs : List Reg} (keep : Keep rs s s')
    (sep : ∀ r ∈ coreRegs, r ∉ rs) : CoreFrame s s' := by
  refine ⟨fun r hr => keep.reg r (sep r hr), keep.rd, keep.wr, ?_⟩
  rw [keep.mem]; exact Frame.refl _ _

theorem CoreFrame.of_key {s s' : State} (h : KeyFrame s s') : CoreFrame s s' := by
  have sep : ∀ r ∈ coreRegs, r ∉ keyTemps := by decide
  exact ⟨fun r hr => h.reg r (sep r hr), h.rd, h.wr, h.mem⟩

theorem CoreFrame.trans {s₀ s₁ s₂ : State} (h₁ : CoreFrame s₀ s₁) (h₂ : CoreFrame s₁ s₂) :
    CoreFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .edi (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem expandCopyFill_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (keyFit : (s.gpr .ebp).toNat + t ≤ 2 ^ 32)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 t) (zero : s.gpr .ecx = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (addr32 (s.gpr .ebp)) t).Disjoint ⟨addr32 (s.gpr .edi), 128⟩) :
    WP isa expandCopyFill s (fun s' => KeyFrame s s' ∧
      BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill (Spec.Rc2.bytesAt s.mem (addr32 (s.gpr .ebp)) t) (128 - t)) 128) := by
  rw [expandCopyFill]
  apply WP.seq
  apply WP.mono (copyLoop_ok s t ht ht' keyFit outFit len zero readable writable sep)
  intro s₁ h₁
  have length : (Spec.Rc2.bytesAt s.mem (addr32 (s.gpr .ebp)) t).length = t := by
    simp [Spec.Rc2.bytesAt]
  have ptr₁ := h₁.2.1.reg .edi (by decide)
  have writes : ∀ i < 128, InRegions s₁.wr (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    rw [h₁.2.1.wr, ptr₁]; exact writable
  apply WP.mono (maybeFill_ok s₁ (Spec.Rc2.bytesAt s.mem (addr32 (s.gpr .ebp)) t)
    (by rw [length]; exact ht) (by rw [length]; exact ht') (by rw [ptr₁]; exact outFit)
    (by rw [length]; exact (h₁.2.1.reg .esi (by decide)).trans len)
    (by rw [length]; exact h₁.1) writes (by rw [ptr₁, length]; exact h₁.2.2))
  intro s₂ h₂
  exact ⟨h₁.2.1.trans h₂.2.1, by rw [length, ptr₁] at h₂; exact h₂.2.2⟩

theorem reduceDescend_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 ((bits + 7) / 8))
    (index : s.gpr .ecx = BitVec.ofNat 32 (128 - (bits + 7) / 8))
    (mask : (s.gpr .ebx).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))))
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (addr32 (s.gpr .edi)) l 128) :
    WP isa (.seq (.block reduceKey) (.seq (.block [.alu .cmp .ecx (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block [])))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (addr32 (s.gpr .edi))
          (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  have bound : 1 ≤ (bits + 7) / 8 ∧ (bits + 7) / 8 ≤ 128 := by omega
  have writes : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1 := by
    rw [index, addr_add (by omega)]; exact writable _ (by omega)
  have reads : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx)) 1 := by
    obtain ⟨r, hr, hc⟩ := writes
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  apply WP.mono (reduceKey_ok s reads writes)
  intro s₁ h₁
  have keep₁ := h₁.2
  rw [index, addr_add (by omega), initialPrefix _ (by omega), mask] at keep₁
  have frame₁ := (KeyFrame.refl s).step _ (by omega) _ keep₁
  have ptr₁ := keep₁.reg .edi (by decide)
  have prefix₁ : BytesPrefix s₁.mem (addr32 (s.gpr .edi)) (reduce l bits) 128 := by
    rw [keep₁.mem]
    exact initialPrefix.write (by decide) (by omega) _
  have write₁ : ∀ i < 128, InRegions s₁.wr (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.wr, ptr₁]; exact writable
  apply WP.mono (maybeDescend_ok s₁ (reduce l bits) ((bits + 7) / 8) bound.1 bound.2 (by rw [ptr₁]; exact outFit)
    ((keep₁.reg .esi (by decide)).trans len) (h₁.1.trans index) write₁
    (by rw [ptr₁]; exact prefix₁))
  intro s₂ h₂
  exact ⟨frame₁.trans h₂.1, by rw [ptr₁] at h₂; exact h₂.2⟩

theorem expandReduce_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .esp + 12)) 4)
    (input : s.mem.readW (addr32 (s.gpr .esp + 12)) 32 = BitVec.ofNat 32 bits)
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (addr32 (s.gpr .edi)) l 128) :
    WP isa expandReduce s (fun s' => CoreFrame s s' ∧ BytesPrefix s'.mem (addr32 (s.gpr .edi))
      (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  rw [expandReduce]
  apply WP.seq
  obtain ⟨s₁, run₁, len₁, index₁, keep₁⟩ := setReduction_ok s bits hb hb' readable input
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  have stack₁ := keep₁.reg .esp (by decide)
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .esp + 12)) 4 := by
    rw [keep₁.rd, keep₁.wr, stack₁]; exact readable
  have input₁ : s₁.mem.readW (addr32 (s₁.gpr .esp + 12)) 32 = BitVec.ofNat 32 bits := by
    rw [keep₁.mem, stack₁]; exact input
  apply WP.mono (maskCode_ok s₁ bits hb hb' read₁ input₁)
  intro s₂ h₂
  have frame := (CoreFrame.of_keep keep₁ (by decide)).trans (CoreFrame.of_keep h₂.2 (by decide))
  have ptr₂ := frame.reg .edi (by decide)
  have writes : ∀ i < 128, InRegions s₂.wr (addr32 (s₂.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    rw [frame.wr, ptr₂]; exact writable
  apply WP.mono (reduceDescend_ok s₂ l bits hb hb' (by rw [ptr₂]; exact outFit)
    ((h₂.2.reg .esi (by decide)).trans len₁) ((h₂.2.reg .ecx (by decide)).trans index₁) h₂.1 writes
    (by rw [ptr₂, h₂.2.mem, keep₁.mem]; exact initialPrefix))
  intro s₃ h₃
  exact ⟨frame.trans (CoreFrame.of_key h₃.1), by rw [ptr₂] at h₃; exact h₃.2⟩

end VG.Proof.Rc2.X86

end

/-! # Stack arguments and callee saves for RC2 key expansion -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

def savedReg (i : Nat) : Reg := saved.getD i .eax

theorem keySave_eq : save = saveCode .eax savedReg 4 := rfl

theorem keyRestore_eq : restore = restoreCode .eax savedReg (List.range 4) := rfl

theorem argAddr_eq (s : State) (i : Nat) (fit : (s.gpr .esp).toNat + 4 + 4 * i < 2 ^ 32) :
    argAddr s i = addr32 (s.gpr .esp) + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_add (by omega)

theorem argContains (s : State) (fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32)
    (i : Nat) (hi : i < 5) :
    (Region.mk (argAddr s 0) 20).Contains
      (addr32 (s.gpr .esp) + BitVec.ofNat 64 (4 + 4 * i)) 4 := by
  rw [argAddr_eq s 0 (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by decide)

theorem args_frame {s s' : State} {rs : List Region}
    (frame : Frame rs s.mem s'.mem) (sp : s'.gpr .esp = s.gpr .esp)
    (fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32)
    (sep : ∀ r ∈ rs, (Region.mk (argAddr s 0) 20).Disjoint r) :
    ∀ i < 5, arg s' i = arg s i := by
  intro i hi
  unfold arg
  have e : argAddr s' i = argAddr s i := by unfold argAddr; rw [sp]
  rw [e, argAddr_eq s i (by omega)]
  exact frame.readW (argContains s fit i hi) sep (by decide)

theorem loadArg_ok (s : State) (r : Reg) (i : Nat)
    (readable : InRegions (s.rd ++ s.wr) (argAddr s i) 4) :
    ∃ s', runBlock isa [.mov r (.mem (memOp .esp (4 + 4 * i)))] s = some s' ∧
      s'.gpr r = arg s i ∧ Keep [r] s s' := by
  simp only [argAddr] at readable
  refine ⟨s.setReg r (arg s i), ?_, gpr_setReg_self _ _ _, ?_⟩
  · simp only [runBlock_cons, exec, readSrc, State.ea, memOp, State.load32,
      readable, ite_true, Option.map_some, runStep_some, runBlock_nil]
    rfl
  · exact ⟨fun _ hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem arg_keep {s s' : State} {rs : List Reg} (keep : Keep rs s s')
    (hsp : .esp ∉ rs) (i : Nat) : arg s' i = arg s i := by
  unfold arg argAddr
  rw [keep.mem, keep.reg .esp hsp]

theorem pinKey_ok (s : State)
    (readable : ∀ i < 5, InRegions (s.rd ++ s.wr) (argAddr s i) 4) :
    WP isa (.block [.mov .ebp (.mem (memOp .esp 4)), .mov .esi (.mem (memOp .esp 8)),
      .mov .edi (.mem (memOp .esp 16)), imm .ecx 0]) s (fun s' =>
      s'.gpr .ebp = arg s 0 ∧ s'.gpr .esi = arg s 1 ∧ s'.gpr .edi = arg s 3 ∧
      s'.gpr .ecx = 0 ∧ Keep [.ebp, .esi, .edi, .ecx] s s') := by
  have r0 := readable 0 (by decide)
  have r1 := readable 1 (by decide)
  have r3 := readable 3 (by decide)
  simp only [argAddr, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at r0 r1 r3
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, exec, imm, memOp, State.ea,
      readSrc, State.load32, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      r0, r1, r3, Option.map_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Key`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.KeyCorrect`. -/
section

/-! # Verified RC2 key expansion -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), (arg s 1).toNat⟩
    let out : Region := ⟨addr32 (arg s 3), 128⟩
    let scratch : Region := ⟨addr32 (arg s 4), 512⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    s.rd = [key, args] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint out ∧
      (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint scratch ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 128 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      Spec.Rc2.validKey (arg s 1).toNat (arg s 2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (addr32 (arg s 3)) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat) (arg s 2).toNat
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => abiPreserved s s' ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, argsOut, argsScratch, retOut, retScratch, keyFit, outFit, scratchFit, spFit, ht, ht', hb, hb'⟩ := hs
  have writes : ∀ i < 4, InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have argRead (st : State) (rd : st.rd = s.rd) (wr : st.wr = s.wr)
      (sp : st.gpr .esp = s.gpr .esp) : ∀ i < 5, InRegions (st.rd ++ st.wr) (argAddr st i) 4 := by
    intro i hi
    have fit : (st.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by rw [sp]; exact spFit
    rw [argAddr_eq st i (by omega), sp, rd, wr, hrd, hwr]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i hi⟩
  rw [expandKey]
  apply WP.seq
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadArg_ok s .eax 4 (argRead s rfl rfl rfl 4 (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have gpr₀ (r : Reg) (hr : r ≠ .eax) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (saveCode_ok s₀ .eax savedReg 4 (by decide)
    (by rw [scratch₀]; omega) (by rw [keep₀.wr, scratch₀]; exact writes))
  intro s₁ h₁
  have sp₁ : s₁.gpr .esp = s.gpr .esp := by rw [h₁.1]; exact gpr₀ .esp (by decide)
  have savedFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2, keep₀.mem, scratch₀]
    apply (saveMem_frame_le _ _ _ 4 64 (by decide) (by decide)).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨addr32 (arg s 4), 512⟩, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have args₁ : ∀ i < 5, arg s₁ i = arg s i :=
    args_frame savedFrame sp₁ spFit (by simpa using argsScratch)
  apply WP.mono (pinKey_ok s₁ (argRead s₁ (h₁.2.1.trans keep₀.rd) (h₁.2.2.1.trans keep₀.wr) sp₁))
  intro s₂ ⟨key₂, len₂, ptr₂, zero₂, keep₂⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at len₂
  rw [args₁ 3 (by decide)] at ptr₂
  have scratchFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem]; exact savedFrame
  have sp₂ : s₂.gpr .esp = s.gpr .esp := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (addr32 (s₂.gpr .ebp)) (arg s 1).toNat =
      Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat := by
    rw [key₂]
    exact VG.Proof.Rc2.X86.bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega)
  have read₂ : ∀ i < (arg s 1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨addr32 (arg s 0), (arg s 1).toNat⟩, by simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (addr32 (s₂.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨addr32 (arg s 3), 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ (arg s 1).toNat ht ht' (by rw [key₂]; exact keyFit) (by rw [ptr₂]; exact outFit)
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (addr32 (s₃.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .edi (by decide)]; exact write₂
  have sp₃ : s₃.gpr .esp = s.gpr .esp := (h₃.1.reg .esp (by decide)).trans sp₂
  have argFrame₃ : Frame [⟨addr32 (arg s 4), 512⟩, ⟨addr32 (arg s 3), 128⟩] s.mem s₃.mem := by
    have outFrame₃ := h₃.1.mem
    rw [ptr₂] at outFrame₃
    exact (scratchFrame.mono (by simp)).trans (outFrame₃.mono (by simp))
  have args₃ := args_frame argFrame₃ sp₃ spFit (by simpa using And.intro argsScratch argsOut)
  apply WP.mono (expandReduce_ok s₃ _ (arg s 2).toNat hb hb'
    (by rw [h₃.1.reg .edi (by decide), ptr₂]; exact outFit)
    (argRead s₃ (h₃.1.rd.trans rd₂) (h₃.1.wr.trans wr₂) sp₃ 2 (by decide))
    (by simpa only [arg, argAddr, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_toNat, BitVec.setWidth_eq, addr32, BitVec.ofNat_eq_ofNat] using args₃ 2 (by decide))
    write₃ (by rw [h₃.1.reg .edi (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨addr32 (arg s 3), 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have sp₄ : s₄.gpr .esp = s.gpr .esp := (core.reg .esp (by decide)).trans sp₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (addr32 (arg s 3))
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat) (arg s 2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .edi (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat).length = (arg s 1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  rw [WP.block_append_iff]
  have frame₄ : Frame [⟨addr32 (arg s 4), 512⟩, ⟨addr32 (arg s 3), 128⟩] s.mem s₄.mem :=
    (scratchFrame.mono (by simp)).trans (outFrame.mono (by simp))
  have args₄ := args_frame frame₄ sp₄ spFit (by simpa using And.intro argsScratch argsOut)
  obtain ⟨s₅, run₅, base₅, keep₅⟩ := loadArg_ok s₄ .eax 4 (argRead s₄ rd₄ wr₄ sp₄ 4 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [args₄ 4 (by decide)] at base₅
  have rd₅ := keep₅.rd.trans rd₄
  have wr₅ := keep₅.wr.trans wr₄
  have scratchRead : ∀ i ∈ List.range 4,
      InRegions (s₅.rd ++ s₅.wr) (addr32 (s₅.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [rd₅, wr₅, base₅, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have stored : ∀ i ∈ List.range 4,
      s₅.mem.readW (addr32 (s₅.gpr .eax) + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [keep₅.mem, base₅, outFrame.readW (r := ⟨addr32 (arg s 4), 512⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀]
    rw [saveMem_read _ _ _ 4 (by decide) i bound]
    exact gpr₀ _ (by
      have sep : ∀ i ∈ List.range 4, savedReg i ≠ .eax := by decide
      exact sep i hi)
  rw [keyRestore_eq]
  apply WP.mono (restoreCode_ok s₅ .eax savedReg (List.range 4) s.gpr (by rw [base₅]; omega)
    (by decide) (by decide) scratchRead stored)
  intro s₆ h₆
  constructor
  · constructor
    · intro r hr
      by_cases he : r = .esp
      · subst r
        exact (h₆.2.reg .esp (by decide)).trans ((keep₅.reg .esp (by decide)).trans sp₄)
      · exact h₆.1 r (by
          have covered : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ (List.range 4).map savedReg := by decide
          exact covered r hr he)
    · rw [h₆.2.mem, keep₅.mem]
      exact frame₄.readW (Region.contains_self _ _) (by simpa [addr32] using And.intro retScratch retOut) (by decide)
  · change Spec.Rc2.scheduleAt s₆.mem (addr32 (arg s 3)) = _
    rw [h₆.2.mem, keep₅.mem]
    exact scheduleAt_expanded expanded


end VG.Proof.Rc2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.KeyLit`. -/
section

namespace VG.Impl.Rc2.X86

open VG.X86

/-- `piStep`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piStepLit (i : Nat) : List Instr :=
  selectMask i ++
    ([.alu .and .edx (.imm ((BitVec.ofNat 8 (VG.Rc2.piNat i)).setWidth 32)),
      .alu .or .ebx (.reg .edx)] : List Instr)

/-- `piLookup`, reading PITABLE from its packed table. -/
def piLookupLit : List Instr :=
  ([.alu .and .eax (.imm 255), imm .ebx 0] : List Instr) ++
    (List.range 256).flatMap VG.Impl.Rc2.X86.piStepLit ++ ([rr .eax .ebx] : List Instr)

materialize_value VG.Impl.Rc2.X86.piLookupLit

/-- The literal of `piLookup`, evaluated through the packed PITABLE. -/
noncomputable abbrev piLookup.lit : List Instr := piLookupLit.lit

theorem piLookup.lit_eq : piLookup = piLookup.lit := by
  have : piStep = VG.Impl.Rc2.X86.piStepLit := by
    funext i; simp only [piStep, VG.Impl.Rc2.X86.piStepLit, VG.Rc2.piTable_getD]
  refine Eq.trans ?_ piLookupLit.lit_eq
  simp only [piLookup, VG.Impl.Rc2.X86.piLookupLit, this]

materialize_code expandKey

end VG.Impl.Rc2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Key`. -/
section

/-! # RC2 key expansion against the shared API contract -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def keyTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 24 }

theorem keyTaint_wf {s : State} (h : keyContract.pre s) : VG.X86.Taint.Wf VG.Proof.Rc2.X86.keyTaint s := by
  obtain ⟨_, wr, _, _, _, ao, asc, ro, rsc, _, _, _, spfit, _⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [VG.Proof.Rc2.X86.keyTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (n := 20) (by omega) ro ao
  · exact Taint.frame_disjoint (n := 20) (by omega) rsc asc

theorem keyTaint_agree {s₁ s₂ : State} (h₁ : keyContract.pre s₁) (h₂ : keyContract.pre s₂)
    (hp : keyContract.pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.Rc2.X86.keyTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, keyContract.pre s → (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    VG.Proof.Rc2.X86.keyTaint_wf h₁, VG.Proof.Rc2.X86.keyTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Rc2.X86.keyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [VG.Proof.Rc2.X86.keyTaint] at hk
    rw [show Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem expandKey_constantTime : ConstantTime isa keyContract.pre keyContract.pub expandKey := by
  exact VG.Taint.constantTime (A := taint) VG.Proof.Rc2.X86.keyTaint (fun _ _ h₁ h₂ hp => VG.Proof.Rc2.X86.keyTaint_agree h₁ h₂ hp)
    (by taint_decide)

def keySatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4008 then 1 else
    if a = 0x400c then 8 else if a = 0x4011 then 0x20 else if a = 0x4015 then 0x30 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x4004, 20⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

theorem key_verified : Verified target expandKey (Spec.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct VG.Proof.Rc2.X86.key_body_correct VG.Proof.Rc2.X86.expandKey_constantTime ?_
  sig_implies [Spec.Rc2.expandKeyContract, Spec.Rc2.expandKeySig, abi, argSlots, argVal,
    argBytes, addr32, VG.Proof.Rc2.X86.keyContract, Spec.Rc2.validKey]
    [keySatState, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86.keySatState

end VG.Proof.Rc2.X86

end

end
