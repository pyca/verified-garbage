import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Impl.Argon2.X86_64.CountCandidates
import VerifiedGarbage.Impl.Argon2.X86_64.Divide
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.Argon2.X86_64.AddressCache
import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.CompressImpl
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite
import VerifiedGarbage.Impl.Argon2.X86_64.FillCompress
import VerifiedGarbage.Impl.Argon2.X86_64.AddressCalls
import VerifiedGarbage.Impl.Argon2.X86_64.AddressHeader
import VerifiedGarbage.Proof.Argon2.AddressInput
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.BlockAddress
import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Impl.Argon2.X86_64.ClearBlock
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Impl.Argon2.X86_64.FillKernel
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceCount
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Argon2.X86_64.SelectWindow
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap
import VerifiedGarbage.Impl.Argon2.X86_64.FillColumn
import VerifiedGarbage.Impl.Argon2.X86_64.FillPointers
import VerifiedGarbage.Impl.Argon2.X86_64.Wrap
import VerifiedGarbage.Impl.Argon2.X86_64.Relative
import VerifiedGarbage.Impl.Argon2.X86_64.FirstLane
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceLane
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Impl.Argon2.X86_64.DependentWord
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Argon2.X86_64.Derive
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Impl.Argon2.X86_64.ReduceBlock
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.Initial
import VerifiedGarbage.Impl.Argon2.X86_64.Parameters
import VerifiedGarbage.Impl.Argon2.X86_64.FillBlock
import VerifiedGarbage.Impl.Argon2.X86_64.RandomSource
import VerifiedGarbage.Impl.Argon2.X86_64.AddressMode
import VerifiedGarbage.Impl.Argon2.X86_64.FillSegment
import VerifiedGarbage.Impl.Argon2.X86_64.ReduceLane
import VerifiedGarbage.Impl.Argon2.X86_64.ReducePointers

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DivideStep`. -/
section

/-! # One bit of Argon2's fixed-time index division -/

namespace VG.Proof.Argon2.X86_64.Divide

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Divide

/-- All state except the listed registers and arithmetic flags is unchanged. -/
structure Keeps (rs : List Reg) (s t : State) : Prop where
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem Keeps.mono {rs rs' : List Reg} {s t : State} (h : VG.Proof.Argon2.X86_64.Divide.Keeps rs s t)
    (hh : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Argon2.X86_64.Divide.Keeps rs' s t :=
  ⟨fun r hr => h.regs r (fun hm => hr (hh r hm)), h.mem, h.rd, h.wr, h.mxcsr⟩

theorem Keeps.trans {rs : List Reg} {s t u : State} (h : VG.Proof.Argon2.X86_64.Divide.Keeps rs s t)
    (k : VG.Proof.Argon2.X86_64.Divide.Keeps rs t u) : VG.Proof.Argon2.X86_64.Divide.Keeps rs s u :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.mxcsr.trans h.mxcsr⟩

def mask (b : Bool) : BitVec 64 := if b then -1 else 0

theorem sbb_mask (x : BitVec 64) (b : Bool) :
    x - x - (BitVec.ofBool b).setWidth 64 = VG.Proof.Argon2.X86_64.Divide.mask b := by
  rw [BitVec.sub_self]
  cases b <;> decide

theorem subtract_ok (s : State) (j : Nat) (hj : j < 32) :
    let v := s.gpr .r8 + s.gpr .r8 +
      (BitVec.ofBool ((s.gpr .rdi).getLsbD j)).setWidth 64
    WP isa (.block (subtract j)) s fun t =>
      t.gpr .r8 = v - s.gpr .rsi ∧ t.gpr .r10 = v ∧
      t.gpr .rax = VG.Proof.Argon2.X86_64.Divide.mask (decide (v.toNat < (s.gpr .rsi).toNat)) ∧
      VG.Proof.Argon2.X86_64.Divide.Keeps [.rcx, .r8, .r10, .rax] s t := by
  intro v
  apply WP.of_runBlock
  simp only [subtract, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    execShift, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags,
    RegUpd.cf_arithFlags, show 1 ≤ j + 1 ∧ j + 1 ≤ 63 by omega,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', Nat.add_sub_cancel, and_self, VG.Proof.Argon2.X86_64.Divide.sbb_mask]
  refine ⟨rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem select_value (b : Bool) (reduced original : BitVec 64) :
    reduced ^^^ ((original ^^^ reduced) &&& VG.Proof.Argon2.X86_64.Divide.mask b) =
      if b then original else reduced := by
  cases b
  · apply BitVec.eq_of_toNat_eq
    simp [VG.Proof.Argon2.X86_64.Divide.mask]
  · simp only [VG.Proof.Argon2.X86_64.Divide.mask, ite_true, show (-1 : BitVec 64) = BitVec.allOnes 64 from rfl,
      BitVec.and_allOnes]
    rw [BitVec.xor_comm original reduced, ← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor]

theorem select_ok (s : State) (b : Bool) (hm : s.gpr .rax = VG.Proof.Argon2.X86_64.Divide.mask b) :
    WP isa (.block VG.Impl.Argon2.X86_64.Divide.select) s fun t =>
      t.gpr .r8 = (if b then s.gpr .r10 else s.gpr .r8) ∧
      t.gpr .r9 = (s.gpr .r9 + s.gpr .r9) + (if b then 0 else 1) ∧
      VG.Proof.Argon2.X86_64.Divide.Keeps [.r10, .r8, .rax, .r9] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.Divide.select, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.bind_some,
    Option.some.injEq, exists_eq_left', hm, VG.Proof.Argon2.X86_64.Divide.select_value,
    show BitVec.signExtend 64 (1 : BitVec 32) = 1 from rfl]
  refine ⟨trivial, ?_, ?_⟩
  · cases b <;> rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    all_goals rfl

theorem double_bit (x : BitVec 64) (b : Bool) (hx : x.toNat < 2 ^ 32) :
    (x + x + (BitVec.ofBool b).setWidth 64).toNat = 2 * x.toNat + b.toNat := by
  have hsum : x.toNat + x.toNat < 2 ^ 64 := by omega
  cases b <;> simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
    Bool.toNat_false, Bool.toNat_true, Nat.zero_mod, Nat.one_mod,
    Nat.mod_eq_of_lt hsum, Nat.add_zero] <;> omega

theorem reduced_value (v d : BitVec 64) :
    (if v.toNat < d.toNat then v else v - d).toNat =
      if v.toNat < d.toNat then v.toNat else v.toNat - d.toNat := by
  split
  · rfl
  · next h =>
    rw [BitVec.toNat_sub]
    have hv := v.isLt
    have hd := d.isLt
    omega

theorem bit_ok (s : State) (j : Nat) (hj : j < 32)
    (hr : (s.gpr .r8).toNat < 2 ^ 32) (hq : (s.gpr .r9).toNat < 2 ^ 32) :
    let v := 2 * (s.gpr .r8).toNat + ((s.gpr .rdi).getLsbD j).toNat
    let d := (s.gpr .rsi).toNat
    WP isa (.block (VG.Impl.Argon2.X86_64.Divide.bit j)) s fun t =>
      (t.gpr .r8).toNat = (if v < d then v else v - d) ∧
      (t.gpr .r9).toNat = 2 * (s.gpr .r9).toNat + (if v < d then 0 else 1) ∧
      VG.Proof.Argon2.X86_64.Divide.Keeps [.rcx, .r8, .r10, .rax, .r9] s t := by
  intro v d
  rw [VG.Impl.Argon2.X86_64.Divide.bit, WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Divide.subtract_ok s j hj).mono ?_
  rintro u ⟨hu8, hu10, huax, hu⟩
  refine (VG.Proof.Argon2.X86_64.Divide.select_ok u _ huax).mono ?_
  rintro t ⟨ht8, ht9, ht⟩
  have hv := VG.Proof.Argon2.X86_64.Divide.double_bit (s.gpr .r8) ((s.gpr .rdi).getLsbD j) hr
  have hu9 := hu.regs .r9 (by decide)
  refine ⟨?_, ?_, (hu.mono (by decide)).trans (ht.mono (by decide))⟩
  · simp only [ht8, hu8, hu10, decide_eq_true_eq]
    rw [VG.Proof.Argon2.X86_64.Divide.reduced_value, hv]
  · simp only [ht9, hu9, hv, decide_eq_true_eq]
    change (s.gpr .r9 + s.gpr .r9 + (if v < d then 0 else 1)).toNat =
      2 * (s.gpr .r9).toNat + (if v < d then 0 else 1)
    by_cases h : v < d
    · simp only [h, ite_true]
      exact VG.Proof.Argon2.X86_64.Divide.double_bit (s.gpr .r9) false hq
    · simp only [h, ite_false]
      exact VG.Proof.Argon2.X86_64.Divide.double_bit (s.gpr .r9) true hq

end VG.Proof.Argon2.X86_64.Divide

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.CountCandidates`. -/
section

/-! # Candidate window arithmetic before selecting the reference lane -/

namespace VG.Proof.Argon2.X86_64.CountCandidates

open VG VG.X86_64 VG.Impl.Argon2.X86_64.CountCandidates

structure Candidates (s t : State) (base : Addr) : Prop where
  same : t.gpr .rdx = base + s.gpr .r15 - 1
  other : t.gpr .rcx = base
  keeps : Divide.Keeps [.rax, .rdx, .rcx] s t

theorem first_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.CountCandidates.first) s
    (VG.Proof.Argon2.X86_64.CountCandidates.Candidates s · (s.gpr .r13 * s.gpr .r14)) := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.CountCandidates.first, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    execMul, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem later_ok (s : State) : WP isa (.block later) s
    (VG.Proof.Argon2.X86_64.CountCandidates.Candidates s · (s.gpr .r12 - s.gpr .r13)) := by
  apply WP.of_runBlock
  simp only [later, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

structure Adjusted (s t : State) : Prop where
  count : t.gpr .rcx = s.gpr .rcx + Divide.mask (decide ((s.gpr .r15).toNat < 1))
  keeps : Divide.Keeps [.r8, .r9, .rcx] s t

theorem adjust_ok (s : State) : WP isa (.block adjust) s (VG.Proof.Argon2.X86_64.CountCandidates.Adjusted s) := by
  apply WP.of_runBlock
  simp only [adjust, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', Divide.sbb_mask,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show (1 : Addr).toNat = 1 from rfl]
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block [.alu .cmp .r9 (.imm 0)]) s
    fun t => t.zf = decide (s.gpr .r9 = 0) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    execAlu, RegUpd.zf_arithFlags,
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change (s.gpr .r9 - (0 : Addr) == (0 : Addr)) = decide (s.gpr .r9 = 0)
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change s.gpr .r9 - 0#64 = 0#64 ↔ s.gpr .r9 = 0#64
    rw [BitVec.sub_zero]
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

def base (s : State) : Addr :=
  if s.gpr .r9 = 0 then s.gpr .r13 * s.gpr .r14 else s.gpr .r12 - s.gpr .r13

def changed : List Reg := [.rax, .rdx, .rcx, .r8, .r9]

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.CountCandidates.code s fun t =>
    t.gpr .rdx = VG.Proof.Argon2.X86_64.CountCandidates.base s + s.gpr .r15 - 1 ∧
    t.gpr .rcx = VG.Proof.Argon2.X86_64.CountCandidates.base s + Divide.mask (decide ((s.gpr .r15).toNat < 1)) ∧
    Divide.Keeps VG.Proof.Argon2.X86_64.CountCandidates.changed s t := by
  unfold VG.Impl.Argon2.X86_64.CountCandidates.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  have branches : WP isa (.ite .e (.block VG.Impl.Argon2.X86_64.CountCandidates.first) (.block later)) a
      (VG.Proof.Argon2.X86_64.CountCandidates.Candidates s · (VG.Proof.Argon2.X86_64.CountCandidates.base s)) := by
    refine WP.ite (decide (s.gpr .r9 = 0)) (by simp only [eval, flag]) ?_ ?_
    · intro h
      have zero : s.gpr .r9 = 0 := of_decide_eq_true h
      refine (VG.Proof.Argon2.X86_64.CountCandidates.first_ok a).mono ?_
      intro b hb
      refine ⟨?_, ?_, keeps.mono (by simp) |>.trans hb.keeps⟩
      · simpa only [VG.Proof.Argon2.X86_64.CountCandidates.base, zero, ite_true, keeps.regs .r13 (by simp),
          keeps.regs .r14 (by simp), keeps.regs .r15 (by simp)] using hb.same
      · simpa only [VG.Proof.Argon2.X86_64.CountCandidates.base, zero, ite_true, keeps.regs .r13 (by simp),
          keeps.regs .r14 (by simp)] using hb.other
    · intro h
      have nonzero : s.gpr .r9 ≠ 0 := of_decide_eq_false h
      refine (VG.Proof.Argon2.X86_64.CountCandidates.later_ok a).mono ?_
      intro b hb
      refine ⟨?_, ?_, keeps.mono (by simp) |>.trans hb.keeps⟩
      · simpa only [VG.Proof.Argon2.X86_64.CountCandidates.base, nonzero, ite_false, keeps.regs .r12 (by simp),
          keeps.regs .r13 (by simp), keeps.regs .r15 (by simp)] using hb.same
      · simpa only [VG.Proof.Argon2.X86_64.CountCandidates.base, nonzero, ite_false, keeps.regs .r12 (by simp),
          keeps.regs .r13 (by simp)] using hb.other
  refine WP.seq (branches.mono ?_)
  intro b hb
  refine (VG.Proof.Argon2.X86_64.CountCandidates.adjust_ok b).mono ?_
  intro t ht
  refine ⟨?_, ?_, (hb.keeps.mono (by decide)).trans (ht.keeps.mono (by decide))⟩
  · exact (ht.keeps.regs .rdx (by decide)).trans hb.same
  · rw [ht.count, hb.other, hb.keeps.regs .r15 (by decide)]

end VG.Proof.Argon2.X86_64.CountCandidates

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart`. -/
section

/-! The reference window starts at the next slice on later passes. -/

namespace VG.Proof.Argon2.X86_64.ReferenceStart

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceStart

theorem sub_zero_iff (x y : Addr) : x - y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = (x - y) + y := (BitVec.sub_add_cancel x y).symm
      _ = y := by rw [h]; exact BitVec.zero_add y
  · intro h; rw [h, BitVec.sub_self]; rfl

theorem zero_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.ReferenceStart.zero) s fun t =>
    t.gpr .r10 = 0 ∧ Divide.Keeps [.r10] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.ReferenceStart.zero, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    RegUpd.gpr_setReg, Option.map_some, Option.some.injEq, exists_eq_left',
    ite_true, show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem advance_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.ReferenceStart.advance) s fun t =>
    t.gpr .r10 = (s.gpr .r14 + 1) * s.gpr .r13 ∧
    t.zf = decide (s.gpr .r14 = 3) ∧ Divide.Keeps [.rax, .rdx, .r10] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.ReferenceStart.advance, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    execAlu, execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (3 : BitVec 32) = (3 : Addr) from rfl]
  refine ⟨trivial, ?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, VG.Proof.Argon2.X86_64.ReferenceStart.sub_zero_iff]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
        hr.1, hr.2.1, hr.2.2, ite_false]
    all_goals rfl

def changed : List Reg := [.rax, .rdx, .r10]

def value (s : State) : Addr :=
  if s.gpr .r9 = 0 then 0 else
    if s.gpr .r14 = 3 then 0 else (s.gpr .r14 + 1) * s.gpr .r13

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.ReferenceStart.code s fun t =>
    t.gpr .r10 = VG.Proof.Argon2.X86_64.ReferenceStart.value s ∧ Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceStart.changed s t := by
  unfold VG.Impl.Argon2.X86_64.ReferenceStart.code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .r9 = 0)) (by simp only [eval, flag]) ?_ ?_
  · intro h
    have firstPass : s.gpr .r9 = 0 := of_decide_eq_true h
    refine (VG.Proof.Argon2.X86_64.ReferenceStart.zero_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by simp)).trans (tail.mono (by decide))⟩
    simpa only [VG.Proof.Argon2.X86_64.ReferenceStart.value, firstPass, ite_true] using out
  · intro h
    have laterPass : s.gpr .r9 ≠ 0 := of_decide_eq_false h
    refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceStart.advance_ok a).mono ?_)
    rintro b ⟨out, flag, advanceKeeps⟩
    have sliceReg := keeps.regs .r14 (by simp)
    have segmentReg := keeps.regs .r13 (by simp)
    refine WP.ite (decide (s.gpr .r14 = 3))
      (by simp only [eval, flag, sliceReg]) ?_ ?_
    · intro h
      have lastSlice : s.gpr .r14 = 3 := of_decide_eq_true h
      refine (VG.Proof.Argon2.X86_64.ReferenceStart.zero_ok b).mono ?_
      rintro t ⟨out, tail⟩
      refine ⟨?_, ((keeps.mono (by simp)).trans advanceKeeps).trans (tail.mono (by decide))⟩
      simpa only [VG.Proof.Argon2.X86_64.ReferenceStart.value, laterPass, lastSlice, ite_false, ite_true] using out
    · intro h
      have earlierSlice : s.gpr .r14 ≠ 3 := of_decide_eq_false h
      apply WP.of_runBlock
      simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
      refine ⟨?_, (keeps.mono (by simp)).trans advanceKeeps⟩
      simpa only [VG.Proof.Argon2.X86_64.ReferenceStart.value, laterPass, earlierSlice, ite_false, sliceReg, segmentReg] using out

theorem start_nat (p : Spec.Argon2.Params) (hl : 0 < p.lanes)
    (hg : 0 < p.segmentLen) (slice : Nat) (hs : slice < 4) :
    (slice + 1) * p.segmentLen % p.laneLen =
      if slice = 3 then 0 else (slice + 1) * p.segmentLen := by
  rw [Proof.Argon2.laneLen_segments p hl]
  by_cases lastSlice : slice = 3
  · simp only [lastSlice, ite_true, show (3 : Nat) + 1 = 4 from rfl, Nat.mod_self]
  · have smaller : (slice + 1) * p.segmentLen < 4 * p.segmentLen :=
      Nat.mul_lt_mul_of_pos_right (by omega) hg
    rw [Nat.mod_eq_of_lt smaller]
    simp only [lastSlice, ite_false]

theorem value_nat (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (hl : 0 < p.lanes) (hg : 0 < p.segmentLen) (hs : slice < 4)
    (passReg : (s.gpr .r9).toNat = pass)
    (sliceReg : s.gpr .r14 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen) :
    VG.Proof.Argon2.X86_64.ReferenceStart.value s = BitVec.ofNat 64
      (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) := by
  have isZero : s.gpr .r9 = 0 ↔ pass = 0 := by
    rw [← passReg]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  have isLast : s.gpr .r14 = 3 ↔ slice = 3 := by
    rw [sliceReg]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
      exact hn
    · intro h; rw [h]; rfl
  unfold VG.Proof.Argon2.X86_64.ReferenceStart.value
  simp only [isZero, isLast]
  by_cases firstPass : pass = 0
  · simp only [firstPass, ite_true]; rfl
  · simp only [firstPass, ite_false, VG.Proof.Argon2.X86_64.ReferenceStart.start_nat p hl hg slice hs]
    by_cases lastSlice : slice = 3
    · simp only [lastSlice, ite_true]; rfl
    · simp only [lastSlice, ite_false]
      rw [sliceReg, segmentReg]
      change (BitVec.ofNat 64 slice + BitVec.ofNat 64 1) *
        BitVec.ofNat 64 p.segmentLen = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (hl : 0 < p.lanes) (hg : 0 < p.segmentLen) (hs : slice < 4)
    (passReg : (s.gpr .r9).toNat = pass)
    (sliceReg : s.gpr .r14 = BitVec.ofNat 64 slice)
    (segmentReg : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen) :
    WP isa VG.Impl.Argon2.X86_64.ReferenceStart.code s fun t =>
      t.gpr .r10 = BitVec.ofNat 64
        (if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen) ∧
      Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceStart.changed s t :=
  (VG.Proof.Argon2.X86_64.ReferenceStart.code_ok s).mono (fun _ h =>
    ⟨h.1.trans (VG.Proof.Argon2.X86_64.ReferenceStart.value_nat s p pass slice hl hg hs passReg sliceReg segmentReg), h.2⟩)

end VG.Proof.Argon2.X86_64.ReferenceStart

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCall`. -/
section

/-! Invoke the verified compression primitive with narrowed permissions,
retaining the surrounding matrix and derivation frame. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64

structure CallReady (s : State) : Prop where
  left : Covers [⟨s.gpr .rdi, 1024⟩] (s.rd ++ s.wr)
  right : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .rdx, 1024⟩] s.wr
  scratch : Covers [⟨s.gpr .rcx, 4096⟩] s.wr
  leftScratch : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨s.gpr .rcx, 4096⟩
  rightScratch : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rcx, 4096⟩
  outputScratch : (⟨s.gpr .rdx, 1024⟩ : Region).Disjoint ⟨s.gpr .rcx, 4096⟩
  stackLeft : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdi, 1024⟩
  stackRight : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rsi, 1024⟩
  stackOutput : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdx, 1024⟩
  stackScratch : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rcx, 4096⟩

structure Called (s t : State) : Prop where
  result : Spec.Argon2.blockAt t.mem (s.gpr .rdx) = Spec.Argon2.compress
    (Spec.Argon2.blockAt s.mem (s.gpr .rdi)) (Spec.Argon2.blockAt s.mem (s.gpr .rsi))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩, below (s.gpr .rsp) 8] s.mem t.mem


theorem call_hyps (s : State) (h : VG.Proof.Argon2.X86_64.FillCompress.CallReady s) :
    compressLocal.pre (s.callEntry.withRegions [⟨s.gpr .rdi, 1024⟩, ⟨s.gpr .rsi, 1024⟩]
      [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩]) ∧
    Covers [⟨s.gpr .rdi, 1024⟩, ⟨s.gpr .rsi, 1024⟩,
      ⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s.wr := by
  have g : ∀ r, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun _ hr => State.callEntry_gpr s hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [compressLocal, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_rsp]
    exact ⟨trivial, trivial, h.outputScratch, h.leftScratch, h.rightScratch,
      h.stackOutput, h.stackScratch⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.left p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact h.right p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.scratch p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact h.scratch p n ⟨_, List.mem_singleton_self _, hc⟩

theorem callEntry_block (s : State) (p : Addr)
    (h : (below (s.gpr .rsp) 8).Disjoint ⟨p, 1024⟩) :
    Spec.Argon2.blockAt s.callEntry.mem p = Spec.Argon2.blockAt s.mem p := by
  have frame : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem]
    exact (Frame.refl _ _).writeW (r := below (s.gpr .rsp) 8) (by simp) _
      (below_call _ (by decide) (by decide))
  apply Vector.ext
  intro i hi
  have read := frame.readW (r := ⟨p, 1024⟩) (a := off p (8 * i)) (w := 64)
    (Offset.contains_base p (d := 8 * i) (n := 8) (k := 1024) (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.symm) (by decide)
  rw [← blockAt_get s.callEntry.mem p ⟨i, hi⟩, ← blockAt_get s.mem p ⟨i, hi⟩] at read
  exact read

theorem call_ok [CompressImpl] (s : State) (h : VG.Proof.Argon2.X86_64.FillCompress.CallReady s) :
    WP isa (.call Impl.Argon2.X86_64.Compressor.name Impl.Argon2.X86_64.Compressor.code) s
      (fun t => VG.Proof.Argon2.X86_64.FillCompress.Called s t ∧ ctl t.mxcsr = ctl s.mxcsr) := by
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.X86_64.FillCompress.call_hyps s h
  refine WP.call_mx (k := compressLocal) CompressImpl.correct CompressImpl.noSp
    (by rw [CompressImpl.depth]; decide) pre cover writes ?_
  intro t rd wr regs frame _ ⟨u, memU, regsU, result⟩ mx
  change Spec.Argon2.blockAt u.mem (s.callEntry.gpr .rdx) = Spec.Argon2.compress
    (Spec.Argon2.blockAt s.callEntry.mem (s.callEntry.gpr .rdi))
    (Spec.Argon2.blockAt s.callEntry.mem (s.callEntry.gpr .rsi)) at result
  rw [State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), memU,
    VG.Proof.Argon2.X86_64.FillCompress.callEntry_block s _ h.stackLeft, VG.Proof.Argon2.X86_64.FillCompress.callEntry_block s _ h.stackRight] at result
  rw [CompressImpl.depth] at frame
  exact ⟨⟨result, regs, rd, wr, frame⟩, mx⟩

end VG.Proof.Argon2.X86_64.FillCompress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillWritePrefix`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillWriteWord`. -/
section
/-! One output word, keeping register writes folded during execution. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillWrite

def value (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Nat) : Addr :=
  let next := m.readW (off src (8 * i)) 64
  if xorOld then next ^^^ m.readW (off dest (8 * i)) 64 else next

/-- The source is readable and the destination writable; its old contents
are read only on later passes. -/
theorem word_ok (xorOld : Bool) (s : State) (i : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rsi) (8 * i)) 8)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8)
    (ho : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.X86_64.FillWrite.word xorOld i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i))
        (VG.Proof.Argon2.X86_64.FillWrite.value xorOld s.mem (s.gpr .rsi) (s.gpr .rdi) i) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  cases xorOld <;> apply WP.of_runBlock <;>
    simp only [Impl.Argon2.X86_64.FillWrite.word, VG.Proof.Argon2.X86_64.FillWrite.value, Bool.false_eq_true, ite_false, ite_true,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
      State.load64, State.store64, execAlu, VG.Proof.Argon2.X86_64.ea_at, hr, hw, ho,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, reduceCtorEq, ite_true, ite_false,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨trivial, ?_, trivial, trivial, rfl⟩
    intro r hr
    simp only [hr, ite_false]

end VG.Proof.Argon2.X86_64.FillWrite
end

/-! Compose the word writes without re-executing a long load/store block. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillWrite

def result (xorOld : Bool) (m : Mem) (src dest : Addr) : Block :=
  if xorOld then xorBlock (blockAt m src) (blockAt m dest) else blockAt m src

theorem result_get (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Fin 128) :
    (VG.Proof.Argon2.X86_64.FillWrite.result xorOld m src dest)[i] = VG.Proof.Argon2.X86_64.FillWrite.value xorOld m src dest i.val := by
  cases xorOld <;> simp only [VG.Proof.Argon2.X86_64.FillWrite.result, VG.Proof.Argon2.X86_64.FillWrite.value, Bool.false_eq_true, ite_false, ite_true,
    xorBlock_get, blockAt_get]

theorem frame_extend {m m' : Mem} {dest : Addr} {n k : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (h : n ≤ k) : Frame [⟨dest, 8 * k⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨_, by simp, Region.sub_prefix (Nat.mul_le_mul_left 8 h)⟩

theorem source_read {m m' : Mem} {src dest : Addr} {n : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hn : n ≤ 128)
    (hd : (⟨src, 1024⟩ : Region).Disjoint ⟨dest, 1024⟩) (i : Fin 128) :
    m'.readW (off src (8 * i.val)) 64 = m.readW (off src (8 * i.val)) 64 := by
  have full := VG.Proof.Argon2.X86_64.FillWrite.frame_extend hf hn
  exact full.readW (r := ⟨src, 1024⟩)
    (Offset.contains_base src (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem old_read {m m' : Mem} {dest : Addr} {n : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hn : n < 128) :
    m'.readW (off dest (8 * n)) 64 = m.readW (off dest (8 * n)) 64 :=
  hf.readW (r := ⟨off dest (8 * n), 8⟩) (Region.contains_self _ _)
    (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint_base dest (Nat.le_refl _) (by omega)) (by decide)

theorem prefix_ok (xorOld : Bool) (n : Nat) (hn : n ≤ 128) (s : State)
    (hs : (⟨s.gpr .rsi, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .rdi, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa (.block (VG.Impl.Argon2.X86_64.FillWrite.words xorOld n)) s fun t =>
      Written t.mem (s.gpr .rdi) (VG.Proof.Argon2.X86_64.FillWrite.result xorOld s.mem (s.gpr .rsi) (s.gpr .rdi)) n ∧
      Frame [⟨s.gpr .rdi, 8 * n⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [VG.Impl.Argon2.X86_64.FillWrite.words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    have hn' : n < 128 := by omega
    have src : t.gpr .rsi = s.gpr .rsi := keeps.1 .rsi (by decide)
    have dest : t.gpr .rdi = s.gpr .rdi := keeps.1 .rdi (by decide)
    have write : InRegions t.wr (off (t.gpr .rdi) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    have read : InRegions (t.rd ++ t.wr) (off (t.gpr .rsi) (8 * n)) 8 := by
      rw [src, keeps.2.1, keeps.2.2]
      exact ⟨_, hs, Offset.contains_base _ (by omega) (by omega)⟩
    have old : InRegions (t.rd ++ t.wr) (off (t.gpr .rdi) (8 * n)) 8 := by
      obtain ⟨r, hr, hc⟩ := write
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine (VG.Proof.Argon2.X86_64.FillWrite.word_ok xorOld t n read write old).mono ?_
    rintro u ⟨mem, regs, rd, wr, mx'⟩
    have v : VG.Proof.Argon2.X86_64.FillWrite.value xorOld t.mem (t.gpr .rsi) (t.gpr .rdi) n =
        (VG.Proof.Argon2.X86_64.FillWrite.result xorOld s.mem (s.gpr .rsi) (s.gpr .rdi))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [VG.Proof.Argon2.X86_64.FillWrite.result_get, src, dest]
      unfold VG.Proof.Argon2.X86_64.FillWrite.value
      rw [VG.Proof.Argon2.X86_64.FillWrite.source_read frame (by omega) hd ⟨n, hn'⟩]
      cases xorOld
      · rfl
      · rw [VG.Proof.Argon2.X86_64.FillWrite.old_read frame hn']
    refine ⟨?_, ?_, keeps.trans ⟨regs, rd, wr⟩, mx'.trans mx⟩
    · rw [mem, v, dest]
      exact written_step hn' written
    · rw [mem, dest]
      exact (VG.Proof.Argon2.X86_64.FillWrite.frame_extend frame (Nat.le_succ n)).writeW
        (r := ⟨s.gpr .rdi, 8 * (n + 1)⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Argon2.X86_64.FillWrite

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillWriteCover`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillWrite`. -/
section
/-! Whole-block first-pass copying and later-pass XOR, with a frame proof. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillWrite

theorem code_ok (s : State)
    (hs : (⟨s.gpr .rsi, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .rdi, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa VG.Impl.Argon2.X86_64.FillWrite.code s fun t =>
      blockAt t.mem (s.gpr .rdi) =
        (if s.gpr .r9 = 0 then blockAt s.mem (s.gpr .rsi)
          else xorBlock (blockAt s.mem (s.gpr .rsi)) (blockAt s.mem (s.gpr .rdi))) ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  unfold VG.Impl.Argon2.X86_64.FillWrite.code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have src : a.gpr .rsi = s.gpr .rsi := ka.regs .rsi (by simp)
  have dest : a.gpr .rdi = s.gpr .rdi := ka.regs .rdi (by simp)
  have hs' : (⟨a.gpr .rsi, 1024⟩ : Region) ∈ a.rd ++ a.wr := by
    rw [src, ka.rd, ka.wr]; exact hs
  have hw' : (⟨a.gpr .rdi, 1024⟩ : Region) ∈ a.wr := by
    rw [dest, ka.wr]; exact hw
  have hd' : (⟨a.gpr .rsi, 1024⟩ : Region).Disjoint ⟨a.gpr .rdi, 1024⟩ := by
    rw [src, dest]; exact hd
  refine WP.ite (decide (s.gpr .r9 = 0)) (by simp only [eval, flag]) ?_ ?_
  · intro h
    have zero := of_decide_eq_true h
    refine (VG.Proof.Argon2.X86_64.FillWrite.prefix_ok false 128 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.mxcsr⟩
    · rw [dest] at written
      rw [ite_eq_left zero, written_block written]
      simp only [VG.Proof.Argon2.X86_64.FillWrite.result, Bool.false_eq_true, ite_false, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ => ka.regs r (by simp), ka.rd, ka.wr⟩).trans keeps
  · intro h
    have nonzero := of_decide_eq_false h
    refine (VG.Proof.Argon2.X86_64.FillWrite.prefix_ok true 128 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.mxcsr⟩
    · rw [dest] at written
      rw [ite_eq_right nonzero, written_block written]
      simp only [VG.Proof.Argon2.X86_64.FillWrite.result, ite_true, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ => ka.regs r (by simp), ka.rd, ka.wr⟩).trans keeps

end VG.Proof.Argon2.X86_64.FillWrite
end

/-! Use block writes in a matrix allocation with larger permission regions. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillWrite

theorem code_cover_ok (s : State)
    (hs : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (hd : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa VG.Impl.Argon2.X86_64.FillWrite.code s fun t =>
      blockAt t.mem (s.gpr .rdi) =
        (if s.gpr .r9 = 0 then blockAt s.mem (s.gpr .rsi)
          else xorBlock (blockAt s.mem (s.gpr .rsi)) (blockAt s.mem (s.gpr .rdi))) ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  let a := s.withRegions [⟨s.gpr .rsi, 1024⟩] [⟨s.gpr .rdi, 1024⟩]
  obtain ⟨tr, t, he, value, frame, keeps, mx⟩ := VG.Proof.Argon2.X86_64.FillWrite.code_ok a (by simp [a]) (by simp [a]) hd
  have cover : Covers (a.rd ++ a.wr) (s.rd ++ s.wr) := by
    intro p n ⟨r, hr, hc⟩
    change r ∈ [⟨s.gpr .rsi, 1024⟩, ⟨s.gpr .rdi, 1024⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs p n ⟨_, by simp, hc⟩
    · obtain ⟨r, hr, hc⟩ := hw p n ⟨_, by simp, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have he' := Exec.widen (rd := s.rd) (wr := s.wr) he cover hw
  simp only [a, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr, t.withRegions s.rd s.wr, he', value, frame, ?_, mx⟩
  exact ⟨keeps.1, rfl, rfl⟩

end VG.Proof.Argon2.X86_64.FillWrite

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillCompressOperation`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillCompressArgs`. -/
section
/-! Save the current cell across G and reload the block-write arguments. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

theorem saveCurrent_ok (s : State)
    (hw : InRegions s.wr (off (s.gpr .rbp) 16) 8) :
    WP isa (.block saveCurrent) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [saveCurrent, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, VG.Proof.Argon2.X86_64.ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem compressArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block compressArgs) s fun t =>
      t.gpr .rcx = s.mem.readW (off (s.gpr .rbp) 248) 64 ∧
      t.gpr .rdx = s.mem.readW (off (s.gpr .rbp) 248) 64 + 4096 ∧
      Divide.Keeps [.rcx, .rdx] s t := by
  apply WP.of_runBlock
  simp only [compressArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, VG.Proof.Argon2.X86_64.ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (4096 : BitVec 32) = (4096 : Addr) from rfl]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem writeArgs_ok (s : State)
    (destRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 16) 8)
    (workRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block writeArgs) s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 16) 64 ∧
      t.gpr .rsi = s.mem.readW (off (s.gpr .rbp) 248) 64 + 4096 ∧
      t.gpr .r9 = s.mem.readW (off (s.gpr .rbp) 0) 64 ∧
      Divide.Keeps [.rdi, .rsi, .r9] s t := by
  apply WP.of_runBlock
  simp only [writeArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, VG.Proof.Argon2.X86_64.ea_at, destRead, workRead, passRead, execAlu,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (4096 : BitVec 32) = (4096 : Addr) from rfl]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.FillCompress
end

/-! Compression followed by first/later-pass writing, preserving the frame
slots and the old destination cell across the compression call. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillCompress

def callWrites (s : State) : List Region :=
  [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩, below (s.gpr .rsp) 8]

def destination (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 16) 64

def pass (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 0) 64

structure OperationReady (s : State) : Prop where
  call : VG.Proof.Argon2.X86_64.FillCompress.CallReady s
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  workWord : s.mem.readW (off (s.gpr .rbp) 248) 64 = s.gpr .rcx
  outputPointer : s.gpr .rcx + 4096 = s.gpr .rdx
  destinationWrite : Covers [⟨VG.Proof.Argon2.X86_64.FillCompress.destination s, 1024⟩] s.wr
  frameSafe : ∀ r ∈ VG.Proof.Argon2.X86_64.FillCompress.callWrites s, (⟨s.gpr .rbp, 272⟩ : Region).Disjoint r
  destinationSafe : ∀ r ∈ VG.Proof.Argon2.X86_64.FillCompress.callWrites s, (⟨VG.Proof.Argon2.X86_64.FillCompress.destination s, 1024⟩ : Region).Disjoint r

structure OperationDone (s t : State) : Prop where
  block : blockAt t.mem (VG.Proof.Argon2.X86_64.FillCompress.destination s) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    if VG.Proof.Argon2.X86_64.FillCompress.pass s = 0 then next else xorBlock next (blockAt s.mem (VG.Proof.Argon2.X86_64.FillCompress.destination s))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (⟨VG.Proof.Argon2.X86_64.FillCompress.destination s, 1024⟩ :: VG.Proof.Argon2.X86_64.FillCompress.callWrites s) s.mem t.mem

theorem frame_word {s t : State} (h : VG.Proof.Argon2.X86_64.FillCompress.OperationReady s) (called : VG.Proof.Argon2.X86_64.FillCompress.Called s t)
    (d : Nat) (hd : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 :=
  called.frame.readW (r := ⟨s.gpr .rbp, 272⟩)
    (Offset.contains_base _ hd (by omega)) h.frameSafe (by decide)

theorem destination_unchanged {s t : State} (h : VG.Proof.Argon2.X86_64.FillCompress.OperationReady s) (called : VG.Proof.Argon2.X86_64.FillCompress.Called s t) :
    blockAt t.mem (VG.Proof.Argon2.X86_64.FillCompress.destination s) = blockAt s.mem (VG.Proof.Argon2.X86_64.FillCompress.destination s) := by
  apply Vector.ext
  intro i hi
  have read : t.mem.readW (off (VG.Proof.Argon2.X86_64.FillCompress.destination s) (8 * i)) 64 =
      s.mem.readW (off (VG.Proof.Argon2.X86_64.FillCompress.destination s) (8 * i)) 64 :=
    called.frame.readW (r := ⟨VG.Proof.Argon2.X86_64.FillCompress.destination s, 1024⟩)
      (Offset.contains_base _ (by omega) (by omega)) h.destinationSafe (by decide)
  rw [← blockAt_get t.mem (VG.Proof.Argon2.X86_64.FillCompress.destination s) ⟨i, hi⟩,
    ← blockAt_get s.mem (VG.Proof.Argon2.X86_64.FillCompress.destination s) ⟨i, hi⟩] at read
  exact read

theorem operation_ok [CompressImpl] (s : State) (h : VG.Proof.Argon2.X86_64.FillCompress.OperationReady s) :
    WP isa operation s fun t => VG.Proof.Argon2.X86_64.FillCompress.OperationDone s t ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold operation
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillCompress.call_ok s h.call).mono ?_)
  rintro a ⟨called, mx1⟩
  have bp : a.gpr .rbp = s.gpr .rbp := called.regs .rbp (by simp [calleeSaved])
  have reads (d : Nat) (hd : d ∈ [0, 16, 248]) :
      InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) d) 8 := by
    rw [called.rd, called.wr, bp]; exact h.frameRead d hd
  refine WP.seq ((WP.with_mx (by lit_decide) (VG.Proof.Argon2.X86_64.FillCompress.writeArgs_ok a (reads 16 (by simp))
    (reads 248 (by simp)) (reads 0 (by simp)))).mono ?_)
  rintro b ⟨⟨dest, src, counter, keeps⟩, mx2⟩
  have dest' : b.gpr .rdi = VG.Proof.Argon2.X86_64.FillCompress.destination s := by
    rw [dest, bp, VG.Proof.Argon2.X86_64.FillCompress.frame_word h called 16 (by decide), VG.Proof.Argon2.X86_64.FillCompress.destination]
  have src' : b.gpr .rsi = s.gpr .rdx := by
    rw [src, bp, VG.Proof.Argon2.X86_64.FillCompress.frame_word h called 248 (by decide), h.workWord, h.outputPointer]
  have counter' : b.gpr .r9 = VG.Proof.Argon2.X86_64.FillCompress.pass s := by
    rw [counter, bp, VG.Proof.Argon2.X86_64.FillCompress.frame_word h called 0 (by decide), VG.Proof.Argon2.X86_64.FillCompress.pass]
  have readable : Covers [⟨b.gpr .rsi, 1024⟩] (b.rd ++ b.wr) := by
    rw [src', keeps.rd, keeps.wr, called.rd, called.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := h.call.output p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writable : Covers [⟨b.gpr .rdi, 1024⟩] b.wr := by
    rw [dest', keeps.wr, called.wr]; exact h.destinationWrite
  have sep : (⟨b.gpr .rsi, 1024⟩ : Region).Disjoint ⟨b.gpr .rdi, 1024⟩ := by
    rw [src', dest']; exact (h.destinationSafe _ (by simp [VG.Proof.Argon2.X86_64.FillCompress.callWrites])).symm
  refine (WP.with_mx (by lit_decide) (FillWrite.code_cover_ok b readable writable sep)).mono ?_
  rintro t ⟨⟨value, frame, tk, _⟩, mx3⟩
  refine ⟨⟨?_, ?_, tk.2.1.trans (keeps.rd.trans called.rd),
    tk.2.2.trans (keeps.wr.trans called.wr), ?_⟩, by rw [mx3, mx2]; exact mx1⟩
  · rw [dest', src', counter', keeps.mem, called.result, VG.Proof.Argon2.X86_64.FillCompress.destination_unchanged h called] at value
    exact value
  · intro r hr
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have nk : r ∉ [Reg.rdi, .rsi, .r9] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r ne).trans ((keeps.regs r nk).trans (called.regs r hr))
  · rw [dest'] at frame
    rw [keeps.mem] at frame
    exact (called.frame.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans
      (frame.mono (by simp))

end VG.Proof.Argon2.X86_64.FillCompress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillCompressSetup`. -/
section

/-! Establish compression-and-write invariants from the frame and allocations. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillCompress

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def prefixWrites (s : State) : List Region := [⟨off (s.gpr .rbp) 16, 8⟩]

structure Ready (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .rbp) 16) 8
  leftRead : Covers [⟨s.gpr .rdi, 1024⟩] (s.rd ++ s.wr)
  rightRead : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr)
  destinationWrite : Covers [⟨s.gpr .r10, 1024⟩] s.wr
  workWrite : Covers [⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩] s.wr
  leftWork : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩
  rightWork : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩
  destinationWork : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩
  leftFrame : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  rightFrame : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  destinationFrame : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  stackLeft : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdi, 1024⟩
  stackRight : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rsi, 1024⟩
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩
  destinationStack : (⟨s.gpr .r10, 1024⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)

structure Prepared (s t : State) : Prop where
  ready : VG.Proof.Argon2.X86_64.FillCompress.OperationReady t
  dest : VG.Proof.Argon2.X86_64.FillCompress.destination t = s.gpr .r10
  counter : VG.Proof.Argon2.X86_64.FillCompress.pass t = VG.Proof.Argon2.X86_64.FillCompress.pass s
  scratch : t.gpr .rcx = VG.Proof.Argon2.X86_64.FillCompress.work s
  output : t.gpr .rdx = VG.Proof.Argon2.X86_64.FillCompress.work s + 4096
  left : t.gpr .rdi = s.gpr .rdi
  right : t.gpr .rsi = s.gpr .rsi
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.FillCompress.prefixWrites s) s.mem t.mem
  leftBlock : blockAt t.mem (t.gpr .rdi) = blockAt s.mem (s.gpr .rdi)
  rightBlock : blockAt t.mem (t.gpr .rsi) = blockAt s.mem (s.gpr .rsi)
  oldBlock : blockAt t.mem (VG.Proof.Argon2.X86_64.FillCompress.destination t) = blockAt s.mem (s.gpr .r10)

theorem block_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (p : Addr) (sep : ∀ r ∈ rs, (⟨p, 1024⟩ : Region).Disjoint r) :
    blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have read : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega)) sep (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at read
  exact read

theorem work_cover (s : State) (h : VG.Proof.Argon2.X86_64.FillCompress.Ready s) (d n : Nat) (hd : d + n ≤ 5120) :
    Covers [⟨off (VG.Proof.Argon2.X86_64.FillCompress.work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (VG.Proof.Argon2.X86_64.FillCompress.work s) d, n⟩] [⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

theorem prepared_of_setup (s a b : State) (h : VG.Proof.Argon2.X86_64.FillCompress.Ready s)
    (mem : a.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10))
    (regs : a.gpr = s.gpr) (rd : a.rd = s.rd) (wr : a.wr = s.wr)
    (scratch : b.gpr .rcx = a.mem.readW (off (a.gpr .rbp) 248) 64)
    (output : b.gpr .rdx = a.mem.readW (off (a.gpr .rbp) 248) 64 + 4096)
    (keeps : Divide.Keeps [.rcx, .rdx] a b) : VG.Proof.Argon2.X86_64.FillCompress.Prepared s b := by
  have g (r : Reg) (hr : r ∉ [Reg.rcx, .rdx]) : b.gpr r = s.gpr r :=
    (keeps.regs r hr).trans (congrFun regs r)
  have brd : b.rd = s.rd := keeps.rd.trans rd
  have bwr : b.wr = s.wr := keeps.wr.trans wr
  have bm : b.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10) := keeps.mem.trans mem
  have unchanged (d : Nat) (sep : d + 8 ≤ 16 ∨ 24 ≤ d) (bound : d + 8 ≤ 272) :
      b.mem.readW (off (b.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bm, g .rbp (by decide)]
    exact Mem.readW_writeW_sep (Offset.sep _ sep (by omega) (by decide)) (by decide)
  have work' : b.gpr .rcx = VG.Proof.Argon2.X86_64.FillCompress.work s := by
    rw [scratch, regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have out' : b.gpr .rdx = VG.Proof.Argon2.X86_64.FillCompress.work s + 4096 := by
    rw [output, regs, mem,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), VG.Proof.Argon2.X86_64.FillCompress.work]
  have dest : VG.Proof.Argon2.X86_64.FillCompress.destination b = s.gpr .r10 := by
    unfold VG.Proof.Argon2.X86_64.FillCompress.destination
    rw [bm, g .rbp (by decide), Mem.readW_writeW_self64]
  have counter : VG.Proof.Argon2.X86_64.FillCompress.pass b = VG.Proof.Argon2.X86_64.FillCompress.pass s := unchanged 0 (by decide) (by decide)
  have frame : Frame (VG.Proof.Argon2.X86_64.FillCompress.prefixWrites s) s.mem b.mem := by
    rw [bm]
    exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 16, 8⟩) (by simp [VG.Proof.Argon2.X86_64.FillCompress.prefixWrites]) _
      (Region.contains_self _ _)
  have cellFrame (p : Addr) (sep : (⟨p, 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩) :
      blockAt b.mem p = blockAt s.mem p :=
    VG.Proof.Argon2.X86_64.FillCompress.block_frame frame p (by
      intro r hr
      simp only [VG.Proof.Argon2.X86_64.FillCompress.prefixWrites, List.mem_singleton] at hr
      subst r
      exact sep.sub_right (Offset.sub_base _ (by decide)))
  have tempSub : Region.Sub ⟨VG.Proof.Argon2.X86_64.FillCompress.work s + 4096, 1024⟩ ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩ :=
    Offset.sub_base _ (by decide)
  have scratchSub : Region.Sub ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 4096⟩ ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 5120⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, dest, counter, work', out', g .rdi (by decide), g .rsi (by decide), ?_, brd, bwr,
    frame, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [g .rdi (by decide), brd, bwr]; exact h.leftRead
      · rw [g .rsi (by decide), brd, bwr]; exact h.rightRead
      · rw [out', bwr]; exact VG.Proof.Argon2.X86_64.FillCompress.work_cover s h 4096 1024 (by decide)
      · rw [work', bwr]
        simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
          using VG.Proof.Argon2.X86_64.FillCompress.work_cover s h 0 4096 (by decide)
      · rw [g .rdi (by decide), work']; exact h.leftWork.sub_right scratchSub
      · rw [g .rsi (by decide), work']; exact h.rightWork.sub_right scratchSub
      · rw [out', work']; exact Offset.disjoint_base _ (by decide) (by decide)
      · rw [g .rsp (by decide), g .rdi (by decide)]; exact h.stackLeft
      · rw [g .rsp (by decide), g .rsi (by decide)]; exact h.stackRight
      · rw [g .rsp (by decide), out']; exact h.stackWork.sub_right tempSub
      · rw [g .rsp (by decide), work']; exact h.stackWork.sub_right scratchSub
    · intro d hd
      rw [brd, bwr, g .rbp (by decide)]; exact h.frameRead d hd
    · rw [unchanged 248 (by decide) (by decide), work']; rfl
    · rw [work', out']
    · rw [dest, bwr]; exact h.destinationWrite
    · intro r hr
      simp only [VG.Proof.Argon2.X86_64.FillCompress.callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g .rbp (by decide), out']; exact h.frameWork.sub_right tempSub
      · rw [g .rbp (by decide), work']; exact h.frameWork.sub_right scratchSub
      · rw [g .rbp (by decide), g .rsp (by decide)]; exact h.frameStack
    · intro r hr
      rw [dest]
      simp only [VG.Proof.Argon2.X86_64.FillCompress.callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [out']; exact h.destinationWork.sub_right tempSub
      · rw [work']; exact h.destinationWork.sub_right scratchSub
      · rw [g .rsp (by decide)]; exact h.destinationStack
  · intro r hr
    apply g r
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [g .rdi (by decide)]; exact cellFrame _ h.leftFrame
  · rw [g .rsi (by decide)]; exact cellFrame _ h.rightFrame
  · rw [dest]; exact cellFrame _ h.destinationFrame

theorem setup_ok (s : State) (h : VG.Proof.Argon2.X86_64.FillCompress.Ready s) :
    WP isa VG.Impl.Argon2.X86_64.FillCompress.setup s (VG.Proof.Argon2.X86_64.FillCompress.Prepared s) := by
  unfold VG.Impl.Argon2.X86_64.FillCompress.setup
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillCompress.saveCurrent_ok s h.frameWrite).mono ?_)
  rintro a ⟨mem, regs, rd, wr, _⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 248) 8 := by
    rw [rd, wr, regs]; exact h.frameRead 248 (by simp)
  refine (VG.Proof.Argon2.X86_64.FillCompress.compressArgs_ok a read).mono ?_
  rintro b ⟨scratch, output, keeps⟩
  exact VG.Proof.Argon2.X86_64.FillCompress.prepared_of_setup s a b h mem regs rd wr scratch output keeps

end VG.Proof.Argon2.X86_64.FillCompress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderWords`. -/
section

/-! Merged from `Proof.Argon2.X86_64.BlockStore`. -/
section
/-! A single matrix or scratch block word write as a vector update. -/

namespace VG.Proof.Argon2.X86_64

open VG VG.Spec.Argon2

theorem blockAt_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    blockAt (m.writeW (off p (8 * i.val)) v) p = (blockAt m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases eq : i.val = j
  · subst j
    simp only [ite_true]
    change (m.writeW (off p (8 * i.val)) v).readW (off p (8 * i.val)) 64 = v
    exact Mem.readW_writeW_self64 _ _ _
  · simp only [eq, ite_false]
    change (m.writeW (off p (8 * i.val)) v).readW (off p (8 * j)) 64 =
      m.readW (off p (8 * j)) 64
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem blockAt_write_nat (m : Mem) (p : Addr) (i : Nat) (hi : i < 128) (v : Word) :
    blockAt (m.writeW (off p (8 * i)) v) p = (blockAt m p).set i v hi :=
  VG.Proof.Argon2.X86_64.blockAt_write m p ⟨i, hi⟩ v

end VG.Proof.Argon2.X86_64
end

/-! Short independent-address input header writes. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressHeader

theorem registerWord_ok (s : State) (i : Nat) (r : Reg)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (registerWord i r)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i)) (s.gpr r) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [registerWord, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, VG.Proof.Argon2.X86_64.ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem frameWord_ok (s : State) (i offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) offset) 8)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (frameWord i offset)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i))
        (s.mem.readW (off (s.gpr .rbp) offset) 64) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [frameWord, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.X86_64.readSrc, State.load64, State.store64, VG.Proof.Argon2.X86_64.ea_at, hr, hw,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, trivial, trivial, rfl⟩
  intro r hr
  simp only [hr, ite_false]

end VG.Proof.Argon2.X86_64.AddressHeader

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsStage`. -/
section

/-! Merged from `Proof.Argon2.X86_64.AddressCallsLayout`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressCallsArgs`. -/
section
/-! Independent-address compression arguments from one fixed frame read. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def displacement (n : Nat) : Addr := BitVec.signExtend 64 (BitVec.ofNat 32 n)

theorem pointer_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block (VG.Impl.Argon2.X86_64.AddressCalls.pointer offset)) s fun t =>
      t.gpr .rdi = VG.Proof.Argon2.X86_64.AddressCalls.work s + VG.Proof.Argon2.X86_64.AddressCalls.displacement offset ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.AddressCalls.pointer, VG.Proof.Argon2.X86_64.AddressCalls.work, VG.Proof.Argon2.X86_64.AddressCalls.displacement, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, VG.Proof.Argon2.X86_64.ea_at, hr, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, ite_true, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem args_ok (s : State) (x y out : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block (VG.Impl.Argon2.X86_64.AddressCalls.args x y out)) s fun t =>
      t.gpr .rcx = VG.Proof.Argon2.X86_64.AddressCalls.work s ∧ t.gpr .rdi = VG.Proof.Argon2.X86_64.AddressCalls.work s + VG.Proof.Argon2.X86_64.AddressCalls.displacement x ∧
      t.gpr .rsi = VG.Proof.Argon2.X86_64.AddressCalls.work s + VG.Proof.Argon2.X86_64.AddressCalls.displacement y ∧ t.gpr .rdx = VG.Proof.Argon2.X86_64.AddressCalls.work s + VG.Proof.Argon2.X86_64.AddressCalls.displacement out ∧
      Divide.Keeps [.rcx, .rdi, .rsi, .rdx] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.AddressCalls.args, VG.Proof.Argon2.X86_64.AddressCalls.work, VG.Proof.Argon2.X86_64.AddressCalls.displacement, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, VG.Proof.Argon2.X86_64.ea_at, hr, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Permissions and separation for either address-generation compression call. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64

structure Ready (s : State) : Prop where
  frameRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8
  workWrite : Covers [⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩] s.wr
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩

theorem displacement_eq (n : Nat) (bound : n ≤ 8192) : VG.Proof.Argon2.X86_64.AddressCalls.displacement n = BitVec.ofNat 64 n := by
  have n32 : n < 2 ^ 32 := by omega
  have msb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n32]
    omega
  unfold VG.Proof.Argon2.X86_64.AddressCalls.displacement
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb,
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) n32]

theorem work_cover (s : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (d n : Nat) (hd : d + n ≤ 8192) :
    Covers [⟨off (VG.Proof.Argon2.X86_64.AddressCalls.work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (VG.Proof.Argon2.X86_64.AddressCalls.work s) d, n⟩] [⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

structure Args (s a : State) (x y out : Nat) : Prop where
  scratch : a.gpr .rcx = VG.Proof.Argon2.X86_64.AddressCalls.work s
  left : a.gpr .rdi = off (VG.Proof.Argon2.X86_64.AddressCalls.work s) x
  right : a.gpr .rsi = off (VG.Proof.Argon2.X86_64.AddressCalls.work s) y
  output : a.gpr .rdx = off (VG.Proof.Argon2.X86_64.AddressCalls.work s) out
  keeps : Divide.Keeps [.rcx, .rdi, .rsi, .rdx] s a

theorem args_nat_ok (s : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (x y out : Nat)
    (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192) :
    WP isa (.block (Impl.Argon2.X86_64.AddressCalls.args x y out)) s (VG.Proof.Argon2.X86_64.AddressCalls.Args s · x y out) := by
  refine (VG.Proof.Argon2.X86_64.AddressCalls.args_ok s x y out h.frameRead).mono ?_
  rintro a ⟨scratch, left, right, output, keeps⟩
  rw [VG.Proof.Argon2.X86_64.AddressCalls.displacement_eq x hx] at left
  rw [VG.Proof.Argon2.X86_64.AddressCalls.displacement_eq y hy] at right
  rw [VG.Proof.Argon2.X86_64.AddressCalls.displacement_eq out ho] at output
  exact ⟨scratch, left, right, output, keeps⟩

theorem args_call_ready (s a : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (args : VG.Proof.Argon2.X86_64.AddressCalls.Args s a x y out) : FillCompress.CallReady a := by
  have read (d : Nat) (hd : d + 1024 ≤ 8192) :
      Covers [⟨off (VG.Proof.Argon2.X86_64.AddressCalls.work s) d, 1024⟩] (a.rd ++ a.wr) := by
    rw [args.keeps.rd, args.keeps.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := VG.Proof.Argon2.X86_64.AddressCalls.work_cover s h d 1024 hd p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have sp : a.gpr .rsp = s.gpr .rsp := args.keeps.regs .rsp (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [args.left]; exact read x bx
  · rw [args.right]; exact read y by_
  · rw [args.output, args.keeps.wr]; exact VG.Proof.Argon2.X86_64.AddressCalls.work_cover s h out 1024 bo
  · rw [args.scratch, args.keeps.wr]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using VG.Proof.Argon2.X86_64.AddressCalls.work_cover s h 0 4096 (by decide)
  · rw [args.left, args.scratch]; exact Offset.disjoint_base _ hx (by omega)
  · rw [args.right, args.scratch]; exact Offset.disjoint_base _ hy (by omega)
  · rw [args.output, args.scratch]; exact Offset.disjoint_base _ ho (by omega)
  · rw [sp, args.left]; exact h.stackWork.sub_right (Offset.sub_base _ bx)
  · rw [sp, args.right]; exact h.stackWork.sub_right (Offset.sub_base _ by_)
  · rw [sp, args.output]; exact h.stackWork.sub_right (Offset.sub_base _ bo)
  · rw [sp, args.scratch]; exact h.stackWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! One verified G call within the independent-address scratch layout. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

def stageWrites (s : State) (out : Nat) : List Region :=
  [⟨off (VG.Proof.Argon2.X86_64.AddressCalls.work s) out, 1024⟩, ⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 4096⟩, below (s.gpr .rsp) 8]

structure StageDone (s t : State) (x y out : Nat) : Prop where
  result : blockAt t.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) out) = Spec.Argon2.compress
    (blockAt s.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) x)) (blockAt s.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) y))
  ready : VG.Proof.Argon2.X86_64.AddressCalls.Ready t
  work : VG.Proof.Argon2.X86_64.AddressCalls.work t = VG.Proof.Argon2.X86_64.AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.AddressCalls.stageWrites s out) s.mem t.mem

theorem Args.callee {s a : State} {x y out : Nat} (h : VG.Proof.Argon2.X86_64.AddressCalls.Args s a x y out)
    (r : Reg) (hr : r ∈ calleeSaved) : a.gpr r = s.gpr r := by
  apply h.keeps.regs
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ready_of_frame {s t : State} (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (out : Nat) (ho : out + 1024 ≤ 8192)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame (VG.Proof.Argon2.X86_64.AddressCalls.stageWrites s out) s.mem t.mem) : VG.Proof.Argon2.X86_64.AddressCalls.Ready t ∧ VG.Proof.Argon2.X86_64.AddressCalls.work t = VG.Proof.Argon2.X86_64.AddressCalls.work s := by
  have bp := regs .rbp (by simp [calleeSaved])
  have sp := regs .rsp (by simp [calleeSaved])
  have safe : ∀ r ∈ VG.Proof.Argon2.X86_64.AddressCalls.stageWrites s out, (⟨s.gpr .rbp, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [VG.Proof.Argon2.X86_64.AddressCalls.stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.frameWork.sub_right (Offset.sub_base _ ho)
    · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
    · exact h.frameStack
  have read : t.mem.readW (off (s.gpr .rbp) 248) 64 = s.mem.readW (off (s.gpr .rbp) 248) 64 :=
    frame.readW (r := ⟨s.gpr .rbp, 272⟩)
      (Offset.contains_base _ (by decide) (by decide)) safe (by decide)
  have work' : VG.Proof.Argon2.X86_64.AddressCalls.work t = VG.Proof.Argon2.X86_64.AddressCalls.work s := by unfold VG.Proof.Argon2.X86_64.AddressCalls.work; rw [bp, read]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work'⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem stage_ok [CompressImpl] (s : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192) :
    WP isa (stage x y out) s fun t => VG.Proof.Argon2.X86_64.AddressCalls.StageDone s t x y out ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold stage
  refine WP.seq ((WP.with_mx (by rfl) (VG.Proof.Argon2.X86_64.AddressCalls.args_nat_ok s h x y out (by omega) (by omega)
    (by omega))).mono ?_)
  rintro a ⟨args, mx1⟩
  have callReady := VG.Proof.Argon2.X86_64.AddressCalls.args_call_ready s a h x y out hx hy ho bx by_ bo args
  refine (FillCompress.call_ok a callReady).mono ?_
  rintro t ⟨called, mx2⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r :=
    fun r hr => (called.regs r hr).trans (args.callee r hr)
  have rd := called.rd.trans args.keeps.rd
  have wr := called.wr.trans args.keeps.wr
  have frame : Frame (VG.Proof.Argon2.X86_64.AddressCalls.stageWrites s out) s.mem t.mem := by
    have hf := called.frame
    rw [args.output, args.scratch, args.callee .rsp (by simp [calleeSaved]), args.keeps.mem] at hf
    exact hf
  obtain ⟨ready, work'⟩ := VG.Proof.Argon2.X86_64.AddressCalls.ready_of_frame h out bo regs rd wr frame
  refine ⟨⟨?_, ready, work', regs, rd, wr, frame⟩, by rw [mx2, mx1]⟩
  have result := called.result
  rw [args.output, args.left, args.right, args.keeps.mem] at result
  exact result

end VG.Proof.Argon2.X86_64.AddressCalls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsPrepare`. -/
section

/-! Merged from `Proof.Argon2.X86_64.AddressHeaderCorrect`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressHeader`. -/
section
/-! Compose the seven input fields, preserving frame reads across every write. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressHeader

def value (s : State) (i : Nat) : Addr :=
  if i = 1 then s.gpr .rbx else if i = 2 then s.gpr .r14
  else s.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64

def headerMem (s : State) (p : Addr) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (VG.Proof.Argon2.X86_64.AddressHeader.headerMem s p n).writeW (off p (8 * n)) (VG.Proof.Argon2.X86_64.AddressHeader.value s n)

theorem field_ok (s : State) (i : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) (frameOffset i)) 8)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (field i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i)) (VG.Proof.Argon2.X86_64.AddressHeader.value s i) ∧
      CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  unfold field VG.Proof.Argon2.X86_64.AddressHeader.value
  by_cases one : i = 1
  · simp only [one, ite_true]
    refine (VG.Proof.Argon2.X86_64.AddressHeader.registerWord_ok s 1 .rbx (one ▸ hw)).mono ?_
    rintro t ⟨mem, regs, rd, wr, mx⟩
    exact ⟨mem, ⟨fun r _ => congrFun regs r, rd, wr⟩, mx⟩
  · simp only [one, ite_false]
    by_cases two : i = 2
    · simp only [two, ite_true]
      refine (VG.Proof.Argon2.X86_64.AddressHeader.registerWord_ok s 2 .r14 (two ▸ hw)).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨fun r _ => congrFun regs r, rd, wr⟩, mx⟩
    · simp only [two, ite_false]
      refine (VG.Proof.Argon2.X86_64.AddressHeader.frameWord_ok s i (frameOffset i) hr hw).mono ?_
      rintro t ⟨mem, regs, rd, wr, mx⟩
      exact ⟨mem, ⟨regs, rd, wr⟩, mx⟩

theorem offset_bound : ∀ i < 7, frameOffset i + 8 ≤ 272 := by decide +kernel

theorem offset_read (s : State) (i : Nat)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) (frameOffset i)) 8 := by
  apply reads
  unfold frameOffset
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> [simp; skip]
  split <;> simp

theorem value_kept {s t : State} (keeps : CopyKeeps s t)
    (hf : Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (i : Nat) (hi : i < 7) : VG.Proof.Argon2.X86_64.AddressHeader.value t i = VG.Proof.Argon2.X86_64.AddressHeader.value s i := by
  unfold VG.Proof.Argon2.X86_64.AddressHeader.value
  rw [keeps.1 .rbx (by decide), keeps.1 .r14 (by decide), keeps.1 .rbp (by decide)]
  have read : t.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64 =
      s.mem.readW (off (s.gpr .rbp) (frameOffset i)) 64 :=
    hf.readW (r := ⟨s.gpr .rbp, 272⟩)
      (Offset.contains_base _ (VG.Proof.Argon2.X86_64.AddressHeader.offset_bound i hi)
        (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (VG.Proof.Argon2.X86_64.AddressHeader.offset_bound i hi)) (by decide)))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep) (by decide)
  rw [read]

theorem prefix_ok (n : Nat) (hn : n ≤ 7) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa (.block (fields n)) s fun t =>
      t.mem = VG.Proof.Argon2.X86_64.AddressHeader.headerMem s (s.gpr .rdi) n ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, Frame.refl _ _, CopyKeeps.refl s, rfl⟩
  | succ n ih =>
    simp only [fields, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨mem, frame, keeps, mx⟩
    have dest : a.gpr .rdi = s.gpr .rdi := keeps.1 .rdi (by decide)
    have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) (frameOffset n)) 8 := by
      rw [keeps.2.1, keeps.2.2, keeps.1 .rbp (by decide)]
      exact VG.Proof.Argon2.X86_64.AddressHeader.offset_read s n reads
    have writable : InRegions a.wr (off (a.gpr .rdi) (8 * n)) 8 := by
      rw [dest, keeps.2.2]
      exact write _ _ ⟨⟨s.gpr .rdi, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega) (by omega)⟩
    refine (VG.Proof.Argon2.X86_64.AddressHeader.field_ok a n read writable).mono ?_
    rintro t ⟨mem', keeps', mx'⟩
    have value' := VG.Proof.Argon2.X86_64.AddressHeader.value_kept keeps frame sep n (by omega)
    refine ⟨?_, ?_, keeps.trans keeps', mx'.trans mx⟩
    · rw [mem', dest, value', mem]
      rfl
    · rw [mem', dest]
      exact frame.writeW (r := ⟨s.gpr .rdi, 1024⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Argon2.X86_64.AddressHeader
end

/-! The prepared input agrees with RFC 9106's seven public address words. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressHeader

def input (s : State) : Block :=
  zeroBlock |>.set 0 (VG.Proof.Argon2.X86_64.AddressHeader.value s 0) |>.set 1 (VG.Proof.Argon2.X86_64.AddressHeader.value s 1) |>.set 2 (VG.Proof.Argon2.X86_64.AddressHeader.value s 2)
    |>.set 3 (VG.Proof.Argon2.X86_64.AddressHeader.value s 3) |>.set 4 (VG.Proof.Argon2.X86_64.AddressHeader.value s 4) |>.set 5 (VG.Proof.Argon2.X86_64.AddressHeader.value s 5) |>.set 6 (VG.Proof.Argon2.X86_64.AddressHeader.value s 6)

theorem headerMem_block (s : State) (p : Addr) (zero : blockAt s.mem p = zeroBlock) :
    blockAt (VG.Proof.Argon2.X86_64.AddressHeader.headerMem s p 7) p = VG.Proof.Argon2.X86_64.AddressHeader.input s := by
  rw [VG.Proof.Argon2.X86_64.AddressHeader.headerMem, VG.Proof.Argon2.X86_64.blockAt_write_nat _ p 6 (by decide),
    VG.Proof.Argon2.X86_64.AddressHeader.headerMem, VG.Proof.Argon2.X86_64.blockAt_write_nat _ p 5 (by decide),
    VG.Proof.Argon2.X86_64.AddressHeader.headerMem, VG.Proof.Argon2.X86_64.blockAt_write_nat _ p 4 (by decide),
    VG.Proof.Argon2.X86_64.AddressHeader.headerMem, VG.Proof.Argon2.X86_64.blockAt_write_nat _ p 3 (by decide),
    VG.Proof.Argon2.X86_64.AddressHeader.headerMem, VG.Proof.Argon2.X86_64.blockAt_write_nat _ p 2 (by decide),
    VG.Proof.Argon2.X86_64.AddressHeader.headerMem, VG.Proof.Argon2.X86_64.blockAt_write_nat _ p 1 (by decide),
    VG.Proof.Argon2.X86_64.AddressHeader.headerMem, VG.Proof.Argon2.X86_64.blockAt_write_nat _ p 0 (by decide), VG.Proof.Argon2.X86_64.AddressHeader.headerMem, zero]
  rfl

theorem code_ok (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (zero : blockAt s.mem (s.gpr .rdi) = zeroBlock) :
    WP isa VG.Impl.Argon2.X86_64.AddressHeader.code s fun t => blockAt t.mem (s.gpr .rdi) = VG.Proof.Argon2.X86_64.AddressHeader.input s ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  refine (VG.Proof.Argon2.X86_64.AddressHeader.prefix_ok 7 (by decide) s reads write sep).mono ?_
  rintro t ⟨mem, frame, keeps, mx⟩
  exact ⟨by rw [mem]; exact VG.Proof.Argon2.X86_64.AddressHeader.headerMem_block s _ zero, frame, keeps, mx⟩

structure Words (p : Params) (pass lane slice counter : Nat) (s : State) : Prop where
  passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  laneWord : s.gpr .rbx = BitVec.ofNat 64 lane
  sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice
  blocksWord : s.mem.readW (off (s.gpr .rbp) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .rbp) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code
  counterWord : s.mem.readW (off (s.gpr .rbp) 8) 64 = BitVec.ofNat 64 counter

theorem input_spec (p : Params) (pass lane slice counter : Nat) (s : State)
    (h : VG.Proof.Argon2.X86_64.AddressHeader.Words p pass lane slice counter s) :
    VG.Proof.Argon2.X86_64.AddressHeader.input s = Proof.Argon2.addressInput p pass lane slice counter := by
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, VG.Proof.Argon2.X86_64.AddressHeader.input, VG.Proof.Argon2.X86_64.AddressHeader.value, frameOffset,
    h.passWord, h.laneWord, h.sliceWord, h.blocksWord,
    h.passesWord, h.variantWord, h.counterWord, Proof.Argon2.addressInput]

theorem code_spec_ok (p : Params) (pass lane slice counter : Nat) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (zero : blockAt s.mem (s.gpr .rdi) = zeroBlock)
    (words : VG.Proof.Argon2.X86_64.AddressHeader.Words p pass lane slice counter s) :
    WP isa VG.Impl.Argon2.X86_64.AddressHeader.code s fun t =>
      blockAt t.mem (s.gpr .rdi) = Proof.Argon2.addressInput p pass lane slice counter ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr :=
  (VG.Proof.Argon2.X86_64.AddressHeader.code_ok s reads write sep zero).mono (fun _ h =>
    ⟨h.1.trans (VG.Proof.Argon2.X86_64.AddressHeader.input_spec p pass lane slice counter s words), h.2⟩)

end VG.Proof.Argon2.X86_64.AddressHeader
end

/-! Merged from `Proof.Argon2.X86_64.AddressCallsClear`. -/
section
/-! Clear an address-generation block, retaining the allocation invariants. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

structure Cleared (s t : State) (offset : Nat) : Prop where
  block : blockAt t.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) offset) = zeroBlock
  ready : VG.Proof.Argon2.X86_64.AddressCalls.Ready t
  work_eq : VG.Proof.Argon2.X86_64.AddressCalls.work t = VG.Proof.Argon2.X86_64.AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (VG.Proof.Argon2.X86_64.AddressCalls.work s) offset, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem clearAt_ok (s : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (offset : Nat) (bound : offset + 1024 ≤ 8192) :
    WP isa (clearAt offset) s (VG.Proof.Argon2.X86_64.AddressCalls.Cleared s · offset) := by
  unfold clearAt
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCalls.pointer_ok s offset h.frameRead).mono ?_)
  rintro a ⟨dest, keeps⟩
  rw [VG.Proof.Argon2.X86_64.AddressCalls.displacement_eq offset (by omega)] at dest
  have write : Covers [⟨a.gpr .rdi, 1024⟩] a.wr := by
    rw [dest, keeps.wr]; exact VG.Proof.Argon2.X86_64.AddressCalls.work_cover s h offset 1024 bound
  refine (ClearBlock.code_ok a write).mono ?_
  rintro t ⟨zero, frame, tk, mx⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ≠ .rax ∧ r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (tk.1 r ne.1).trans (keeps.regs r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using ne.2))
  have rd := tk.2.1.trans keeps.rd
  have wr := tk.2.2.trans keeps.wr
  have hf : Frame [⟨off (VG.Proof.Argon2.X86_64.AddressCalls.work s) offset, 1024⟩] s.mem t.mem := by
    rw [dest, keeps.mem] at frame; exact frame
  have bigger : Frame (VG.Proof.Argon2.X86_64.AddressCalls.stageWrites s offset) s.mem t.mem :=
    hf.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [VG.Proof.Argon2.X86_64.AddressCalls.stageWrites])
  obtain ⟨ready, work'⟩ := VG.Proof.Argon2.X86_64.AddressCalls.ready_of_frame h offset bound regs rd wr bigger
  rw [dest] at zero
  exact ⟨zero, ready, work', regs, rd, wr, hf, mx.trans keeps.mxcsr⟩

theorem Cleared.full_frame {s t : State} {offset : Nat} (h : VG.Proof.Argon2.X86_64.AddressCalls.Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : Frame [⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩] s.mem t.mem := by
  apply h.frame.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩, by simp, Offset.sub_base _ bound⟩

theorem frame_word {s t : State} (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (frame : Frame [⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩] s.mem t.mem)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (s.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 :=
  frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.frameWork) (by decide)

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Prepare the independent-address input and zero block from arbitrary scratch. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

structure Stable (s t : State) : Prop where
  ready : VG.Proof.Argon2.X86_64.AddressCalls.Ready t
  work_eq : VG.Proof.Argon2.X86_64.AddressCalls.work t = VG.Proof.Argon2.X86_64.AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem Stable.trans {s a t : State} (h : VG.Proof.Argon2.X86_64.AddressCalls.Stable s a) (k : VG.Proof.Argon2.X86_64.AddressCalls.Stable a t) : VG.Proof.Argon2.X86_64.AddressCalls.Stable s t := by
  have hf := k.frame
  rw [h.work_eq] at hf
  exact ⟨k.ready, k.work_eq.trans h.work_eq, fun r hr => (k.regs r hr).trans (h.regs r hr),
    k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans hf, k.mxcsr.trans h.mxcsr⟩

theorem Cleared.stable {s t : State} {offset : Nat} (h : VG.Proof.Argon2.X86_64.AddressCalls.Cleared s t offset)
    (bound : offset + 1024 ≤ 8192) : VG.Proof.Argon2.X86_64.AddressCalls.Stable s t :=
  ⟨h.ready, h.work_eq, h.regs, h.rd, h.wr, h.full_frame bound, h.mxcsr⟩

theorem stable_of_frame {s t : State} (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame [⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩] s.mem t.mem) (mx : t.mxcsr = s.mxcsr) : VG.Proof.Argon2.X86_64.AddressCalls.Stable s t := by
  have bp := regs .rbp (by simp [calleeSaved])
  have sp := regs .rsp (by simp [calleeSaved])
  have work' : VG.Proof.Argon2.X86_64.AddressCalls.work t = VG.Proof.Argon2.X86_64.AddressCalls.work s := by
    unfold VG.Proof.Argon2.X86_64.AddressCalls.work
    rw [bp, VG.Proof.Argon2.X86_64.AddressCalls.frame_word h frame 248 (by decide)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work', regs, rd, wr, frame, mx⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem Stable.reads {s t : State} (h : VG.Proof.Argon2.X86_64.AddressCalls.Stable s t)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    ∀ d ∈ [0, 8, 72, 112, 240], InRegions (t.rd ++ t.wr) (off (t.gpr .rbp) d) 8 := by
  rw [h.rd, h.wr, h.regs .rbp (by simp [calleeSaved])]
  exact reads

theorem Stable.words {s t : State} {p : Params} {pass lane slice counter : Nat} (ready : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (h : VG.Proof.Argon2.X86_64.AddressCalls.Stable s t)
    (words : AddressHeader.Words p pass lane slice counter s) :
    AddressHeader.Words p pass lane slice counter t := by
  have bp := h.regs .rbp (by simp [calleeSaved])
  have read (d : Nat) (hd : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bp]; exact VG.Proof.Argon2.X86_64.AddressCalls.frame_word ready h.frame d hd
  exact ⟨(read 0 (by decide)).trans words.passWord,
    (h.regs .rbx (by simp [calleeSaved])).trans words.laneWord,
    (h.regs .r14 (by simp [calleeSaved])).trans words.sliceWord,
    (read 240 (by decide)).trans words.blocksWord,
    (read 72 (by decide)).trans words.passesWord,
    (read 112 (by decide)).trans words.variantWord,
    (read 8 (by decide)).trans words.counterWord⟩

theorem pointer_stable {s a : State} (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s)
    (k : Divide.Keeps [.rdi] s a) : VG.Proof.Argon2.X86_64.AddressCalls.Stable s a := by
  apply VG.Proof.Argon2.X86_64.AddressCalls.stable_of_frame h _ k.rd k.wr _ k.mxcsr
  · intro r hr
    apply k.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem Stable.input {s t : State} (ready : VG.Proof.Argon2.X86_64.AddressCalls.Ready s) (h : VG.Proof.Argon2.X86_64.AddressCalls.Stable s t) :
    AddressHeader.input t = AddressHeader.input s := by
  have value (i : Nat) (hi : i < 7) : AddressHeader.value t i = AddressHeader.value s i := by
    unfold AddressHeader.value
    rw [h.regs .rbx (by simp [calleeSaved]), h.regs .r14 (by simp [calleeSaved]),
      h.regs .rbp (by simp [calleeSaved]),
      VG.Proof.Argon2.X86_64.AddressCalls.frame_word ready h.frame (Impl.Argon2.X86_64.AddressHeader.frameOffset i)
        (AddressHeader.offset_bound i hi)]
  unfold AddressHeader.input
  rw [value 0 (by decide), value 1 (by decide), value 2 (by decide), value 3 (by decide),
    value 4 (by decide), value 5 (by decide), value 6 (by decide)]

structure PreparedInput (s t : State) : Prop where
  stable : VG.Proof.Argon2.X86_64.AddressCalls.Stable s t
  zero : blockAt t.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 7168) = zeroBlock
  input : blockAt t.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 5120) = AddressHeader.input s

structure Prepared (s t : State) (p : Params) (pass lane slice counter : Nat) : Prop where
  stable : VG.Proof.Argon2.X86_64.AddressCalls.Stable s t
  zero : blockAt t.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 7168) = zeroBlock
  input : blockAt t.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter

theorem prepare_layout_ok (s : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    : WP isa VG.Impl.Argon2.X86_64.AddressCalls.prepare s (VG.Proof.Argon2.X86_64.AddressCalls.PreparedInput s) := by
  unfold VG.Impl.Argon2.X86_64.AddressCalls.prepare
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCalls.clearAt_ok s h 5120 (by decide)).mono ?_)
  intro a inputClear
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCalls.clearAt_ok a inputClear.ready 7168 (by decide)).mono ?_)
  intro b zeroClear
  have stableB := (inputClear.stable (by decide)).trans (zeroClear.stable (by decide))
  have inputZero : blockAt b.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 5120) = zeroBlock := by
    have kept := FillCompress.block_frame zeroClear.frame (p := off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 5120) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [inputClear.work_eq]
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
    exact kept.trans inputClear.block
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCalls.pointer_ok b 5120 zeroClear.ready.frameRead).mono ?_)
  rintro c ⟨dest, keeps⟩
  rw [VG.Proof.Argon2.X86_64.AddressCalls.displacement_eq 5120 (by decide)] at dest
  have stableC := stableB.trans (VG.Proof.Argon2.X86_64.AddressCalls.pointer_stable zeroClear.ready keeps)
  have dest' : c.gpr .rdi = off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 5120 := by rw [dest, stableB.work_eq]
  have write : Covers [⟨c.gpr .rdi, 1024⟩] c.wr := by
    rw [dest, keeps.wr]; exact VG.Proof.Argon2.X86_64.AddressCalls.work_cover b zeroClear.ready 5120 1024 (by decide)
  have sep : (⟨c.gpr .rbp, 272⟩ : Region).Disjoint ⟨c.gpr .rdi, 1024⟩ := by
    rw [dest', stableC.regs .rbp (by simp [calleeSaved])]
    exact h.frameWork.sub_right (Offset.sub_base _ (by decide))
  have zero : blockAt c.mem (c.gpr .rdi) = zeroBlock := by rw [dest', keeps.mem]; exact inputZero
  refine (AddressHeader.code_ok c (stableC.reads reads) write sep zero).mono ?_
  rintro t ⟨input, frame, tk, mx⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = c.gpr r := by
    intro r hr
    apply tk.1
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have frame' : Frame [⟨VG.Proof.Argon2.X86_64.AddressCalls.work c, 8192⟩] c.mem t.mem := by
    apply frame.sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    refine ⟨⟨VG.Proof.Argon2.X86_64.AddressCalls.work c, 8192⟩, by simp, ?_⟩
    rw [dest', stableC.work_eq]
    exact Offset.sub_base _ (by decide)
  have stableT := stableC.trans (VG.Proof.Argon2.X86_64.AddressCalls.stable_of_frame stableC.ready regs tk.2.1 tk.2.2 frame' mx)
  refine ⟨stableT, ?_, ?_⟩
  · have kept := FillCompress.block_frame frame (p := off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 7168) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      rw [dest']
      exact Offset.disjoint _ (by decide) (by decide) (by decide))
    rw [kept, keeps.mem, ← inputClear.work_eq]
    exact zeroClear.block
  · rw [dest'] at input
    exact input.trans (stableC.input h)

theorem prepare_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa VG.Impl.Argon2.X86_64.AddressCalls.prepare s (VG.Proof.Argon2.X86_64.AddressCalls.Prepared s · p pass lane slice counter) :=
  (VG.Proof.Argon2.X86_64.AddressCalls.prepare_layout_ok s h reads).mono (fun _ k =>
    ⟨k.stable, k.zero, k.input.trans (AddressHeader.input_spec p pass lane slice counter s words)⟩)

end VG.Proof.Argon2.X86_64.AddressCalls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheMeta`. -/
section

/-! Public cache counters and indexed-word arguments. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

def counter (index : Addr) : Addr := (index >>> 7) + 1

theorem check_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 8) 8) :
    WP isa (.block VG.Impl.Argon2.X86_64.AddressCache.check) s fun t => t.gpr .rax = VG.Proof.Argon2.X86_64.AddressCache.counter (s.gpr .r15) ∧
      t.zf = decide (VG.Proof.Argon2.X86_64.AddressCache.counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64) ∧
      Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.AddressCache.check, VG.Proof.Argon2.X86_64.AddressCache.counter, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, State.load64, VG.Proof.Argon2.X86_64.ea_at, hr, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_arithFlags, reduceCtorEq, ite_true, ite_false, and_self,
    show 1 ≤ (7 : Nat) ∧ (7 : Nat) ≤ 63 from by decide,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ReferenceStart.sub_zero_iff]
    exact ⟨fun h => decide_eq_true h, of_decide_eq_true⟩
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem counter_nat (index : Addr) : VG.Proof.Argon2.X86_64.AddressCache.counter index = BitVec.ofNat 64 (index.toNat / 128 + 1) := by
  have shifted : index >>> 7 = BitVec.ofNat 64 (index.toNat / 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := index.isLt; omega)]
  unfold VG.Proof.Argon2.X86_64.AddressCache.counter
  rw [shifted]
  exact (BitVec.ofNat_add _ _).symm

theorem counter_ne_zero (index : Addr) : VG.Proof.Argon2.X86_64.AddressCache.counter index ≠ 0 := by
  have bound : index.toNat / 128 + 1 < 2 ^ 64 := by have := index.isLt; omega
  intro h
  have nat := congrArg BitVec.toNat h
  rw [VG.Proof.Argon2.X86_64.AddressCache.counter_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at nat
  change index.toNat / 128 + 1 = 0 at nat
  omega

theorem wordArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block wordArgs) s fun t => t.gpr .rcx = AddressCalls.work s ∧
      t.gpr .rax = s.gpr .r15 &&& 127 ∧ Divide.Keeps [.rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [wordArgs, AddressCalls.work, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, VG.Proof.Argon2.X86_64.ea_at, hr, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (127 : BitVec 32) = (127 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem index_nat (index : Addr) : index &&& 127 = BitVec.ofNat 64 (index.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod index.toNat 7

end VG.Proof.Argon2.X86_64.AddressCache

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.AddressCalls`. -/
section

/-! Both compression calls produce exactly the reviewed independent-address block. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

def writes (s : State) : List Region := [⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩, below (s.gpr .rsp) 8]

structure Generated (s t : State) (p : Params) (pass lane slice counter : Nat) : Prop where
  block : blockAt t.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 6144) = addressBlock p pass lane slice counter
  ready : VG.Proof.Argon2.X86_64.AddressCalls.Ready t
  work : VG.Proof.Argon2.X86_64.AddressCalls.work t = VG.Proof.Argon2.X86_64.AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.AddressCalls.writes s) s.mem t.mem

theorem stage_frame_full {s t : State} {out : Nat} (bound : out + 1024 ≤ 8192)
    (hf : Frame (VG.Proof.Argon2.X86_64.AddressCalls.stageWrites s out) s.mem t.mem) : Frame (VG.Proof.Argon2.X86_64.AddressCalls.writes s) s.mem t.mem := by
  apply hf.sub
  intro r hr
  simp only [VG.Proof.Argon2.X86_64.AddressCalls.stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩, by simp [VG.Proof.Argon2.X86_64.AddressCalls.writes], Offset.sub_base _ bound⟩
  · exact ⟨⟨VG.Proof.Argon2.X86_64.AddressCalls.work s, 8192⟩, by simp [VG.Proof.Argon2.X86_64.AddressCalls.writes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.AddressCalls.writes], fun _ h => h⟩

theorem zero_preserved {s t : State} (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s)
    (hf : Frame (VG.Proof.Argon2.X86_64.AddressCalls.stageWrites s 4096) s.mem t.mem) :
    blockAt t.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 7168) = blockAt s.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 7168) := by
  apply FillCompress.block_frame hf
  intro r hr
  simp only [VG.Proof.Argon2.X86_64.AddressCalls.stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact (h.stackWork.sub_right (Offset.sub_base _ (by decide))).symm

theorem calls_ok [CompressImpl] (p : Params) (pass lane slice counter : Nat) (s : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s)
    (zero : blockAt s.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 7168) = zeroBlock)
    (input : blockAt s.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work s) 5120) = Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s fun t => VG.Proof.Argon2.X86_64.AddressCalls.Generated s t p pass lane slice counter ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold calls
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCalls.stage_ok s h 7168 5120 4096 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_)
  rintro a ⟨first, mx1⟩
  refine (VG.Proof.Argon2.X86_64.AddressCalls.stage_ok a first.ready 7168 4096 6144 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨second, mx2⟩
  refine ⟨⟨?_, second.ready, second.work.trans first.work,
    fun r hr => (second.regs r hr).trans (first.regs r hr),
    second.rd.trans first.rd, second.wr.trans first.wr, ?_⟩, by rw [mx2, mx1]⟩
  · have result := second.result
    rw [first.work, VG.Proof.Argon2.X86_64.AddressCalls.zero_preserved h first.frame, zero, first.result, zero, input] at result
    rw [Proof.Argon2.addressBlock_eq]
    exact result
  · have next := VG.Proof.Argon2.X86_64.AddressCalls.stage_frame_full (by decide) second.frame
    simp only [VG.Proof.Argon2.X86_64.AddressCalls.writes, first.work, first.regs .rsp (by simp [calleeSaved])] at next
    exact (VG.Proof.Argon2.X86_64.AddressCalls.stage_frame_full (by decide) first.frame).trans next

end VG.Proof.Argon2.X86_64.AddressCalls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheSelect`. -/
section

/-! Merged from `Proof.Argon2.X86_64.AddressGeneration`. -/
section
/-! Complete independent-address generation against the reviewed algorithm. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

theorem code_ok [CompressImpl] (p : Params) (pass lane slice counter : Nat) (s : State) (h : VG.Proof.Argon2.X86_64.AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa VG.Impl.Argon2.X86_64.AddressCalls.code s fun t => VG.Proof.Argon2.X86_64.AddressCalls.Generated s t p pass lane slice counter ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold VG.Impl.Argon2.X86_64.AddressCalls.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCalls.prepare_ok p pass lane slice counter s h reads words).mono ?_)
  intro a prepared
  have zero : blockAt a.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work a) 7168) = zeroBlock := by
    rw [prepared.stable.work_eq]; exact prepared.zero
  have input : blockAt a.mem (off (VG.Proof.Argon2.X86_64.AddressCalls.work a) 5120) = Proof.Argon2.addressInput p pass lane slice counter := by
    rw [prepared.stable.work_eq]; exact prepared.input
  refine (VG.Proof.Argon2.X86_64.AddressCalls.calls_ok p pass lane slice counter a prepared.stable.ready zero input).mono ?_
  rintro t ⟨generated, mx⟩
  have frame := generated.frame
  rw [VG.Proof.Argon2.X86_64.AddressCalls.writes, prepared.stable.work_eq, prepared.stable.regs .rsp (by simp [calleeSaved])] at frame
  have firstFrame : Frame (VG.Proof.Argon2.X86_64.AddressCalls.writes s) s.mem a.mem :=
    prepared.stable.frame.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [VG.Proof.Argon2.X86_64.AddressCalls.writes])
  refine ⟨⟨?_, generated.ready, generated.work.trans prepared.stable.work_eq,
    fun r hr => (generated.regs r hr).trans (prepared.stable.regs r hr),
    generated.rd.trans prepared.stable.rd, generated.wr.trans prepared.stable.wr,
    firstFrame.trans frame⟩, mx.trans (ctl_eq_of prepared.stable.mxcsr)⟩
  have block := generated.block
  rw [prepared.stable.work_eq] at block
  exact block

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheSave`. -/
section
/-! Save the public cache counter without disturbing scratch or header fields. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

theorem save_ok (s : State) (hw : InRegions s.wr (off (s.gpr .rbp) 8) 8) :
    WP isa (.block save) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 8) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    VG.Proof.Argon2.X86_64.ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 8) (s.gpr .rax)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  ready : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  frame : Frame [⟨off (s.gpr .rbp) 8, 8⟩] s.mem t.mem

theorem save_ready (s : State) (h : AddressCalls.Ready s)
    (hw : InRegions s.wr (off (s.gpr .rbp) 8) 8) : WP isa (.block save) s (VG.Proof.Argon2.X86_64.AddressCache.Saved s) := by
  refine (VG.Proof.Argon2.X86_64.AddressCache.save_ok s hw).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx⟩
  have work' : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work
    rw [regs, mem, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
  have ready : AddressCalls.Ready t := by
    constructor
    · rw [rd, wr, regs]; exact h.frameRead
    · rw [work', wr]; exact h.workWrite
    · rw [regs, work']; exact h.frameWork
    · rw [regs]; exact h.frameStack
    · rw [regs, work']; exact h.stackWork
  refine ⟨mem, regs, rd, wr, mx, ready, work', ?_⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 8, 8⟩) (by simp) _
    (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : VG.Proof.Argon2.X86_64.AddressCache.Saved s t) (d : Nat)
    (hd : d + 8 ≤ 8 ∨ 16 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ hd (by omega) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old counter : Nat}
    (h : VG.Proof.Argon2.X86_64.AddressCache.Saved s t) (words : AddressHeader.Words p pass lane slice old s)
    (value : s.gpr .rax = BitVec.ofNat 64 counter) :
    AddressHeader.Words p pass lane slice counter t := by
  refine ⟨(h.read 0 (by decide) (by decide)).trans words.passWord,
    ?_, ?_, (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord, ?_⟩
  · rw [h.regs]; exact words.laneWord
  · rw [h.regs]; exact words.sliceWord
  · rw [h.regs, h.mem, Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Regenerate only when the public one-based block counter changes. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

def wanted (s : State) : Nat := (s.gpr .r15).toNat / 128 + 1

def writes (s : State) : List Region :=
  [⟨AddressCalls.work s, 8192⟩, below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 8, 8⟩]

structure Ready (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  cached : VG.Proof.Argon2.X86_64.AddressCache.counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64 →
    blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (VG.Proof.Argon2.X86_64.AddressCache.wanted s)

theorem ready_zero (p : Params) (pass lane slice : Nat) (s : State)
    (layout : AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : InRegions s.wr (off (s.gpr .rbp) 8) 8)
    (words : AddressHeader.Words p pass lane slice 0 s) : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice 0 s :=
  ⟨layout, reads, write, words, fun same => False.elim
    (VG.Proof.Argon2.X86_64.AddressCache.counter_ne_zero _ (same.trans words.counterWord))⟩

structure Selected (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  block : blockAt t.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (VG.Proof.Argon2.X86_64.AddressCache.wanted s)
  layout : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.AddressCache.writes s) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  counterWord : t.mem.readW (off (t.gpr .rbp) 8) 64 = VG.Proof.Argon2.X86_64.AddressCache.counter (s.gpr .r15)

theorem check_stable {s a : State} (h : AddressCalls.Ready s) (k : Divide.Keeps [.rax] s a) :
    AddressCalls.Stable s a := by
  apply AddressCalls.stable_of_frame h _ k.rd k.wr _ k.mxcsr
  · intro r hr
    apply k.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem selected_ok [CompressImpl] (p : Params) (pass lane slice old : Nat) (s : State)
    (h : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old s) :
    WP isa VG.Impl.Argon2.X86_64.AddressCache.select s (VG.Proof.Argon2.X86_64.AddressCache.Selected s · p pass lane slice) := by
  unfold VG.Impl.Argon2.X86_64.AddressCache.select
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCache.check_ok s (h.reads 8 (by simp))).mono ?_)
  rintro a ⟨value, flag, keeps⟩
  have stableA := VG.Proof.Argon2.X86_64.AddressCache.check_stable h.layout keeps
  refine WP.ite (decide (VG.Proof.Argon2.X86_64.AddressCache.counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64))
    (by simp only [eval, flag]) ?_ ?_
  · intro same
    have equal := of_decide_eq_true same
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, stableA.ready, stableA.work_eq, stableA.regs, keeps.rd, keeps.wr,
      ?_, ctl_eq_of keeps.mxcsr, ?_⟩
    · rw [keeps.mem]; exact h.cached equal
    · rw [keeps.mem]; exact Frame.refl _ _
    · rw [stableA.regs .rbp (by simp [calleeSaved]), keeps.mem]; exact equal.symm
  · intro _
    have write : InRegions a.wr (off (a.gpr .rbp) 8) 8 := by
      rw [keeps.wr, stableA.regs .rbp (by simp [calleeSaved])]; exact h.write
    refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCache.save_ready a stableA.ready write).mono ?_)
    intro b saved
    have words : AddressHeader.Words p pass lane slice (VG.Proof.Argon2.X86_64.AddressCache.wanted s) b := by
      apply saved.words (stableA.words h.layout h.words)
      rw [value, VG.Proof.Argon2.X86_64.AddressCache.counter_nat]; rfl
    have reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (b.rd ++ b.wr) (off (b.gpr .rbp) d) 8 := by
      rw [saved.rd, saved.wr, saved.regs]; exact stableA.reads h.reads
    refine (AddressCalls.code_ok p pass lane slice (VG.Proof.Argon2.X86_64.AddressCache.wanted s) b saved.ready reads words).mono ?_
    rintro t ⟨generated, mx⟩
    have workB : AddressCalls.work b = AddressCalls.work s := saved.work_eq.trans stableA.work_eq
    have regsB (r : Reg) (hr : r ∈ calleeSaved) : b.gpr r = s.gpr r :=
      (congrFun saved.regs r).trans (stableA.regs r hr)
    have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r :=
      fun r hr => (generated.regs r hr).trans (regsB r hr)
    have firstFrame : Frame (VG.Proof.Argon2.X86_64.AddressCache.writes s) s.mem b.mem := by
      have frame := saved.frame
      rw [stableA.regs .rbp (by simp [calleeSaved]), keeps.mem] at frame
      exact frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp [VG.Proof.Argon2.X86_64.AddressCache.writes])
    have finalFrame : Frame (VG.Proof.Argon2.X86_64.AddressCache.writes s) b.mem t.mem := by
      have frame := generated.frame
      rw [AddressCalls.writes, workB, regsB .rsp (by simp [calleeSaved])] at frame
      exact frame.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [VG.Proof.Argon2.X86_64.AddressCache.writes])
    refine ⟨?_, generated.ready, generated.work.trans workB, regs,
      generated.rd.trans (saved.rd.trans keeps.rd), generated.wr.trans (saved.wr.trans keeps.wr),
      firstFrame.trans finalFrame, mx.trans (ctl_eq_of (saved.mxcsr.trans keeps.mxcsr)), ?_⟩
    · have block := generated.block
      rw [workB] at block
      exact block
    · have preserved : t.mem.readW (off (b.gpr .rbp) 8) 64 = b.mem.readW (off (b.gpr .rbp) 8) 64 :=
        generated.frame.readW (r := ⟨b.gpr .rbp, 272⟩)
          (Offset.contains_base _ (by decide) (by decide)) (by
            intro r hr
            simp only [AddressCalls.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact saved.ready.frameWork
            · exact saved.ready.frameStack) (by decide)
      rw [generated.regs .rbp (by simp [calleeSaved]), preserved, saved.regs, saved.mem,
        Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.X86_64.AddressCache

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheWord`. -/
section

/-! Read exactly the public indexed word of the cached address block. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

def wordAddress (s : State) : Addr :=
  s.gpr .rcx + s.gpr .rax * BitVec.ofNat 64 8 + BitVec.ofInt 64 6144

theorem wordRead_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.AddressCache.wordAddress s) 8) :
    WP isa (.block wordRead) s fun t => t.gpr .rdi = s.mem.readW (VG.Proof.Argon2.X86_64.AddressCache.wordAddress s) 64 ∧
      Divide.Keeps [.rdi] s t := by
  dsimp only [VG.Proof.Argon2.X86_64.AddressCache.wordAddress] at hr
  apply WP.of_runBlock
  simp only [wordRead, VG.Proof.Argon2.X86_64.AddressCache.wordAddress, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, State.ea, hr, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem wordAddress_args {s a : State}
    (scratch : a.gpr .rcx = AddressCalls.work s)
    (index : a.gpr .rax = s.gpr .r15 &&& 127) :
    VG.Proof.Argon2.X86_64.AddressCache.wordAddress a = off (off (AddressCalls.work s) 6144) (8 * ((s.gpr .r15).toNat % 128)) := by
  unfold VG.Proof.Argon2.X86_64.AddressCache.wordAddress off
  rw [scratch, index, VG.Proof.Argon2.X86_64.AddressCache.index_nat, ← BitVec.ofNat_mul, Nat.mul_comm]
  change AddressCalls.work s + BitVec.ofNat 64 (8 * ((s.gpr .r15).toNat % 128)) +
    BitVec.ofNat 64 6144 = _
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .r15).toNat % 128)))
    (BitVec.ofNat 64 6144), ← BitVec.add_assoc]

theorem word_ok (s : State) (h : AddressCalls.Ready s) :
    WP isa Impl.Argon2.X86_64.AddressCache.word s fun t => t.gpr .rdi =
      (blockAt s.mem (off (AddressCalls.work s) 6144))[(s.gpr .r15).toNat % 128]'(Nat.mod_lt _ (by decide)) ∧
      Divide.Keeps [.rcx, .rax, .rdi] s t := by
  unfold Impl.Argon2.X86_64.AddressCache.word
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCache.wordArgs_ok s h.frameRead).mono ?_)
  rintro a ⟨scratch, index, keeps⟩
  have address := VG.Proof.Argon2.X86_64.AddressCache.wordAddress_args scratch index
  have read : InRegions (a.rd ++ a.wr) (VG.Proof.Argon2.X86_64.AddressCache.wordAddress a) 8 := by
    rw [address, keeps.rd, keeps.wr]
    have cover := AddressCalls.work_cover s h 6144 1024 (by decide)
    have writable := cover _ _ ⟨⟨off (AddressCalls.work s) 6144, 1024⟩, by simp,
      Offset.contains_base _ (d := 8 * ((s.gpr .r15).toNat % 128)) (n := 8) (k := 1024)
        (by have := Nat.mod_lt (s.gpr .r15).toNat (by decide : 0 < 128); omega) (by omega)⟩
    obtain ⟨r, hr, hc⟩ := writable
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (VG.Proof.Argon2.X86_64.AddressCache.wordRead_ok a read).mono ?_
  rintro t ⟨value, tail⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
  rw [value, address, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨_, Nat.mod_lt _ (by decide)⟩ : Fin 128)]
  rw [blockAt_get]

end VG.Proof.Argon2.X86_64.AddressCache

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderLit`. -/
section

/-! Checked literal of the independent-address input header. -/

namespace VG

materialize_code Impl.Argon2.X86_64.AddressHeader.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSteps`. -/
section

/-! # Public pointer advances and lane countdowns -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64

structure Advanced (s t : State) : Prop where
  destination : t.gpr .r14 = s.gpr .r14 + 1024
  other : ∀ r, r ≠ .r14 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .r14 (.imm 1024)]) s (VG.Proof.Argon2.X86_64.MemoryInit.Advanced s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left',
    show (BitVec.signExtend 64 (1024 : BitVec 32)) = 1024 from rfl]
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hr, ite_false]

structure LaneEnd (s t : State) : Prop where
  destination : t.gpr .r14 = s.gpr .r14 + s.gpr .r13 - 1024
  lane : t.gpr .r12 = s.gpr .r12 + 1
  remaining : t.gpr .r15 = s.gpr .r15 - 1
  zf : t.zf = some (s.gpr .r15 - 1 == 0)
  other : ∀ r, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem laneEnd_ok (s : State) :
    WP isa (.block [.alu .add .r14 (.reg .r13), .alu .sub .r14 (.imm 1024),
      .alu .add .r12 (.imm 1), .alu .sub .r15 (.imm 1)]) s (VG.Proof.Argon2.X86_64.MemoryInit.LaneEnd s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left',
    show (BitVec.signExtend 64 (1024 : BitVec 32)) = 1024 from rfl,
    show (BitVec.signExtend 64 (1 : BitVec 32)) = 1 from rfl]
  refine ⟨rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, h1, h2, h3, ite_false]

end VG.Proof.Argon2.X86_64.MemoryInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitScale`. -/
section

/-! # Fixed public scaling by powers of two using baseline additions -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64

structure Scaled (s t : State) (r : Reg) (n : Nat) : Prop where
  value : t.gpr r = s.gpr r * BitVec.ofNat 64 (2 ^ n)
  other : ∀ q, q ≠ r → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem double_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add r (.reg r)]) s fun t =>
      t.gpr r = s.gpr r + s.gpr r ∧ (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, ite_true]
  · simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hr, ite_false]

theorem scale_ok (s : State) (r : Reg) (n : Nat) :
    WP isa (.block (List.replicate n (.alu .add r (.reg r)))) s fun t => VG.Proof.Argon2.X86_64.MemoryInit.Scaled s t r n := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨by rw [Nat.pow_zero]; exact (BitVec.mul_one _).symm,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    change WP isa (.block (([.alu .add r (.reg r)] : List Instr) ++
      List.replicate n (.alu .add r (.reg r)))) s _
    rw [WP.block_append_iff]
    refine (VG.Proof.Argon2.X86_64.MemoryInit.double_ok s r).mono ?_
    rintro a ⟨value, other, mem, rd, wr⟩
    refine (ih a).mono ?_
    intro t ht
    refine ⟨?_, fun q hq => (ht.other q hq).trans (other q hq),
      ht.mem.trans mem, ht.rd.trans rd, ht.wr.trans wr⟩
    rw [ht.value, value, ← BitVec.mul_two, Nat.pow_succ, BitVec.ofNat_mul,
      BitVec.mul_assoc]
    exact congrArg (fun v => s.gpr r * v) (BitVec.mul_comm _ _)

end VG.Proof.Argon2.X86_64.MemoryInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.BlockAddress`. -/
section

/-! Fault-free matrix pointer calculation, with no memory accesses. -/

namespace VG.Proof.Argon2.X86_64.BlockAddress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.BlockAddress

theorem flatten_ok (s : State) : WP isa (.block flatten) s fun t =>
    t.gpr .rax = s.gpr .rax * s.gpr .r12 + s.gpr .rcx ∧
    Divide.Keeps [.rax, .rdx] s t := by
  apply WP.of_runBlock
  simp only [flatten, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execMul, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.some.injEq,
    exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2, ite_false]
  all_goals rfl

theorem scale_ok (s : State) : WP isa (.block scale) s fun t =>
    t.gpr .rax = s.gpr .rax * 1024 ∧ Divide.Keeps [.rax] s t := by
  refine WP.mono_mx (by decide +kernel) (MemoryInit.scale_ok s .rax 10) ?_
  intro t h mx
  refine ⟨h.value, ?_, h.mem, h.rd, h.wr, mx⟩
  intro r hr
  exact h.other r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)

theorem base_ok (s : State) : WP isa (.block [.alu .add .rax (.reg .r8)]) s fun t =>
    t.gpr .rax = s.gpr .rax + s.gpr .r8 ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [ite_true], ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.BlockAddress.code s fun t =>
    t.gpr .rax = (s.gpr .rax * s.gpr .r12 + s.gpr .rcx) * 1024 + s.gpr .r8 ∧
    Divide.Keeps [.rax, .rdx] s t := by
  unfold VG.Impl.Argon2.X86_64.BlockAddress.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.BlockAddress.flatten_ok s).mono ?_)
  rintro a ⟨flat, ka⟩
  refine WP.seq ((VG.Proof.Argon2.X86_64.BlockAddress.scale_ok a).mono ?_)
  rintro b ⟨scaled, kb⟩
  refine (VG.Proof.Argon2.X86_64.BlockAddress.base_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ka.trans ((kb.mono (by simp)).trans (kt.mono (by simp)))⟩
  rw [result, scaled, flat, kb.regs .r8 (by decide), ka.regs .r8 (by decide)]

theorem code_nat_ok (s : State) (lane column q : Nat)
    (hl : s.gpr .rax = BitVec.ofNat 64 lane)
    (hc : s.gpr .rcx = BitVec.ofNat 64 column)
    (hq : s.gpr .r12 = BitVec.ofNat 64 q) :
    WP isa VG.Impl.Argon2.X86_64.BlockAddress.code s fun t =>
      t.gpr .rax = s.gpr .r8 + BitVec.ofNat 64 ((lane * q + column) * 1024) ∧
      Divide.Keeps [.rax, .rdx] s t := by
  refine (VG.Proof.Argon2.X86_64.BlockAddress.code_ok s).mono ?_
  rintro t ⟨h, k⟩
  refine ⟨?_, k⟩
  rw [h, hl, hc, hq, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  change BitVec.ofNat 64 (lane * q + column) * BitVec.ofNat 64 1024 + s.gpr .r8 = _
  rw [← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_secret_rel : RelCT isa (fun _ _ => True) VG.Impl.Argon2.X86_64.BlockAddress.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.BlockAddress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit`. -/
section

/-! Checked literal of a complete address-generation block clear. -/

namespace VG

materialize_code Impl.Argon2.X86_64.ClearBlock.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit`. -/
section

/-! A checked literal for the block write after compression. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FillWrite.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillCompress`. -/
section

/-! The complete compression/update sequence from allocation and frame invariants. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillCompress

def writes (s : State) : List Region :=
  [⟨s.gpr .r10, 1024⟩, ⟨VG.Proof.Argon2.X86_64.FillCompress.work s + 4096, 1024⟩, ⟨VG.Proof.Argon2.X86_64.FillCompress.work s, 4096⟩,
    below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 16, 8⟩]

structure Done (s t : State) : Prop where
  block : blockAt t.mem (s.gpr .r10) =
    let next := Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    if VG.Proof.Argon2.X86_64.FillCompress.pass s = 0 then next else xorBlock next (blockAt s.mem (s.gpr .r10))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.FillCompress.writes s) s.mem t.mem

theorem code_mx_ok [CompressImpl] (s : State) (h : VG.Proof.Argon2.X86_64.FillCompress.Ready s) :
    WP isa VG.Impl.Argon2.X86_64.FillCompress.code s fun t => VG.Proof.Argon2.X86_64.FillCompress.Done s t ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold VG.Impl.Argon2.X86_64.FillCompress.code
  refine WP.seq ((WP.with_mx (by lit_decide) (VG.Proof.Argon2.X86_64.FillCompress.setup_ok s h)).mono ?_)
  rintro a ⟨prepared, mx1⟩
  refine (VG.Proof.Argon2.X86_64.FillCompress.operation_ok a prepared.ready).mono ?_
  rintro t ⟨done, mx2⟩
  refine ⟨⟨?_, fun r hr => (done.regs r hr).trans (prepared.regs r hr),
    done.rd.trans prepared.rd, done.wr.trans prepared.wr, ?_⟩, by rw [mx2, mx1]⟩
  · have block := done.block
    rw [prepared.oldBlock, prepared.dest, prepared.counter, prepared.leftBlock,
      prepared.rightBlock] at block
    exact block
  · have frame : Frame (VG.Proof.Argon2.X86_64.FillCompress.writes s) a.mem t.mem := by
      have original := done.frame
      rw [prepared.dest] at original
      simp only [VG.Proof.Argon2.X86_64.FillCompress.callWrites, prepared.output, prepared.scratch,
        prepared.regs .rsp (by simp [calleeSaved])] at original
      exact original.mono (by intro r hr; exact List.mem_append_left _ hr)
    have savedFrame : Frame (VG.Proof.Argon2.X86_64.FillCompress.writes s) s.mem a.mem := prepared.frame.mono (by
      intro r hr
      simp only [VG.Proof.Argon2.X86_64.FillCompress.prefixWrites, List.mem_singleton] at hr
      subst r
      simp [VG.Proof.Argon2.X86_64.FillCompress.writes])
    exact savedFrame.trans frame

end VG.Proof.Argon2.X86_64.FillCompress

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ReferenceCount`. -/
section

/-! Merged from `Proof.Argon2.X86_64.SelectWindow`. -/
section
/-! # Same-lane window selection with no leakage from the equality test -/

namespace VG.Proof.Argon2.X86_64.SelectWindow

open VG VG.X86_64 VG.Impl.Argon2.X86_64.SelectWindow

theorem equality_test (x y : Addr) : (x ^^^ y).toNat < 1 ↔ x = y := by
  constructor
  · intro h
    have zero : x ^^^ y = 0 := by
      apply BitVec.eq_of_toNat_eq
      change (x ^^^ y).toNat = 0
      omega
    exact BitVec.xor_eq_zero_iff.mp zero
  · intro h
    rw [h, BitVec.xor_self]
    decide

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.SelectWindow.code s fun t =>
    t.gpr .r8 = (if s.gpr .rdi = s.gpr .rsi then s.gpr .rdx else s.gpr .rcx) ∧
    Divide.Keeps [.rax, .r8, .rdx] s t := by
  unfold VG.Impl.Argon2.X86_64.SelectWindow.code
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show (1 : Addr).toNat = 1 from rfl, VG.Proof.Argon2.X86_64.SelectWindow.equality_test, Divide.sbb_mask, Divide.select_value, decide_eq_true_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem code_secret_rel : RelCT isa (fun _ _ => True) VG.Impl.Argon2.X86_64.SelectWindow.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.SelectWindow
end

/-! Merged from `Proof.Argon2.X86_64.CountCandidatesLit`. -/
section
/-! A checked literal for reference-window candidate arithmetic. -/

namespace VG

materialize_code Impl.Argon2.X86_64.CountCandidates.code

end VG
end

/-! Merged from `Proof.Argon2.X86_64.CountCandidatesCT`. -/
section
/-! Only the public pass affects reference-window arithmetic's trace. -/

namespace VG.Proof.Argon2.X86_64.CountCandidates

open VG VG.X86_64 VG.Impl.Argon2.X86_64.CountCandidates

theorem code_rel : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9) VG.Impl.Argon2.X86_64.CountCandidates.code
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r9])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.CountCandidates
end

/-! The selected reference window, with public pass control only. -/

namespace VG.Proof.Argon2.X86_64.ReferenceCount

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceCount

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.ReferenceCount.code s fun t =>
    t.gpr .r8 = (if s.gpr .rdi = s.gpr .rsi then
      CountCandidates.base s + s.gpr .r15 - 1 else
      CountCandidates.base s + Divide.mask (decide ((s.gpr .r15).toNat < 1))) ∧
    Divide.Keeps CountCandidates.changed s t := by
  unfold VG.Impl.Argon2.X86_64.ReferenceCount.code
  refine WP.seq ((CountCandidates.code_ok s).mono ?_)
  rintro a ⟨same, other, keeps⟩
  refine (SelectWindow.code_ok a).mono ?_
  rintro t ⟨out, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [out, keeps.regs .rdi (by decide), keeps.regs .rsi (by decide), same, other]

theorem same_word (b i : Nat) (positive : 0 < b + i) :
    BitVec.ofNat 64 b + BitVec.ofNat 64 i - (1 : Addr) =
      BitVec.ofNat 64 (b + i - 1) := by
  rw [← BitVec.ofNat_add]
  change BitVec.ofNat 64 (b + i) - BitVec.ofNat 64 1 = _
  exact Offset.ofNat_sub_ofNat (by omega)

theorem other_word (b i : Nat) (bound : i < 2 ^ 64) (positive : i = 0 → 0 < b) :
    BitVec.ofNat 64 b + Divide.mask (decide ((BitVec.ofNat 64 i).toNat < 1)) =
      BitVec.ofNat 64 (b - (if i = 0 then 1 else 0)) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  by_cases zero : i = 0
  · simp only [zero, show decide ((0 : Nat) < 1) = true from rfl, Divide.mask, ite_true]
    rw [BitVec.add_neg_eq_sub]
    change BitVec.ofNat 64 b - BitVec.ofNat 64 1 = _
    exact Offset.ofNat_sub_ofNat (by have := positive zero; omega)
  · have notSmall : ¬i < 1 := by omega
    simp only [notSmall, decide_false, Divide.mask, Bool.false_eq_true, ite_false,
      zero, Nat.sub_zero]
    change BitVec.ofNat 64 b + 0#64 = BitVec.ofNat 64 b
    rw [BitVec.add_zero]

theorem selected_word (b i : Nat) (same : Bool) (bound : i < 2 ^ 64)
    (positive : 0 < b + i) (atZero : i = 0 → 0 < b) :
    (if same then BitVec.ofNat 64 b + BitVec.ofNat 64 i - (1 : Addr) else
      BitVec.ofNat 64 b + Divide.mask (decide ((BitVec.ofNat 64 i).toNat < 1))) =
      BitVec.ofNat 64 (if same then b + i - 1 else b - (if i = 0 then 1 else 0)) := by
  cases same
  · exact VG.Proof.Argon2.X86_64.ReferenceCount.other_word b i bound atZero
  · exact VG.Proof.Argon2.X86_64.ReferenceCount.same_word b i positive

theorem spec_count (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      let b := if pass = 0 then slice * p.segmentLen else p.laneLen - p.segmentLen
      if same then b + index - 1 else b - (if index = 0 then 1 else 0) := by
  unfold Spec.Argon2.referenceCount
  by_cases firstPass : pass = 0 <;> cases same <;>
    simp only [firstPass, ite_true, ite_false, Bool.false_eq_true]

def windowBase (p : Spec.Argon2.Params) (pass slice : Nat) : Nat :=
  if pass = 0 then slice * p.segmentLen else p.laneLen - p.segmentLen

theorem base_nat (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (passReg : (s.gpr .r9).toNat = pass)
    (laneReg : s.gpr .r12 = BitVec.ofNat 64 p.laneLen)
    (segmentReg : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen)
    (sliceReg : s.gpr .r14 = BitVec.ofNat 64 slice)
    (segmentBound : p.segmentLen ≤ p.laneLen) :
    CountCandidates.base s = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceCount.windowBase p pass slice) := by
  have isZero : s.gpr .r9 = 0 ↔ pass = 0 := by
    rw [← passReg]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      exact h
  unfold CountCandidates.base VG.Proof.Argon2.X86_64.ReferenceCount.windowBase
  by_cases firstPass : pass = 0
  · simp only [isZero, firstPass, ite_true]
    rw [segmentReg, sliceReg, ← BitVec.ofNat_mul, Nat.mul_comm]
  · simp only [isZero, firstPass, ite_false]
    rw [laneReg, segmentReg]
    exact Offset.ofNat_sub_ofNat segmentBound

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass slice index : Nat)
    (passReg : (s.gpr .r9).toNat = pass)
    (laneReg : s.gpr .r12 = BitVec.ofNat 64 p.laneLen)
    (segmentReg : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen)
    (sliceReg : s.gpr .r14 = BitVec.ofNat 64 slice)
    (indexReg : s.gpr .r15 = BitVec.ofNat 64 index)
    (segmentBound : p.segmentLen ≤ p.laneLen) (indexBound : index < 2 ^ 64)
    (positive : 0 < VG.Proof.Argon2.X86_64.ReferenceCount.windowBase p pass slice + index)
    (atZero : index = 0 → 0 < VG.Proof.Argon2.X86_64.ReferenceCount.windowBase p pass slice) :
    WP isa VG.Impl.Argon2.X86_64.ReferenceCount.code s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (Spec.Argon2.referenceCount p pass slice index
        (decide (s.gpr .rdi = s.gpr .rsi))) ∧
      Divide.Keeps CountCandidates.changed s t := by
  refine (VG.Proof.Argon2.X86_64.ReferenceCount.code_ok s).mono ?_
  rintro t ⟨out, keeps⟩
  refine ⟨out.trans ?_, keeps⟩
  rw [VG.Proof.Argon2.X86_64.ReferenceCount.base_nat s p pass slice passReg laneReg segmentReg sliceReg segmentBound, indexReg,
    VG.Proof.Argon2.X86_64.ReferenceCount.spec_count]
  simpa only [decide_eq_true_eq, VG.Proof.Argon2.X86_64.ReferenceCount.windowBase] using
    VG.Proof.Argon2.X86_64.ReferenceCount.selected_word (VG.Proof.Argon2.X86_64.ReferenceCount.windowBase p pass slice) index
      (decide (s.gpr .rdi = s.gpr .rsi)) indexBound positive atZero

theorem code_rel : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9) VG.Impl.Argon2.X86_64.ReferenceCount.code
    (fun _ _ => True) :=
  CountCandidates.code_rel.seq SelectWindow.code_secret_rel

end VG.Proof.Argon2.X86_64.ReferenceCount

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapState`. -/
section

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapArgs`. -/
section
/-! Register preparation for the reference-index stages. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem pass_ea (s : State) : s.ea { base := .rbp } = s.gpr .rbp := by
  change s.gpr .rbp + 0#64 = s.gpr .rbp
  exact BitVec.add_zero _

theorem loadPass_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp) 8) :
    WP isa (.block loadPass) s fun t =>
      t.gpr .r9 = s.mem.readW (s.gpr .rbp) 64 ∧ Divide.Keeps [.r9] s t := by
  apply WP.of_runBlock
  simp only [loadPass, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    VG.Proof.Argon2.X86_64.ReferenceMap.pass_ea, State.load64, read, ite_true, Option.map_some, RegUpd.gpr_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem laneArgs_ok (s : State) : WP isa (.block laneArgs) s fun t =>
    t.gpr .rdi = s.gpr .r8 ∧ t.gpr .rsi = s.gpr .rbx ∧
    Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [laneArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem relativeArgs_ok (s : State) : WP isa (.block relativeArgs) s fun t =>
    t.gpr .r9 = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .r11 ∧ t.gpr .rsi = s.gpr .r8 ∧
    Divide.Keeps [.r9, .rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [relativeArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem wrapArgs_ok (s : State) : WP isa (.block wrapArgs) s fun t =>
    t.gpr .rdi = s.gpr .rax + s.gpr .r10 ∧ t.gpr .rsi = s.gpr .r12 ∧
    Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [wrapArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Parameters and register invariants for the complete reference mapping. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64

/-- Every stage preserves the enclosing loop's callee-saved registers. -/
def changed : List Reg := [.rax, .rdx, .rcx, .r8, .r9, .r10, .r11, .rdi, .rsi]

structure Bounds (p : Spec.Argon2.Params) (pass lane slice index : Nat) : Prop where
  lanesPositive : 0 < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  memoryMinimum : 8 * p.lanes ≤ p.memory
  memoryBound : p.memory < 2 ^ 32
  passBound : pass < 2 ^ 32
  laneBound : lane < p.lanes
  sliceBound : slice < 4
  indexBound : index < p.segmentLen
  active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index

structure Position (p : Spec.Argon2.Params) (lane slice index : Nat) (s : State) : Prop where
  current : s.gpr .rbx = BitVec.ofNat 64 lane
  laneLength : s.gpr .r12 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen
  slice : s.gpr .r14 = BitVec.ofNat 64 slice
  index : s.gpr .r15 = BitVec.ofNat 64 index

theorem Position.of_keeps {s t : State} {p : Spec.Argon2.Params} {lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Position p lane slice index s) (k : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t) :
    VG.Proof.Argon2.X86_64.ReferenceMap.Position p lane slice index t :=
  ⟨(k.regs .rbx (by decide)).trans h.current,
    (k.regs .r12 (by decide)).trans h.laneLength,
    (k.regs .r13 (by decide)).trans h.segmentLength,
    (k.regs .r14 (by decide)).trans h.slice,
    (k.regs .r15 (by decide)).trans h.index⟩

structure Ready (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s : State) : Prop where
  bounds : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index
  position : VG.Proof.Argon2.X86_64.ReferenceMap.Position p lane slice index s
  lanes : s.gpr .rsi = BitVec.ofNat 64 p.lanes
  passRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp) 8
  passWord : s.mem.readW (s.gpr .rbp) 64 = BitVec.ofNat 64 pass

theorem Ready.lanes_nat {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s : State}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s) : (s.gpr .rsi).toNat = p.lanes := by
  rw [h.lanes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bounds.lanesBound (by decide))]

theorem Ready.of_keeps {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s) (k : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t)
    (lanes : t.gpr .rsi = s.gpr .rsi) : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index t := by
  refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanes, ?_, ?_⟩
  · rw [k.rd, k.wr, k.regs .rbp (by decide)]
    exact h.passRead
  · rw [k.mem, k.regs .rbp (by decide)]
    exact h.passWord

def chosenLane (p : Spec.Argon2.Params) (pass lane slice : Nat) (random : Addr) : Nat :=
  if pass = 0 ∧ slice = 0 then lane else (random >>> 32).toNat % p.lanes

theorem chosenLane_bound (p : Spec.Argon2.Params) (pass lane slice : Nat) (random : Addr)
    (positive : 0 < p.lanes) (bound : lane < p.lanes) :
    VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice random < p.lanes := by
  unfold VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane
  split
  · exact bound
  · exact Nat.mod_lt _ positive

theorem word_nat (n : Nat) (bound : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem word_zero (n : Nat) (bound : n < 2 ^ 64) : BitVec.ofNat 64 n = (0 : Addr) ↔ n = 0 := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [VG.Proof.Argon2.X86_64.ReferenceMap.word_nat n bound] at hn
    exact hn
  · intro h; rw [h]; rfl

theorem word_eq (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [VG.Proof.Argon2.X86_64.ReferenceMap.word_nat x hx, VG.Proof.Argon2.X86_64.ReferenceMap.word_nat y hy] at hn
    exact hn
  · intro h; rw [h]

theorem Bounds.laneLength_bound {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) : p.laneLen < 2 ^ 32 := by
  have hb : p.laneLen ≤ p.blocks := by
    rw [Proof.Argon2.blocks_lanes p h.lanesPositive]
    exact Nat.le_mul_of_pos_left _ h.lanesPositive
  exact Nat.lt_of_le_of_lt (Nat.le_trans hb (Proof.Argon2.blocks_le_memory p)) h.memoryBound

theorem Bounds.window_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) :
    0 < ReferenceCount.windowBase p pass slice + index ∧
      (index = 0 → 0 < ReferenceCount.windowBase p pass slice) := by
  have hp := Proof.Argon2.reference_count_positive p h.lanesPositive h.memoryMinimum
    pass slice index true h.active (by intro _ _; rfl)
  rw [ReferenceCount.spec_count] at hp
  change 0 < ReferenceCount.windowBase p pass slice + index - 1 at hp
  constructor
  · omega
  · intro zero; rw [zero, Nat.add_zero] at hp; omega

def windowSize (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) : Nat :=
  Spec.Argon2.referenceCount p pass slice index (VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice random == lane)

def windowStart (p : Spec.Argon2.Params) (pass slice : Nat) : Nat :=
  if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen

def relativeValue (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) : Nat :=
  let count := VG.Proof.Argon2.X86_64.ReferenceMap.windowSize p pass lane slice index random
  let j := (random &&& 0xffffffff).toNat
  count - 1 - count * (j * j / 2 ^ 32) / 2 ^ 32

theorem Bounds.segment_le_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) : p.segmentLen ≤ p.laneLen := by
  have segments := Proof.Argon2.laneLen_segments p h.lanesPositive
  omega

theorem Bounds.index_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) : index < 2 ^ 64 :=
  Nat.lt_trans (Nat.lt_of_lt_of_le h.indexBound h.segment_le_lane)
    (Nat.lt_trans h.laneLength_bound (by decide))

theorem Bounds.chosenLane_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice random < 2 ^ 64 :=
  Nat.lt_trans (VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane_bound p pass lane slice random h.lanesPositive h.laneBound)
    (Nat.lt_trans h.lanesBound (by decide))

theorem Bounds.lane_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) : lane < 2 ^ 64 :=
  Nat.lt_trans h.laneBound (Nat.lt_trans h.lanesBound (by decide))

theorem Bounds.windowSize_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    0 < VG.Proof.Argon2.X86_64.ReferenceMap.windowSize p pass lane slice index random := by
  apply Proof.Argon2.reference_count_positive p h.lanesPositive h.memoryMinimum
    pass slice index _ h.active
  intro firstPass firstSlice
  simp only [VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane, firstPass, firstSlice, and_self, ite_true]
  exact beq_iff_eq.mpr rfl

theorem Bounds.windowSize_bound32 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    VG.Proof.Argon2.X86_64.ReferenceMap.windowSize p pass lane slice index random < 2 ^ 32 :=
  Proof.Argon2.reference_count_32 p h.lanesPositive h.memoryMinimum h.memoryBound
    pass slice index _ h.sliceBound h.indexBound

theorem Bounds.windowSize_lt_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    VG.Proof.Argon2.X86_64.ReferenceMap.windowSize p pass lane slice index random < p.laneLen :=
  Proof.Argon2.reference_count_lt_lane p h.lanesPositive h.memoryMinimum
    pass slice index _ h.sliceBound h.indexBound

theorem Bounds.laneLength_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) : 0 < p.laneLen := by
  have seg := Proof.Argon2.segmentLen_ge_two p h.lanesPositive h.memoryMinimum
  have len := Proof.Argon2.laneLen_segments p h.lanesPositive
  omega

theorem Bounds.windowStart_lt_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) : VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice < p.laneLen := by
  unfold VG.Proof.Argon2.X86_64.ReferenceMap.windowStart
  split
  · exact h.laneLength_positive
  · exact Nat.mod_lt _ h.laneLength_positive

theorem Bounds.sum_bound {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) (random : Addr) :
    VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue p pass lane slice index random < 2 * p.laneLen := by
  have start := h.windowStart_lt_lane
  have relative := Proof.Argon2.reference_relative_bound _ (random &&& 0xffffffff).toNat
    (h.windowSize_positive random)
  have count := h.windowSize_lt_lane random
  change VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue p pass lane slice index random < VG.Proof.Argon2.X86_64.ReferenceMap.windowSize p pass lane slice index random at relative
  omega

end VG.Proof.Argon2.X86_64.ReferenceMap

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Wrap`. -/
section

/-! # Masked subtraction agrees with wrapping the reference column -/

namespace VG.Proof.Argon2.X86_64.Wrap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Wrap

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.Wrap.code s fun t =>
    t.gpr .rdi = (if (s.gpr .rdi).toNat < (s.gpr .rsi).toNat
      then s.gpr .rdi else s.gpr .rdi - s.gpr .rsi) ∧
    Divide.Keeps [.rdi, .r10, .rax] s t := by
  unfold VG.Impl.Argon2.X86_64.Wrap.code
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg,     RegUpd.gpr_arithFlags,     RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, Divide.select_value, decide_eq_true_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]
  all_goals rfl

theorem wrap_nat (x q : Addr) (bound : x.toNat < 2 * q.toNat) :
    (if x.toNat < q.toNat then x else x - q) = BitVec.ofNat 64 (x.toNat % q.toNat) := by
  rw [Proof.Argon2.reference_wrap _ _ bound]
  by_cases small : x.toNat < q.toNat
  · rw [ite_eq_left small, ite_eq_left small]
    exact (BitVec.ofNat_toNat 64 x).symm
  · rw [ite_eq_right small, ite_eq_right small]
    calc
      x - q = BitVec.ofNat 64 x.toNat - BitVec.ofNat 64 q.toNat := by
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := Offset.ofNat_sub_ofNat (by omega)

theorem code_nat_ok (s : State) (bound : (s.gpr .rdi).toNat < 2 * (s.gpr .rsi).toNat) :
    WP isa VG.Impl.Argon2.X86_64.Wrap.code s fun t =>
      t.gpr .rdi = BitVec.ofNat 64 ((s.gpr .rdi).toNat % (s.gpr .rsi).toNat) ∧
      Divide.Keeps [.rdi, .r10, .rax] s t :=
  (VG.Proof.Argon2.X86_64.Wrap.code_ok s).mono (fun _ h => ⟨h.1.trans (VG.Proof.Argon2.X86_64.Wrap.wrap_nat _ _ bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun _ _ => True) VG.Impl.Argon2.X86_64.Wrap.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Wrap

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Relative`. -/
section

/-! # The baseline reference-window mapping is fixed time and preserves memory -/

namespace VG.Proof.Argon2.X86_64.Relative

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Relative

def value (random count : Addr) : Addr :=
  let j := random &&& 0xffffffff
  let x := (j * j) >>> 32
  let y := (x * count) >>> 32
  count - 1 - y

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.Relative.code s fun t =>
    t.gpr .rax = VG.Proof.Argon2.X86_64.Relative.value (s.gpr .rdi) (s.gpr .rsi) ∧
    (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold VG.Impl.Argon2.X86_64.Relative.code
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, readSrc, State.setReg32, execMul, execAlu, execShift,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, reduceCtorEq, and_self, ite_true, ite_false,
    show 1 ≤ (32 : Nat) ∧ (32 : Nat) ≤ 63 from by decide,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨?_, ?_, trivial⟩
  · rw [VG.Proof.Argon2.X86_64.low32]; rfl
  · intro r h1 h2 h3
    simp only [h1, h2, h3, ite_false]

theorem mul_shift_toNat (x y : Addr) (bound : x.toNat * y.toNat < 2 ^ 64) :
    ((x * y) >>> 32).toNat = x.toNat * y.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul,
    Nat.mod_eq_of_lt bound]

theorem value_nat (random count : Addr) (lo : 0 < count.toNat)
    (bound : count.toNat < 2 ^ 32) :
    VG.Proof.Argon2.X86_64.Relative.value random count = BitVec.ofNat 64
      (count.toNat - 1 - count.toNat * ((random &&& 0xffffffff).toNat *
        (random &&& 0xffffffff).toNat / 2 ^ 32) / 2 ^ 32) := by
  let j := random &&& 0xffffffff
  have hj : j.toNat < 2 ^ 32 := by
    have h32 := (random.setWidth 32).isLt
    rw [show j = (random.setWidth 32).setWidth 64 from (low32 random).symm,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    exact h32
  have hx := VG.Proof.Argon2.X86_64.Relative.mul_shift_toNat j j (Proof.Argon2.reference_square_bound _ hj)
  have product : ((j * j) >>> 32).toNat * count.toNat < 2 ^ 64 := by
    rw [hx, Nat.mul_comm]
    exact Proof.Argon2.reference_product_bound _ _ bound hj
  have hy := VG.Proof.Argon2.X86_64.Relative.mul_shift_toNat ((j * j) >>> 32) count product
  rw [hx, Nat.mul_comm] at hy
  have hyBound : count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32 < count.toNat :=
    Proof.Argon2.reference_scale_lt_count _ _ lo hj
  have hyWord : (((j * j) >>> 32) * count) >>> 32 = BitVec.ofNat 64
      (count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [hy, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold VG.Proof.Argon2.X86_64.Relative.value
  change count - 1 - ((((j * j) >>> 32) * count) >>> 32) = _
  rw [hyWord]
  change count - (1 : Addr) - BitVec.ofNat 64
    (count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32) = _
  have countWord : count = BitVec.ofNat 64 count.toNat := by
    exact (BitVec.ofNat_toNat 64 count).symm
  have countSub : count - 1 = BitVec.ofNat 64 (count.toNat - 1) := by
    calc
      count - 1 = BitVec.ofNat 64 count.toNat - BitVec.ofNat 64 1 :=
        congrArg (fun x : Addr => x - 1) countWord
      _ = _ := Offset.ofNat_sub_ofNat (by omega)
  rw [countSub, Offset.ofNat_sub_ofNat (by omega)]

theorem code_nat_ok (s : State) (lo : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.X86_64.Relative.code s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        ((s.gpr .rsi).toNat - 1 - (s.gpr .rsi).toNat *
          ((s.gpr .rdi &&& 0xffffffff).toNat * (s.gpr .rdi &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  (VG.Proof.Argon2.X86_64.Relative.code_ok s).mono (fun _ h => ⟨h.1.trans (VG.Proof.Argon2.X86_64.Relative.value_nat _ _ lo bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun _ _ => True) VG.Impl.Argon2.X86_64.Relative.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Relative

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Divide`. -/
section

/-! # Complete fixed-time division for Argon2's indices -/

namespace VG.Proof.Argon2.X86_64.Divide

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Divide

theorem prefix_step (x : BitVec 64) (j : Nat) :
    x.toNat / 2 ^ j = 2 * (x.toNat / 2 ^ (j + 1)) + (x.getLsbD j).toNat := by
  have h := Nat.mod_add_div (x.toNat / 2 ^ j) 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ] at h
  simp only [Nat.succ_eq_add_one] at h
  simp only [← BitVec.testBit_toNat, Nat.toNat_testBit]
  omega

def changed : List Reg := [.rcx, .r8, .r10, .rax, .r9]

/-- The already-consumed prefix equals quotient times divisor plus remainder. -/
structure Invariant (n : Nat) (s : State) : Prop where
  numerator : (s.gpr .rdi).toNat < 2 ^ 32
  divisor : 0 < (s.gpr .rsi).toNat
  divisorBound : (s.gpr .rsi).toNat < 2 ^ 32
  remainder : (s.gpr .r8).toNat < (s.gpr .rsi).toNat
  equation : (s.gpr .rdi).toNat / 2 ^ n =
    (s.gpr .r9).toNat * (s.gpr .rsi).toNat + (s.gpr .r8).toNat

theorem bit_invariant (s : State) (n : Nat) (hn : n < 32) (h : VG.Proof.Argon2.X86_64.Divide.Invariant (n + 1) s) :
    WP isa (.block (VG.Impl.Argon2.X86_64.Divide.bit n)) s fun t => VG.Proof.Argon2.X86_64.Divide.Invariant n t ∧ VG.Proof.Argon2.X86_64.Divide.Keeps VG.Proof.Argon2.X86_64.Divide.changed s t := by
  have hqmul := Nat.le_mul_of_pos_right (s.gpr .r9).toNat h.divisor
  have hprefix := Nat.div_le_self (s.gpr .rdi).toNat (2 ^ (n + 1))
  have he := h.equation
  have hb := h.numerator
  have hq : (s.gpr .r9).toNat < 2 ^ 32 := by omega
  have hr : (s.gpr .r8).toNat < 2 ^ 32 := Nat.lt_trans h.remainder h.divisorBound
  refine (VG.Proof.Argon2.X86_64.Divide.bit_ok s n hn hr hq).mono ?_
  rintro t ⟨ht8, ht9, ht⟩
  have hdi := ht.regs .rdi (by decide)
  have hsi := ht.regs .rsi (by decide)
  have hs := VG.Proof.Argon2.divide_step h.equation h.remainder
    (Bool.toNat_le ((s.gpr .rdi).getLsbD n))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ht⟩
  · rw [hdi]; exact h.numerator
  · rw [hsi]; exact h.divisor
  · rw [hsi]; exact h.divisorBound
  · rw [ht8, hsi]; exact hs.2
  · rw [hdi, hsi, ht8, ht9, VG.Proof.Argon2.X86_64.Divide.prefix_step]
    exact hs.1

theorem bits_ok (n : Nat) (hn : n ≤ 32) (s : State) (h : VG.Proof.Argon2.X86_64.Divide.Invariant n s) :
    WP isa (.block ((List.range n).reverse.flatMap VG.Impl.Argon2.X86_64.Divide.bit)) s fun t =>
      VG.Proof.Argon2.X86_64.Divide.Invariant 0 t ∧ VG.Proof.Argon2.X86_64.Divide.Keeps VG.Proof.Argon2.X86_64.Divide.changed s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨h, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine (VG.Proof.Argon2.X86_64.Divide.bit_invariant s n (by omega) h).mono ?_
    rintro t ⟨ht, kt⟩
    refine (ih (by omega) t ht).mono ?_
    rintro u ⟨hu, ku⟩
    exact ⟨hu, kt.trans ku⟩

theorem setup_ok (s : State) (hn : (s.gpr .rdi).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .rsi).toNat) (hd' : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa (.block [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0),
      .mov32 .rax (.imm 0), .alu .cmp .rax (.imm 0)]) s fun t =>
      VG.Proof.Argon2.X86_64.Divide.Invariant 32 t ∧ VG.Proof.Argon2.X86_64.Divide.Keeps VG.Proof.Argon2.X86_64.Divide.changed s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, State.setReg32, VG.X86_64.readSrc, execAlu,
    RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hn, hd, hd', ?_, ?_⟩, ?_⟩
  · exact hd
  · change (s.gpr .rdi).toNat / 2 ^ 32 = 0 * (s.gpr .rsi).toNat + 0
    rw [Nat.div_eq_of_lt hn, Nat.zero_mul, Nat.zero_add]
  · constructor
    · intro r hr
      simp only [VG.Proof.Argon2.X86_64.Divide.changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    all_goals rfl

theorem code_ok (s : State) (hn : (s.gpr .rdi).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .rsi).toNat) (hd' : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.X86_64.Divide.code s fun t =>
      (t.gpr .r9).toNat = (s.gpr .rdi).toNat / (s.gpr .rsi).toNat ∧
      (t.gpr .r8).toNat = (s.gpr .rdi).toNat % (s.gpr .rsi).toNat ∧
      VG.Proof.Argon2.X86_64.Divide.Keeps VG.Proof.Argon2.X86_64.Divide.changed s t := by
  rw [VG.Impl.Argon2.X86_64.Divide.code, WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Divide.setup_ok s hn hd hd').mono ?_
  rintro u ⟨hu, ku⟩
  refine (VG.Proof.Argon2.X86_64.Divide.bits_ok 32 (by decide) u hu).mono ?_
  rintro t ⟨ht, kt⟩
  have k := ku.trans kt
  have he := ht.equation
  simp only [Nat.pow_zero, Nat.div_one] at he
  obtain ⟨hq, hr⟩ := VG.Proof.Argon2.divide_result ht.divisor he ht.remainder
  rw [k.regs .rdi (by decide), k.regs .rsi (by decide)] at hq hr
  exact ⟨hq, hr, k⟩

end VG.Proof.Argon2.X86_64.Divide

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DivideCT`. -/
section

/-! Merged from `Proof.Argon2.X86_64.DivideLit`. -/
section
/-! A checked literal for the unrolled index-division code. -/

namespace VG

materialize_code Impl.Argon2.X86_64.Divide.code

end VG
end

/-! # Constant-time index division, including secret numerators -/

namespace VG.Proof.Argon2.X86_64.Divide

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Divide

/-- Neither operand changes the execution trace. Public inputs additionally
produce public outputs for the parameter-setup divisions. -/
theorem code_rel :
    RelCT isa (fun s t => s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi)
      VG.Impl.Argon2.X86_64.Divide.code (fun s t => ∀ r ∈ [Reg.r8, .r9], s.gpr r = t.gpr r) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) [.r8, .r9] (by taint_decide)

theorem code_secret_rel : RelCT isa (fun _ _ => True) VG.Impl.Argon2.X86_64.Divide.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Divide

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapLane`. -/
section

/-! Merged from `Proof.Argon2.X86_64.ReferenceLane`. -/
section
/-! # Secret J₂ does not affect the lane-selection trace -/

namespace VG.Proof.Argon2.X86_64.ReferenceLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceLane

structure Prefix (s t : State) : Prop where
  high : t.gpr .rdi = s.gpr .rdi >>> 32
  original : t.gpr .r11 = s.gpr .rdi
  keeps : Divide.Keeps [.rdi, .r11] s t

theorem highArgs_ok (s : State) : WP isa (.block highArgs) s (VG.Proof.Argon2.X86_64.ReferenceLane.Prefix s) := by
  apply WP.of_runBlock
  simp only [highArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, RegUpd.gpr_setReg,
    show 1 ≤ (32 : Nat) ∧ (32 : Nat) ≤ 63 from by decide,
    and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  all_goals rfl

def changed : List Reg := [.rdi, .r11] ++ Divide.changed

theorem code_ok (s : State) (lo : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.X86_64.ReferenceLane.code s fun t =>
      (t.gpr .r8).toNat = (s.gpr .rdi >>> 32).toNat % (s.gpr .rsi).toNat ∧
      t.gpr .r11 = s.gpr .rdi ∧ Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceLane.changed s t := by
  unfold VG.Impl.Argon2.X86_64.ReferenceLane.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceLane.highArgs_ok s).mono ?_)
  intro a ha
  have si := ha.keeps.regs .rsi (by decide)
  refine (Divide.code_ok a ?_ (by rw [si]; exact lo) (by rw [si]; exact bound)).mono ?_
  · rw [ha.high]
    simpa only [show 64 - 32 = (32 : Nat) from rfl] using
      BitVec.toNat_ushiftRight_lt (s.gpr .rdi) 32 (by decide)
  · intro t ht
    refine ⟨?_, ?_, (ha.keeps.mono ?_).trans (ht.2.2.mono ?_)⟩
    · rw [ht.2.1, ha.high, si]
    · exact (ht.2.2.regs .r11 (by decide)).trans ha.original
    · intro r hr; exact List.mem_append_left _ hr
    · intro r hr; exact List.mem_append_right _ hr

theorem highArgs_secret_rel : RelCT isa (fun _ _ => True) (.block highArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem code_secret_rel : RelCT isa (fun _ _ => True) VG.Impl.Argon2.X86_64.ReferenceLane.code (fun _ _ => True) :=
  highArgs_secret_rel.seq Divide.code_secret_rel

end VG.Proof.Argon2.X86_64.ReferenceLane
end

/-! Merged from `Proof.Argon2.X86_64.FirstLane`. -/
section
/-! The first reference window stays in the current lane. -/

namespace VG.Proof.Argon2.X86_64.FirstLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FirstLane

theorem test_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.FirstLane.test) s fun t =>
    t.zf = decide (s.gpr .r9 = 0 ∧ s.gpr .r14 = 0) ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.FirstLane.test, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags,
    reduceCtorEq, ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change (s.gpr .r9 ||| s.gpr .r14) = 0#64 ↔ _
    exact BitVec.or_eq_zero_iff
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem current_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.FirstLane.current) s fun t =>
    t.gpr .r8 = s.gpr .rbx ∧ Divide.Keeps [.r8] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.FirstLane.current, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.FirstLane.code s fun t =>
    t.gpr .r8 = (if s.gpr .r9 = 0 ∧ s.gpr .r14 = 0 then s.gpr .rbx else s.gpr .r8) ∧
    Divide.Keeps [.rax, .r8] s t := by
  unfold VG.Impl.Argon2.X86_64.FirstLane.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.FirstLane.test_ok s).mono ?_)
  rintro a ⟨flag, keeps⟩
  refine WP.ite (decide (s.gpr .r9 = 0 ∧ s.gpr .r14 = 0))
    (by simp only [eval, flag]) ?_ ?_
  · intro h
    have position := of_decide_eq_true h
    refine (VG.Proof.Argon2.X86_64.FirstLane.current_ok a).mono ?_
    rintro t ⟨out, tail⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
    simpa only [position, and_self, ite_true, keeps.regs .rbx (by decide)] using out
  · intro h
    have position := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, keeps.mono (by decide)⟩
    simp only [position, ite_false]
    exact keeps.regs .r8 (by decide)

end VG.Proof.Argon2.X86_64.FirstLane
end

/-! Choose the reference lane, restore the pass and prepare the window inputs. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Chosen (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice (s.gpr .rdi))
  pass : t.gpr .r9 = BitVec.ofNat 64 pass
  original : t.gpr .r11 = s.gpr .rdi
  position : VG.Proof.Argon2.X86_64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t

theorem chooseLane_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa chooseLane s (VG.Proof.Argon2.X86_64.ReferenceMap.Chosen p pass lane slice index s) := by
  have lanesNat : (s.gpr .rsi).toNat = p.lanes := by
    rw [ready.lanes, VG.Proof.Argon2.X86_64.ReferenceMap.word_nat _ (by have := ready.bounds.lanesBound; omega)]
  unfold chooseLane
  refine WP.seq ((ReferenceLane.code_ok s
    (by rw [lanesNat]; exact ready.bounds.lanesPositive)
    (by rw [lanesNat]; exact ready.bounds.lanesBound)).mono ?_)
  rintro a ⟨laneNat, original, ka⟩
  have ka' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s a := ka.mono (by decide)
  have readA : InRegions (a.rd ++ a.wr) (a.gpr .rbp) 8 := by
    rw [ka'.rd, ka'.wr, ka'.regs .rbp (by decide)]
    exact ready.passRead
  have laneWord : a.gpr .r8 = BitVec.ofNat 64 ((s.gpr .rdi >>> 32).toNat % p.lanes) := by
    calc
      a.gpr .r8 = BitVec.ofNat 64 (a.gpr .r8).toNat := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = _ := by rw [laneNat, lanesNat]
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceMap.loadPass_ok a readA).mono ?_)
  rintro b ⟨loaded, kb⟩
  have kb' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed a b := kb.mono (by decide)
  have kab := ka'.trans kb'
  have pb := ready.position.of_keeps kab
  have passWord : b.gpr .r9 = BitVec.ofNat 64 pass := by
    rw [loaded, ka'.mem, ka'.regs .rbp (by decide)]
    exact ready.passWord
  have passZero : b.gpr .r9 = 0 ↔ pass = 0 := by
    rw [passWord]
    exact VG.Proof.Argon2.X86_64.ReferenceMap.word_zero _ (by have := ready.bounds.passBound; omega)
  have sliceZero : b.gpr .r14 = 0 ↔ slice = 0 := by
    rw [pb.slice]
    exact VG.Proof.Argon2.X86_64.ReferenceMap.word_zero _ (by have := ready.bounds.sliceBound; omega)
  refine (FirstLane.code_ok b).mono ?_
  rintro t ⟨out, kt⟩
  have kt' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ready.position.of_keeps (kab.trans kt'), kab.trans kt'⟩
  · rw [out]
    by_cases position : pass = 0 ∧ slice = 0 <;>
      simp only [passZero, sliceZero, pb.current, kb.regs .r8 (by decide), laneWord,
        VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane, position, and_self, ite_true, ite_false]
  · exact (kt.regs .r9 (by decide)).trans passWord
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans original)

structure Prepared (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .rdi = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice (s.gpr .rdi))
  current : t.gpr .rsi = BitVec.ofNat 64 lane
  pass : (t.gpr .r9).toNat = pass
  original : t.gpr .r11 = s.gpr .rdi
  position : VG.Proof.Argon2.X86_64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t

theorem prepareLanes_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa prepareLanes s (VG.Proof.Argon2.X86_64.ReferenceMap.Prepared p pass lane slice index s) := by
  unfold prepareLanes
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceMap.chooseLane_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine (VG.Proof.Argon2.X86_64.ReferenceMap.laneArgs_ok a).mono ?_
  rintro t ⟨laneOut, currentOut, kt⟩
  have kt' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed a t := kt.mono (by decide)
  refine ⟨laneOut.trans ha.selected, currentOut.trans ha.position.current, ?_,
    (kt.regs .r11 (by decide)).trans ha.original,
    ha.position.of_keeps kt', ha.keeps.trans kt'⟩
  rw [kt.regs .r9 (by decide), ha.pass, VG.Proof.Argon2.X86_64.ReferenceMap.word_nat _ (by have := ready.bounds.passBound; omega)]

end VG.Proof.Argon2.X86_64.ReferenceMap

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillKernelArgs`. -/
section

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapWindow`. -/
section
/-! The selected eligible window and its chronological starting column. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Counted (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .rdi = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice (s.gpr .rdi))
  current : t.gpr .rsi = BitVec.ofNat 64 lane
  count : t.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.windowSize p pass lane slice index (s.gpr .rdi))
  start : t.gpr .r10 = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice)
  original : t.gpr .r11 = s.gpr .rdi
  position : VG.Proof.Argon2.X86_64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t

theorem window_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) (prepared : VG.Proof.Argon2.X86_64.ReferenceMap.Prepared p pass lane slice index s a) :
    WP isa window a (VG.Proof.Argon2.X86_64.ReferenceMap.Counted p pass lane slice index s) := by
  have segmentPositive : 0 < p.segmentLen :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2)
      (Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum)
  unfold window
  refine WP.seq ((ReferenceStart.code_nat_ok a p pass slice bounds.lanesPositive
    segmentPositive bounds.sliceBound prepared.pass prepared.position.slice
    prepared.position.segmentLength).mono ?_)
  rintro b ⟨startWord, kb⟩
  have kb' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed a b := kb.mono (by decide)
  have pb := prepared.position.of_keeps kb'
  have passB : (b.gpr .r9).toNat = pass := by
    rw [kb.regs .r9 (by decide), prepared.pass]
  have same : decide (b.gpr .rdi = b.gpr .rsi) =
      (VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice (s.gpr .rdi) == lane) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    rw [kb.regs .rdi (by decide), kb.regs .rsi (by decide), prepared.selected, prepared.current]
    exact VG.Proof.Argon2.X86_64.ReferenceMap.word_eq _ _ (bounds.chosenLane_bound64 _) bounds.lane_bound64
  refine (ReferenceCount.code_nat_ok b p pass slice index passB pb.laneLength
    pb.segmentLength pb.slice pb.index bounds.segment_le_lane bounds.index_bound64
    bounds.window_positive.1 bounds.window_positive.2).mono ?_
  rintro t ⟨countWord, kt⟩
  have kt' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, pb.of_keeps kt', prepared.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .rdi (by decide)).trans ((kb.regs .rdi (by decide)).trans prepared.selected)
  · exact (kt.regs .rsi (by decide)).trans ((kb.regs .rsi (by decide)).trans prepared.current)
  · simpa only [VG.Proof.Argon2.X86_64.ReferenceMap.windowSize, same] using countWord
  · exact (kt.regs .r10 (by decide)).trans startWord
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans prepared.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapRelative`. -/
section
/-! Apply the squared J₁ mapping while retaining the lane and window start. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem relativeWord_ok (s : State) (positive : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.X86_64.Relative.code s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        ((s.gpr .rsi).toNat - 1 - (s.gpr .rsi).toNat *
          ((s.gpr .rdi &&& 0xffffffff).toNat * (s.gpr .rdi &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧ Divide.Keeps [.rax, .rdx, .rcx] s t := by
  refine WP.mono_mx (by decide +kernel) (Relative.code_nat_ok s positive bound) ?_
  rintro t ⟨out, other, mem, rd, wr⟩ mx
  refine ⟨out, ⟨?_, mem, rd, wr, mx⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact other r hr.1 hr.2.1 hr.2.2

structure Mapped (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice (s.gpr .rdi))
  relative : t.gpr .rax = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .rdi))
  start : t.gpr .r10 = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice)
  original : t.gpr .r11 = s.gpr .rdi
  position : VG.Proof.Argon2.X86_64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t

theorem relative_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) (counted : VG.Proof.Argon2.X86_64.ReferenceMap.Counted p pass lane slice index s a) :
    WP isa relative a (VG.Proof.Argon2.X86_64.ReferenceMap.Mapped p pass lane slice index s) := by
  unfold relative
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceMap.relativeArgs_ok a).mono ?_)
  rintro b ⟨selected, random, count, kb⟩
  have countNat : (b.gpr .rsi).toNat = VG.Proof.Argon2.X86_64.ReferenceMap.windowSize p pass lane slice index (s.gpr .rdi) := by
    rw [count, counted.count, VG.Proof.Argon2.X86_64.ReferenceMap.word_nat _ (Nat.lt_trans (bounds.windowSize_bound32 _) (by decide))]
  have randomWord : b.gpr .rdi = s.gpr .rdi := random.trans counted.original
  refine (VG.Proof.Argon2.X86_64.ReferenceMap.relativeWord_ok b
    (by rw [countNat]; exact bounds.windowSize_positive _)
    (by rw [countNat]; exact bounds.windowSize_bound32 _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, counted.position.of_keeps (kb'.trans kt'),
    counted.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .r9 (by decide)).trans (selected.trans counted.selected)
  · simpa only [VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue, countNat, randomWord] using out
  · exact (kt.regs .r10 (by decide)).trans ((kb.regs .r10 (by decide)).trans counted.start)
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans counted.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapFinish`. -/
section
/-! Wrap the selected relative position into the lane's columns. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Result (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice (s.gpr .rdi))
  column : t.gpr .rdi = BitVec.ofNat 64
    ((VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .rdi)) % p.laneLen)
  original : t.gpr .r11 = s.gpr .rdi
  position : VG.Proof.Argon2.X86_64.ReferenceMap.Position p lane slice index t
  keeps : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t

theorem finish_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : VG.Proof.Argon2.X86_64.ReferenceMap.Bounds p pass lane slice index) (mapped : VG.Proof.Argon2.X86_64.ReferenceMap.Mapped p pass lane slice index s a) :
    WP isa VG.Impl.Argon2.X86_64.ReferenceMap.finish a (VG.Proof.Argon2.X86_64.ReferenceMap.Result p pass lane slice index s) := by
  unfold VG.Impl.Argon2.X86_64.ReferenceMap.finish
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceMap.wrapArgs_ok a).mono ?_)
  rintro b ⟨sum, length, kb⟩
  have sumWord : b.gpr .rdi = BitVec.ofNat 64
      (VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .rdi)) := by
    rw [sum, mapped.relative, mapped.start, ← BitVec.ofNat_add, Nat.add_comm]
  have sumBound : VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .rdi)
      < 2 ^ 64 := by
    have small := bounds.sum_bound (s.gpr .rdi)
    have q := bounds.laneLength_bound
    omega
  have sumNat : (b.gpr .rdi).toNat =
      VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue p pass lane slice index (s.gpr .rdi) := by
    rw [sumWord, VG.Proof.Argon2.X86_64.ReferenceMap.word_nat _ sumBound]
  have lengthNat : (b.gpr .rsi).toNat = p.laneLen := by
    rw [length, mapped.position.laneLength,
      VG.Proof.Argon2.X86_64.ReferenceMap.word_nat _ (Nat.lt_trans bounds.laneLength_bound (by decide))]
  refine (Wrap.code_nat_ok b (by rw [sumNat, lengthNat]; exact bounds.sum_bound _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, mapped.position.of_keeps (kb'.trans kt'),
    mapped.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .r9 (by decide)).trans ((kb.regs .r9 (by decide)).trans mapped.selected)
  · rw [out, sumNat, lengthNat]
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans mapped.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.ReferenceMap`. -/
section
/-! Complete reference mapping against the reviewed RFC specification. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem code_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.X86_64.ReferenceMap.code s (VG.Proof.Argon2.X86_64.ReferenceMap.Result p pass lane slice index s) := by
  unfold VG.Impl.Argon2.X86_64.ReferenceMap.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceMap.prepareLanes_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceMap.window_ok s a p pass lane slice index ready.bounds ha).mono ?_)
  intro b hb
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReferenceMap.relative_ok s b p pass lane slice index ready.bounds hb).mono ?_)
  intro c hc
  exact VG.Proof.Argon2.X86_64.ReferenceMap.finish_ok s c p pass lane slice index ready.bounds hc

theorem spec_lane (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).1 = VG.Proof.Argon2.X86_64.ReferenceMap.chosenLane p pass lane slice random := rfl

theorem spec_column (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).2 =
      (VG.Proof.Argon2.X86_64.ReferenceMap.windowStart p pass slice + VG.Proof.Argon2.X86_64.ReferenceMap.relativeValue p pass lane slice index random) % p.laneLen := rfl

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.X86_64.ReferenceMap.Ready p pass lane slice index s) :
    WP isa VG.Impl.Argon2.X86_64.ReferenceMap.code s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).1 ∧
      t.gpr .rdi = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).2 ∧
      t.gpr .r11 = s.gpr .rdi ∧ Divide.Keeps VG.Proof.Argon2.X86_64.ReferenceMap.changed s t := by
  refine (VG.Proof.Argon2.X86_64.ReferenceMap.code_ok s p pass lane slice index ready).mono ?_
  intro t h
  rw [VG.Proof.Argon2.X86_64.ReferenceMap.spec_lane, VG.Proof.Argon2.X86_64.ReferenceMap.spec_column]
  exact ⟨h.selected, h.column, h.original, h.keeps⟩

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Merged from `Proof.Argon2.X86_64.FillPointersNat`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillPointersArgs`. -/
section
/-! Short register-setup steps for the filling pointers. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

theorem saveReference_ok (s : State) : WP isa (.block saveReference) s fun t =>
    t.gpr .rsi = s.gpr .rdi ∧ Divide.Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [saveReference, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem currentArgs_ok (s : State) : WP isa (.block currentArgs) s fun t =>
    t.gpr .rax = s.gpr .rbx ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [currentArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem previousArgs_ok (s : State) : WP isa (.block previousArgs) s fun t =>
    t.gpr .r10 = s.gpr .rax ∧ t.gpr .rcx = s.gpr .rdi ∧ t.gpr .rax = s.gpr .rbx ∧
    Divide.Keeps [.r10, .rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [previousArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem referenceArgs_ok (s : State) : WP isa (.block referenceArgs) s fun t =>
    t.gpr .r11 = s.gpr .rax ∧ t.gpr .rcx = s.gpr .rsi ∧ t.gpr .rax = s.gpr .r9 ∧
    Divide.Keeps [.r11, .rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [referenceArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem finishArgs_ok (s : State) : WP isa (.block finishArgs) s fun t =>
    t.gpr .rsi = s.gpr .rax ∧ t.gpr .rdi = s.gpr .r11 ∧
    Divide.Keeps [.rsi, .rdi] s t := by
  apply WP.of_runBlock
  simp only [finishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Merged from `Proof.Argon2.X86_64.FillPointers`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillColumn`. -/
section
/-! Current-column arithmetic and the cyclic predecessor, preserving the
matrix, enclosing loop registers and MXCSR. -/

namespace VG.Proof.Argon2.X86_64.FillColumn

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillColumn

theorem current_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.FillColumn.current) s fun t =>
    t.gpr .rcx = s.gpr .r14 * s.gpr .r13 + s.gpr .r15 ∧
    Divide.Keeps [.rax, .rdx, .rcx] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.FillColumn.current, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execMul, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem compare_ok (s : State) : WP isa (.block [.alu .cmp .rcx (.imm 0)]) s
    fun t => t.zf = decide (s.gpr .rcx = 0) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl]
  refine ⟨?_, ?_⟩
  · change (s.gpr .rcx - 0#64 == 0#64) = decide (s.gpr .rcx = 0#64)
    rw [BitVec.sub_zero]
    exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq])
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

theorem move_ok (s : State) (r : Reg) : WP isa (.block [.mov .rdi (.reg r)]) s
    fun t => t.gpr .rdi = s.gpr r ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ite_eq_right hq
  all_goals rfl

theorem decrement_ok (s : State) : WP isa (.block [.alu .sub .rdi (.imm 1)]) s
    fun t => t.gpr .rdi = s.gpr .rdi - 1 ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem previous_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.FillColumn.previous s fun t =>
    t.gpr .rdi = (if s.gpr .rcx = 0 then s.gpr .r12 else s.gpr .rcx) - 1 ∧
    Divide.Keeps [.rdi] s t := by
  unfold VG.Impl.Argon2.X86_64.FillColumn.previous
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillColumn.compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have selected : WP isa VG.Impl.Argon2.X86_64.FillColumn.select a fun b =>
      b.gpr .rdi = (if s.gpr .rcx = 0 then s.gpr .r12 else s.gpr .rcx) ∧
      Divide.Keeps [.rdi] s b := by
    unfold VG.Impl.Argon2.X86_64.FillColumn.select
    refine WP.ite (decide (s.gpr .rcx = 0)) (by simp only [eval, flag]) ?_ ?_
    · intro h
      have zero := of_decide_eq_true h
      refine (VG.Proof.Argon2.X86_64.FillColumn.move_ok a .r12).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .r12 (by simp), ite_eq_left zero],
        (ka.mono (by simp)).trans kb⟩
    · intro h
      have nonzero := of_decide_eq_false h
      refine (VG.Proof.Argon2.X86_64.FillColumn.move_ok a .rcx).mono ?_
      rintro b ⟨value, kb⟩
      exact ⟨by rw [value, ka.regs .rcx (by simp), ite_eq_right nonzero],
        (ka.mono (by simp)).trans kb⟩
  refine WP.seq (selected.mono ?_)
  rintro b ⟨value, kb⟩
  refine (VG.Proof.Argon2.X86_64.FillColumn.decrement_ok b).mono ?_
  rintro t ⟨result, kt⟩
  exact ⟨by rw [result, value], kb.trans kt⟩

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.FillColumn.code s fun t =>
    let column := s.gpr .r14 * s.gpr .r13 + s.gpr .r15
    t.gpr .rcx = column ∧
    t.gpr .rdi = (if column = 0 then s.gpr .r12 else column) - 1 ∧
    Divide.Keeps [.rax, .rdx, .rcx, .rdi] s t := by
  unfold VG.Impl.Argon2.X86_64.FillColumn.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillColumn.current_ok s).mono ?_)
  rintro a ⟨column, ka⟩
  refine (VG.Proof.Argon2.X86_64.FillColumn.previous_ok a).mono ?_
  rintro t ⟨previous, kt⟩
  refine ⟨(kt.regs .rcx (by decide)).trans column, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [previous, column, ka.regs .r12 (by decide)]

theorem previous_nat (column q : Nat) (positive : 0 < q) (bound : column < q) :
    (if column = 0 then q else column) - 1 = (column + q - 1) % q := by
  by_cases zero : column = 0
  · simp only [zero, ite_true, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (by omega : q - 1 < q)).symm
  · simp only [zero, ite_false]
    have sub : column + q - 1 - q = column - 1 := by omega
    rw [Nat.mod_eq_sub_mod (by omega : q ≤ column + q - 1), sub,
      Nat.mod_eq_of_lt (by omega : column - 1 < q)]

theorem previous_word_nat (column q : Nat) (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : column < q) :
    (if BitVec.ofNat 64 column = 0#64 then BitVec.ofNat 64 q else BitVec.ofNat 64 column) - 1 =
      BitVec.ofNat 64 ((column + q - 1) % q) := by
  have zero : BitVec.ofNat 64 column = 0#64 ↔
      column = 0 := by
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound qBound)] at hn
      exact hn
    · intro h; rw [h]
  simp only [zero]
  by_cases h : column = 0
  · simp only [h, ite_true]
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat positive, Nat.zero_add, Nat.mod_eq_of_lt (by omega : q - 1 < q)]
  · simp only [h, ite_false]
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 1 ≤ column),
      ← VG.Proof.Argon2.X86_64.FillColumn.previous_nat _ q positive bound, ite_eq_right h]

theorem code_nat_ok (s : State) (slice segment index q : Nat)
    (hs : s.gpr .r14 = BitVec.ofNat 64 slice)
    (hg : s.gpr .r13 = BitVec.ofNat 64 segment)
    (hi : s.gpr .r15 = BitVec.ofNat 64 index)
    (hq : s.gpr .r12 = BitVec.ofNat 64 q)
    (positive : 0 < q) (qBound : q < 2 ^ 64)
    (bound : slice * segment + index < q) :
    WP isa VG.Impl.Argon2.X86_64.FillColumn.code s fun t =>
      t.gpr .rcx = BitVec.ofNat 64 (slice * segment + index) ∧
      t.gpr .rdi = BitVec.ofNat 64 ((slice * segment + index + q - 1) % q) ∧
      Divide.Keeps [.rax, .rdx, .rcx, .rdi] s t := by
  refine (VG.Proof.Argon2.X86_64.FillColumn.code_ok s).mono ?_
  rintro t ⟨column, previous, keeps⟩
  have word : s.gpr .r14 * s.gpr .r13 + s.gpr .r15 =
      BitVec.ofNat 64 (slice * segment + index) := by
    rw [hs, hg, hi, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  refine ⟨column.trans word, ?_, keeps⟩
  rw [previous, word, hq]
  exact VG.Proof.Argon2.X86_64.FillColumn.previous_word_nat _ q positive qBound bound

end VG.Proof.Argon2.X86_64.FillColumn
end

/-! Compose the matrix addresses while retaining the enclosing loop position. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

def address (base lane column q : Addr) : Addr := (lane * q + column) * 1024 + base

def column (s : State) : Addr := s.gpr .r14 * s.gpr .r13 + s.gpr .r15

def predecessor (s : State) : Addr :=
  (if VG.Proof.Argon2.X86_64.FillPointers.column s = 0 then s.gpr .r12 else VG.Proof.Argon2.X86_64.FillPointers.column s) - 1

def changed : List Reg := [.rax, .rdx, .rcx, .rdi, .rsi, .r10, .r11]

theorem current_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.FillPointers.current s fun t =>
    t.gpr .rax = VG.Proof.Argon2.X86_64.FillPointers.address (s.gpr .r8) (s.gpr .rbx) (s.gpr .rcx) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx] s t := by
  unfold VG.Impl.Argon2.X86_64.FillPointers.current
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillPointers.currentArgs_ok s).mono ?_)
  rintro a ⟨lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨?_, (ka.mono (by simp)).trans kt⟩
  rw [pointer, lane, ka.regs .r12 (by decide), ka.regs .rcx (by decide), ka.regs .r8 (by decide), VG.Proof.Argon2.X86_64.FillPointers.address]

theorem previous_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.FillPointers.previous s fun t =>
    t.gpr .r10 = s.gpr .rax ∧
    t.gpr .rax = VG.Proof.Argon2.X86_64.FillPointers.address (s.gpr .r8) (s.gpr .rbx) (s.gpr .rdi) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx, .rcx, .r10] s t := by
  unfold VG.Impl.Argon2.X86_64.FillPointers.previous
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillPointers.previousArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .r10 (by decide)).trans saved, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [pointer, lane, col, ka.regs .r12 (by decide), ka.regs .r8 (by decide), VG.Proof.Argon2.X86_64.FillPointers.address]

theorem reference_ok (s : State) : WP isa reference s fun t =>
    t.gpr .r11 = s.gpr .rax ∧
    t.gpr .rax = VG.Proof.Argon2.X86_64.FillPointers.address (s.gpr .r8) (s.gpr .r9) (s.gpr .rsi) (s.gpr .r12) ∧
    Divide.Keeps [.rax, .rdx, .rcx, .r11] s t := by
  unfold reference
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillPointers.referenceArgs_ok s).mono ?_)
  rintro a ⟨saved, col, lane, ka⟩
  refine (BlockAddress.code_ok a).mono ?_
  rintro t ⟨pointer, kt⟩
  refine ⟨(kt.regs .r11 (by decide)).trans saved, ?_,
    (ka.mono (by simp)).trans (kt.mono (by simp))⟩
  rw [pointer, lane, col, ka.regs .r12 (by decide), ka.regs .r8 (by decide), VG.Proof.Argon2.X86_64.FillPointers.address]

theorem code_ok (s : State) : WP isa VG.Impl.Argon2.X86_64.FillPointers.code s fun t =>
    t.gpr .r10 = VG.Proof.Argon2.X86_64.FillPointers.address (s.gpr .r8) (s.gpr .rbx) (VG.Proof.Argon2.X86_64.FillPointers.column s) (s.gpr .r12) ∧
    t.gpr .rdi = VG.Proof.Argon2.X86_64.FillPointers.address (s.gpr .r8) (s.gpr .rbx) (VG.Proof.Argon2.X86_64.FillPointers.predecessor s) (s.gpr .r12) ∧
    t.gpr .rsi = VG.Proof.Argon2.X86_64.FillPointers.address (s.gpr .r8) (s.gpr .r9) (s.gpr .rdi) (s.gpr .r12) ∧
    Divide.Keeps VG.Proof.Argon2.X86_64.FillPointers.changed s t := by
  unfold VG.Impl.Argon2.X86_64.FillPointers.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillPointers.saveReference_ok s).mono ?_)
  rintro a ⟨refColumn, ka⟩
  refine WP.seq ((FillColumn.code_ok a).mono ?_)
  rintro b ⟨curColumn, prevColumn, kb⟩
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillPointers.current_ok b).mono ?_)
  rintro c ⟨curPointer, kc⟩
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillPointers.previous_ok c).mono ?_)
  rintro d ⟨savedCurrent, prevPointer, kd⟩
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillPointers.reference_ok d).mono ?_)
  rintro e ⟨savedPrevious, refPointer, ke⟩
  refine (VG.Proof.Argon2.X86_64.FillPointers.finishArgs_ok e).mono ?_
  rintro t ⟨referenceResult, previousResult, kt⟩
  have coords : VG.Proof.Argon2.X86_64.FillPointers.column a = VG.Proof.Argon2.X86_64.FillPointers.column s := by
    unfold VG.Proof.Argon2.X86_64.FillPointers.column
    rw [ka.regs .r14 (by decide), ka.regs .r13 (by decide), ka.regs .r15 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kt.regs .r10 (by decide), ke.regs .r10 (by decide), savedCurrent, curPointer,
      kb.regs .r8 (by decide), ka.regs .r8 (by decide), kb.regs .rbx (by decide),
      ka.regs .rbx (by decide), kb.regs .r12 (by decide), ka.regs .r12 (by decide), curColumn]
    exact congrArg (fun col => VG.Proof.Argon2.X86_64.FillPointers.address (s.gpr .r8) (s.gpr .rbx) col (s.gpr .r12)) coords
  · rw [previousResult, savedPrevious, prevPointer, kc.regs .r8 (by decide),
      kc.regs .rbx (by decide), kc.regs .rdi (by decide), kc.regs .r12 (by decide),
      kb.regs .r8 (by decide), ka.regs .r8 (by decide), kb.regs .rbx (by decide),
      ka.regs .rbx (by decide), kb.regs .r12 (by decide), ka.regs .r12 (by decide), prevColumn]
    change VG.Proof.Argon2.X86_64.FillPointers.address _ _ ((if VG.Proof.Argon2.X86_64.FillPointers.column a = 0 then a.gpr .r12 else VG.Proof.Argon2.X86_64.FillPointers.column a) - 1) _ = _
    rw [coords, ka.regs .r12 (by decide), VG.Proof.Argon2.X86_64.FillPointers.predecessor]
  · rw [referenceResult, refPointer, kd.regs .r8 (by decide), kd.regs .r9 (by decide),
      kd.regs .rsi (by decide), kd.regs .r12 (by decide), kc.regs .r8 (by decide),
      kc.regs .r9 (by decide), kc.regs .rsi (by decide), kc.regs .r12 (by decide),
      kb.regs .r8 (by decide), kb.regs .r9 (by decide), kb.regs .rsi (by decide),
      kb.regs .r12 (by decide), ka.regs .r8 (by decide), ka.regs .r9 (by decide),
      ka.regs .r12 (by decide), refColumn]
  · exact (((((ka.mono (by simp [VG.Proof.Argon2.X86_64.FillPointers.changed])).trans (kb.mono (by simp [VG.Proof.Argon2.X86_64.FillPointers.changed]))).trans
      (kc.mono (by simp [VG.Proof.Argon2.X86_64.FillPointers.changed]))).trans (kd.mono (by simp [VG.Proof.Argon2.X86_64.FillPointers.changed]))).trans
      (ke.mono (by simp [VG.Proof.Argon2.X86_64.FillPointers.changed]))).trans (kt.mono (by simp [VG.Proof.Argon2.X86_64.FillPointers.changed]))

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Matrix pointers are the natural-number block offsets in the specification. -/

namespace VG.Proof.Argon2.X86_64.FillPointers

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillPointers

def cell (base : Addr) (p : Spec.Argon2.Params) (lane column : Nat) : Addr :=
  off base ((lane * p.laneLen + column) * 1024)

theorem address_nat (base : Addr) (lane column q : Nat) :
    VG.Proof.Argon2.X86_64.FillPointers.address base (BitVec.ofNat 64 lane) (BitVec.ofNat 64 column) (BitVec.ofNat 64 q) =
      off base ((lane * q + column) * 1024) := by
  unfold VG.Proof.Argon2.X86_64.FillPointers.address off
  change (BitVec.ofNat 64 lane * BitVec.ofNat 64 q + BitVec.ofNat 64 column) *
    BitVec.ofNat 64 1024 + base = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_nat_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index refLane refColumn : Nat)
    (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (rl : s.gpr .r9 = BitVec.ofNat 64 refLane)
    (rc : s.gpr .rdi = BitVec.ofNat 64 refColumn) :
    WP isa VG.Impl.Argon2.X86_64.FillPointers.code s fun t =>
      t.gpr .r10 = VG.Proof.Argon2.X86_64.FillPointers.cell (s.gpr .r8) p lane (slice * p.segmentLen + index) ∧
      t.gpr .rdi = VG.Proof.Argon2.X86_64.FillPointers.cell (s.gpr .r8) p lane ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) ∧
      t.gpr .rsi = VG.Proof.Argon2.X86_64.FillPointers.cell (s.gpr .r8) p refLane refColumn ∧ Divide.Keeps VG.Proof.Argon2.X86_64.FillPointers.changed s t := by
  refine (VG.Proof.Argon2.X86_64.FillPointers.code_ok s).mono ?_
  rintro t ⟨current, previous, reference, keeps⟩
  have col : VG.Proof.Argon2.X86_64.FillPointers.column s = BitVec.ofNat 64 (slice * p.segmentLen + index) := by
    unfold VG.Proof.Argon2.X86_64.FillPointers.column
    rw [position.slice, position.segmentLength, position.index, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  have prev : VG.Proof.Argon2.X86_64.FillPointers.predecessor s = BitVec.ofNat 64
      ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) := by
    unfold VG.Proof.Argon2.X86_64.FillPointers.predecessor
    rw [col, position.laneLength]
    have positive := Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum
    have q := Proof.Argon2.laneLen_segments p bounds.lanesPositive
    exact FillColumn.previous_word_nat _ _ (by omega)
      (Nat.lt_trans bounds.laneLength_bound (by decide))
      (Proof.Argon2.column_lt p bounds.lanesPositive bounds.sliceBound bounds.indexBound)
  refine ⟨?_, ?_, ?_, keeps⟩
  · rw [current, position.current, col, position.laneLength, VG.Proof.Argon2.X86_64.FillPointers.address_nat]; rfl
  · rw [previous, position.current, prev, position.laneLength, VG.Proof.Argon2.X86_64.FillPointers.address_nat]; rfl
  · rw [reference, rl, rc, position.laneLength, VG.Proof.Argon2.X86_64.FillPointers.address_nat]; rfl

end VG.Proof.Argon2.X86_64.FillPointers
end

/-! Merged from `Proof.Argon2.X86_64.FillKernelLayout`. -/
section
/-! One allocation invariant covers all matrix cells used by the filling step. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 232) 64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

structure Layout (p : Params) (s : State) : Prop where
  frameRead : ∀ d ∈ [0, 16, 184, 232, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  frameWrite : InRegions s.wr (off (s.gpr .rbp) 16) 8
  matrixWrite : Covers [⟨VG.Proof.Argon2.X86_64.FillKernel.matrix s, p.blocks * 1024⟩] s.wr
  workWrite : Covers [⟨VG.Proof.Argon2.X86_64.FillKernel.work s, 5120⟩] s.wr
  matrixWork : (⟨VG.Proof.Argon2.X86_64.FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.FillKernel.work s, 5120⟩
  matrixFrame : (⟨VG.Proof.Argon2.X86_64.FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  matrixStack : (⟨VG.Proof.Argon2.X86_64.FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨VG.Proof.Argon2.X86_64.FillKernel.work s, 5120⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨VG.Proof.Argon2.X86_64.FillKernel.work s, 5120⟩

theorem Layout.of_keeps {p : Params} {s t : State} (h : VG.Proof.Argon2.X86_64.FillKernel.Layout p s)
    (k : Divide.Keeps ReferenceMap.changed s t) : VG.Proof.Argon2.X86_64.FillKernel.Layout p t := by
  have bp := k.regs .rbp (by decide)
  have sp := k.regs .rsp (by decide)
  have matrix' : VG.Proof.Argon2.X86_64.FillKernel.matrix t = VG.Proof.Argon2.X86_64.FillKernel.matrix s := by unfold VG.Proof.Argon2.X86_64.FillKernel.matrix; rw [bp, k.mem]
  have work' : VG.Proof.Argon2.X86_64.FillKernel.work t = VG.Proof.Argon2.X86_64.FillKernel.work s := by unfold VG.Proof.Argon2.X86_64.FillKernel.work; rw [bp, k.mem]
  constructor
  · rw [k.rd, k.wr, bp]; exact h.frameRead
  · rw [k.wr, bp]; exact h.frameWrite
  · rw [matrix', k.wr]; exact h.matrixWrite
  · rw [work', k.wr]; exact h.workWrite
  · rw [matrix', work']; exact h.matrixWork
  · rw [matrix', bp]; exact h.matrixFrame
  · rw [matrix', sp]; exact h.matrixStack
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem cell_sub (p : Params) (base : Addr) (positive : 0 < p.lanes) {lane column : Nat}
    (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Region.Sub ⟨FillPointers.cell base p lane column, 1024⟩ ⟨base, p.blocks * 1024⟩ :=
  Offset.sub_base base (Proof.Argon2.cell_bytes p positive hl hc)

theorem Layout.cell_cover {p : Params} {s : State} (h : VG.Proof.Argon2.X86_64.FillKernel.Layout p s) (positive : 0 < p.lanes)
    {lane column : Nat} (hl : lane < p.lanes) (hc : column < p.laneLen) :
    Covers [⟨FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p lane column, 1024⟩] s.wr := by
  have sub : Covers [⟨FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p lane column, 1024⟩]
      [⟨VG.Proof.Argon2.X86_64.FillKernel.matrix s, p.blocks * 1024⟩] := Covers.of_sub (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨⟨VG.Proof.Argon2.X86_64.FillKernel.matrix s, p.blocks * 1024⟩, by simp, (lane * p.laneLen + column) * 1024,
          rfl, Proof.Argon2.cell_bytes p positive hl hc⟩)
  exact fun a n ha => h.matrixWrite a n (sub a n ha)

theorem compress_ready (p : Params) (s : State) (layout : VG.Proof.Argon2.X86_64.FillKernel.Layout p s)
    (positive : 0 < p.lanes) (leftLane leftColumn rightLane rightColumn destLane destColumn : Nat)
    (ll : leftLane < p.lanes) (lc : leftColumn < p.laneLen)
    (rl : rightLane < p.lanes) (rc : rightColumn < p.laneLen)
    (dl : destLane < p.lanes) (dc : destColumn < p.laneLen)
    (left : s.gpr .rdi = FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p leftLane leftColumn)
    (right : s.gpr .rsi = FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p rightLane rightColumn)
    (dest : s.gpr .r10 = FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p destLane destColumn) : FillCompress.Ready s := by
  have leftSub := VG.Proof.Argon2.X86_64.FillKernel.cell_sub p (VG.Proof.Argon2.X86_64.FillKernel.matrix s) positive ll lc
  have rightSub := VG.Proof.Argon2.X86_64.FillKernel.cell_sub p (VG.Proof.Argon2.X86_64.FillKernel.matrix s) positive rl rc
  have destSub := VG.Proof.Argon2.X86_64.FillKernel.cell_sub p (VG.Proof.Argon2.X86_64.FillKernel.matrix s) positive dl dc
  have read (lane column : Nat) (hl : lane < p.lanes) (hc : column < p.laneLen) :
      Covers [⟨FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p lane column, 1024⟩] (s.rd ++ s.wr) := by
    intro a n ha
    obtain ⟨r, hr, hc⟩ := layout.cell_cover positive hl hc a n ha
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  constructor
  · intro d hd
    exact layout.frameRead d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> simp)
  · exact layout.frameWrite
  · rw [left]; exact read leftLane leftColumn ll lc
  · rw [right]; exact read rightLane rightColumn rl rc
  · rw [dest]; exact layout.cell_cover positive dl dc
  · exact layout.workWrite
  · rw [left]; exact layout.matrixWork.sub_left leftSub
  · rw [right]; exact layout.matrixWork.sub_left rightSub
  · rw [dest]; exact layout.matrixWork.sub_left destSub
  · exact layout.frameWork
  · rw [left]; exact layout.matrixFrame.sub_left leftSub
  · rw [right]; exact layout.matrixFrame.sub_left rightSub
  · rw [dest]; exact layout.matrixFrame.sub_left destSub
  · rw [left]; exact (layout.matrixStack.sub_left leftSub).symm
  · rw [right]; exact (layout.matrixStack.sub_left rightSub).symm
  · exact layout.stackWork
  · rw [dest]; exact layout.matrixStack.sub_left destSub
  · exact layout.frameStack

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Reload frame arguments and compose reference mapping with matrix addresses. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem load_ok (s : State) (r : Reg) (d : Nat)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8) :
    WP isa (.block [.mov r (.mem (Impl.Argon2.X86_64.at_ .rbp d))]) s fun t =>
      t.gpr r = s.mem.readW (off (s.gpr .rbp) d) 64 ∧ Divide.Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    VG.Proof.Argon2.X86_64.ea_at, read, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ite_eq_right hq
  all_goals rfl

structure Ready (p : Params) (pass lane slice index : Nat) (s : State) : Prop where
  layout : VG.Proof.Argon2.X86_64.FillKernel.Layout p s
  bounds : ReferenceMap.Bounds p pass lane slice index
  position : ReferenceMap.Position p lane slice index s
  passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

structure Mapped (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  selected : t.gpr .r9 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).1
  column : t.gpr .rdi = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).2
  original : t.gpr .r11 = s.gpr .rdi
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem mapping_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.mapping s (VG.Proof.Argon2.X86_64.FillKernel.Mapped s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.mapping
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillKernel.load_ok s .rsi 184 (h.layout.frameRead 184 (by simp))).mono ?_)
  rintro a ⟨lanes, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have ready : ReferenceMap.Ready p pass lane slice index a := by
    refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanesWord, ?_, ?_⟩
    · rw [k.rd, k.wr, k.regs .rbp (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        using h.layout.frameRead 0 (by simp)
    · rw [k.mem, k.regs .rbp (by decide)]
      simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using h.passWord
  refine (ReferenceMap.code_spec_ok a p pass lane slice index ready).mono ?_
  rintro t ⟨lane, column, original, tail⟩
  rw [keeps.regs .rdi (by decide)] at lane column original
  exact ⟨lane, column, original, k.trans tail⟩

structure Pointers (s t : State) (p : Params) (lane slice index refLane refColumn : Nat) : Prop where
  current : t.gpr .r10 = FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p lane (slice * p.segmentLen + index)
  previous : t.gpr .rdi = FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen)
  reference : t.gpr .rsi = FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p refLane refColumn
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem pointers_ok (s : State) (p : Params) (pass lane slice index refLane refColumn : Nat)
    (layout : VG.Proof.Argon2.X86_64.FillKernel.Layout p s) (bounds : ReferenceMap.Bounds p pass lane slice index)
    (position : ReferenceMap.Position p lane slice index s)
    (laneWord : s.gpr .r9 = BitVec.ofNat 64 refLane) (columnWord : s.gpr .rdi = BitVec.ofNat 64 refColumn) :
    WP isa Impl.Argon2.X86_64.FillKernel.pointers s (VG.Proof.Argon2.X86_64.FillKernel.Pointers s · p lane slice index refLane refColumn) := by
  unfold Impl.Argon2.X86_64.FillKernel.pointers
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillKernel.load_ok s .r8 232 (layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, keeps⟩
  have k : Divide.Keeps ReferenceMap.changed s a := keeps.mono (by decide)
  have lane' : a.gpr .r9 = BitVec.ofNat 64 refLane := (keeps.regs .r9 (by decide)).trans laneWord
  have col' : a.gpr .rdi = BitVec.ofNat 64 refColumn := (keeps.regs .rdi (by decide)).trans columnWord
  refine (FillPointers.code_nat_ok a p pass lane slice index refLane refColumn bounds
    (position.of_keeps k) lane' col').mono ?_
  rintro t ⟨current, previous, reference, tail⟩
  rw [base] at current previous reference
  exact ⟨current, previous, reference, k.trans (tail.mono (by decide))⟩

end VG.Proof.Argon2.X86_64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillKernelPrepare`. -/
section

/-! Complete active-cell update from a random word and the matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def currentColumn (p : Params) (slice index : Nat) : Nat := slice * p.segmentLen + index

def previousColumn (p : Params) (slice index : Nat) : Nat :=
  (VG.Proof.Argon2.X86_64.FillKernel.currentColumn p slice index + p.laneLen - 1) % p.laneLen

def current (s : State) (p : Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p lane (VG.Proof.Argon2.X86_64.FillKernel.currentColumn p slice index)

def previous (s : State) (p : Params) (lane slice index : Nat) : Addr :=
  FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p lane (VG.Proof.Argon2.X86_64.FillKernel.previousColumn p slice index)

def referenced (s : State) (p : Params) (pass lane slice index : Nat) : Addr :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)
  FillPointers.cell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p ref.1 ref.2

structure Prepared (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  ready : FillCompress.Ready t
  currentPtr : t.gpr .r10 = VG.Proof.Argon2.X86_64.FillKernel.current s p lane slice index
  previousPtr : t.gpr .rdi = VG.Proof.Argon2.X86_64.FillKernel.previous s p lane slice index
  referencePtr : t.gpr .rsi = VG.Proof.Argon2.X86_64.FillKernel.referenced s p pass lane slice index
  keeps : Divide.Keeps ReferenceMap.changed s t

theorem prepare_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.prepare s (VG.Proof.Argon2.X86_64.FillKernel.Prepared s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.prepare
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillKernel.mapping_ok s p pass lane slice index h).mono ?_)
  intro a mapped
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)
  refine ((VG.Proof.Argon2.X86_64.FillKernel.pointers_ok a p pass lane slice index ref.1 ref.2
    (h.layout.of_keeps mapped.keeps) h.bounds (h.position.of_keeps mapped.keeps)
    mapped.selected mapped.column).mono ?_)
  intro b pointers
  have keeps := mapped.keeps.trans pointers.keeps
  have matrixA : VG.Proof.Argon2.X86_64.FillKernel.matrix a = VG.Proof.Argon2.X86_64.FillKernel.matrix s := by
    unfold VG.Proof.Argon2.X86_64.FillKernel.matrix; rw [mapped.keeps.mem, mapped.keeps.regs .rbp (by decide)]
  have matrixB : VG.Proof.Argon2.X86_64.FillKernel.matrix b = VG.Proof.Argon2.X86_64.FillKernel.matrix a := by
    unfold VG.Proof.Argon2.X86_64.FillKernel.matrix; rw [pointers.keeps.mem, pointers.keeps.regs .rbp (by decide)]
  have cur : b.gpr .r10 = VG.Proof.Argon2.X86_64.FillKernel.current s p lane slice index := by
    rw [pointers.current, matrixA]; rfl
  have prev : b.gpr .rdi = VG.Proof.Argon2.X86_64.FillKernel.previous s p lane slice index := by
    rw [pointers.previous, matrixA]; rfl
  have other : b.gpr .rsi = VG.Proof.Argon2.X86_64.FillKernel.referenced s p pass lane slice index := by
    rw [pointers.reference, matrixA]; rfl
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have previousBound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  obtain ⟨refLane, refColumn⟩ := Proof.Argon2.reference_bounds p h.bounds.lanesPositive
    h.bounds.memoryMinimum pass lane slice index (s.gpr .rdi) h.bounds.laneBound
  have compressReady : FillCompress.Ready b := by
    apply VG.Proof.Argon2.X86_64.FillKernel.compress_ready p b (h.layout.of_keeps keeps) h.bounds.lanesPositive
      lane (VG.Proof.Argon2.X86_64.FillKernel.previousColumn p slice index) ref.1 ref.2 lane (VG.Proof.Argon2.X86_64.FillKernel.currentColumn p slice index)
      h.bounds.laneBound previousBound refLane refColumn h.bounds.laneBound columnBound
    · rw [pointers.previous, matrixB]; rfl
    · rw [pointers.reference, matrixB]
    · rw [pointers.current, matrixB]; rfl
  exact ⟨compressReady, cur, prev, other, keeps⟩

end VG.Proof.Argon2.X86_64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillKernel`. -/
section

/-! Complete active-cell update from a random word and the matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) (lane slice index : Nat) : List Region :=
  [⟨VG.Proof.Argon2.X86_64.FillKernel.current s p lane slice index, 1024⟩, ⟨VG.Proof.Argon2.X86_64.FillKernel.work s, 5120⟩,
    below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 16, 8⟩]

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  block : blockAt t.mem (VG.Proof.Argon2.X86_64.FillKernel.current s p lane slice index) =
    let next := Spec.Argon2.compress (blockAt s.mem (VG.Proof.Argon2.X86_64.FillKernel.previous s p lane slice index))
      (blockAt s.mem (VG.Proof.Argon2.X86_64.FillKernel.referenced s p pass lane slice index))
    if pass = 0 then next else xorBlock next (blockAt s.mem (VG.Proof.Argon2.X86_64.FillKernel.current s p lane slice index))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.FillKernel.writes s p lane slice index) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr

theorem code_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index : Nat)
    (h : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.code s (VG.Proof.Argon2.X86_64.FillKernel.Done s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.FillKernel.prepare_ok s p pass lane slice index h).mono ?_)
  intro b prepared
  have keeps := prepared.keeps
  have cur := prepared.currentPtr
  have prev := prepared.previousPtr
  have other := prepared.referencePtr
  refine (FillCompress.code_mx_ok b prepared.ready).mono ?_
  rintro t ⟨done, mx⟩
  have counter : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [keeps.mem, keeps.regs .rbp (by decide)]
    exact h.passWord
  refine ⟨?_, ?_, done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_, mx.trans (ctl_eq_of keeps.mxcsr)⟩
  · have block := done.block
    rw [cur, prev, other, keeps.mem, counter] at block
    simp only [ReferenceMap.word_zero pass (Nat.lt_trans h.bounds.passBound (by decide))] at block
    exact block
  · intro r hr
    have ne : r ∉ ReferenceMap.changed := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (done.regs r hr).trans (keeps.regs r ne)
  · have workB : FillCompress.work b = VG.Proof.Argon2.X86_64.FillKernel.work s := by
      unfold FillCompress.work VG.Proof.Argon2.X86_64.FillKernel.work
      rw [keeps.regs .rbp (by decide), keeps.mem]
    have frame := done.frame
    rw [FillCompress.writes, workB, cur, keeps.regs .rsp (by decide), keeps.regs .rbp (by decide), keeps.mem] at frame
    change Frame [⟨VG.Proof.Argon2.X86_64.FillKernel.current s p lane slice index, 1024⟩, ⟨VG.Proof.Argon2.X86_64.FillKernel.work s + 4096, 1024⟩,
      ⟨VG.Proof.Argon2.X86_64.FillKernel.work s, 4096⟩, below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 16, 8⟩] s.mem t.mem at frame
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillKernel.writes], fun _ h => h⟩
    · exact ⟨⟨VG.Proof.Argon2.X86_64.FillKernel.work s, 5120⟩, by simp [VG.Proof.Argon2.X86_64.FillKernel.writes], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨VG.Proof.Argon2.X86_64.FillKernel.work s, 5120⟩, by simp [VG.Proof.Argon2.X86_64.FillKernel.writes], Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillKernel.writes], fun _ h => h⟩
    · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillKernel.writes], fun _ h => h⟩

end VG.Proof.Argon2.X86_64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillKernelSpec`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillKernelMatrix`. -/
section
/-! The filling step updates exactly one cell of the specification's block array. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def currentIndex (p : Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + VG.Proof.Argon2.X86_64.FillKernel.currentColumn p slice index

def previousIndex (p : Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + VG.Proof.Argon2.X86_64.FillKernel.previousColumn p slice index

def referenceIndex (s : State) (p : Params) (pass lane slice index : Nat) : Nat :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)
  ref.1 * p.laneLen + ref.2

def nextBlock (s : State) (p : Params) (pass lane slice index : Nat) (blocks : Array Block) : Block :=
  let next := Spec.Argon2.compress (blocks[VG.Proof.Argon2.X86_64.FillKernel.previousIndex p lane slice index]?.getD zeroBlock)
    (blocks[VG.Proof.Argon2.X86_64.FillKernel.referenceIndex s p pass lane slice index]?.getD zeroBlock)
  if pass = 0 then next else xorBlock next (blocks[VG.Proof.Argon2.X86_64.FillKernel.currentIndex p lane slice index]?.getD zeroBlock)

theorem Done.represents {s t : State} {p : Params} {pass lane slice index : Nat}
    (ready : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) (done : VG.Proof.Argon2.X86_64.FillKernel.Done s t p pass lane slice index)
    (blocks : Array Block) (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p.blocks
      (blocks.set! (VG.Proof.Argon2.X86_64.FillKernel.currentIndex p lane slice index) (VG.Proof.Argon2.X86_64.FillKernel.nextBlock s p pass lane slice index blocks)) := by
  have currentBound := Proof.Argon2.current_cell_lt p ready.bounds.lanesPositive
    ready.bounds.laneBound ready.bounds.sliceBound ready.bounds.indexBound
  have previousBound := Proof.Argon2.previous_cell_lt p ready.bounds.lanesPositive
    ready.bounds.memoryMinimum ready.bounds.laneBound (column := VG.Proof.Argon2.X86_64.FillKernel.currentColumn p slice index)
  have referenceBound := Proof.Argon2.reference_cell_lt p ready.bounds.lanesPositive
    ready.bounds.memoryMinimum pass lane slice index (s.gpr .rdi) ready.bounds.laneBound
  apply represented.update (VG.Proof.Argon2.X86_64.FillKernel.currentIndex p lane slice index) currentBound (VG.Proof.Argon2.X86_64.FillKernel.nextBlock s p pass lane slice index blocks)
  · have block := done.block
    change blockAt t.mem (Proof.Argon2.matrixCell (VG.Proof.Argon2.X86_64.FillKernel.matrix s) (VG.Proof.Argon2.X86_64.FillKernel.currentIndex p lane slice index)) = _ at block
    have prev := represented.block (VG.Proof.Argon2.X86_64.FillKernel.previousIndex p lane slice index) previousBound
    have other := represented.block (VG.Proof.Argon2.X86_64.FillKernel.referenceIndex s p pass lane slice index) referenceBound
    have old := represented.block (VG.Proof.Argon2.X86_64.FillKernel.currentIndex p lane slice index) currentBound
    change blockAt s.mem (VG.Proof.Argon2.X86_64.FillKernel.previous s p lane slice index) = _ at prev
    change blockAt s.mem (VG.Proof.Argon2.X86_64.FillKernel.referenced s p pass lane slice index) = _ at other
    change blockAt s.mem (VG.Proof.Argon2.X86_64.FillKernel.current s p lane slice index) = _ at old
    rw [prev, other, old] at block
    exact block
  · intro j hj different
    apply FillCompress.block_frame done.frame
    intro r hr
    simp only [VG.Proof.Argon2.X86_64.FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have blocksBound := Nat.lt_of_le_of_lt (Proof.Argon2.blocks_le_memory p) ready.bounds.memoryBound
      exact Proof.Argon2.matrixCell_disjoint _ p.blocks j (VG.Proof.Argon2.X86_64.FillKernel.currentIndex p lane slice index)
        (Nat.lt_trans (Nat.mul_lt_mul_of_pos_right blocksBound (by decide)) (by decide)) hj currentBound different
    · exact ready.layout.matrixWork.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)
    · exact ready.layout.matrixStack.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)
    · exact (ready.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)).sub_right
        (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Relate the complete assembly step to the reviewed filling-state transition. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem update_spec (s : State) (p : Params) (pass lane slice index : Nat) (state : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (random : s.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    state.memory.set! (VG.Proof.Argon2.X86_64.FillKernel.currentIndex p lane slice index) (VG.Proof.Argon2.X86_64.FillKernel.nextBlock s p pass lane slice index state.memory) =
      (fillBlock p pass slice lane index state).memory := by
  rw [Proof.Argon2.FillStep.memory p pass lane slice index state active]
  unfold VG.Proof.Argon2.X86_64.FillKernel.nextBlock VG.Proof.Argon2.X86_64.FillKernel.referenceIndex
  rw [random]
  rfl

theorem code_spec_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index : Nat)
    (ready : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p.blocks state.memory)
    (random : s.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory) :
    WP isa Impl.Argon2.X86_64.FillKernel.code s fun t => VG.Proof.Argon2.X86_64.FillKernel.Done s t p pass lane slice index ∧
      Proof.Argon2.Represents t.mem (VG.Proof.Argon2.X86_64.FillKernel.matrix s) p.blocks (fillBlock p pass slice lane index state).memory := by
  refine (VG.Proof.Argon2.X86_64.FillKernel.code_ok s p pass lane slice index ready).mono ?_
  intro t done
  have represented' := done.represents ready state.memory represented
  rw [VG.Proof.Argon2.X86_64.FillKernel.update_spec s p pass lane slice index state ready.bounds.active random] at represented'
  exact ⟨done, represented'⟩

end VG.Proof.Argon2.X86_64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DependentWord`. -/
section

/-! Merged from `Proof.Argon2.X86_64.DependentWordPointer`. -/
section
/-! The data-dependent word's address is the specification's cyclic predecessor. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem args_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.DependentWord.args) s fun t =>
    t.gpr .rcx = s.gpr .rdi ∧ t.gpr .rax = s.gpr .rbx ∧ Divide.Keeps [.rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.DependentWord.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem pointer_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa VG.Impl.Argon2.X86_64.DependentWord.pointer s fun t =>
      t.gpr .rax = FillKernel.previous s p lane slice index ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold VG.Impl.Argon2.X86_64.DependentWord.pointer
  refine WP.seq ((FillKernel.load_ok s .r8 232 (h.layout.frameRead 232 (by simp))).mono ?_)
  rintro a ⟨base, ka⟩
  have k : Divide.Keeps ReferenceMap.changed s a := ka.mono (by decide)
  have pos := h.position.of_keeps k
  have columnBound := Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound
  have segment := Proof.Argon2.segmentLen_ge_two p h.bounds.lanesPositive h.bounds.memoryMinimum
  have q := Proof.Argon2.laneLen_segments p h.bounds.lanesPositive
  refine WP.seq ((FillColumn.code_nat_ok a slice p.segmentLen index p.laneLen
    pos.slice pos.segmentLength pos.index pos.laneLength (by omega)
    (Nat.lt_trans h.bounds.laneLength_bound (by decide)) columnBound).mono ?_)
  rintro b ⟨_, prev, kb⟩
  refine WP.seq ((VG.Proof.Argon2.X86_64.DependentWord.args_ok b).mono ?_)
  rintro c ⟨col, laneReg, kc⟩
  have col' := col.trans prev
  have lane' : c.gpr .rax = BitVec.ofNat 64 lane := laneReg.trans ((kb.regs .rbx (by decide)).trans pos.current)
  have length : c.gpr .r12 = BitVec.ofNat 64 p.laneLen :=
    (kc.regs .r12 (by decide)).trans ((kb.regs .r12 (by decide)).trans pos.laneLength)
  refine (BlockAddress.code_nat_ok c lane
    ((slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen) p.laneLen lane' col' length).mono ?_
  rintro t ⟨address, kt⟩
  refine ⟨?_, ((k.trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [address, kc.regs .r8 (by decide), kb.regs .r8 (by decide), base]
  rfl

end VG.Proof.Argon2.X86_64.DependentWord
end

/-! Select the specified secret random word from the public previous-cell address. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem read_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax) 8) :
    WP isa (.block Impl.Argon2.X86_64.DependentWord.read) s fun t => t.gpr .rdi = s.mem.readW (s.gpr .rax) 64 ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.DependentWord.read, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    VG.Proof.Argon2.X86_64.ea_at, BitVec.add_zero, hr, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem code_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa VG.Impl.Argon2.X86_64.DependentWord.code s fun t =>
      t.gpr .rdi = (blockAt s.mem (FillKernel.previous s p lane slice index))[0] ∧
      Divide.Keeps ReferenceMap.changed s t := by
  unfold VG.Impl.Argon2.X86_64.DependentWord.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.DependentWord.pointer_ok s p pass lane slice index h).mono ?_)
  rintro a ⟨pointer, keeps⟩
  have bound := Proof.Argon2.previous_column_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    (slice * p.segmentLen + index)
  have cover := h.layout.cell_cover h.bounds.lanesPositive h.bounds.laneBound bound
  have hr : InRegions (a.rd ++ a.wr) (a.gpr .rax) 8 := by
    rw [keeps.rd, keeps.wr, pointer]
    have contains : (⟨FillKernel.previous s p lane slice index, 1024⟩ : Region).Contains
        (FillKernel.previous s p lane slice index) 8 :=
      by simpa only [BitVec.add_zero] using (Offset.contains_base
        (FillKernel.previous s p lane slice index) (d := 0) (n := 8) (k := 1024) (by decide) (by decide))
    obtain ⟨r, hr, hc⟩ := cover _ _ ⟨⟨FillKernel.previous s p lane slice index, 1024⟩,
      by simp [FillKernel.previous, FillKernel.previousColumn, FillKernel.currentColumn], contains⟩
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (VG.Proof.Argon2.X86_64.DependentWord.read_ok a hr).mono ?_
  rintro t ⟨random, tail⟩
  refine ⟨?_, keeps.trans (tail.mono (by decide))⟩
  rw [random, pointer, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨0, by decide⟩ : Fin 128)]
  rw [blockAt_get]
  change s.mem.readW _ 64 = s.mem.readW (_ + 0#64) 64
  rw [BitVec.add_zero]

theorem code_spec_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa VG.Impl.Argon2.X86_64.DependentWord.code s fun t =>
      t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (VG.Proof.Argon2.X86_64.DependentWord.code_ok s p pass lane slice index h).mono ?_
  rintro t ⟨random, keeps⟩
  have bound := Proof.Argon2.previous_cell_lt p h.bounds.lanesPositive h.bounds.memoryMinimum
    h.bounds.laneBound (column := FillKernel.currentColumn p slice index)
  have block := represented.block (FillKernel.previousIndex p lane slice index) bound
  change blockAt s.mem (FillKernel.previous s p lane slice index) = _ at block
  rw [block] at random
  refine ⟨?_, keeps⟩
  simpa only [Proof.Argon2.FillStep.random, dependent, Bool.false_eq_true, ite_false, FillKernel.previousIndex, FillKernel.previousColumn,
    FillKernel.currentColumn] using random

end VG.Proof.Argon2.X86_64.DependentWord

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DeriveAbi`. -/
section

/-! Decode the reviewed System V contract without requiring normalized upper bits. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def abiWord (s : State) (d : Nat) : Addr := s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64
def abiParams (s : State) : Spec.Argon2.Params := Spec.Argon2.params
  ((s.gpr .rdi).setWidth 32).toNat ((s.gpr .r9).setWidth 32).toNat
  ((VG.Proof.Argon2.X86_64.Derive.abiWord s 8).setWidth 32).toNat ((VG.Proof.Argon2.X86_64.Derive.abiWord s 16).setWidth 32).toNat (VG.Proof.Argon2.X86_64.Derive.abiWord s 96).toNat

def abiInputs (s : State) : List Region :=
  [⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
    ⟨VG.Proof.Argon2.X86_64.Derive.abiWord s 32, (VG.Proof.Argon2.X86_64.Derive.abiWord s 40).toNat⟩, ⟨VG.Proof.Argon2.X86_64.Derive.abiWord s 48, (VG.Proof.Argon2.X86_64.Derive.abiWord s 56).toNat⟩]
def abiMatrix (s : State) : Region := ⟨VG.Proof.Argon2.X86_64.Derive.abiWord s 64, (VG.Proof.Argon2.X86_64.Derive.abiWord s 72).toNat * 1024⟩
def abiWork (s : State) : Region := ⟨VG.Proof.Argon2.X86_64.Derive.abiWord s 80, 16384⟩
def abiOutput (s : State) : Region := ⟨VG.Proof.Argon2.X86_64.Derive.abiWord s 88, (VG.Proof.Argon2.X86_64.Derive.abiWord s 96).toNat⟩
def abiArguments (s : State) : Region := ⟨s.gpr .rsp + BitVec.ofNat 64 8, 96⟩
def abiBuffers (s : State) : List (Region × Bool) :=
  (VG.Proof.Argon2.X86_64.Derive.abiInputs s).map (·, false) ++ [(VG.Proof.Argon2.X86_64.Derive.abiMatrix s, true), (VG.Proof.Argon2.X86_64.Derive.abiWork s, true), (VG.Proof.Argon2.X86_64.Derive.abiOutput s, true)]

structure AbiEnvironment (s : State) : Prop where
  stack : 344 ≤ (s.gpr .rsp).toNat
  wrap : (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64
  rd : s.rd = VG.Proof.Argon2.X86_64.Derive.abiInputs s ++ [VG.Proof.Argon2.X86_64.Derive.abiArguments s]
  wr : s.wr = [VG.Proof.Argon2.X86_64.Derive.abiMatrix s, VG.Proof.Argon2.X86_64.Derive.abiWork s, VG.Proof.Argon2.X86_64.Derive.abiOutput s]
  pairs : (VG.Proof.Argon2.X86_64.Derive.abiBuffers s ++ [(VG.Proof.Argon2.X86_64.Derive.abiArguments s, false)]).Pairwise
    (fun a b => (a.2 || b.2) → a.1.Disjoint b.1)
  reserved : ∀ r ∈ [⟨s.gpr .rsp, 8⟩, below (s.gpr .rsp) 344],
    ∀ b ∈ VG.Proof.Argon2.X86_64.Derive.abiBuffers s ++ [(VG.Proof.Argon2.X86_64.Derive.abiArguments s, false)], r.Disjoint b.1
  bounds : ∀ b ∈ VG.Proof.Argon2.X86_64.Derive.abiBuffers s, b.1.base.toNat + b.1.len ≤ 2 ^ 64
  kind : ((s.gpr .rdi).setWidth 32).toNat ≤ 2
  valid : Spec.Argon2.valid (VG.Proof.Argon2.X86_64.Derive.abiParams s) (s.gpr .rdx).toNat (s.gpr .r8).toNat
    (VG.Proof.Argon2.X86_64.Derive.abiWord s 40).toNat (VG.Proof.Argon2.X86_64.Derive.abiWord s 56).toNat
  threads : 1 ≤ ((VG.Proof.Argon2.X86_64.Derive.abiWord s 24).setWidth 32).toNat ∧ ((VG.Proof.Argon2.X86_64.Derive.abiWord s 24).setWidth 32).toNat < 2 ^ 24
  blocks : (VG.Proof.Argon2.X86_64.Derive.abiWord s 72).toNat = (VG.Proof.Argon2.X86_64.Derive.abiParams s).blocks

theorem abi_environment (s : State) (h : (Spec.Argon2.deriveContract X86_64.abi 344).pre s) :
    VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s := by
  sig_pre [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  constructor
  all_goals sig_eval [VG.Proof.Argon2.X86_64.Derive.abiInputs, VG.Proof.Argon2.X86_64.Derive.abiArguments, VG.Proof.Argon2.X86_64.Derive.abiMatrix, VG.Proof.Argon2.X86_64.Derive.abiWork, VG.Proof.Argon2.X86_64.Derive.abiOutput, VG.Proof.Argon2.X86_64.Derive.abiBuffers,
    VG.Proof.Argon2.X86_64.Derive.abiWord, VG.Proof.Argon2.X86_64.Derive.abiParams, below]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

end VG.Proof.Argon2.X86_64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DeriveFrame`. -/
section

/-! Compose the nested saved-register frames and the 272-byte local allocation. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def frameStart (s : State) : List Reg → State
  | [] => pushed (List.replicate 34 .rax) s
  | r :: rs => VG.Proof.Argon2.X86_64.Derive.frameStart (pushed [r] s) rs

def frameEnd (s : State) : List Reg → State
  | [] => popped .rax 34 s
  | r :: rs => popped r 1 (VG.Proof.Argon2.X86_64.Derive.frameEnd s rs)

theorem frameEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.gpr .rsp = (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).gpr .rsp)
    (wr : t.wr = (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).wr) :
    (VG.Proof.Argon2.X86_64.Derive.frameEnd t rs).gpr .rsp = s.gpr .rsp ∧ (VG.Proof.Argon2.X86_64.Derive.frameEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil =>
    constructor
    · rw [VG.Proof.Argon2.X86_64.Derive.frameEnd, popped_rsp, sp, VG.Proof.Argon2.X86_64.Derive.frameStart, pushed_rsp]
      simp only [List.length_replicate, Nat.reduceMul, BitVec.sub_add_cancel]
    · rw [VG.Proof.Argon2.X86_64.Derive.frameEnd, popped_wr, wr, VG.Proof.Argon2.X86_64.Derive.frameStart, pushed_wr]; rfl
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed [r] s) sp wr
    constructor
    · rw [VG.Proof.Argon2.X86_64.Derive.frameEnd, popped_rsp, innerSp, pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one, BitVec.sub_add_cancel]
    · rw [VG.Proof.Argon2.X86_64.Derive.frameEnd, popped_wr, innerWr, pushed_wr]; rfl

theorem frame_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (notSp : .rsp ∉ rs) (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (run : WP isa body (VG.Proof.Argon2.X86_64.Derive.frameStart s rs) fun t =>
      t.gpr .rsp = (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).gpr .rsp ∧ t.wr = (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).wr ∧ Q (VG.Proof.Argon2.X86_64.Derive.frameEnd t rs)) :
    WP isa (Impl.Argon2.X86_64.Derive.frame body rs) s Q := by
  induction rs generalizing s Q with
  | nil =>
    exact WP.frame (by decide) (by decide) (by decide) (by simpa using space) run
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have pushedBound : ((pushed [r] s).gpr .rsp).toNat = (s.gpr .rsp).toNat - 8 := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      exact toNat_sub_ofNat (by simp only [List.length_cons] at space; omega)
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega
    apply WP.frame (by simp) (by simpa using notSp.1) (Ne.symm notSp.1)
      (by simp only [List.length_cons] at space; simp only [List.length_singleton, Nat.mul_one]; omega)
    apply ih (pushed [r] s) (fun t => t.gpr .rsp = (pushed [r] s).gpr .rsp ∧
      t.wr = (pushed [r] s).wr ∧ Q (popped r 1 t)) notSp.2 innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    obtain ⟨endSp, endWr⟩ := VG.Proof.Argon2.X86_64.Derive.frameEnd_metadata (pushed [r] s) t rs sp wr
    exact ⟨sp, wr, endSp, endWr, result⟩

end VG.Proof.Argon2.X86_64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit`. -/
section

/-! Checked literal of the complete filling pointer setup. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FillPointers.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit`. -/
section

namespace VG.Impl.Argon2.X86_64.ReduceBlock

materialize_code VG.Impl.Argon2.X86_64.ReduceBlock.code

end VG.Impl.Argon2.X86_64.ReduceBlock

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DeriveLit`. -/
section

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapLit`. -/
section
/-! A checked literal for complete reference-index mapping. -/

namespace VG

materialize_code Impl.Argon2.X86_64.ReferenceMap.code

end VG
end

/-! Checked literals for the entry point's fixed instruction shapes. -/

namespace VG

materialize_code Impl.Argon2.X86_64.Derive.prepare
materialize_code Impl.Argon2.X86_64.FillSetup.code
materialize_code Impl.Argon2.X86_64.FinalReduction.code

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.InitialArgs`. -/
section

/-! # Argument handling for Argon2 H₀ -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Impl.Argon2.X86_64.HPrime (at_)

theorem ea_at (s : State) (r : Reg) (d : Nat) :
    s.ea (VG.Impl.Argon2.X86_64.HPrime.at_ r d) = s.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.Argon2.X86_64.HPrime.at_, BitVec.ofInt_natCast]

theorem headerWord_ok (s : State) (source destination : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 source) 8)
    (hw : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 destination) 4) :
    WP isa (.block (headerWord source destination)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 destination)
        ((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 source) 64).setWidth 32) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [headerWord, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    State.load64, State.store32, VG.Proof.Argon2.X86_64.Initial.ea_at, RegUpd.gpr_setReg, RegUpd.wr_setReg,
    RegUpd.rd_setReg, RegUpd.mem_setReg, hr, hw, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, trivial, trivial⟩
  intro r hr
  simp only [hr, ite_false]

structure LengthArgs (s : State) (offset : Nat) (t : State) : Prop where
  length : t.gpr .r14 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64
  count : t.gpr .rsi = s.gpr .r12
  pointer : t.gpr .rdx = s.gpr .rbx + 792
  size : t.gpr .rcx = 4
  other : ∀ r, r ≠ .r14 → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem.writeW (s.gpr .rbx + 792)
    ((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64).setWidth 32)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lengthArgs_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 offset) 8)
    (hw : InRegions s.wr (s.gpr .rbx + 792) 4) :
    WP isa (.block (lengthArgs offset)) s (VG.Proof.Argon2.X86_64.Initial.LengthArgs s offset) := by
  apply WP.of_runBlock
  simp only [lengthArgs, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    VG.X86_64.readSrc32, State.setReg32, State.load64, State.store32, execAlu, VG.Proof.Argon2.X86_64.Initial.ea_at,
    RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.rd_setReg,
    RegUpd.mem_setReg, hr, hw, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.ofNat 64 792 = (792 : Addr) from rfl]
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r h1 h2 h3 h4
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, h4, ite_false]

structure InputArgs (s t : State) (offset : Nat) : Prop where
  total : t.gpr .r12 = s.gpr .r12 + 4
  count : t.gpr .rsi = s.gpr .r12 + 4
  pointer : t.gpr .rdx = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64
  length : t.gpr .rcx = s.gpr .r14
  other : ∀ r, r ≠ .r12 → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem inputArgs_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (inputArgs offset)) s (fun t => VG.Proof.Argon2.X86_64.Initial.InputArgs s t offset) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    State.load64, execAlu, VG.Proof.Argon2.X86_64.Initial.ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, hr, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r h1 h2 h3 h4
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, h4, ite_false]

end VG.Proof.Argon2.X86_64.Initial

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DeriveNormalize`. -/
section

/-! Normalize u32 stack arguments without assuming anything about their upper bits. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.Derive

structure Normalized (s t : State) (d : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d)
    (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem normalize_ok (s : State) (d : Nat)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (write : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    WP isa (.block (normalize d)) s (VG.Proof.Argon2.X86_64.Derive.Normalized s · d) := by
  apply WP.of_runBlock
  simp only [normalize, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    VG.X86_64.readSrc32, State.load64, State.store64, State.setReg32, State.ea, Impl.Argon2.X86_64.at_, BitVec.ofInt_natCast,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    read, write, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem Normalized.word {s t : State} {d : Nat} (h : VG.Proof.Argon2.X86_64.Derive.Normalized s t d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
      (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64) := by
  rw [h.regs .rbp (by decide), h.mem, Mem.readW_writeW_self64]

theorem Normalized.frame {s t : State} {d : Nat} (h : VG.Proof.Argon2.X86_64.Derive.Normalized s t d) :
    Frame [⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Normalized.other_word {s t : State} {d : Nat} (h : VG.Proof.Argon2.X86_64.Derive.Normalized s t d)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 < 2 ^ 64) (dd : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .rbp (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate (Nat.le_of_lt ed) (Nat.le_of_lt dd)) (by decide)

end VG.Proof.Argon2.X86_64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Parameters`. -/
section

/-! Merged from `Proof.Argon2.X86_64.ParametersSteps`. -/
section
/-! Public frame loads and fixed arithmetic for the RFC's rounded memory dimensions. -/

namespace VG.Proof.Argon2.X86_64.Parameters

open VG VG.X86_64

theorem args_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 176) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8) :
    WP isa (.block Impl.Argon2.X86_64.Parameters.args) s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 176) 64 ∧
      t.gpr .rsi = (s.mem.readW (off (s.gpr .rbp) 184) 64) * 4 ∧ Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Parameters.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, State.load64, VG.Proof.Argon2.X86_64.ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, memoryRead, lanesRead, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
    all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.X86_64.Parameters.finish) s fun t =>
    t.gpr .r13 = s.gpr .r9 * 4 ∧ Divide.Keeps [.r13] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Parameters.finish, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

end VG.Proof.Argon2.X86_64.Parameters
end

/-! Exact rounded lane length using the verified fixed-time divider. -/

namespace VG.Proof.Argon2.X86_64.Parameters

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 176) 8
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  memoryWord : s.mem.readW (off (s.gpr .rbp) 176) 64 = BitVec.ofNat 64 p.memory
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes
  positive : 0 < p.lanes
  memoryBound : p.memory < 2 ^ 32
  lanesBound : p.lanes < 2 ^ 24

def changed : List Reg := [.rdi, .rsi] ++ Divide.changed ++ [.r13]

theorem code_ok (s : State) (p : Params) (h : VG.Proof.Argon2.X86_64.Parameters.Ready p s) :
    WP isa Impl.Argon2.X86_64.Parameters.code s fun t =>
      t.gpr .r13 = BitVec.ofNat 64 p.laneLen ∧ Divide.Keeps VG.Proof.Argon2.X86_64.Parameters.changed s t := by
  unfold Impl.Argon2.X86_64.Parameters.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.Parameters.args_ok s h.memoryRead h.lanesRead).mono ?_)
  rintro a ⟨memory, lanes, ka⟩
  have divisor : a.gpr .rsi = BitVec.ofNat 64 (4 * p.lanes) := by
    rw [lanes, h.lanesWord, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  have n : (a.gpr .rdi).toNat = p.memory := by
    rw [memory, h.memoryWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.memoryBound (by decide))]
  have bound : 4 * p.lanes < 2 ^ 32 := by have lanesBound := h.lanesBound; omega
  have d : (a.gpr .rsi).toNat = 4 * p.lanes := by
    rw [divisor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  refine WP.seq ((Divide.code_ok a (by rw [n]; exact h.memoryBound)
    (by rw [d]; have positive := h.positive; omega) (by rw [d]; exact bound)).mono ?_)
  rintro b ⟨quotient, _, kb⟩
  rw [n, d] at quotient
  have word : b.gpr .r9 = BitVec.ofNat 64 (p.memory / (4 * p.lanes)) := by
    rw [← quotient]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (VG.Proof.Argon2.X86_64.Parameters.finish_ok b).mono ?_
  rintro t ⟨value, kt⟩
  refine ⟨?_, (ka.mono (by simp [VG.Proof.Argon2.X86_64.Parameters.changed])).trans
    ((kb.mono (by
      intro r hr
      simp only [VG.Proof.Argon2.X86_64.Parameters.changed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl (Or.inr hr))).trans (kt.mono (by simp [VG.Proof.Argon2.X86_64.Parameters.changed])))⟩
  rw [value, word, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul,
    Nat.mul_comm, ← Proof.Argon2.laneLen_eq p h.positive]

end VG.Proof.Argon2.X86_64.Parameters

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DeriveSaved`. -/
section

/-! Merged from `Proof.Argon2.X86_64.DeriveFrameState`. -/
section
/-! Exact stack depth and memory modified by the entry-point prologue. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_sp (s : State) (rs : List Reg) :
    (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (272 + 8 * rs.length) := by
  induction rs generalizing s with
  | nil => rw [VG.Proof.Argon2.X86_64.Derive.frameStart, pushed_rsp]; rfl
  | cons r rs ih =>
    rw [VG.Proof.Argon2.X86_64.Derive.frameStart, ih, pushed_rsp]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
    exact congrArg (fun n => s.gpr .rsp - BitVec.ofNat 64 n) (by omega)

theorem frameStart_reg (s : State) (rs : List Reg) (r : Reg) (notSp : r ≠ .rsp) :
    (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => exact pushed_gpr _ _ notSp
  | cons x xs ih => exact (ih (pushed [x] s)).trans (pushed_gpr _ _ notSp)

theorem frameStart_rd (s : State) (rs : List Reg) : (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).rd = s.rd := by
  induction rs generalizing s with
  | nil => exact pushed_rd ..
  | cons r rs ih => exact (ih (pushed [r] s)).trans (pushed_rd ..)

theorem frameStart_frame (s : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat) :
    Frame [below (s.gpr .rsp) (272 + 8 * rs.length)] s.mem (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).mem := by
  induction rs generalizing s with
  | nil =>
    exact (pushRegs_mem s (List.replicate 34 .rax) (by decide) (by simpa using space)).1
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have enough : 8 ≤ (s.gpr .rsp).toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      rw [toNat_sub_ofNat enough]
      simp only [List.length_cons] at space; omega
    have outer := (pushRegs_mem s [r] (by simpa using notSp.1)
      (by simpa using enough)).1
    have inner := ih (pushed [r] s) notSp.2 innerSpace
    apply (outer.sub ?_).trans (inner.sub ?_)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Offset.sub_below (s.gpr .rsp) (by simp only [List.length_cons, List.length_nil]; omega)
        (by simp only [List.length_singleton, Nat.mul_one]; omega)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [pushed_rsp]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one, below]
      rw [BitVec.sub_sub, ← BitVec.ofNat_add,
        show 8 + (272 + 8 * rs.length) = 272 + 8 * (rs.length + 1) by omega]
      exact Region.sub_prefix (by omega)

theorem frameEnd_mem (s : State) (rs : List Reg) : (VG.Proof.Argon2.X86_64.Derive.frameEnd s rs).mem = s.mem := by
  induction rs with
  | nil => exact popped_mem ..
  | cons r rs ih => exact (popped_mem ..).trans ih

theorem frameEnd_rd (s : State) (rs : List Reg) : (VG.Proof.Argon2.X86_64.Derive.frameEnd s rs).rd = s.rd := by
  induction rs with
  | nil => exact popped_rd ..
  | cons r rs ih => exact (popped_rd ..).trans ih

end VG.Proof.Argon2.X86_64.Derive
end

/-! The nested prologue stores every callee-saved register at its exact ABI slot. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_word (s : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat) (j : Nat) (bound : j < rs.length) :
    (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s j with
  | nil => exact absurd bound (Nat.not_lt_zero _)
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have enough : 8 ≤ (s.gpr .rsp).toNat := by simp only [List.length_cons] at space; omega
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      rw [toNat_sub_ofNat enough]
      simp only [List.length_cons] at space; omega
    cases j with
    | zero =>
      have stored := (pushRegs_mem s [r] (by simpa using notSp.1)
        (by simpa using enough)).2 0 (by simp)
      have inner := VG.Proof.Argon2.X86_64.Derive.frameStart_frame (pushed [r] s) rs notSp.2 innerSpace
      have unchanged : (VG.Proof.Argon2.X86_64.Derive.frameStart (pushed [r] s) rs).mem.readW ((pushed [r] s).gpr .rsp) 64 =
          (pushed [r] s).mem.readW ((pushed [r] s).gpr .rsp) 64 := inner.readW
        (r := ⟨(pushed [r] s).gpr .rsp, 8⟩) (Region.contains_self _ _) (by
          intro region hr
          simp only [List.mem_singleton] at hr; subst region
          apply Offset.base_disjoint_below
          have limit := (s.gpr .rsp).isLt
          simp only [List.length_cons] at space; omega) (by decide)
      rw [pushed_rsp] at unchanged
      simp only [List.length_singleton, Nat.mul_one] at unchanged
      exact unchanged.trans stored
    | succ j =>
      have word := ih (pushed [r] s) notSp.2 innerSpace j (by simpa using bound)
      rw [pushed_rsp, pushed_gpr _ _ (fun h => notSp.2 (h ▸ List.getElem_mem _))] at word
      simp only [List.length_singleton, Nat.mul_one] at word
      rw [BitVec.sub_sub, ← BitVec.ofNat_add,
        show 8 + 8 * (j + 1) = 8 * (j + 1 + 1) by omega] at word
      exact word

end VG.Proof.Argon2.X86_64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.DeriveRegions`. -/
section

/-! Merged from `Proof.Argon2.X86_64.DeriveStore`. -/
section
/-! Save each incoming argument with one short symbolic execution. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure Stored (s t : State) (d : Nat) (r : Reg) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d) (s.gpr r)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem store_ok (s : State) (d : Nat) (r : Reg)
    (write : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store (Impl.Argon2.X86_64.at_ .rbp d) r]) s (VG.Proof.Argon2.X86_64.Derive.Stored s · d r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    State.ea, Impl.Argon2.X86_64.at_, BitVec.ofInt_natCast, write,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Stored.word {s t : State} {d : Nat} {r : Reg} (h : VG.Proof.Argon2.X86_64.Derive.Stored s t d r) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.gpr r := by
  rw [h.regs, h.mem, Mem.readW_writeW_self64]

theorem Stored.frame {s t : State} {d : Nat} {r : Reg} (h : VG.Proof.Argon2.X86_64.Derive.Stored s t d r) :
    Frame [⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Stored.other_word {s t : State} {d : Nat} {r : Reg} (h : VG.Proof.Argon2.X86_64.Derive.Stored s t d r)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 ≤ 2 ^ 64) (dd : d + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate ed dd) (by decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveStores`. -/
section
/-! Compose argument stores without re-executing a growing symbolic memory state. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def saveMemory (s : State) (args : List (Nat × Reg)) : Mem :=
  args.foldl (fun m arg => m.writeW (s.gpr .rbp + BitVec.ofNat 64 arg.1) (s.gpr arg.2)) s.mem

structure Saved (s t : State) (args : List (Nat × Reg)) : Prop where
  mem : t.mem = VG.Proof.Argon2.X86_64.Derive.saveMemory s args
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (args.map fun arg => (⟨s.gpr .rbp + BitVec.ofNat 64 arg.1, 8⟩ : Region)) s.mem t.mem

theorem stores_ok (args : List (Nat × Reg)) (s : State)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 arg.1) 8) :
    WP isa (.block (args.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2)) s (VG.Proof.Argon2.X86_64.Derive.Saved s · args) := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons arg args ih =>
    rw [List.map_cons]
    change WP isa (.block (([.store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (VG.Proof.Argon2.X86_64.Derive.store_ok s arg.1 arg.2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))).mono ?_
    intro u hu
    refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
    · rw [hu.mem]
      unfold VG.Proof.Argon2.X86_64.Derive.saveMemory
      rw [ht.regs, ht.mem, List.foldl_cons]
    · apply (ht.frame.mono ?_).trans
      · have frame := hu.frame
        rw [ht.regs] at frame
        exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
      · intro region hr
        simp only [List.mem_singleton] at hr; subst region
        exact List.mem_cons_self ..

theorem Saved.other_word {s t : State} {args : List (Nat × Reg)} (h : VG.Proof.Argon2.X86_64.Derive.Saved s t args)
    (e : Nat) (bound : e + 8 ≤ 2 ^ 64)
    (separate : ∀ arg ∈ args, e + 8 ≤ arg.1 ∨ arg.1 + 8 ≤ e)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨arg, member, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate arg member) bound (bounds arg member)

theorem stores_values_ok (args : List (Nat × Reg)) (s : State)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 arg.1) 8)
    (separate : args.Pairwise fun a b => a.1 + 8 ≤ b.1 ∨ b.1 + 8 ≤ a.1)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    WP isa (.block (args.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2)) s fun t =>
      VG.Proof.Argon2.X86_64.Derive.Saved s t args ∧ ∀ arg ∈ args, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = s.gpr arg.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩, by simp⟩
  | cons arg args ih =>
    obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
    rw [List.map_cons]
    change WP isa (.block (([.store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (VG.Proof.Argon2.X86_64.Derive.store_ok s arg.1 arg.2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))
      tailSep (fun a ha => bounds a (List.mem_cons_of_mem arg ha))).mono ?_
    rintro u ⟨hu, values⟩
    have saved : VG.Proof.Argon2.X86_64.Derive.Saved s u (arg :: args) := by
      refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
      · rw [hu.mem]; unfold VG.Proof.Argon2.X86_64.Derive.saveMemory; rw [ht.regs, ht.mem, List.foldl_cons]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..
    refine ⟨saved, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hu.other_word a.1 (bounds a (List.mem_cons_self ..)) headSep
        (fun b hb => bounds b (List.mem_cons_of_mem a hb))]
      exact ht.word
    · rw [values a ha, ht.regs]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveSetup`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveScratch`. -/
section
/-! Load the caller-supplied hash workspace after saving incoming arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure ScratchLoaded (s t : State) : Prop where
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rbp + 248) 64
  regs : ∀ r, r ≠ .rbx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem scratch_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 248) 8) :
    WP isa (.block [.mov .rbx (.mem (Impl.Argon2.X86_64.at_ .rbp 248))]) s (VG.Proof.Argon2.X86_64.Derive.ScratchLoaded s) := by
  have ea : s.ea (Impl.Argon2.X86_64.at_ .rbp 248) = s.gpr .rbp + 248 := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea, read,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact RegUpd.gpr_setReg_self ..
  · intro r hr
    exact RegUpd.gpr_setReg_of_ne _ _ hr

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveEntry`. -/
section
/-! Establish the local frame base and normalize register-passed u32 arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure Entered (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  kind : t.gpr .rdi = ((s.gpr .rdi).setWidth 32).setWidth 64
  passes : t.gpr .r9 = ((s.gpr .r9).setWidth 32).setWidth 64
  regs : ∀ r, r ≠ .rbp → r ≠ .rdi → r ≠ .r9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem entry_ok (s : State) :
    WP isa (.block [.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9)]) s (VG.Proof.Argon2.X86_64.Derive.Entered s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, reduceCtorEq,
    ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hb hd h9
  simp only [RegUpd.gpr_setReg, hb, hd, h9, ite_false]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Save the register arguments into the local derivation frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def arguments : List (Nat × Reg) :=
  [(72, .r9), (80, .r8), (88, .rcx), (96, .rdx), (104, .rsi), (112, .rdi)]

def argumentValue (s : State) (r : Reg) : Addr :=
  if r = .rdi ∨ r = .r9 then ((s.gpr r).setWidth 32).setWidth 64 else s.gpr r

theorem Entered.argument {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.Entered s t) (r : Reg) (bp : r ≠ .rbp) :
    t.gpr r = VG.Proof.Argon2.X86_64.Derive.argumentValue s r := by
  unfold VG.Proof.Argon2.X86_64.Derive.argumentValue
  by_cases di : r = .rdi
  · subst r; rw [ite_eq_left (Or.inl rfl)]; exact h.kind
  · by_cases nine : r = .r9
    · subst r; rw [ite_eq_left (Or.inr rfl)]; exact h.passes
    · rw [ite_eq_right (by simp only [di, nine, or_self, not_false_eq_true])]
      exact h.regs r bp di nine

structure SetupDone (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 248) 64
  values : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = VG.Proof.Argon2.X86_64.Derive.argumentValue s arg.2
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame [⟨s.gpr .rsp, 120⟩] s.mem t.mem

theorem setup_ok (s : State) (frameWrite : Covers [⟨s.gpr .rsp, 120⟩] s.wr)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 248) 8) :
    WP isa (.block Impl.Argon2.X86_64.Derive.setup) s (VG.Proof.Argon2.X86_64.Derive.SetupDone s) := by
  change WP isa (.block (([.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9)] : List Instr) ++
    (arguments.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2) ++
    ([.mov .rbx (.mem (Impl.Argon2.X86_64.at_ .rbp 248))] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Derive.entry_ok s).mono ?_
  intro a entered
  rw [WP.block_append_iff]
  have write : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, InRegions a.wr (a.gpr .rbp + BitVec.ofNat 64 arg.1) 8 := by
    intro arg ha
    rw [entered.wr, entered.bp]
    apply frameWrite
    have bounds : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, arg.1 + 8 ≤ 120 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (bounds arg ha) (by have := bounds arg ha; omega)⟩
  refine (VG.Proof.Argon2.X86_64.Derive.stores_values_ok VG.Proof.Argon2.X86_64.Derive.arguments a write (by decide) (by decide)).mono ?_
  rintro b ⟨saved, values⟩
  have bp : b.gpr .rbp = s.gpr .rsp := by rw [saved.regs, entered.bp]
  have scratchWord : b.mem.readW (b.gpr .rbp + 248) 64 = s.mem.readW (s.gpr .rsp + 248) 64 := by
    have kept := saved.other_word 248 (by decide) (by decide) (by decide)
    change b.mem.readW (b.gpr .rbp + 248) 64 = a.mem.readW (a.gpr .rbp + 248) 64 at kept
    rw [kept, entered.bp, entered.mem]
  refine (VG.Proof.Argon2.X86_64.Derive.scratch_ok b (by rw [saved.rd, saved.wr, bp, entered.rd, entered.wr]; exact read)).mono ?_
  intro t loaded
  refine ⟨(loaded.regs .rbp (by decide)).trans bp, ?_, loaded.scratch.trans scratchWord, ?_, ?_,
    loaded.rd.trans (saved.rd.trans entered.rd), loaded.wr.trans (saved.wr.trans entered.wr),
    loaded.mxcsr.trans (saved.mxcsr.trans entered.mxcsr), ?_⟩
  · rw [loaded.regs .rsp (by decide), saved.regs]
    exact entered.regs .rsp (by decide) (by decide) (by decide)
  · intro arg ha
    rw [loaded.mem, loaded.regs .rbp (by decide), values arg ha]
    have notBp : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, arg.2 ≠ .rbp := by decide
    exact entered.argument arg.2 (notBp arg ha)
  · intro r hr hb hx
    have other : ∀ r ∈ calleeSaved, r ≠ .rdi ∧ r ≠ .r9 := by decide
    rw [loaded.regs r hx, saved.regs]
    exact entered.regs r hb (other r hr).1 (other r hr).2
  · rw [loaded.mem, ← entered.mem]
    have frame := saved.frame
    rw [entered.bp] at frame
    apply frame.sub
    intro region hr
    obtain ⟨arg, ha, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, arg.1 + 8 ≤ 120 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (bounds arg ha)⟩

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePrologue`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DerivePrivatePrepare`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DerivePrepare`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveNormalizeArgs`. -/
section
/-! Normalize distinct stack slots while retaining every other frame word. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def normalizedWord (s : State) (d : Nat) : Addr :=
  (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)

structure NormalizedArgs (s t : State) (ds : List Nat) : Prop where
  values : ∀ d ∈ ds, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = VG.Proof.Argon2.X86_64.Derive.normalizedWord s d
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (ds.map fun d => (⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩ : Region)) s.mem t.mem

theorem NormalizedArgs.other_word {s t : State} {ds : List Nat} (h : VG.Proof.Argon2.X86_64.Derive.NormalizedArgs s t ds)
    (e : Nat) (bound : e + 8 < 2 ^ 64)
    (separate : ∀ d ∈ ds, e + 8 ≤ d ∨ d + 8 ≤ e)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .rbp (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate d hd) (Nat.le_of_lt bound) (Nat.le_of_lt (bounds d hd))

theorem normalizeArgs_ok (ds : List Nat) (s : State)
    (read : ∀ d ∈ ds, InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ ds, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (separate : ds.Pairwise fun d e => d + 8 ≤ e ∨ e + 8 ≤ d)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    WP isa (Impl.Argon2.X86_64.Derive.normalizeArgs ds) s (VG.Proof.Argon2.X86_64.Derive.NormalizedArgs s · ds) := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons d ds ih =>
    cases ds with
    | nil =>
      refine (VG.Proof.Argon2.X86_64.Derive.normalize_ok s d (read d (by simp)) (write d (by simp))).mono ?_
      intro t ht
      exact ⟨fun e he => by simp only [List.mem_singleton] at he; subst e; exact ht.word,
        ht.regs, ht.rd, ht.wr, ht.mxcsr, ht.frame⟩
    | cons e ds =>
      obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
      refine WP.seq ((VG.Proof.Argon2.X86_64.Derive.normalize_ok s d (read d (List.mem_cons_self ..))
        (write d (List.mem_cons_self ..))).mono ?_)
      intro t ht
      refine (ih t
        (fun x hx => by rw [ht.rd, ht.wr, ht.regs .rbp (by decide)]; exact read x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.wr, ht.regs .rbp (by decide)]; exact write x (List.mem_cons_of_mem d hx))
        tailSep (fun x hx => bounds x (List.mem_cons_of_mem d hx))).mono ?_
      intro u hu
      refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
        hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hu.other_word x (bounds x (List.mem_cons_self ..)) headSep
            (fun a ha => bounds a (List.mem_cons_of_mem x ha))]
          exact ht.word
        · rw [hu.values x hx]
          unfold VG.Proof.Argon2.X86_64.Derive.normalizedWord
          have sep : x + 8 ≤ d ∨ d + 8 ≤ x := (headSep x hx).symm
          rw [ht.other_word x sep (bounds x (List.mem_cons_of_mem d hx)) (bounds d (List.mem_cons_self ..))]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs .rbp (by decide)] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..

end VG.Proof.Argon2.X86_64.Derive
end

/-! Complete ABI preparation retains the inputs and exposes normalized public arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def normalizedOffsets : List Nat := [176, 184, 192]

def prepareWrites (s : State) : List Region :=
  ⟨s.gpr .rsp, 120⟩ :: normalizedOffsets.map fun d => ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩

theorem SetupDone.other_word {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.SetupDone s t) (d : Nat)
    (afterFrame : 120 ≤ d) (bound : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_singleton] at hr; subst region
  simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .rsp) (d := d) (n := 8) (e := 0) (k := 120)
    (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)

structure Prepared (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 248) 64
  values : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = VG.Proof.Argon2.X86_64.Derive.argumentValue s arg.2
  normalized : ∀ d ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
    (((s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (VG.Proof.Argon2.X86_64.Derive.prepareWrites s) s.mem t.mem

theorem Prepared.other_word {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.Prepared s t) (d : Nat)
    (afterFrame : 120 ≤ d) (bound : d + 8 < 2 ^ 64)
    (separate : ∀ e ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, d + 8 ≤ e ∨ e + 8 ≤ d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .rsp) (d := d) (n := 8) (e := 0) (k := 120)
      (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ e ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, e + 8 ≤ 2 ^ 64 := by decide
    exact Offset.disjoint _ (separate e he) (Nat.le_of_lt bound) (bounds e he)

theorem prepareLocal_ok (s : State) (frameWrite : Covers [⟨s.gpr .rsp, 120⟩] s.wr)
    (read : ∀ d ∈ 248 :: VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 d) 8) :
    WP isa Impl.Argon2.X86_64.Derive.prepareLocal s (VG.Proof.Argon2.X86_64.Derive.Prepared s) := by
  unfold Impl.Argon2.X86_64.Derive.prepareLocal
  have scratchRead : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 248) 8 := read 248 (List.mem_cons_self ..)
  refine WP.seq ((VG.Proof.Argon2.X86_64.Derive.setup_ok s frameWrite scratchRead).mono ?_)
  intro a setup
  refine (VG.Proof.Argon2.X86_64.Derive.normalizeArgs_ok VG.Proof.Argon2.X86_64.Derive.normalizedOffsets a
    (fun d hd => by rw [setup.rd, setup.wr, setup.bp]; exact read d (List.mem_cons_of_mem _ hd))
    (fun d hd => by rw [setup.wr, setup.bp]; exact write d hd) (by decide) (by decide)).mono ?_
  intro t normalized
  refine ⟨(normalized.regs .rbp (by decide)).trans setup.bp,
    (normalized.regs .rsp (by decide)).trans setup.sp,
    (normalized.regs .rbx (by decide)).trans setup.scratch, ?_, ?_, ?_,
    normalized.rd.trans setup.rd, normalized.wr.trans setup.wr, normalized.mxcsr.trans setup.mxcsr, ?_⟩
  · intro arg ha
    have bound : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, arg.1 + 8 < 2 ^ 64 := by decide
    have separate : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, ∀ d ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, arg.1 + 8 ≤ d ∨ d + 8 ≤ arg.1 := by decide
    rw [normalized.other_word arg.1 (bound arg ha) (separate arg ha) (by decide)]
    exact setup.values arg ha
  · intro d hd
    rw [normalized.values d hd]
    unfold VG.Proof.Argon2.X86_64.Derive.normalizedWord
    have afterFrame : ∀ d ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, 120 ≤ d := by decide
    have bound : ∀ d ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, d + 8 < 2 ^ 64 := by decide
    rw [setup.other_word d (afterFrame d hd) (bound d hd)]
  · intro r hr hb hx
    have notAx : ∀ r ∈ calleeSaved, r ≠ .rax := by decide
    exact (normalized.regs r (notAx r hr)).trans (setup.regs r hr hb hx)
  · apply (setup.frame.mono (by
      intro region hr
      simp only [List.mem_singleton] at hr
      subst region
      exact List.mem_cons_self ..)).trans
    have frame := normalized.frame
    rw [setup.bp] at frame
    exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveCopyArgs`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveCopyArg`. -/
section
/-! Copy a read-only caller argument into the private derivation frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def copySource (j : Nat) : Nat := 328 + 8 * j
def copyDestination (j : Nat) : Nat := 176 + 8 * j

structure CopiedArg (s t : State) (j : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j))
    (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 64)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem copyArg_ok (s : State) (j : Nat)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 8)
    (write : InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j)) 8) :
    WP isa (.block (Impl.Argon2.X86_64.Derive.copyArg j)) s (VG.Proof.Argon2.X86_64.Derive.CopiedArg s · j) := by
  change InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (328 + 8 * j)) 8 at read
  change InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (176 + 8 * j)) 8 at write
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Derive.copyArg, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load64, State.store64, readSrc, State.ea, Impl.Argon2.X86_64.at_,
    BitVec.ofInt_natCast, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, read, write, reduceCtorEq,
    ite_true, ite_false, Option.some.injEq, Option.map_some, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem CopiedArg.frame {s t : State} {j : Nat} (h : VG.Proof.Argon2.X86_64.Derive.CopiedArg s t j) :
    Frame [⟨s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j), 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem CopiedArg.word {s t : State} {j : Nat} (h : VG.Proof.Argon2.X86_64.Derive.CopiedArg s t j) :
    t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j)) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 64 := by
  rw [h.regs .rsp (by decide), h.mem, Mem.readW_writeW_self64]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Copy all stack arguments without modifying their caller-owned storage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure CopiedArgs (s t : State) (js : List Nat) : Prop where
  values : ∀ j ∈ js, t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j)) 64 =
    s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 64
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (js.map fun j => (⟨s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j), 8⟩ : Region)) s.mem t.mem

theorem CopiedArgs.other_word {s t : State} {js : List Nat} (h : VG.Proof.Argon2.X86_64.Derive.CopiedArgs s t js)
    (d : Nat) (bound : d + 8 ≤ 2 ^ 64)
    (separate : ∀ j ∈ js, d + 8 ≤ VG.Proof.Argon2.X86_64.Derive.copyDestination j ∨ VG.Proof.Argon2.X86_64.Derive.copyDestination j + 8 ≤ d)
    (bounds : ∀ j ∈ js, VG.Proof.Argon2.X86_64.Derive.copyDestination j + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.regs .rsp (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate j hj) bound (bounds j hj)

theorem copyArgs_ok (js : List Nat) (s : State) (bounds : ∀ j ∈ js, j < 12)
    (distinct : js.Nodup)
    (read : ∀ j ∈ js, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 8)
    (write : ∀ j ∈ js, InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j)) 8) :
    WP isa (.block (js.flatMap Impl.Argon2.X86_64.Derive.copyArg)) s (VG.Proof.Argon2.X86_64.Derive.CopiedArgs s · js) := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons j js ih =>
    have nodup := List.nodup_cons.mp distinct
    have jBound := bounds j (List.mem_cons_self ..)
    have tailBounds : ∀ x ∈ js, x < 12 := fun x hx => bounds x (List.mem_cons_of_mem _ hx)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine (VG.Proof.Argon2.X86_64.Derive.copyArg_ok s j (read j (List.mem_cons_self ..)) (write j (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t tailBounds nodup.2
      (fun x hx => by rw [ht.rd, ht.wr, ht.regs .rsp (by decide)]; exact read x (List.mem_cons_of_mem _ hx))
      (fun x hx => by rw [ht.wr, ht.regs .rsp (by decide)]; exact write x (List.mem_cons_of_mem _ hx))).mono ?_
    intro u hu
    refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
      hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hu.other_word (VG.Proof.Argon2.X86_64.Derive.copyDestination x) (by unfold VG.Proof.Argon2.X86_64.Derive.copyDestination; omega) (by
          intro y hy
          have ne : y ≠ x := fun eq => nodup.1 (eq ▸ hy)
          unfold VG.Proof.Argon2.X86_64.Derive.copyDestination; omega) (by
          intro y hy; have := tailBounds y hy; unfold VG.Proof.Argon2.X86_64.Derive.copyDestination; omega)]
        exact ht.word
      · rw [hu.values x hx, ht.regs .rsp (by decide), ht.mem]
        apply Mem.readW_writeW_sep ?_ (by decide)
        have xBound := tailBounds x hx
        exact Offset.sep _ (Or.inr (by unfold VG.Proof.Argon2.X86_64.Derive.copyDestination VG.Proof.Argon2.X86_64.Derive.copySource; omega))
          (by unfold VG.Proof.Argon2.X86_64.Derive.copySource; omega) (by unfold VG.Proof.Argon2.X86_64.Derive.copyDestination; omega)
    · apply (ht.frame.mono ?_).trans
      · have frame := hu.frame
        rw [ht.regs .rsp (by decide)] at frame
        exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
      · intro region hr
        simp only [List.mem_singleton] at hr; subst region
        exact List.mem_cons_self ..

end VG.Proof.Argon2.X86_64.Derive
end

/-! Prepare private copies of every ABI argument, preserving caller-owned storage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def privateWrites (s : State) : List Region := [⟨s.gpr .rsp, 120⟩, ⟨s.gpr .rsp + 176, 96⟩]

structure PrivatePrepared (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 400) 64
  values : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = VG.Proof.Argon2.X86_64.Derive.argumentValue s arg.2
  stackWords : ∀ j < 12, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j)) 64 =
    let w := s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 64
    if j < 3 then (w.setWidth 32).setWidth 64 else w
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.Derive.privateWrites s) s.mem t.mem

theorem private_prepare_ok (s : State) (locals : Covers [⟨s.gpr .rsp, 272⟩] s.wr)
    (read : ∀ j < 12, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 8) :
    WP isa Impl.Argon2.X86_64.Derive.prepare s (VG.Proof.Argon2.X86_64.Derive.PrivatePrepared s) := by
  have localWord : ∀ d, d + 8 ≤ 272 → InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 d) 8 := by
    intro d hd
    exact locals _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  unfold Impl.Argon2.X86_64.Derive.prepare Impl.Argon2.X86_64.Derive.copyArgs
  refine WP.seq ((VG.Proof.Argon2.X86_64.Derive.copyArgs_ok (List.range 12) s
    (fun _ h => List.mem_range.mp h) List.nodup_range (fun j h => read j (List.mem_range.mp h))
    (fun j h => localWord _ (by have := List.mem_range.mp h; unfold VG.Proof.Argon2.X86_64.Derive.copyDestination; omega))).mono ?_)
  intro a copied
  have sp := copied.regs .rsp (by decide)
  refine (VG.Proof.Argon2.X86_64.Derive.prepareLocal_ok a (by
    intro p n h
    rw [copied.wr]
    rw [sp] at h
    apply locals p n
    exact Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, 0, (BitVec.add_zero _).symm, show 0 + 120 ≤ 272 by decide⟩) p n h)
    (by
      intro d hd
      rw [copied.rd, copied.wr, sp]
      have bound : ∀ d ∈ 248 :: VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, d + 8 ≤ 272 := by decide
      obtain ⟨region, member, contains⟩ := localWord d (bound d hd)
      exact ⟨region, List.mem_append_right _ member, contains⟩)
    (by
      intro d hd; rw [copied.wr, sp]
      have bound : ∀ d ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, d + 8 ≤ 272 := by decide
      exact localWord d (bound d hd))).mono ?_
  intro t prepared
  refine ⟨prepared.bp.trans sp, prepared.sp.trans sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans copied.rd, prepared.wr.trans copied.wr, ?_⟩
  · have word := copied.values 9 (by decide)
    change a.mem.readW (a.gpr .rsp + 248) 64 = s.mem.readW (s.gpr .rsp + 400) 64 at word
    exact prepared.scratch.trans word
  · intro arg ha
    rw [prepared.values arg ha]
    unfold VG.Proof.Argon2.X86_64.Derive.argumentValue
    have notAx : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, arg.2 ≠ .rax := by decide
    rw [copied.regs arg.2 (notAx arg ha)]
  · intro j hj
    by_cases small : j < 3
    · have slot : ∀ j < 3, VG.Proof.Argon2.X86_64.Derive.copyDestination j ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets := by decide
      rw [prepared.normalized _ (slot j small), copied.values j (List.mem_range.mpr hj), ite_eq_left small]
    · rw [ite_eq_right small, prepared.other_word _ (by unfold VG.Proof.Argon2.X86_64.Derive.copyDestination; omega)
        (by unfold VG.Proof.Argon2.X86_64.Derive.copyDestination; omega) (by
          intro d hd
          have upper : ∀ d ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, d + 8 ≤ 200 := by decide
          have := upper d hd; unfold VG.Proof.Argon2.X86_64.Derive.copyDestination; omega)]
      exact copied.values j (List.mem_range.mpr hj)
  · intro r hr hb hx
    have notAx : ∀ r ∈ calleeSaved, r ≠ .rax := by decide
    exact (prepared.regs r hr hb hx).trans (copied.regs r (notAx r hr))
  · apply (copied.frame.sub ?_).trans (prepared.frame.sub ?_)
    · intro region hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hj
      refine ⟨⟨s.gpr .rsp + 176, 96⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      unfold VG.Proof.Argon2.X86_64.Derive.copyDestination
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact Offset.sub_base _ (by omega)
    · intro region hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [sp]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
        rw [sp]
        have bounds : ∀ d ∈ VG.Proof.Argon2.X86_64.Derive.normalizedOffsets, 176 ≤ d ∧ d + 8 ≤ 272 := by decide
        obtain ⟨lo, hi⟩ := bounds d hd
        refine ⟨⟨s.gpr .rsp + 176, 96⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [show d = 176 + (d - 176) by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
        exact Offset.sub_base _ (by omega)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Private frame permissions and caller argument values after the ABI prologue. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def prologueState (s : State) : State := VG.Proof.Argon2.X86_64.Derive.frameStart s Impl.Argon2.X86_64.Derive.saved

theorem prologue_sp (s : State) : (VG.Proof.Argon2.X86_64.Derive.prologueState s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 320 :=
  VG.Proof.Argon2.X86_64.Derive.frameStart_sp s _

theorem frameStart_locals (s : State) (rs : List Reg) :
    (⟨(VG.Proof.Argon2.X86_64.Derive.frameStart s rs).gpr .rsp, 272⟩ : Region) ∈ (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => rw [VG.Proof.Argon2.X86_64.Derive.frameStart, pushed_wr, pushed_rsp]; exact List.mem_cons_self ..
  | cons r rs ih => exact ih (pushed [r] s)

theorem prologue_locals (s : State) : Covers [⟨(VG.Proof.Argon2.X86_64.Derive.prologueState s).gpr .rsp, 272⟩] (VG.Proof.Argon2.X86_64.Derive.prologueState s).wr := by
  intro p n ⟨region, member, contains⟩
  simp only [List.mem_singleton] at member; subst region
  exact ⟨_, VG.Proof.Argon2.X86_64.Derive.frameStart_locals s _, contains⟩

theorem prologue_source (s : State) (j : Nat) :
    (VG.Proof.Argon2.X86_64.Derive.prologueState s).gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j) =
      s.gpr .rsp + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [VG.Proof.Argon2.X86_64.Derive.prologue_sp]
  unfold VG.Proof.Argon2.X86_64.Derive.copySource
  rw [show 328 + 8 * j = 320 + 8 * (j + 1) by omega,
    BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem prologue_reads {s : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s) :
    ∀ j < 12, InRegions ((VG.Proof.Argon2.X86_64.Derive.prologueState s).rd ++ (VG.Proof.Argon2.X86_64.Derive.prologueState s).wr)
      ((VG.Proof.Argon2.X86_64.Derive.prologueState s).gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 8 := by
  intro j hj
  rw [VG.Proof.Argon2.X86_64.Derive.prologue_source]
  refine ⟨VG.Proof.Argon2.X86_64.Derive.abiArguments s, List.mem_append_left _ ?_, ?_⟩
  · change VG.Proof.Argon2.X86_64.Derive.abiArguments s ∈ (VG.Proof.Argon2.X86_64.Derive.frameStart s Impl.Argon2.X86_64.Derive.saved).rd
    rw [VG.Proof.Argon2.X86_64.Derive.frameStart_rd, h.rd]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · unfold VG.Proof.Argon2.X86_64.Derive.abiArguments
    rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega) (by omega)

theorem prologue_word {s : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s) (j : Nat) (hj : j < 12) :
    (VG.Proof.Argon2.X86_64.Derive.prologueState s).mem.readW ((VG.Proof.Argon2.X86_64.Derive.prologueState s).gpr .rsp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copySource j)) 64 =
      VG.Proof.Argon2.X86_64.Derive.abiWord s (8 * (j + 1)) := by
  rw [VG.Proof.Argon2.X86_64.Derive.prologue_source]
  have frame := VG.Proof.Argon2.X86_64.Derive.frameStart_frame s Impl.Argon2.X86_64.Derive.saved (by decide) (by
    have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  apply frame.readW (r := VG.Proof.Argon2.X86_64.Derive.abiArguments s) ?_ ?_ (by decide)
  · unfold VG.Proof.Argon2.X86_64.Derive.abiArguments
    rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega) (by omega)
  · intro region hr
    simp only [List.mem_singleton] at hr; subst region
    unfold VG.Proof.Argon2.X86_64.Derive.abiArguments
    exact Offset.disjoint_below _ (by decide)

theorem prologue_prepare (s : State) (h : VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s) :
    WP isa Impl.Argon2.X86_64.Derive.prepare (VG.Proof.Argon2.X86_64.Derive.prologueState s) (VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s)) :=
  VG.Proof.Argon2.X86_64.Derive.private_prepare_ok _ (VG.Proof.Argon2.X86_64.Derive.prologue_locals s) (VG.Proof.Argon2.X86_64.Derive.prologue_reads h)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveMetadata`. -/
section
/-! The private frame contains the exact arguments decoded by the shared contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_stack_word {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t) (j : Nat) (hj : j < 12) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.Derive.copyDestination j)) 64 =
      let word := VG.Proof.Argon2.X86_64.Derive.abiWord s (8 * (j + 1))
      if j < 3 then (word.setWidth 32).setWidth 64 else word := by
  rw [prepared.stackWords j hj, VG.Proof.Argon2.X86_64.Derive.prologue_word h j hj]

theorem private_argument_word {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t)
    (arg : Nat × Reg) (member : arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = VG.Proof.Argon2.X86_64.Derive.argumentValue s arg.2 := by
  rw [prepared.values arg member]
  unfold VG.Proof.Argon2.X86_64.Derive.argumentValue
  have notSp : ∀ arg ∈ VG.Proof.Argon2.X86_64.Derive.arguments, arg.2 ≠ .rsp := by decide
  unfold VG.Proof.Argon2.X86_64.Derive.prologueState
  rw [VG.Proof.Argon2.X86_64.Derive.frameStart_reg s _ arg.2 (notSp arg member)]

theorem private_local_write {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) : InRegions t.wr (t.gpr .rbp + BitVec.ofNat 64 d) n := by
  rw [prepared.wr, prepared.bp]
  apply VG.Proof.Argon2.X86_64.Derive.prologue_locals s
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem private_local_read {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) :
    InRegions (t.rd ++ t.wr) (t.gpr .rbp + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := VG.Proof.Argon2.X86_64.Derive.private_local_write prepared d n bound
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem private_parameters {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t) : Parameters.Ready (VG.Proof.Argon2.X86_64.Derive.abiParams s) t := by
  refine ⟨VG.Proof.Argon2.X86_64.Derive.private_local_read prepared 176 8 (by decide), VG.Proof.Argon2.X86_64.Derive.private_local_read prepared 184 8 (by decide),
    ?_, ?_, h.valid.1, h.valid.2.2.2.2.2.1, h.valid.2.1⟩
  · have word := VG.Proof.Argon2.X86_64.Derive.private_stack_word h prepared 0 (by decide)
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 176) 64 =
      (((VG.Proof.Argon2.X86_64.Derive.abiWord s 8).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 176) 64 =
      BitVec.ofNat 64 ((VG.Proof.Argon2.X86_64.Derive.abiWord s 8).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have word := VG.Proof.Argon2.X86_64.Derive.private_stack_word h prepared 1 (by decide)
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 184) 64 =
      (((VG.Proof.Argon2.X86_64.Derive.abiWord s 16).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 ((VG.Proof.Argon2.X86_64.Derive.abiWord s 16).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]

end VG.Proof.Argon2.X86_64.Derive
end

/-! The private frame and called functions stay within the reviewed stack allowance. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_wr_member (s : State) (rs : List Reg) (region : Region) (member : region ∈ s.wr) :
    region ∈ (VG.Proof.Argon2.X86_64.Derive.frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => rw [VG.Proof.Argon2.X86_64.Derive.frameStart, pushed_wr]; exact List.mem_cons_of_mem _ member
  | cons r rs ih => apply ih; rw [pushed_wr]; exact List.mem_cons_of_mem _ member

theorem private_wr_member {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t)
    (region : Region) (member : region ∈ s.wr) : region ∈ t.wr := by
  rw [prepared.wr]
  exact VG.Proof.Argon2.X86_64.Derive.frameStart_wr_member s _ region member

theorem private_bp {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t) :
    t.gpr .rbp = s.gpr .rsp - BitVec.ofNat 64 320 := prepared.bp.trans (VG.Proof.Argon2.X86_64.Derive.prologue_sp s)

theorem private_sp {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t) :
    t.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 320 := prepared.sp.trans (VG.Proof.Argon2.X86_64.Derive.prologue_sp s)

theorem private_frame_sub {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t) :
    Region.Sub ⟨t.gpr .rbp, 272⟩ (below (s.gpr .rsp) 344) := by
  rw [VG.Proof.Argon2.X86_64.Derive.private_bp prepared]
  exact Offset.sub_below _ (by decide) (by decide)

theorem private_stack_sub {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t)
    (n : Nat) (bound : n ≤ 24) : Region.Sub (below (t.gpr .rsp) n) (below (s.gpr .rsp) 344) := by
  rw [VG.Proof.Argon2.X86_64.Derive.private_sp prepared]
  unfold below
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

theorem private_frame_disjoint {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ VG.Proof.Argon2.X86_64.Derive.abiBuffers s ++ [(VG.Proof.Argon2.X86_64.Derive.abiArguments s, false)]) :
    (⟨t.gpr .rbp, 272⟩ : Region).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) buffer member).sub_left
    (VG.Proof.Argon2.X86_64.Derive.private_frame_sub prepared)

theorem private_stack_disjoint {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ VG.Proof.Argon2.X86_64.Derive.abiBuffers s ++ [(VG.Proof.Argon2.X86_64.Derive.abiArguments s, false)]) (n : Nat) (bound : n ≤ 24) :
    (below (t.gpr .rsp) n).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) buffer member).sub_left
    (VG.Proof.Argon2.X86_64.Derive.private_stack_sub prepared n bound)

theorem private_frame_stack {s t : State} (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t)
    (n : Nat) (bound : n ≤ 24) : (⟨t.gpr .rbp, 272⟩ : Region).Disjoint (below (t.gpr .rsp) n) := by
  rw [prepared.bp, prepared.sp]
  exact Offset.base_disjoint_below _ (by omega)

theorem private_work_member {s t : State} (h : VG.Proof.Argon2.X86_64.Derive.AbiEnvironment s)
    (prepared : VG.Proof.Argon2.X86_64.Derive.PrivatePrepared (VG.Proof.Argon2.X86_64.Derive.prologueState s) t) : VG.Proof.Argon2.X86_64.Derive.abiWork s ∈ t.wr := by
  apply VG.Proof.Argon2.X86_64.Derive.private_wr_member prepared
  rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

end VG.Proof.Argon2.X86_64.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillKernelStable`. -/
section

/-! Register-only helpers retain the filling allocation and position invariants. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64

theorem Ready.of_keeps {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index t := by
  refine ⟨h.layout.of_keeps k, h.bounds, h.position.of_keeps k, ?_, ?_⟩
  · rw [k.mem, k.regs .rbp (by decide)]; exact h.passWord
  · rw [k.mem, k.regs .rbp (by decide)]; exact h.lanesWord

end VG.Proof.Argon2.X86_64.FillKernel

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.RandomSourcePrepare`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillKernelInvariant`. -/
section
/-! Each active-cell update retains the frame and matrix allocation invariant. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) (done : VG.Proof.Argon2.X86_64.FillKernel.Done s t p pass lane slice index)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 16 ∨ 24 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved])]
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  have currentSub : Region.Sub ⟨VG.Proof.Argon2.X86_64.FillKernel.current s p lane slice index, 1024⟩ ⟨VG.Proof.Argon2.X86_64.FillKernel.matrix s, p.blocks * 1024⟩ :=
    VG.Proof.Argon2.X86_64.FillKernel.cell_sub p _ h.bounds.lanesPositive h.bounds.laneBound
      (Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound)
  exact done.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [VG.Proof.Argon2.X86_64.FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ((h.layout.matrixFrame.sub_left currentSub).symm).sub_left sub
    · exact h.layout.frameWork.sub_left sub
    · exact h.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

theorem Done.retains {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index s) (done : VG.Proof.Argon2.X86_64.FillKernel.Done s t p pass lane slice index) :
    VG.Proof.Argon2.X86_64.FillKernel.Ready p pass lane slice index t := by
  have bp := done.regs .rbp (by simp [calleeSaved])
  have sp := done.regs .rsp (by simp [calleeSaved])
  have matrix' : VG.Proof.Argon2.X86_64.FillKernel.matrix t = VG.Proof.Argon2.X86_64.FillKernel.matrix s := done.frame_word h 232 (by decide) (by decide)
  have work' : VG.Proof.Argon2.X86_64.FillKernel.work t = VG.Proof.Argon2.X86_64.FillKernel.work s := done.frame_word h 248 (by decide) (by decide)
  refine ⟨?_, h.bounds, ?_, (done.frame_word h 0 (by decide) (by decide)).trans h.passWord,
    (done.frame_word h 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [done.rd, done.wr, bp]; exact h.layout.frameRead
    · rw [done.wr, bp]; exact h.layout.frameWrite
    · rw [matrix', done.wr]; exact h.layout.matrixWrite
    · rw [work', done.wr]; exact h.layout.workWrite
    · rw [matrix', work']; exact h.layout.matrixWork
    · rw [matrix', bp]; exact h.layout.matrixFrame
    · rw [matrix', sp]; exact h.layout.matrixStack
    · rw [bp, work']; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work']; exact h.layout.stackWork
  · exact ⟨(done.regs .rbx (by simp [calleeSaved])).trans h.position.current,
      (done.regs .r12 (by simp [calleeSaved])).trans h.position.laneLength,
      (done.regs .r13 (by simp [calleeSaved])).trans h.position.segmentLength,
      (done.regs .r14 (by simp [calleeSaved])).trans h.position.slice,
      (done.regs .r15 (by simp [calleeSaved])).trans h.position.index⟩

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! Merged from `Proof.Argon2.X86_64.AddressModeSteps`. -/
section
/-! Short mask computations for the public addressing-mode predicate. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

theorem zero_nat (x : Addr) : x.toNat < 1 ↔ x = 0#64 := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp h)
  · intro h; rw [h]; decide

theorem xor_nat (x y : Addr) : (x ^^^ y).toNat < 1 ↔ x = y := by
  rw [VG.Proof.Argon2.X86_64.AddressMode.zero_nat, BitVec.xor_eq_zero_iff]

theorem kind_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8) :
    WP isa (.block kind) s fun t =>
      t.gpr .r10 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 112) 64 = 1)) ∧
      t.gpr .r8 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 112) 64 = 2)) ∧
      Divide.Keeps [.rax, .r10, .r8] s t := by
  apply WP.of_runBlock
  simp only [kind, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    VG.Proof.Argon2.X86_64.ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (2 : BitVec 32) = (2 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (1 : Addr).toNat = 1 from rfl, VG.Proof.Argon2.X86_64.AddressMode.xor_nat]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem pass_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block VG.Impl.Argon2.X86_64.AddressMode.pass) s fun t =>
      t.gpr .r9 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 0) 64 = 0#64)) ∧
      Divide.Keeps [.r9] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.AddressMode.pass, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    VG.Proof.Argon2.X86_64.ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, ite_true,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (1 : Addr).toNat = 1 from rfl, VG.Proof.Argon2.X86_64.AddressMode.zero_nat]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem slice_ok (s : State) : WP isa (.block slice) s fun t =>
    t.gpr .r10 = (s.gpr .r10 ||| ((s.gpr .r8 &&& s.gpr .r9) &&&
      Divide.mask (decide ((s.gpr .r14).toNat < 2)))) &&& 1 ∧
    Divide.Keeps [.r8, .r11, .r10] s t := by
  apply WP.of_runBlock
  simp only [slice, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (2 : BitVec 32) = (2 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (2 : Addr).toNat = 2 from rfl]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.AddressMode
end

/-! Merged from `Proof.Argon2.X86_64.AddressMode`. -/
section
/-! The segment mode is exactly the reviewed Argon2d/i/id addressing predicate. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

def value (s : State) : Addr :=
  let kind := s.mem.readW (off (s.gpr .rbp) 112) 64
  let pass := s.mem.readW (off (s.gpr .rbp) 0) 64
  (Divide.mask (decide (kind = 1)) ||| ((Divide.mask (decide (kind = 2)) &&&
    Divide.mask (decide (pass = 0#64))) &&& Divide.mask (decide ((s.gpr .r14).toNat < 2)))) &&& 1

def changed : List Reg := [.rax, .r8, .r9, .r10, .r11]

theorem code_ok (s : State)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa VG.Impl.Argon2.X86_64.AddressMode.code s fun t => t.gpr .r10 = VG.Proof.Argon2.X86_64.AddressMode.value s ∧ Divide.Keeps VG.Proof.Argon2.X86_64.AddressMode.changed s t := by
  unfold VG.Impl.Argon2.X86_64.AddressMode.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressMode.kind_ok s kindRead).mono ?_)
  rintro a ⟨i, id, ka⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 0) 8 := by
    rw [ka.rd, ka.wr, ka.regs .rbp (by decide)]; exact passRead
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressMode.pass_ok a read).mono ?_)
  rintro b ⟨zero, kb⟩
  refine (VG.Proof.Argon2.X86_64.AddressMode.slice_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [result, kb.regs .r10 (by decide), i, kb.regs .r8 (by decide), id, zero,
    ka.mem, ka.regs .rbp (by decide), kb.regs .r14 (by decide), ka.regs .r14 (by decide)]
  rfl

theorem masks : ∀ a b c d : Bool,
    (Divide.mask a ||| ((Divide.mask b &&& Divide.mask c) &&& Divide.mask d)) &&& 1 =
      (BitVec.ofBool (a || (b && c && d))).setWidth 64 := by decide +kernel

theorem variants : ∀ v : Spec.Argon2.Variant, ∀ a b : Bool,
    (decide (BitVec.ofNat 64 v.code = (1 : Addr)) ||
      (decide (BitVec.ofNat 64 v.code = (2 : Addr)) && a && b)) =
    ((v == .i) || ((v == .id) && a && b)) := by
  intro v
  cases v <;> decide +kernel

theorem value_spec (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    VG.Proof.Argon2.X86_64.AddressMode.value s = (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 := by
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
  unfold VG.Proof.Argon2.X86_64.AddressMode.value
  rw [kindWord, passWord, sliceWord, VG.Proof.Argon2.X86_64.AddressMode.masks,
    ReferenceMap.word_nat slice sliceBound]
  simp only [passZero]
  unfold Spec.Argon2.independent
  rw [VG.Proof.Argon2.X86_64.AddressMode.variants, Bool.beq_eq_decide_eq pass 0]

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8)
    (kindWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    WP isa VG.Impl.Argon2.X86_64.AddressMode.code s fun t => t.gpr .r10 =
      (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 ∧ Divide.Keeps VG.Proof.Argon2.X86_64.AddressMode.changed s t :=
  (VG.Proof.Argon2.X86_64.AddressMode.code_ok s kindRead passRead).mono (fun _ h =>
    ⟨h.1.trans (VG.Proof.Argon2.X86_64.AddressMode.value_spec s p pass slice kindWord passWord sliceWord passBound sliceBound), h.2⟩)

end VG.Proof.Argon2.X86_64.AddressMode
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheState`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressCache`. -/
section
/-! Complete cached random-word selection against RFC 9106's address block. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

structure Done (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  selected : VG.Proof.Argon2.X86_64.AddressCache.Selected s t p pass lane slice
  random : t.gpr .rdi =
    (addressBlock p pass lane slice (VG.Proof.Argon2.X86_64.AddressCache.wanted s))[(s.gpr .r15).toNat % 128]'(Nat.mod_lt _ (by decide))

theorem code_ok [CompressImpl] (p : Params) (pass lane slice old : Nat) (s : State)
    (h : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old s) :
    WP isa VG.Impl.Argon2.X86_64.AddressCache.code s (VG.Proof.Argon2.X86_64.AddressCache.Done s · p pass lane slice) := by
  unfold VG.Impl.Argon2.X86_64.AddressCache.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.AddressCache.selected_ok p pass lane slice old s h).mono ?_)
  intro a selected
  refine (VG.Proof.Argon2.X86_64.AddressCache.word_ok a selected.layout).mono ?_
  rintro t ⟨random, keeps⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ∉ [Reg.rcx, .rax, .rdi] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (keeps.regs r ne).trans (selected.regs r hr)
  have bp := keeps.regs .rbp (by decide)
  have sp := keeps.regs .rsp (by decide)
  have work' : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [bp, keeps.mem]
  have layout : AddressCalls.Ready t := by
    constructor
    · rw [keeps.rd, keeps.wr, bp]; exact selected.layout.frameRead
    · rw [work', keeps.wr]; exact selected.layout.workWrite
    · rw [bp, work']; exact selected.layout.frameWork
    · rw [bp, sp]; exact selected.layout.frameStack
    · rw [sp, work']; exact selected.layout.stackWork
  refine ⟨⟨?_, layout, work'.trans selected.work_eq, regs,
    keeps.rd.trans selected.rd, keeps.wr.trans selected.wr, ?_,
    (ctl_eq_of keeps.mxcsr).trans selected.mxcsr, ?_⟩, ?_⟩
  · rw [keeps.mem]; exact selected.block
  · rw [keeps.mem]; exact selected.frame
  · rw [bp, keeps.mem]; exact selected.counterWord
  · rw [selected.work_eq, selected.regs .r15 (by simp [calleeSaved]), selected.block] at random
    exact random

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Retain the filling header and allocation across independent-address regeneration. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2

theorem Selected.frame_word {s t : State} {p : Params} {pass lane slice : Nat}
    (layout : AddressCalls.Ready s) (h : VG.Proof.Argon2.X86_64.AddressCache.Selected s t p pass lane slice)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs .rbp (by simp [calleeSaved])]
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact h.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [VG.Proof.Argon2.X86_64.AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact layout.frameWork.sub_left sub
    · exact layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

theorem Selected.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old s) (h : VG.Proof.Argon2.X86_64.AddressCache.Selected s t p pass lane slice) :
    AddressHeader.Words p pass lane slice (VG.Proof.Argon2.X86_64.AddressCache.wanted s) t := by
  exact ⟨(h.frame_word ready.layout 0 (by decide) (by decide)).trans ready.words.passWord,
    (h.regs .rbx (by simp [calleeSaved])).trans ready.words.laneWord,
    (h.regs .r14 (by simp [calleeSaved])).trans ready.words.sliceWord,
    (h.frame_word ready.layout 240 (by decide) (by decide)).trans ready.words.blocksWord,
    (h.frame_word ready.layout 72 (by decide) (by decide)).trans ready.words.passesWord,
    (h.frame_word ready.layout 112 (by decide) (by decide)).trans ready.words.variantWord,
    h.counterWord.trans (VG.Proof.Argon2.X86_64.AddressCache.counter_nat _)⟩

theorem Ready.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old t := by
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    apply k.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have stable := AddressCalls.stable_of_frame h.layout regs k.rd k.wr
    (by rw [k.mem]; exact Frame.refl _ _) k.mxcsr
  refine ⟨stable.ready, stable.reads h.reads, ?_, stable.words h.layout h.words, ?_⟩
  · rw [k.wr, k.regs .rbp (by decide)]; exact h.write
  · intro same
    have wanted' : VG.Proof.Argon2.X86_64.AddressCache.wanted t = VG.Proof.Argon2.X86_64.AddressCache.wanted s := by unfold VG.Proof.Argon2.X86_64.AddressCache.wanted; rw [k.regs .r15 (by decide)]
    rw [k.mem, k.regs .rbp (by decide), k.regs .r15 (by decide)] at same
    rw [k.mem, stable.work_eq, wanted']
    exact h.cached same

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheMatrix`. -/
section
/-! Independent-address generation leaves every matrix cell intact. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2

theorem Selected.filling_ready {s t : State} {p : Params} {pass lane slice index : Nat}
    (cacheLayout : AddressCalls.Ready s) (h : FillKernel.Ready p pass lane slice index s)
    (done : VG.Proof.Argon2.X86_64.AddressCache.Selected s t p pass lane slice) : FillKernel.Ready p pass lane slice index t := by
  have bp := done.regs .rbp (by simp [calleeSaved])
  have sp := done.regs .rsp (by simp [calleeSaved])
  have matrix' : FillKernel.matrix t = FillKernel.matrix s := done.frame_word cacheLayout 232 (by decide) (by decide)
  have work' : FillKernel.work t = FillKernel.work s := done.frame_word cacheLayout 248 (by decide) (by decide)
  refine ⟨?_, h.bounds, ?_, (done.frame_word cacheLayout 0 (by decide) (by decide)).trans h.passWord,
    (done.frame_word cacheLayout 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [done.rd, done.wr, bp]; exact h.layout.frameRead
    · rw [done.wr, bp]; exact h.layout.frameWrite
    · rw [matrix', done.wr]; exact h.layout.matrixWrite
    · rw [work', done.wr]; exact h.layout.workWrite
    · rw [matrix', work']; exact h.layout.matrixWork
    · rw [matrix', bp]; exact h.layout.matrixFrame
    · rw [matrix', sp]; exact h.layout.matrixStack
    · rw [bp, work']; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work']; exact h.layout.stackWork
  · exact ⟨(done.regs .rbx (by simp [calleeSaved])).trans h.position.current,
      (done.regs .r12 (by simp [calleeSaved])).trans h.position.laneLength,
      (done.regs .r13 (by simp [calleeSaved])).trans h.position.segmentLength,
      (done.regs .r14 (by simp [calleeSaved])).trans h.position.slice,
      (done.regs .r15 (by simp [calleeSaved])).trans h.position.index⟩

theorem Selected.represents {s t : State} {p : Params} {pass lane slice index : Nat}
    (cacheLayout : AddressCalls.Ready s) (h : FillKernel.Ready p pass lane slice index s)
    (matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩)
    (done : VG.Proof.Argon2.X86_64.AddressCache.Selected s t p pass lane slice) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word cacheLayout 232 (by decide) (by decide)
  rw [base]
  refine ⟨represented.size, ?_⟩
  intro k hk
  have kept : blockAt t.mem (Proof.Argon2.matrixCell (FillKernel.matrix s) k) =
      blockAt s.mem (Proof.Argon2.matrixCell (FillKernel.matrix s) k) := by
    apply FillCompress.block_frame done.frame
    intro r hr
    simp only [VG.Proof.Argon2.X86_64.AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact matrixWork.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)
    · exact h.layout.matrixStack.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)
    · exact (h.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
        (Offset.sub_base _ (by decide))
  exact kept.trans (represented.block k hk)

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheInvariant`. -/
section
/-! Cache validity does not depend on the current index, so advancing an index
retains it. Counter zero requires no cached contents; every other counter
identifies its specified independent-address block.
-/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2

structure Invariant (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  bound : old < 2 ^ 64
  cached : old = 0 ∨ blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice old

theorem wanted_bound (s : State) : VG.Proof.Argon2.X86_64.AddressCache.wanted s < 2 ^ 64 := by
  unfold VG.Proof.Argon2.X86_64.AddressCache.wanted
  have := (s.gpr .r15).isLt
  omega

theorem Invariant.ready {p : Params} {pass lane slice old : Nat} {s : State}
    (h : VG.Proof.Argon2.X86_64.AddressCache.Invariant p pass lane slice old s) : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old s := by
  refine ⟨h.layout, h.reads, h.write, h.words, ?_⟩
  intro same
  have word : BitVec.ofNat 64 (VG.Proof.Argon2.X86_64.AddressCache.wanted s) = BitVec.ofNat 64 old := by
    unfold VG.Proof.Argon2.X86_64.AddressCache.wanted
    rw [← VG.Proof.Argon2.X86_64.AddressCache.counter_nat]; exact same.trans h.words.counterWord
  have equal := (ReferenceMap.word_eq _ _ (VG.Proof.Argon2.X86_64.AddressCache.wanted_bound s) h.bound).mp word
  rcases h.cached with zero | cached
  · exfalso
    exact VG.Proof.Argon2.X86_64.AddressCache.counter_ne_zero _ (same.trans (h.words.counterWord.trans (by rw [zero]; rfl)))
  · rw [← equal] at cached
    exact cached

theorem Selected.invariant {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice old s) (h : VG.Proof.Argon2.X86_64.AddressCache.Selected s t p pass lane slice) :
    VG.Proof.Argon2.X86_64.AddressCache.Invariant p pass lane slice (VG.Proof.Argon2.X86_64.AddressCache.wanted s) t := by
  have bp := h.regs .rbp (by simp [calleeSaved])
  refine ⟨h.layout, ?_, ?_, h.words ready, VG.Proof.Argon2.X86_64.AddressCache.wanted_bound s, Or.inr ?_⟩
  · rw [h.rd, h.wr, bp]; exact ready.reads
  · rw [h.wr, bp]; exact ready.write
  · rw [h.work_eq]; exact h.block

theorem Invariant.zero {p : Params} {pass lane slice : Nat} {s : State}
    (h : VG.Proof.Argon2.X86_64.AddressCache.Ready p pass lane slice 0 s) : VG.Proof.Argon2.X86_64.AddressCache.Invariant p pass lane slice 0 s :=
  ⟨h.layout, h.reads, h.write, h.words, by decide, Or.inl rfl⟩

theorem Invariant.of_state {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.AddressCache.Invariant p pass lane slice old s)
    (regs : ∀ r ∈ [Reg.rsp, .rbp, .rbx, .r14], t.gpr r = s.gpr r)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    VG.Proof.Argon2.X86_64.AddressCache.Invariant p pass lane slice old t := by
  have bp := regs .rbp (by simp)
  have sp := regs .rsp (by simp)
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [mem, bp]
  refine ⟨?_, ?_, ?_, ?_, h.bound, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.layout.frameRead
    · rw [wr, work]; exact h.layout.workWrite
    · rw [bp, work]; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work]; exact h.layout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · exact ⟨by rw [mem, bp]; exact h.words.passWord,
      (regs .rbx (by simp)).trans h.words.laneWord,
      (regs .r14 (by simp)).trans h.words.sliceWord,
      by rw [mem, bp]; exact h.words.blocksWord,
      by rw [mem, bp]; exact h.words.passesWord,
      by rw [mem, bp]; exact h.words.variantWord,
      by rw [mem, bp]; exact h.words.counterWord⟩
  · rw [mem, work]; exact h.cached

theorem Invariant.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.AddressCache.Invariant p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.X86_64.AddressCache.Invariant p pass lane slice old t := by
  apply h.of_state _ k.mem k.rd k.wr
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide)

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Retain the source invariants while selecting the public addressing mode. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.RandomSource

structure Ready (p : Params) (pass lane slice index old : Nat) (s : State) : Prop where
  filling : FillKernel.Ready p pass lane slice index s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩

theorem Ready.of_keeps {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old t := by
  refine ⟨h.filling.of_keeps k, h.cache.of_keeps k, ?_⟩
  have matrix : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [k.mem, k.regs .rbp (by decide)]
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [k.mem, k.regs .rbp (by decide)]
  rw [matrix, work]; exact h.matrixWork

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.zf = decide (s.gpr .r10 = 0#64) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [test, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change (s.gpr .r10 - 0#64 == 0#64) = decide (s.gpr .r10 = 0#64)
    rw [BitVec.sub_zero]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

theorem bool_zero : ∀ b : Bool, decide ((BitVec.ofBool b).setWidth 64 = 0#64) = !b := by
  decide +kernel

theorem prepare_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) : WP isa VG.Impl.Argon2.X86_64.RandomSource.prepare s fun t =>
      t.zf = !independent p pass slice ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold VG.Impl.Argon2.X86_64.RandomSource.prepare
  refine WP.seq ((AddressMode.code_spec_ok s p pass slice
    (h.cache.reads 112 (by simp)) (h.cache.reads 0 (by simp))
    h.cache.words.variantWord h.filling.passWord h.filling.position.slice
    (Nat.lt_trans h.filling.bounds.passBound (by decide))
    (Nat.lt_trans h.filling.bounds.sliceBound (by decide))).mono ?_)
  rintro a ⟨mode, keeps⟩
  refine (VG.Proof.Argon2.X86_64.RandomSource.test_ok a).mono ?_
  rintro t ⟨flag, tested⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tested.mono (by decide))⟩
  rw [flag, mode, VG.Proof.Argon2.X86_64.RandomSource.bool_zero]

end VG.Proof.Argon2.X86_64.RandomSource

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.RandomSource`. -/
section

/-! Merged from `Proof.Argon2.X86_64.DependentWordState`. -/
section
/-! The dependent source hands the filling step its random word and unchanged matrix. -/

namespace VG.Proof.Argon2.X86_64.DependentWord

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.DependentWord

theorem state_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (dependent : independent p pass slice = false) : WP isa VG.Impl.Argon2.X86_64.DependentWord.code s fun t =>
      t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory ∧
      FillKernel.Ready p pass lane slice index t ∧
      Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory ∧
      Divide.Keeps ReferenceMap.changed s t := by
  refine (VG.Proof.Argon2.X86_64.DependentWord.code_spec_ok s p pass lane slice index h state represented dependent).mono ?_
  rintro t ⟨random, keeps⟩
  refine ⟨random, h.of_keeps keeps, ?_, keeps⟩
  have base : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  rw [keeps.mem, base]; exact represented

end VG.Proof.Argon2.X86_64.DependentWord
end

/-! Both random sources satisfy the same filling-step postcondition. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) : List Region := AddressCache.writes s

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  random : t.gpr .rdi = Proof.Argon2.FillStep.random p pass lane slice index state.memory
  ready : ∃ old, VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.RandomSource.writes s) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr

theorem Ready.index_nat {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) : (s.gpr .r15).toNat = index := by
  rw [h.filling.position.index, ReferenceMap.word_nat index h.filling.bounds.index_bound64]

theorem independent_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = true) :
    WP isa Impl.Argon2.X86_64.AddressCache.code s (VG.Proof.Argon2.X86_64.RandomSource.Done s · p pass lane slice index state) := by
  refine (AddressCache.code_ok p pass lane slice old s h.cache.ready).mono ?_
  intro t done
  have base : FillKernel.matrix t = FillKernel.matrix s :=
    done.selected.frame_word h.cache.layout 232 (by decide) (by decide)
  have nextReady : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index (AddressCache.wanted s) t := by
    refine ⟨done.selected.filling_ready h.cache.layout h.filling,
      done.selected.invariant h.cache.ready, ?_⟩
    rw [base, done.selected.work_eq]; exact h.matrixWork
  refine ⟨?_, ⟨_, nextReady⟩,
    done.selected.represents h.cache.layout h.filling h.matrixWork state.memory represented,
    done.selected.regs, done.selected.rd, done.selected.wr, done.selected.frame, done.selected.mxcsr⟩
  have random := done.random
  unfold AddressCache.wanted at random
  rw [h.index_nat] at random
  unfold Proof.Argon2.FillStep.random
  simp only [mode, ite_true]
  exact random

theorem dependent_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (mode : independent p pass slice = false) :
    WP isa Impl.Argon2.X86_64.DependentWord.code s (VG.Proof.Argon2.X86_64.RandomSource.Done s · p pass lane slice index state) := by
  refine (DependentWord.state_ok s p pass lane slice index h.filling state represented mode).mono ?_
  rintro t ⟨random, _, matrix, keeps⟩
  refine ⟨random, ⟨old, h.of_keeps keeps⟩, matrix, ?_, keeps.rd, keeps.wr, ?_, ctl_eq_of keeps.mxcsr⟩
  · intro r hr
    apply keeps.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem code_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.RandomSource.code s (VG.Proof.Argon2.X86_64.RandomSource.Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.RandomSource.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.RandomSource.prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    have base : FillKernel.matrix a = FillKernel.matrix s := by
      unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
    rw [base, keeps.mem]; exact represented
  have finish {t : State} (done : VG.Proof.Argon2.X86_64.RandomSource.Done a t p pass lane slice index state) :
      VG.Proof.Argon2.X86_64.RandomSource.Done s t p pass lane slice index state := by
    refine ⟨done.random, done.ready, done.represented, ?_, done.rd.trans keeps.rd,
      done.wr.trans keeps.wr, ?_, done.mxcsr.trans (ctl_eq_of keeps.mxcsr)⟩
    · intro r hr
      have ne : r ∉ ReferenceMap.changed := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (done.regs r hr).trans (keeps.regs r ne)
    · have frame := done.frame
      unfold VG.Proof.Argon2.X86_64.RandomSource.writes AddressCache.writes AddressCalls.work at frame ⊢
      rw [keeps.mem, keeps.regs .rbp (by decide), keeps.regs .rsp (by decide)] at frame
      exact frame
  refine WP.ite (!independent p pass slice) (by simp only [eval, flag]) ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by
      cases eq : independent p pass slice <;> simp_all
    exact (VG.Proof.Argon2.X86_64.RandomSource.dependent_ok a p pass lane slice index old next state representedA dependent).mono
      (fun _ done => finish done)
  · intro mode
    have independent : independent p pass slice = true := by
      cases eq : independent p pass slice <;> simp_all
    exact (VG.Proof.Argon2.X86_64.RandomSource.independent_ok a p pass lane slice index old next state representedA independent).mono
      (fun _ done => finish done)

end VG.Proof.Argon2.X86_64.RandomSource

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillBlock`. -/
section

/-! Merged from `Proof.Argon2.X86_64.RandomSourceState`. -/
section
/-! Frame words and public allocation pointers survive random-word dispatch. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index old : Nat} {state : FillState}
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) (done : VG.Proof.Argon2.X86_64.RandomSource.Done s t p pass lane slice index state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved])]
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [VG.Proof.Argon2.X86_64.RandomSource.writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.cache.layout.frameWork.sub_left sub
    · exact h.cache.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.RandomSource
end

/-! Merged from `Proof.Argon2.X86_64.FillCacheInvariant`. -/
section
/-! The cell update does not disturb the cached independent-address block. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

theorem Ready.after_fill {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old s) (done : FillKernel.Done s t p pass lane slice index) :
    VG.Proof.Argon2.X86_64.RandomSource.Ready p pass lane slice index old t := by
  have bp := done.regs .rbp (by simp [calleeSaved])
  have sp := done.regs .rsp (by simp [calleeSaved])
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.filling 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word h.filling 248 (by decide) (by decide)
  refine ⟨done.retains h.filling, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, h.cache.bound, ?_⟩
    · constructor
      · rw [done.rd, done.wr, bp]; exact h.cache.layout.frameRead
      · rw [done.wr, work]; exact h.cache.layout.workWrite
      · rw [bp, work]; exact h.cache.layout.frameWork
      · rw [bp, sp]; exact h.cache.layout.frameStack
      · rw [sp, work]; exact h.cache.layout.stackWork
    · rw [done.rd, done.wr, bp]; exact h.cache.reads
    · rw [done.wr, bp]; exact h.cache.write
    · exact ⟨(done.frame_word h.filling 0 (by decide) (by decide)).trans h.cache.words.passWord,
        (done.regs .rbx (by simp [calleeSaved])).trans h.cache.words.laneWord,
        (done.regs .r14 (by simp [calleeSaved])).trans h.cache.words.sliceWord,
        (done.frame_word h.filling 240 (by decide) (by decide)).trans h.cache.words.blocksWord,
        (done.frame_word h.filling 72 (by decide) (by decide)).trans h.cache.words.passesWord,
        (done.frame_word h.filling 112 (by decide) (by decide)).trans h.cache.words.variantWord,
        (done.frame_word h.filling 8 (by decide) (by decide)).trans h.cache.words.counterWord⟩
    · rcases h.cache.cached with zero | cached
      · exact Or.inl zero
      · apply Or.inr
        rw [work]
        have kept : blockAt t.mem (off (AddressCalls.work s) 6144) =
            blockAt s.mem (off (AddressCalls.work s) 6144) := by
          apply FillCompress.block_frame done.frame
          intro r hr
          simp only [FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
          have cacheSub : Region.Sub ⟨off (AddressCalls.work s) 6144, 1024⟩ ⟨AddressCalls.work s, 8192⟩ :=
            Offset.sub_base _ (by decide)
          rcases hr with rfl | rfl | rfl | rfl
          · exact (h.matrixWork.symm.sub_left cacheSub).sub_right
              (FillKernel.cell_sub p _ h.filling.bounds.lanesPositive h.filling.bounds.laneBound
                (Proof.Argon2.column_lt p h.filling.bounds.lanesPositive
                  h.filling.bounds.sliceBound h.filling.bounds.indexBound))
          · exact Offset.disjoint_base (AddressCalls.work s) (d := 6144) (n := 1024) (k := 5120)
              (by decide) (by decide)
          · exact h.cache.layout.stackWork.symm.sub_left cacheSub
          · exact (h.cache.layout.frameWork.symm.sub_left cacheSub).sub_right
              (Offset.sub_base _ (by decide))
        exact kept.trans cached
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.X86_64.RandomSource
end

/-! Merged from `Proof.Argon2.X86_64.FillBlockFrame`. -/
section
/-! Compose scratch writes with a matrix-cell write inside the derive allocation. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 8, 16⟩]

theorem source_frame {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (done : RandomSource.Done s t p pass lane slice index state) : Frame (VG.Proof.Argon2.X86_64.FillBlock.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [RandomSource.writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillBlock.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillBlock.writes], fun _ h => h⟩
  · exact ⟨⟨off (s.gpr .rbp) 8, 16⟩, by simp [VG.Proof.Argon2.X86_64.FillBlock.writes], Region.sub_prefix (by decide)⟩

theorem kernel_frame {s t : State} {p : Params} {pass lane slice index : Nat}
    (ready : FillKernel.Ready p pass lane slice index s) (done : FillKernel.Done s t p pass lane slice index) :
    Frame (VG.Proof.Argon2.X86_64.FillBlock.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillBlock.writes], FillKernel.cell_sub p _ ready.bounds.lanesPositive ready.bounds.laneBound
      (Proof.Argon2.column_lt p ready.bounds.lanesPositive ready.bounds.sliceBound ready.bounds.indexBound)⟩
  · exact ⟨⟨AddressCalls.work s, 8192⟩, by simp [VG.Proof.Argon2.X86_64.FillBlock.writes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillBlock.writes], fun _ h => h⟩
  · exact ⟨_, by simp [VG.Proof.Argon2.X86_64.FillBlock.writes], Offset.sub _ (d := 16) (n := 8) (e := 8) (k := 16)
      (by decide) (by decide)⟩

end VG.Proof.Argon2.X86_64.FillBlock
end

/-! Complete active filling cell against the reviewed matrix transition. -/

namespace VG.Proof.Argon2.X86_64.FillBlock

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  ready : ∃ old, RandomSource.Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (VG.Proof.Argon2.X86_64.FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr

theorem code_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillBlock.code s (VG.Proof.Argon2.X86_64.FillBlock.Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.FillBlock.code
  refine WP.seq ((RandomSource.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a source
  obtain ⟨counter, ready⟩ := source.ready
  have baseA : FillKernel.matrix a = FillKernel.matrix s := source.frame_word h 232 (by decide) (by decide)
  have workA : AddressCalls.work a = AddressCalls.work s := source.frame_word h 248 (by decide) (by decide)
  refine (FillKernel.code_spec_ok a p pass lane slice index ready.filling state source.represented source.random).mono ?_
  rintro t ⟨done, matrix⟩
  have baseT : FillKernel.matrix t = FillKernel.matrix a := done.frame_word ready.filling 232 (by decide) (by decide)
  have workT : AddressCalls.work t = AddressCalls.work a := done.frame_word ready.filling 248 (by decide) (by decide)
  refine ⟨⟨counter, ready.after_fill done⟩, ?_, baseT.trans baseA, workT.trans workA, ?_,
    done.rd.trans source.rd, done.wr.trans source.wr, ?_, done.mxcsr.trans source.mxcsr⟩
  · rw [baseT]; exact matrix
  · intro r hr; exact (done.regs r hr).trans (source.regs r hr)
  · have frame := VG.Proof.Argon2.X86_64.FillBlock.kernel_frame ready.filling done
    rw [VG.Proof.Argon2.X86_64.FillBlock.writes, baseA, workA, source.regs .rsp (by simp [calleeSaved]),
      source.regs .rbp (by simp [calleeSaved])] at frame
    exact (VG.Proof.Argon2.X86_64.FillBlock.source_frame source).trans frame

end VG.Proof.Argon2.X86_64.FillBlock

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillSegmentBody`. -/
section

/-! Merged from `Proof.Argon2.X86_64.FillIndex`. -/
section
/-! Public segment-index advancement retains the filling and cache allocations. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSegment

theorem advance_ok (s : State) : WP isa (.block VG.Impl.Argon2.X86_64.FillSegment.advance) s fun t =>
    t.gpr .r15 = s.gpr .r15 + 1 ∧
    t.cf = decide ((s.gpr .r15 + 1).toNat < (s.gpr .r13).toNat) ∧
    Divide.Keeps [.r15] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.FillSegment.advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem advance_nat_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : FillKernel.Ready p pass lane slice index s) : WP isa (.block VG.Impl.Argon2.X86_64.FillSegment.advance) s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (index + 1) ∧
      t.cf = decide (index + 1 < p.segmentLen) ∧ Divide.Keeps [.r15] s t := by
  refine (VG.Proof.Argon2.X86_64.FillSegment.advance_ok s).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have added : s.gpr .r15 + 1 = BitVec.ofNat 64 (index + 1) := by
    rw [h.position.index, BitVec.ofNat_add]; rfl
  have endBound : p.segmentLen < 2 ^ 64 := Nat.lt_of_le_of_lt h.bounds.segment_le_lane
    (Nat.lt_trans h.bounds.laneLength_bound (by decide))
  have indexBound := h.bounds.indexBound
  refine ⟨value.trans added, ?_, keeps⟩
  rw [flag, added, h.position.segmentLength,
    ReferenceMap.word_nat (index + 1) (by omega), ReferenceMap.word_nat p.segmentLen endBound]

theorem next_ready {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : RandomSource.Ready p pass lane slice index old s)
    (k : Divide.Keeps [.r15] s t) (value : t.gpr .r15 = BitVec.ofNat 64 (index + 1))
    (active : index + 1 < p.segmentLen) : RandomSource.Ready p pass lane slice (index + 1) old t := by
  have bp := k.regs .rbp (by decide)
  have sp := k.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  have kernelWork : FillKernel.work t = FillKernel.work s := work
  refine ⟨?_, h.cache.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide)) k.mem k.rd k.wr, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · rw [k.rd, k.wr, bp]; exact h.filling.layout.frameRead
      · rw [k.wr, bp]; exact h.filling.layout.frameWrite
      · rw [base, k.wr]; exact h.filling.layout.matrixWrite
      · rw [kernelWork, k.wr]; exact h.filling.layout.workWrite
      · rw [base, kernelWork]; exact h.filling.layout.matrixWork
      · rw [base, bp]; exact h.filling.layout.matrixFrame
      · rw [base, sp]; exact h.filling.layout.matrixStack
      · rw [bp, kernelWork]; exact h.filling.layout.frameWork
      · rw [bp, sp]; exact h.filling.layout.frameStack
      · rw [sp, kernelWork]; exact h.filling.layout.stackWork
    · have bounds := h.filling.bounds
      refine ⟨bounds.lanesPositive, bounds.lanesBound, bounds.memoryMinimum, bounds.memoryBound,
        bounds.passBound, bounds.laneBound, bounds.sliceBound, active, ?_⟩
      rcases bounds.active with hp | hs | hi
      · exact Or.inl hp
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr (by omega))
    · exact ⟨(k.regs .rbx (by decide)).trans h.filling.position.current,
        (k.regs .r12 (by decide)).trans h.filling.position.laneLength,
        (k.regs .r13 (by decide)).trans h.filling.position.segmentLength,
        (k.regs .r14 (by decide)).trans h.filling.position.slice, value⟩
    · rw [k.mem, bp]; exact h.filling.passWord
    · rw [k.mem, bp]; exact h.filling.lanesWord
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.X86_64.FillSegment
end

/-! Merged from `Proof.Argon2.X86_64.FillAllocation`. -/
section
/-! Transport the allocation using just its public pointers and permissions. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem Layout.of_preserved {p : Params} {s t : State} (h : VG.Proof.Argon2.X86_64.FillKernel.Layout p s)
    (bp : t.gpr .rbp = s.gpr .rbp) (sp : t.gpr .rsp = s.gpr .rsp)
    (base : VG.Proof.Argon2.X86_64.FillKernel.matrix t = VG.Proof.Argon2.X86_64.FillKernel.matrix s) (scratch : VG.Proof.Argon2.X86_64.FillKernel.work t = VG.Proof.Argon2.X86_64.FillKernel.work s)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : VG.Proof.Argon2.X86_64.FillKernel.Layout p t := by
  constructor
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [wr, bp]; exact h.frameWrite
  · rw [base, wr]; exact h.matrixWrite
  · rw [scratch, wr]; exact h.workWrite
  · rw [base, scratch]; exact h.matrixWork
  · rw [base, bp]; exact h.matrixFrame
  · rw [base, sp]; exact h.matrixStack
  · rw [bp, scratch]; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, scratch]; exact h.stackWork

end VG.Proof.Argon2.X86_64.FillKernel
end

/-! One segment iteration updates the specified cell and advances its public index. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice (index + 1) t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .r15 → t.gpr r = s.gpr r
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes
  cf : t.cf = decide (index + 1 < p.segmentLen)
  next : index + 1 < p.segmentLen → ∃ old, RandomSource.Ready p pass lane slice (index + 1) old t

theorem body_ok [CompressImpl] (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillSegment.body s (VG.Proof.Argon2.X86_64.FillSegment.Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.X86_64.FillSegment.body
  refine WP.seq ((FillBlock.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a filled
  obtain ⟨counter, ready⟩ := filled.ready
  refine (VG.Proof.Argon2.X86_64.FillSegment.advance_nat_ok a p pass lane slice index ready.filling).mono ?_
  rintro t ⟨value, cf, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [keeps.mem, bp]
  refine ⟨?_, base.trans filled.matrix, work.trans filled.work, ?_, keeps.rd.trans filled.rd,
    keeps.wr.trans filled.wr, ?_, (ctl_eq_of keeps.mxcsr).trans filled.mxcsr, ?_, ?_, ?_, ?_, ?_, ?_, cf, ?_⟩
  · rw [keeps.mem, base]; exact filled.represented
  · exact ⟨(keeps.regs .rbx (by decide)).trans ready.filling.position.current,
      (keeps.regs .r12 (by decide)).trans ready.filling.position.laneLength,
      (keeps.regs .r13 (by decide)).trans ready.filling.position.segmentLength,
      (keeps.regs .r14 (by decide)).trans ready.filling.position.slice, value⟩
  · rw [keeps.mem]; exact filled.frame
  · intro r hr ne
    have outside : r ∉ [Reg.r15] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ne
    exact (keeps.regs r outside).trans (filled.regs r hr)
  · exact ready.filling.layout.of_preserved bp (keeps.regs .rsp (by decide)) base work keeps.rd keeps.wr
  · exact ⟨counter, ready.cache.of_state (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr⟩
  · rw [base, work]; exact ready.matrixWork
  · rw [keeps.mem, bp]; exact ready.filling.passWord
  · rw [keeps.mem, bp]; exact ready.filling.lanesWord
  · intro active; exact ⟨counter, VG.Proof.Argon2.X86_64.FillSegment.next_ready ready keeps value active⟩

end VG.Proof.Argon2.X86_64.FillSegment

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.FillSegment`. -/
section

/-! Termination and correctness of the active suffix of one segment. -/

namespace VG.Proof.Argon2.X86_64.FillSegment

open VG VG.X86_64 VG.Spec.Argon2

structure Finished (s t : State) (p : Params) (pass lane slice : Nat) (state : FillState) : Prop where
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks state.memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  position : ReferenceMap.Position p lane slice p.segmentLen t
  layout : FillKernel.Layout p t
  cache : ∃ old, AddressCache.Invariant p pass lane slice old t
  matrixWork : (⟨FillKernel.matrix t, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work t, 8192⟩
  passWord : t.mem.readW (off (t.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  lanesWord : t.mem.readW (off (t.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes
  regs : ∀ r ∈ calleeSaved, r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (FillBlock.writes s p) s.mem t.mem
  mxcsr : ctl t.mxcsr = ctl s.mxcsr

theorem Done.finished {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (h : VG.Proof.Argon2.X86_64.FillSegment.Done s t p pass lane slice index state) (last : index + 1 = p.segmentLen) :
    VG.Proof.Argon2.X86_64.FillSegment.Finished s t p pass lane slice (fillBlock p pass slice lane index state) :=
  ⟨h.represented, h.matrix, h.work, last ▸ h.position, h.layout, h.cache,
    h.matrixWork, h.passWord, h.lanesWord, h.regs, h.rd, h.wr, h.frame, h.mxcsr⟩

theorem Finished.prepend {s a t : State} {p : Params} {pass lane slice index : Nat}
    {state finalState : FillState} (first : VG.Proof.Argon2.X86_64.FillSegment.Done s a p pass lane slice index state)
    (rest : VG.Proof.Argon2.X86_64.FillSegment.Finished a t p pass lane slice finalState) : VG.Proof.Argon2.X86_64.FillSegment.Finished s t p pass lane slice finalState := by
  refine ⟨rest.represented, rest.matrix.trans first.matrix, rest.work.trans first.work,
    rest.position, rest.layout, rest.cache, rest.matrixWork, rest.passWord, rest.lanesWord,
    ?_, rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr⟩
  · intro r hr ne; exact (rest.regs r hr ne).trans (first.regs r hr ne)
  · have frame := rest.frame
    rw [FillBlock.writes, first.matrix, first.work,
      first.regs .rsp (by simp [calleeSaved]) (by decide),
      first.regs .rbp (by simp [calleeSaved]) (by decide)] at frame
    exact first.frame.trans frame

theorem loop_ok [CompressImpl] (count : Nat) (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory)
    (positive : 0 < count) (endIndex : index + count = p.segmentLen) :
    WP isa Impl.Argon2.X86_64.FillSegment.loop s
      (VG.Proof.Argon2.X86_64.FillSegment.Finished s · p pass lane slice (Proof.Argon2.segment p pass lane slice index count state)) := by
  induction count generalizing s index old state with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := VG.Proof.Argon2.X86_64.FillSegment.body_ok s p pass lane slice index old h state represented
    rw [Proof.Argon2.segment_succ]
    cases n with
    | zero =>
      have last : index + 1 = p.segmentLen := endIndex
      refine ⟨_, a, .loopExit run ?_, ?_⟩
      · simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
      · exact done.finished last
    | succ n =>
      have active : index + 1 < p.segmentLen := by omega
      obtain ⟨nextCounter, nextReady⟩ := done.next active
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (index + 1) nextCounter nextReady
        (fillBlock p pass slice lane index state) done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.FillSegment

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ReducePointers`. -/
section

/-! The last-lane address calculation preserves all callee-saved registers. -/

namespace VG.Proof.Argon2.X86_64.ReducePointers

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.ReducePointers

def changed : List Reg := [.r8, .rax, .rcx, .rdx, .rsi, .rdi]

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 232) 8) :
    WP isa (.block Impl.Argon2.X86_64.ReducePointers.setup) s fun t =>
      t.gpr .r8 = s.mem.readW (off (s.gpr .rbp) 232) 64 ∧
      t.gpr .rax = s.gpr .rbx ∧ t.gpr .rcx = s.gpr .r12 - 1 ∧
      Divide.Keeps [.r8, .rax, .rcx] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ReducePointers.setup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, VG.Proof.Argon2.X86_64.ea_at, read, ite_true, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]
  refine ⟨trivial, trivial, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.X86_64.ReducePointers.finish) s fun t =>
    t.gpr .rsi = s.gpr .rax ∧ t.gpr .rdi = s.gpr .r8 ∧ Divide.Keeps [.rsi, .rdi] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ReducePointers.finish, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem code_ok (s : State) (lane q : Nat) (positive : 0 < q)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 232) 8)
    (laneWord : s.gpr .rbx = BitVec.ofNat 64 lane) (lengthWord : s.gpr .r12 = BitVec.ofNat 64 q) :
    WP isa VG.Impl.Argon2.X86_64.ReducePointers.code s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 232) 64 ∧
      t.gpr .rsi = Proof.Argon2.matrixCell (s.mem.readW (off (s.gpr .rbp) 232) 64) ((lane + 1) * q - 1) ∧
      Divide.Keeps VG.Proof.Argon2.X86_64.ReducePointers.changed s t := by
  unfold VG.Impl.Argon2.X86_64.ReducePointers.code
  refine WP.seq ((VG.Proof.Argon2.X86_64.ReducePointers.setup_ok s read).mono ?_)
  rintro a ⟨base, lan, col, ka⟩
  have column : a.gpr .rcx = BitVec.ofNat 64 (q - 1) := by
    rw [col, lengthWord]
    exact Offset.ofNat_sub_ofNat (by omega : 1 ≤ q)
  refine WP.seq ((BlockAddress.code_nat_ok a lane (q - 1) q (lan.trans laneWord) column
    ((ka.regs .r12 (by decide)).trans lengthWord)).mono ?_)
  rintro b ⟨address, kb⟩
  refine (VG.Proof.Argon2.X86_64.ReducePointers.finish_ok b).mono ?_
  rintro t ⟨src, dest, kt⟩
  refine ⟨dest.trans ((kb.regs .r8 (by decide)).trans base), ?_, ?_⟩
  · rw [src, address, base]
    unfold Proof.Argon2.matrixCell
    have offset : lane * q + (q - 1) = (lane + 1) * q - 1 := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [offset]
  · exact (ka.mono (by simp [VG.Proof.Argon2.X86_64.ReducePointers.changed])).trans
      ((kb.mono (by simp [VG.Proof.Argon2.X86_64.ReducePointers.changed])).trans (kt.mono (by simp [VG.Proof.Argon2.X86_64.ReducePointers.changed])))

end VG.Proof.Argon2.X86_64.ReducePointers

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ReduceLane`. -/
section

/-! Merged from `Proof.Argon2.X86_64.ReductionState`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceBlock`. -/
section
/-! Reuse the verified word loop with allocation-level permissions. -/

namespace VG.Proof.Argon2.X86_64.ReduceBlock

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.ReduceBlock

theorem code_ok (s : State)
    (read : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr))
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (separate : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa VG.Impl.Argon2.X86_64.ReduceBlock.code s fun t =>
      blockAt t.mem (s.gpr .rdi) = xorBlock (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi)) ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  let a := s.withRegions [⟨s.gpr .rsi, 1024⟩] [⟨s.gpr .rdi, 1024⟩]
  obtain ⟨trace, t, run, written, frame, keeps, mx⟩ :=
    FillWrite.prefix_ok true 128 (by decide) a (by simp [a]) (by simp [a]) separate
  have cover : Covers (a.rd ++ a.wr) (s.rd ++ s.wr) := by
    intro q n ⟨r, hr, hc⟩
    change r ∈ [⟨s.gpr .rsi, 1024⟩, ⟨s.gpr .rdi, 1024⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact read q n ⟨_, by simp, hc⟩
    · obtain ⟨r, hr, hc⟩ := write q n ⟨_, by simp, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have run' := Exec.widen (rd := s.rd) (wr := s.wr) run cover write
  simp only [a, State.withRegions_withRegions, State.withRegions_self] at run'
  refine ⟨trace, t.withRegions s.rd s.wr, run', ?_, frame, ⟨keeps.1, rfl, rfl⟩, mx⟩
  exact (written_block written).trans (Proof.Argon2.xorBlock_comm _ _)

end VG.Proof.Argon2.X86_64.ReduceBlock
end

/-! Block zero is the accumulator; every lane's last block remains unchanged. -/

namespace VG.Proof.Argon2.X86_64.ReductionState

open VG VG.X86_64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 232) 64

structure Ready (p : Params) (s : State) : Prop where
  positive : 0 < p.lanes
  minimum : 2 ≤ p.segmentLen
  bound : p.blocks * 1024 < 2 ^ 64
  read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 232) 8
  write : Covers [⟨VG.Proof.Argon2.X86_64.ReductionState.matrix s, p.blocks * 1024⟩] s.wr
  frame : (⟨VG.Proof.Argon2.X86_64.ReductionState.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .rbp, 272⟩
  length : s.gpr .r12 = BitVec.ofNat 64 p.laneLen

structure Represents (p : Params) (memory : Array Block) (acc : Block) (s : State) : Prop where
  accumulator : blockAt s.mem (VG.Proof.Argon2.X86_64.ReductionState.matrix s) = acc
  last : ∀ lane < p.lanes,
    blockAt s.mem (Proof.Argon2.matrixCell (VG.Proof.Argon2.X86_64.ReductionState.matrix s) (Proof.Argon2.lastIndex p lane)) =
      memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock

theorem Ready.block_cover {p : Params} {s : State} (h : VG.Proof.Argon2.X86_64.ReductionState.Ready p s) (k : Nat) (active : k < p.blocks) :
    Covers [⟨Proof.Argon2.matrixCell (VG.Proof.Argon2.X86_64.ReductionState.matrix s) k, 1024⟩] s.wr := by
  have sub : Covers [⟨Proof.Argon2.matrixCell (VG.Proof.Argon2.X86_64.ReductionState.matrix s) k, 1024⟩] [⟨VG.Proof.Argon2.X86_64.ReductionState.matrix s, p.blocks * 1024⟩] :=
    Covers.of_sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨VG.Proof.Argon2.X86_64.ReductionState.matrix s, p.blocks * 1024⟩, by simp, k * 1024, rfl, by change k * 1024 + 1024 ≤ p.blocks * 1024; omega⟩)
  exact fun a n ha => h.write a n (sub a n ha)

theorem Ready.accumulator_cover {p : Params} {s : State} (h : VG.Proof.Argon2.X86_64.ReductionState.Ready p s) :
    Covers [⟨VG.Proof.Argon2.X86_64.ReductionState.matrix s, 1024⟩] s.wr := by
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using h.block_cover 0 (by omega)

theorem Ready.of_keeps {p : Params} {s t : State} (h : VG.Proof.Argon2.X86_64.ReductionState.Ready p s)
    (k : Divide.Keeps ReducePointers.changed s t) : VG.Proof.Argon2.X86_64.ReductionState.Ready p t := by
  have bp := k.regs .rbp (by decide)
  have base : VG.Proof.Argon2.X86_64.ReductionState.matrix t = VG.Proof.Argon2.X86_64.ReductionState.matrix s := by unfold VG.Proof.Argon2.X86_64.ReductionState.matrix; rw [k.mem, bp]
  refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (k.regs .r12 (by decide)).trans h.length⟩
  · rw [k.rd, k.wr, bp]; exact h.read
  · rw [base, k.wr]; exact h.write
  · rw [base, bp]; exact h.frame

theorem Represents.of_keeps {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : VG.Proof.Argon2.X86_64.ReductionState.Represents p memory acc s) (k : Divide.Keeps ReducePointers.changed s t) : VG.Proof.Argon2.X86_64.ReductionState.Represents p memory acc t := by
  have base : VG.Proof.Argon2.X86_64.ReductionState.matrix t = VG.Proof.Argon2.X86_64.ReductionState.matrix s := by unfold VG.Proof.Argon2.X86_64.ReductionState.matrix; rw [k.mem, k.regs .rbp (by decide)]
  constructor
  · rw [k.mem, base]; exact h.accumulator
  · rw [k.mem, base]; exact h.last

end VG.Proof.Argon2.X86_64.ReductionState
end

/-! A lane reduction writes only the accumulator, retaining every last-lane block. -/

namespace VG.Proof.Argon2.X86_64.ReduceLane

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Done (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  ready : VG.Proof.Argon2.X86_64.ReductionState.Ready p t
  represented : ReductionState.Represents p memory acc t
  base : VG.Proof.Argon2.X86_64.ReductionState.matrix t = VG.Proof.Argon2.X86_64.ReductionState.matrix s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨VG.Proof.Argon2.X86_64.ReductionState.matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem code_ok (s : State) (p : Params) (lane : Nat) (h : VG.Proof.Argon2.X86_64.ReductionState.Ready p s) (active : lane < p.lanes)
    (laneWord : s.gpr .rbx = BitVec.ofNat 64 lane) (memory : Array Block) (acc : Block)
    (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.X86_64.ReduceLane.code s
      (VG.Proof.Argon2.X86_64.ReduceLane.Done s · p memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
  have lastBounds := Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active
  have q : 0 < p.laneLen := by
    have eq := Proof.Argon2.laneLen_segments p h.positive
    have minimum := h.minimum
    omega
  unfold Impl.Argon2.X86_64.ReduceLane.code
  refine WP.seq ((ReducePointers.code_ok s lane p.laneLen q h.read laneWord h.length).mono ?_)
  rintro a ⟨dest, src, keeps⟩
  have ha := h.of_keeps keeps
  have rep := represented.of_keeps keeps
  have base : VG.Proof.Argon2.X86_64.ReductionState.matrix a = VG.Proof.Argon2.X86_64.ReductionState.matrix s := by unfold VG.Proof.Argon2.X86_64.ReductionState.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  have dest' : a.gpr .rdi = VG.Proof.Argon2.X86_64.ReductionState.matrix a := dest.trans base.symm
  have src' : a.gpr .rsi = Proof.Argon2.matrixCell (VG.Proof.Argon2.X86_64.ReductionState.matrix a) (Proof.Argon2.lastIndex p lane) := by rw [base]; exact src
  have sourceWrite : Covers [⟨a.gpr .rsi, 1024⟩] a.wr := by rw [src']; exact ha.block_cover _ lastBounds.2
  have sourceRead : Covers [⟨a.gpr .rsi, 1024⟩] (a.rd ++ a.wr) := by
    intro x n hx
    obtain ⟨r, hr, hc⟩ := sourceWrite x n hx
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have destWrite : Covers [⟨a.gpr .rdi, 1024⟩] a.wr := by rw [dest']; exact ha.accumulator_cover
  have sep : (⟨a.gpr .rsi, 1024⟩ : Region).Disjoint ⟨a.gpr .rdi, 1024⟩ := by
    rw [src', dest']
    simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
      Proof.Argon2.matrixCell_disjoint (VG.Proof.Argon2.X86_64.ReductionState.matrix a) p.blocks (Proof.Argon2.lastIndex p lane) 0 ha.bound
        lastBounds.2 (by omega) (by omega)
  refine (ReduceBlock.code_ok a sourceRead destWrite sep).mono ?_
  rintro t ⟨written, frame, copied, mx⟩
  rw [dest'] at frame written
  have bp : t.gpr .rbp = a.gpr .rbp := copied.1 .rbp (by decide)
  have base' : VG.Proof.Argon2.X86_64.ReductionState.matrix t = VG.Proof.Argon2.X86_64.ReductionState.matrix a := by
    unfold VG.Proof.Argon2.X86_64.ReductionState.matrix
    rw [bp]
    exact frame.readW (r := ⟨a.gpr .rbp, 272⟩) (Offset.contains_base _ (by decide) (by decide))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact ha.frame.symm.sub_right (Region.sub_prefix (by omega))) (by decide)
  refine ⟨?_, ?_, base'.trans base, ?_, copied.2.1.trans keeps.rd, copied.2.2.trans keeps.wr,
    ?_, mx.trans keeps.mxcsr⟩
  · refine ⟨ha.positive, ha.minimum, ha.bound, ?_, ?_, ?_, (copied.1 .r12 (by decide)).trans ha.length⟩
    · rw [copied.2.1, copied.2.2, bp]; exact ha.read
    · rw [base', copied.2.2]; exact ha.write
    · rw [base', bp]; exact ha.frame
  · constructor
    · rw [base', written, src', rep.accumulator, rep.last lane active]
    · intro j hj
      rw [base']
      apply Eq.trans _ (rep.last j hj)
      apply FillCompress.block_frame frame
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      have bounds := Proof.Argon2.lastIndex_bounds p ha.positive ha.minimum j hj
      simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
        Proof.Argon2.matrixCell_disjoint (VG.Proof.Argon2.X86_64.ReductionState.matrix a) p.blocks (Proof.Argon2.lastIndex p j) 0 ha.bound
          bounds.2 (by omega) (by omega)
  · intro r hr
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have unchanged : r ∉ ReducePointers.changed := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (copied.1 r ne).trans (keeps.regs r unchanged)
  · rw [base, keeps.mem] at frame; exact frame

end VG.Proof.Argon2.X86_64.ReduceLane

end
