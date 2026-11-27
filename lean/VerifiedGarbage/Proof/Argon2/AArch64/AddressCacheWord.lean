module

public import VerifiedGarbage.Impl.Argon2.AArch64.AddressCache
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Argon2.AArch64.Initialize
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.Carry
public import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
public import VerifiedGarbage.Impl.Argon2.AArch64.AddressCalls
public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions

/-! ### `Argon2.AArch64.AddressCallsStage`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.AArch64.AddressCallsLayout`. -/

@[expose] public section

section
/-! Merged from `Proof.Argon2.AArch64.AddressCallsArgs`. -/
section
/-! Independent-address compression arguments from one fixed frame read. -/
namespace VG.Proof.Argon2.AArch64.AddressCalls
open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCalls
open VG.Impl.Argon2.AArch64

def work (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 248) 64

theorem pointer_ok (s : State) (offset : Nat) (bound : offset ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block (pointer offset)) s fun t =>
      t.gpr .x0 = work s + BitVec.ofNat 64 offset ∧ Divide.Keeps [.x0, .x12, .x15] s t := by
  simp only [pointer, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x0 .x19 248 (by decide) (by decide) hr).mono ?_
  rintro a ⟨value, keeps⟩
  refine (Instructions.addi_ok a .x0 offset (by omega_using [bound]) (by decide) (by decide)).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨out.trans (congrArg (· + BitVec.ofNat 64 offset) value), ?_⟩
  exact (keeps.mono (by simp)).trans kt

theorem args_ok (s : State) (x y out : Nat) (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block (args x y out)) s fun t =>
      t.gpr .x3 = work s ∧ t.gpr .x0 = work s + BitVec.ofNat 64 x ∧
      t.gpr .x1 = work s + BitVec.ofNat 64 y ∧ t.gpr .x2 = work s + BitVec.ofNat 64 out ∧
      Divide.Keeps [.x3, .x0, .x1, .x2, .x12, .x15] s t := by
  simp only [args, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x3 .x19 248 (by decide) (by decide) hr).mono ?_
  rintro a ⟨scratch, ka⟩
  rw [← List.append_assoc (Instructions.mov .x0 .x3) (Instructions.addi .x0 x)]
  apply WP.block_append
  refine (Instructions.pointer_ok a .x0 .x3 x (by omega_using [hx]) (by decide) (by decide)).mono ?_
  rintro b ⟨left, kb⟩
  rw [← List.append_assoc (Instructions.mov .x1 .x3) (Instructions.addi .x1 y)]
  apply WP.block_append
  refine (Instructions.pointer_ok b .x1 .x3 y (by omega_using [hy]) (by decide) (by decide)).mono ?_
  rintro c ⟨right, kc⟩
  refine (Instructions.pointer_ok c .x2 .x3 out (by omega_using [ho]) (by decide) (by decide)).mono ?_
  rintro t ⟨output, kt⟩
  have scrB := kb.regs .x3 (by decide)
  have scrC := kc.regs .x3 (by decide)
  refine ⟨(kt.regs .x3 (by decide)).trans (scrC.trans (scrB.trans scratch)),
    (kt.regs .x0 (by decide)).trans ((kc.regs .x0 (by decide)).trans
      (left.trans (congrArg (· + BitVec.ofNat 64 x) scratch))),
    (kt.regs .x1 (by decide)).trans (right.trans (congrArg (· + BitVec.ofNat 64 y) (scrB.trans scratch))),
    output.trans (congrArg (· + BitVec.ofNat 64 out) (scrC.trans (scrB.trans scratch))), ?_⟩
  exact (ka.mono (by decide)).trans ((kb.mono (by decide)).trans
    ((kc.mono (by decide)).trans (kt.mono (by decide))))
end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! Permissions and separation for either address-generation compression call. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64

structure Ready (s : State) : Prop where
  frameRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8
  workWrite : Covers [⟨work s, 8192⟩] s.wr
  frameWork : (⟨s.gpr .x19, 272⟩ : Region).Disjoint ⟨work s, 8192⟩
  frameStack : (⟨s.gpr .x19, 272⟩ : Region).Disjoint (below s.sp 8)
  stackWork : (below s.sp 8).Disjoint ⟨work s, 8192⟩

theorem work_cover (s : State) (h : Ready s) (d n : Nat) (hd : d + n ≤ 8192) :
    Covers [⟨off (work s) d, n⟩] s.wr := by
  have sub : Covers [⟨off (work s) d, n⟩] [⟨work s, 8192⟩] := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨work s, 8192⟩, by simp, d, rfl, hd⟩
  exact fun p n hp => h.workWrite p n (sub p n hp)

structure Args (s a : State) (x y out : Nat) : Prop where
  scratch : a.gpr .x3 = work s
  left : a.gpr .x0 = off (work s) x
  right : a.gpr .x1 = off (work s) y
  output : a.gpr .x2 = off (work s) out
  keeps : Divide.Keeps [.x3, .x0, .x1, .x2, .x12, .x15] s a

theorem args_nat_ok (s : State) (h : Ready s) (x y out : Nat)
    (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192) :
    WP isa (.block (Impl.Argon2.AArch64.AddressCalls.args x y out)) s (Args s · x y out) := by
  refine (args_ok s x y out hx hy ho h.frameRead).mono ?_
  rintro a ⟨scratch, left, right, output, keeps⟩
  exact ⟨scratch, left, right, output, keeps⟩

theorem args_call_ready (s a : State) (h : Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192)
    (args : Args s a x y out) : FillCompress.CallReady a := by
  have read (d : Nat) (hd : d + 1024 ≤ 8192) :
      Covers [⟨off (work s) d, 1024⟩] (a.rd ++ a.wr) := by
    rw [args.keeps.rd, args.keeps.wr]
    intro p n hp
    obtain ⟨r, hr, hc⟩ := work_cover s h d 1024 hd p n hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have sp : a.sp = s.sp := args.keeps.sp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [args.left]; exact read x bx
  · rw [args.right]; exact read y by_
  · rw [args.output, args.keeps.wr]; exact work_cover s h out 1024 bo
  · rw [args.scratch, args.keeps.wr]
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      using work_cover s h 0 4096 (by decide)
  · rw [args.left, args.scratch]; exact Offset.disjoint_base _ hx (by omega_using [bx])
  · rw [args.right, args.scratch]; exact Offset.disjoint_base _ hy (by omega_using [by_])
  · rw [args.output, args.scratch]; exact Offset.disjoint_base _ ho (by omega_using [bo])
  · rw [sp, args.left]; exact h.stackWork.sub_right (Offset.sub_base _ bx)
  · rw [sp, args.right]; exact h.stackWork.sub_right (Offset.sub_base _ by_)
  · rw [sp, args.output]; exact h.stackWork.sub_right (Offset.sub_base _ bo)
  · rw [sp, args.scratch]; exact h.stackWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.AArch64.AddressCalls
end

/-! One verified G call within the independent-address scratch layout. -/

namespace VG.Proof.Argon2.AArch64.AddressCalls

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCalls

def stageWrites (s : State) (out : Nat) : List Region :=
  [⟨off (work s) out, 1024⟩, ⟨work s, 4096⟩, below s.sp 8]

structure StageDone (s t : State) (x y out : Nat) : Prop where
  result : blockAt t.mem (off (work s) out) = Spec.Argon2.compress
    (blockAt s.mem (off (work s) x)) (blockAt s.mem (off (work s) y))
  ready : Ready t
  work : work t = work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (stageWrites s out) s.mem t.mem

theorem Args.callee {s a : State} {x y out : Nat} (h : Args s a x y out)
    (r : Reg) (hr : r ∈ FillCompress.loopRegs) : a.gpr r = s.gpr r := by
  apply h.keeps.regs
  simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ready_of_frame {s t : State} (h : Ready s) (out : Nat) (ho : out + 1024 ≤ 8192)
    (regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp)
    (frame : Frame (stageWrites s out) s.mem t.mem) : Ready t ∧ work t = work s := by
  have bp := regs .x19 (by simp [FillCompress.loopRegs])
  have safe : ∀ r ∈ stageWrites s out, (⟨s.gpr .x19, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.frameWork.sub_right (Offset.sub_base _ ho)
    · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
    · exact h.frameStack
  have read : t.mem.readW (off (s.gpr .x19) 248) 64 = s.mem.readW (off (s.gpr .x19) 248) 64 :=
    frame.readW (r := ⟨s.gpr .x19, 272⟩)
      (Offset.contains_base _ (by decide) (by decide)) safe (by decide)
  have work' : work t = work s := by unfold work; rw [bp, read]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work'⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem stage_ok (s : State) (h : Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192) :
    WP isa (stage x y out) s (StageDone s · x y out) := by
  unfold stage
  refine WP.seq ((args_nat_ok s h x y out (by omega_using [bx]) (by omega_using [by_]) (by omega_using [bo])).mono ?_)
  intro a args
  have callReady := args_call_ready s a h x y out hx hy ho bx by_ bo args
  refine (FillCompress.call_ok _ a callReady).mono ?_
  intro t called
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r :=
    fun r hr => (called.regs r hr).trans (args.callee r hr)
  have rd := called.rd.trans args.keeps.rd
  have wr := called.wr.trans args.keeps.wr
  have sp := called.sp.trans args.keeps.sp
  have frame : Frame (stageWrites s out) s.mem t.mem := by
    have hf := called.frame
    rw [args.output, args.scratch, args.keeps.sp, args.keeps.mem] at hf
    exact hf
  obtain ⟨ready, work'⟩ := ready_of_frame h out bo regs rd wr sp frame
  refine ⟨?_, ready, work', regs, rd, wr, sp, frame⟩
  have result := called.result
  rw [args.output, args.left, args.right, args.keeps.mem] at result
  exact result

end VG.Proof.Argon2.AArch64.AddressCalls

end

end

/-! ### `Argon2.AArch64.AddressCacheMeta`, which this module and modules that import it used -/

section

/-! Public cache counters and indexed-word arguments. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache
open VG.Impl.Argon2.AArch64

def counter (index : Addr) : Addr := (index >>> 7) + 1

theorem check_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 8) 8) :
    WP isa (.block check) s fun t => t.gpr .x8 = counter (s.gpr .x23) ∧
      t.gpr .x15 = counter (s.gpr .x23) - s.mem.readW (off (s.gpr .x19) 8) 64 ∧
      Divide.Keeps [.x8, .x13, .x14, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [check, counter, Instructions.mov, Instructions.shr, Instructions.mark,
    Instructions.addi, Instructions.comparem, Instructions.compare, Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 8 % 8 = 0 ∧ 8 < 4096 * 8 from by decide,
    show (7 : Nat) < 64 from by decide, show (63 : Nat) < 64 from by decide,
    show 0 < 4096 from by decide, show 1 < 4096 from by decide,
    hr, and_self, ite_true, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_addWithCarry,
    sub_value, Bool.toNat_true, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, BitVec.add_zero,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem counter_nat (index : Addr) : counter index = BitVec.ofNat 64 (index.toNat / 128 + 1) := by
  have shifted : index >>> 7 = BitVec.ofNat 64 (index.toNat / 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := index.isLt; omega_using [])]
  unfold counter
  rw [shifted]
  exact (BitVec.ofNat_add _ _).symm

theorem counter_ne_zero (index : Addr) : counter index ≠ 0 := by
  have bound : index.toNat / 128 + 1 < 2 ^ 64 := by have := index.isLt; omega_using []
  intro h
  have nat := congrArg BitVec.toNat h
  rw [counter_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at nat
  change index.toNat / 128 + 1 = 0 at nat
  omega_using [nat]

theorem wordArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block wordArgs) s fun t => t.gpr .x3 = AddressCalls.work s ∧
      t.gpr .x8 = s.gpr .x23 &&& 127 ∧ Divide.Keeps [.x3, .x8, .x12, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [wordArgs, AddressCalls.work, off, Instructions.mov, Instructions.load,
    Instructions.logici, Instructions.logic, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide, show 127 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, hr, and_self, ite_true,
    RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false, BitVec.add_zero,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem index_nat (index : Addr) : index &&& 127 = BitVec.ofNat 64 (index.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  exact Nat.and_two_pow_sub_one_eq_mod index.toNat 7

end VG.Proof.Argon2.AArch64.AddressCache

end

end

/-! Read exactly the public indexed word of the cached address block. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCache
open VG.Impl.Argon2.AArch64

def wordAddress (s : State) : Addr :=
  s.gpr .x8 * BitVec.ofNat 64 8 + s.gpr .x3 + BitVec.ofInt 64 6144

theorem wordRead_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (wordAddress s) 8) :
    WP isa (.block wordRead) s fun t => t.gpr .x0 = s.mem.readW (wordAddress s) 64 ∧
      Divide.Keeps [.x0, .x12, .x13, .x15] s t := by
  change InRegions (s.rd ++ s.wr) (s.gpr .x8 * 8#64 + s.gpr .x3 + 6144#64) 8 at hr
  apply WP.of_runBlock
  simp only [wordRead, wordAddress, Instructions.mov, Instructions.add, Instructions.addi,
    Instructions.mark, Instructions.imm, Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, addr, State.load,
    Size.bytes, Size.bits, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide, show ¬6144 < 4096 from by decide,
    show 6144 < 65536 from by decide, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, and_self, Option.map_some, Option.bind_some,
    ← BitVec.mul_two, BitVec.mul_assoc,
    show (2#64) * (2#64 * 2#64) = 8#64 from rfl,
    show (6144#16).setWidth 64 = 6144#64 from rfl,
    show BitVec.ofInt 64 6144 = 6144#64 from rfl,
    hr, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem wordAddress_args {s a : State}
    (scratch : a.gpr .x3 = AddressCalls.work s)
    (index : a.gpr .x8 = s.gpr .x23 &&& 127) :
    wordAddress a = off (off (AddressCalls.work s) 6144) (8 * ((s.gpr .x23).toNat % 128)) := by
  unfold wordAddress off
  rw [scratch, index, index_nat, ← BitVec.ofNat_mul, Nat.mul_comm]
  change BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128)) + AddressCalls.work s +
    BitVec.ofNat 64 6144 = _
  rw [BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128))) (AddressCalls.work s),
    BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .x23).toNat % 128)))
      (BitVec.ofNat 64 6144), ← BitVec.add_assoc]

theorem word_ok (s : State) (h : AddressCalls.Ready s) :
    WP isa Impl.Argon2.AArch64.AddressCache.word s fun t => t.gpr .x0 =
      (blockAt s.mem (off (AddressCalls.work s) 6144))[(s.gpr .x23).toNat % 128]'(Nat.mod_lt _ (by decide)) ∧
      Divide.Keeps [.x3, .x8, .x0, .x12, .x13, .x15] s t := by
  unfold Impl.Argon2.AArch64.AddressCache.word
  refine WP.seq ((wordArgs_ok s h.frameRead).mono ?_)
  rintro a ⟨scratch, index, keeps⟩
  have address := wordAddress_args scratch index
  have read : InRegions (a.rd ++ a.wr) (wordAddress a) 8 := by
    rw [address, keeps.rd, keeps.wr]
    have cover := AddressCalls.work_cover s h 6144 1024 (by decide)
    have writable := cover _ _ ⟨⟨off (AddressCalls.work s) 6144, 1024⟩, by simp,
      Offset.contains_base _ (d := 8 * ((s.gpr .x23).toNat % 128)) (n := 8) (k := 1024)
        (by have := Nat.mod_lt (s.gpr .x23).toNat (by decide : 0 < 128); omega_using []) (by omega_using [])⟩
    obtain ⟨r, hr, hc⟩ := writable
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (wordRead_ok a read).mono ?_
  rintro t ⟨value, tail⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
  rw [value, address, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨_, Nat.mod_lt _ (by decide)⟩ : Fin 128)]
  rw [blockAt_get]

end VG.Proof.Argon2.AArch64.AddressCache
