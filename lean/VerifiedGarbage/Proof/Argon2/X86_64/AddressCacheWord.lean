module

public import VerifiedGarbage.Impl.Argon2.X86_64.AddressCache
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart
public import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCall
public import VerifiedGarbage.Impl.Argon2.X86_64.AddressCalls
public import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
public import VerifiedGarbage.Proof.Argon2.X86_64.Memory

/-! ### `Argon2.X86_64.AddressCallsStage`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.X86_64.AddressCallsLayout`. -/

@[expose] public section

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
    WP isa (.block (pointer offset)) s fun t =>
      t.gpr .rdi = work s + displacement offset ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [pointer, work, displacement, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg,
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
    WP isa (.block (args x y out)) s fun t =>
      t.gpr .rcx = work s ∧ t.gpr .rdi = work s + displacement x ∧
      t.gpr .rsi = work s + displacement y ∧ t.gpr .rdx = work s + displacement out ∧
      Divide.Keeps [.rcx, .rdi, .rsi, .rdx] s t := by
  apply WP.of_runBlock
  simp only [args, work, displacement, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg,
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
  workWrite : Covers [⟨work s, 8192⟩] s.wr
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨work s, 8192⟩
  frameStack : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint (below (s.gpr .rsp) 8)
  stackWork : (below (s.gpr .rsp) 8).Disjoint ⟨work s, 8192⟩

theorem displacement_eq (n : Nat) (bound : n ≤ 8192) : displacement n = BitVec.ofNat 64 n := by
  have n32 : n < 2 ^ 32 := by omega_using [bound]
  have msb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n32]
    omega_using [bound]
  unfold displacement
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb,
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) n32]

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
  scratch : a.gpr .rcx = work s
  left : a.gpr .rdi = off (work s) x
  right : a.gpr .rsi = off (work s) y
  output : a.gpr .rdx = off (work s) out
  keeps : Divide.Keeps [.rcx, .rdi, .rsi, .rdx] s a

theorem args_nat_ok (s : State) (h : Ready s) (x y out : Nat)
    (hx : x ≤ 8192) (hy : y ≤ 8192) (ho : out ≤ 8192) :
    WP isa (.block (Impl.Argon2.X86_64.AddressCalls.args x y out)) s (Args s · x y out) := by
  refine (args_ok s x y out h.frameRead).mono ?_
  rintro a ⟨scratch, left, right, output, keeps⟩
  rw [displacement_eq x hx] at left
  rw [displacement_eq y hy] at right
  rw [displacement_eq out ho] at output
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
  have sp : a.gpr .rsp = s.gpr .rsp := args.keeps.regs .rsp (by decide)
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

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! One verified G call within the independent-address scratch layout. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

def stageWrites (s : State) (out : Nat) : List Region :=
  [⟨off (work s) out, 1024⟩, ⟨work s, 4096⟩, below (s.gpr .rsp) 8]

structure StageDone (s t : State) (x y out : Nat) : Prop where
  result : blockAt t.mem (off (work s) out) = Spec.Argon2.compress
    (blockAt s.mem (off (work s) x)) (blockAt s.mem (off (work s) y))
  ready : Ready t
  work : work t = work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (stageWrites s out) s.mem t.mem

theorem Args.callee {s a : State} {x y out : Nat} (h : Args s a x y out)
    (r : Reg) (hr : r ∈ calleeSaved) : a.gpr r = s.gpr r := by
  apply h.keeps.regs
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ready_of_frame {s t : State} (h : Ready s) (out : Nat) (ho : out + 1024 ≤ 8192)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (frame : Frame (stageWrites s out) s.mem t.mem) : Ready t ∧ work t = work s := by
  have bp := regs .rbp (by simp [calleeSaved])
  have sp := regs .rsp (by simp [calleeSaved])
  have safe : ∀ r ∈ stageWrites s out, (⟨s.gpr .rbp, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [stageWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.frameWork.sub_right (Offset.sub_base _ ho)
    · exact h.frameWork.sub_right (Region.sub_prefix (by decide))
    · exact h.frameStack
  have read : t.mem.readW (off (s.gpr .rbp) 248) 64 = s.mem.readW (off (s.gpr .rbp) 248) 64 :=
    frame.readW (r := ⟨s.gpr .rbp, 272⟩)
      (Offset.contains_base _ (by decide) (by decide)) safe (by decide)
  have work' : work t = work s := by unfold work; rw [bp, read]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, work'⟩
  · rw [rd, wr, bp]; exact h.frameRead
  · rw [work', wr]; exact h.workWrite
  · rw [bp, work']; exact h.frameWork
  · rw [bp, sp]; exact h.frameStack
  · rw [sp, work']; exact h.stackWork

theorem stage_ok [CompressImpl] (s : State) (h : Ready s) (x y out : Nat)
    (hx : 4096 ≤ x) (hy : 4096 ≤ y) (ho : 4096 ≤ out)
    (bx : x + 1024 ≤ 8192) (by_ : y + 1024 ≤ 8192) (bo : out + 1024 ≤ 8192) :
    WP isa (stage x y out) s fun t => StageDone s t x y out ∧ ctl t.mxcsr = ctl s.mxcsr := by
  unfold stage
  refine WP.seq ((WP.with_mx (by rfl) (args_nat_ok s h x y out (by omega_using [bx]) (by omega_using [by_])
    (by omega_using [bo]))).mono ?_)
  rintro a ⟨args, mx1⟩
  have callReady := args_call_ready s a h x y out hx hy ho bx by_ bo args
  refine (FillCompress.call_ok a callReady).mono ?_
  rintro t ⟨called, mx2⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r :=
    fun r hr => (called.regs r hr).trans (args.callee r hr)
  have rd := called.rd.trans args.keeps.rd
  have wr := called.wr.trans args.keeps.wr
  have frame : Frame (stageWrites s out) s.mem t.mem := by
    have hf := called.frame
    rw [args.output, args.scratch, args.callee .rsp (by simp [calleeSaved]), args.keeps.mem] at hf
    exact hf
  obtain ⟨ready, work'⟩ := ready_of_frame h out bo regs rd wr frame
  refine ⟨⟨?_, ready, work', regs, rd, wr, frame⟩, by rw [mx2, mx1]⟩
  have result := called.result
  rw [args.output, args.left, args.right, args.keeps.mem] at result
  exact result

end VG.Proof.Argon2.X86_64.AddressCalls

end

end

/-! ### `Argon2.X86_64.AddressCacheMeta`, which this module and modules that import it used -/

section

/-! Public cache counters and indexed-word arguments. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

def counter (index : Addr) : Addr := (index >>> 7) + 1

theorem check_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 8) 8) :
    WP isa (.block check) s fun t => t.gpr .rax = counter (s.gpr .r15) ∧
      t.zf = decide (counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64) ∧
      Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [check, counter, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, State.load64, ea_at, hr, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
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
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block wordArgs) s fun t => t.gpr .rcx = AddressCalls.work s ∧
      t.gpr .rax = s.gpr .r15 &&& 127 ∧ Divide.Keeps [.rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [wordArgs, AddressCalls.work, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu,
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
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  exact Nat.and_two_pow_sub_one_eq_mod index.toNat 7

end VG.Proof.Argon2.X86_64.AddressCache

end

end

/-! Read exactly the public indexed word of the cached address block. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

def wordAddress (s : State) : Addr :=
  s.gpr .rcx + s.gpr .rax * BitVec.ofNat 64 8 + BitVec.ofInt 64 6144

theorem wordRead_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (wordAddress s) 8) :
    WP isa (.block wordRead) s fun t => t.gpr .rdi = s.mem.readW (wordAddress s) 64 ∧
      Divide.Keeps [.rdi] s t := by
  dsimp only [wordAddress] at hr
  apply WP.of_runBlock
  simp only [wordRead, wordAddress, runBlock_cons, runStep_some, runBlock_nil,
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
    wordAddress a = off (off (AddressCalls.work s) 6144) (8 * ((s.gpr .r15).toNat % 128)) := by
  unfold wordAddress off
  rw [scratch, index, index_nat, ← BitVec.ofNat_mul, Nat.mul_comm]
  change AddressCalls.work s + BitVec.ofNat 64 (8 * ((s.gpr .r15).toNat % 128)) +
    BitVec.ofNat 64 6144 = _
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .r15).toNat % 128)))
    (BitVec.ofNat 64 6144), ← BitVec.add_assoc]

theorem word_ok (s : State) (h : AddressCalls.Ready s) :
    WP isa Impl.Argon2.X86_64.AddressCache.word s fun t => t.gpr .rdi =
      (blockAt s.mem (off (AddressCalls.work s) 6144))[(s.gpr .r15).toNat % 128]'(Nat.mod_lt _ (by decide)) ∧
      Divide.Keeps [.rcx, .rax, .rdi] s t := by
  unfold Impl.Argon2.X86_64.AddressCache.word
  refine WP.seq ((wordArgs_ok s h.frameRead).mono ?_)
  rintro a ⟨scratch, index, keeps⟩
  have address := wordAddress_args scratch index
  have read : InRegions (a.rd ++ a.wr) (wordAddress a) 8 := by
    rw [address, keeps.rd, keeps.wr]
    have cover := AddressCalls.work_cover s h 6144 1024 (by decide)
    have writable := cover _ _ ⟨⟨off (AddressCalls.work s) 6144, 1024⟩, by simp,
      Offset.contains_base _ (d := 8 * ((s.gpr .r15).toNat % 128)) (n := 8) (k := 1024)
        (by have := Nat.mod_lt (s.gpr .r15).toNat (by decide : 0 < 128); omega_using []) (by omega_using [])⟩
    obtain ⟨r, hr, hc⟩ := writable
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (wordRead_ok a read).mono ?_
  rintro t ⟨value, tail⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
  rw [value, address, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨_, Nat.mod_lt _ (by decide)⟩ : Fin 128)]
  rw [blockAt_get]

end VG.Proof.Argon2.X86_64.AddressCache
