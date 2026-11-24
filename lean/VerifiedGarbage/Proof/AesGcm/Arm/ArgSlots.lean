module

public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Offset

/-! The one-shot and gather seal headers reorder their public stack arguments.
This proof applies to either ordering, including the fixed memory-address trace. -/

@[expose] public section
namespace VG.Proof.AesGcm.Arm.Args
open VG VG.Arm VG.Proof.AesGcm.Arm

structure Slots where
  count : Nat
  bytes : Nat
  index : Nat → Nat
  indexLt : ∀ j < count, index j < count
  header : 4*count+8 ≤ bytes
  imm : bytes+4*count ≤ 4096
  small : 4*count+8 < 256

def Slots.source (q : Slots) (j : Nat) := q.bytes+4*q.index j
def Slots.move (q : Slots) (j : Nat) : List Instr := [.ldrSp .lr (q.source j), .str .lr .r12 (4*j)]
def Slots.leaks (q : Slots) (sp : BitVec 32) (j : Nat) : List Leak := [.addr (sa sp (q.source j)), .addr (sa sp (4*j))]
def Slots.code (q : Slots) : List Instr :=
  [.addSp .r12 0,.str .lr .r12 (4*q.count+4)] ++ (List.range q.count).flatMap q.move ++
    [.addSp .lr (4*q.count+8),.str .lr .r12 (4*q.count),.ldrSp .lr (4*q.count+4)]

theorem Slots.bound (q : Slots) {j : Nat} (hj : j < q.count) :
    q.bytes ≤ q.source j ∧ q.source j + 4 ≤ q.bytes + 4*q.count := by
  have h := q.indexLt j hj
  unfold source
  omega

variable {q : Slots}

structure Layout (q : Slots) (u : State) : Prop where
  fit : u.sp.toNat+(q.bytes+4*q.count)≤2^32
  read : ∀ j<q.count, InRegions (u.rd++u.wr) (sa u.sp (q.source j)) 4
  write : ∀ d, d+4≤(4*q.count+8) → InRegions u.wr (sa u.sp d) 4

structure Copied (q : Slots) (u t : State) (n : Nat) : Prop where
  sp : t.sp=u.sp
  rd : t.rd=u.rd
  wr : t.wr=u.wr
  regs : ∀ r, r≠.lr → t.gpr r=u.gpr r
  frame : Frame [⟨State.addr u.sp,(4*q.count)⟩] u.mem t.mem
  words : ∀ j<n, t.mem.readW (sa u.sp (4*j)) 32=u.mem.readW (sa u.sp (q.source j)) 32

theorem Layout.sep {u : State} (L : Layout q u) {d e : Nat}
    (gap : d+4≤e ∨ e+4≤d) (dl : d+4≤(q.bytes+4*q.count)) (el : e+4≤(q.bytes+4*q.count)) :
    Mem.Sep (sa u.sp d) (32/8) (sa u.sp e) (32/8) := by
  have fit := L.fit
  rw [sa_eq (by omega),sa_eq (by omega)]
  exact Offset.sep _ gap (by omega) (by omega)

theorem Layout.range {u : State} (L : Layout q u) {d k : Nat} (hk : d+4≤k) (hf : k≤(q.bytes+4*q.count)) :
    (⟨State.addr u.sp,k⟩ : Region).Contains (sa u.sp d) 4 := by
  have fit := L.fit
  rw [sa_eq (by omega)]
  exact Offset.contains_base _ hk (by omega)

theorem copies {u : State} (L : Layout q u) (r12 : u.gpr .r12=u.sp) : ∀ n, n≤q.count →
    ∃ t, execBlock isa ((List.range n).flatMap q.move) u=some (t,(List.range n).flatMap (q.leaks u.sp)) ∧
      Copied q u t n
  | 0,_ => ⟨u,rfl,rfl,rfl,rfl,fun _ _ => rfl,Frame.refl _ _,fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n+1,hn => by
    have header := q.header
    have imm := q.imm
    obtain ⟨t,run,h⟩ := copies L r12 n (by omega)
    have hi : n<q.count := by omega
    have ⟨lower,upper⟩ := q.bound hi
    have base : t.gpr .r12=t.sp := by rw [h.regs _ (by decide),r12,h.sp]
    have read := L.read n hi
    have write := L.write (4*n) (by omega)
    let off : Nat := q.source n - 4*n
    have offEq : off+4*n = q.source n := Nat.sub_add_cancel (by omega)
    have step := copyArg_run (bytes:=off) (j:=n) base (by omega)
      (by rw [h.rd,h.wr,h.sp,offEq]; exact read)
      (by rw [h.wr,h.sp]; exact write)
    have op : q.move n = VG.Impl.StackScratch.Arm.copyArg off n := by
      simp only [Slots.move,VG.Impl.StackScratch.Arm.copyArg,offEq]
    rw [List.range_succ,List.flatMap_append,List.flatMap_append,List.flatMap_singleton,List.flatMap_singleton,
      execBlock_append,run,Option.bind_some,op,step,Option.map_some,h.sp,offEq]
    refine ⟨_,rfl,h.sp,h.rd,h.wr,fun r neq => (copyState_gpr _ _ t neq).trans (h.regs r neq),?_,?_⟩
    · change Frame _ _ (t.mem.writeW (sa t.sp _) _)
      rw [h.sp]
      exact h.frame.writeW (List.mem_singleton_self _) _ (L.range (by omega) (by omega))
    · intro j hj
      change (t.mem.writeW (sa t.sp (4*n)) (t.mem.readW (sa t.sp (off+4*n)) 32)).readW _ 32=_
      rw [h.sp,offEq]
      rcases Nat.lt_or_ge j n with lt|ge
      · rw [Mem.readW_writeW_sep (L.sep (.inl (by omega)) (by omega) (by omega)) (by omega),h.words j lt]
      · obtain rfl : j=n := by omega
        rw [Mem.readW_writeW_self32]
        refine h.frame.readW (r:=⟨sa u.sp (q.source j),4⟩) (Region.contains_self _ _) ?_ (by omega)
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        have fit := L.fit
        rw [sa_eq (by omega)]
        exact Offset.disjoint_base _ (by omega) (by omega)

/-- Stack traffic is fixed for every call. -/
def Slots.frameTrace (q : Slots) (sp : BitVec 32) := [.addr (sa sp (4*q.count+4))] ++ (List.range q.count).flatMap (q.leaks sp) ++
  [.addr (sa sp (4*q.count)),.addr (sa sp (4*q.count+4))]

structure Ready (q : Slots) (u t : State) : Prop where
  sp : t.sp=u.sp
  rd : t.rd=u.rd
  wr : t.wr=u.wr
  regs : ∀ r, r≠.r12 → t.gpr r=u.gpr r
  frame : Frame [⟨State.addr u.sp,(4*q.count+8)⟩] u.mem t.mem
  words : ∀ j<q.count, t.mem.readW (sa u.sp (4*j)) 32=u.mem.readW (sa u.sp (q.source j)) 32
  scratch : t.mem.readW (sa u.sp (4*q.count)) 32 = u.sp+BitVec.ofNat 32 (4*q.count+8)

theorem frameArgs_run {u : State} (L : Layout q u) :
    ∃ t, execBlock isa q.code u=some (t,q.frameTrace u.sp) ∧ Ready q u t := by
  have header := q.header
  have small := q.small
  have imm := q.imm
  let v := savedState q.count u
  have head := head_run (u:=u) (m:=q.count) (by omega) (L.write _ (by omega))
  have vL : Layout q v := ⟨L.fit,L.read,L.write⟩
  obtain ⟨x,run,c⟩ := copies vL (savedState_r12 q.count u) q.count (by omega)
  have sp : x.sp=u.sp := c.sp
  have wr : x.wr=u.wr := c.wr
  have rd : x.rd=u.rd := c.rd
  have r12 : x.gpr .r12=x.sp := (c.regs _ (by decide)).trans ((savedState_r12 _ _).trans sp.symm)
  obtain ⟨t,tail,trd,twr,tsp,regs,mem,lr⟩ := tail_run (m:=q.count) r12 (by omega)
    (by rw [sp,wr]; exact L.write _ (by omega))
    (by rw [sp,rd,wr]; obtain ⟨r,hr,hc⟩ := L.write (4*q.count+4) (by omega); exact ⟨r,List.mem_append_right _ hr,hc⟩)
  have code : q.code = [.addSp .r12 0, .str .lr .r12 (4*q.count+4)] ++ (List.range q.count).flatMap q.move ++
      [.addSp .lr (4*q.count+8),.str .lr .r12 (4*q.count),.ldrSp .lr (4*q.count+4)] := rfl
  have hf : Frame [⟨State.addr u.sp,(4*q.count+8)⟩] u.mem v.mem :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (L.range (d:=4*q.count+4) (by omega) (by omega))
  have hf' : Frame [⟨State.addr u.sp,(4*q.count+8)⟩] u.mem x.mem :=
    hf.trans (c.frame.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_singleton_self _,Region.sub_prefix (by omega)⟩)
  have saved : x.mem.readW (sa u.sp (4*q.count+4)) 32 = u.gpr .lr := by
    rw [c.frame.readW (r:=⟨sa u.sp (4*q.count+4),4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by omega)]
    · exact Mem.readW_writeW_self32 _ _ _
    · obtain rfl := List.mem_singleton.mp hr
      change Region.Disjoint ⟨sa u.sp (4*q.count+4),4⟩ ⟨State.addr u.sp,(4*q.count)⟩
      have fit := L.fit
      rw [sa_eq (by omega)]
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine ⟨t,?_,tsp.trans sp,trd.trans rd,twr.trans wr,?_,?_,?_,?_⟩
  · rw [code,execBlock_append,execBlock_append,head]
    dsimp only [v] at run
    simp only [Option.bind_some,run,Option.map_some,savedState_sp,tail,sp]
    rfl
  · intro r h
    by_cases q : r=.lr
    · subst q; rw [lr,mem,sp,Mem.readW_writeW_sep (L.sep (.inr (by omega)) (by omega) (by omega)) (by omega)]
      exact saved
    · rw [regs r q,c.regs r q]; exact savedState_gpr _ _ h
  · rw [mem,sp]; exact hf'.writeW (List.mem_singleton_self _) _ (L.range (d:=(4*q.count)) (by omega) (by omega))
  · intro j hj
    have ⟨lo,hi⟩ := q.bound hj
    rw [mem,sp,Mem.readW_writeW_sep (L.sep (.inl (by omega)) (by omega) (by omega)) (by omega)]
    have z := c.words j hj
    change x.mem.readW (sa u.sp (4*j)) 32 = (u.mem.writeW (sa u.sp (4*q.count+4)) (u.gpr .lr)).readW (sa u.sp (q.source j)) 32 at z
    rw [z,Mem.readW_writeW_sep (L.sep (.inr (by omega)) hi (by omega)) (by omega)]
  · rw [mem,sp,Mem.readW_writeW_self32]

end VG.Proof.AesGcm.Arm.Args
