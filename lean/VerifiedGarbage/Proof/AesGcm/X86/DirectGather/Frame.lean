module

public import VerifiedGarbage.Impl.AesGcm.X86.DirectGather
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Fn
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.DirectGather

abbrev SP (s : State) := s.gpr .esp - 2612#32
abbrev work (s : State) := SP s + 52#32
abbrev allocated (s : State) := allocState 2612 s
abbrev region (s : State) : Region := ⟨w64 (SP s),52⟩

theorem spFit {s : State} (h : Gather.Lay s) : (SP s).toNat+2660 ≤ 2^32 := by
  have hn := h.hBn
  have hb : (Gather.Bs s).toNat = (s.gpr .esp).toNat - 2688 :=
    by change (w64 (s.gpr .esp) - BitVec.ofNat 64 2688).toNat = _
       rw [toNat_sub64 (by rw [toNat_w64]; exact h.w₁),toNat_w64]
  rw [hb] at hn
  rw [show (SP s).toNat = (s.gpr .esp).toNat - 2612 from Gather.sub_toNat32 (by omega_using [h.w₁])]
  omega_using [hn,h.w₁]

theorem norm {s : State} (h : Gather.Lay s) {d : Nat} (hd : d+4 ≤ 2660) :
    addr (SP s) d = w64 (SP s)+BitVec.ofNat 64 d := addr_eq (by omega_using [spFit h,hd])

theorem origArg (s : State) (i : Nat) : addr (SP s) (2616+4*i) = argAddr s i := by
  rw [show 2616+4*i=2612+(4+4*i) by omega]
  change w64 ((s.gpr .esp-2612#32)+BitVec.ofNat 32 (2612+(4+4*i))) = _
  rw [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.sub_add_cancel]; rfl

theorem argRead {s : State} (h : Gather.Lay s) {i : Nat} (hi : i<11) :
    InRegions ((allocated s).rd++(allocated s).wr) (addr (SP s) (2616+4*i)) 4 := by
  rw [origArg]
  refine ⟨Gather.argR s,List.mem_append_right _ (List.mem_cons_of_mem _ (h.wr ▸ by simp)),?_⟩
  change (⟨argAddr s 0,44⟩ : Region).Contains (argAddr s i) 4
  rw [← origArg,← origArg, norm h (d := 2616+4*0) (by decide),norm h (d := 2616+4*i) (by omega_using [hi])]
  exact Offset.contains _ (by omega_using [hi]) (by omega_using [hi]) (by decide)

theorem privateWrite (s : State) {d : Nat} (hd : d+4 ≤ 2612) (h : Gather.Lay s) :
    InRegions (allocated s).wr (addr (SP s) d) 4 := by
  rw [norm h (by omega_using [hd])]
  exact ⟨_,List.mem_cons_self ..,Offset.contains_base _ hd (by omega)⟩

abbrev copiesTrace (sp : BitVec 32) (n : Nat) := (List.range n).flatMap fun i =>
  [Leak.addr (addr sp (2616+4*sourceSlot i)),.addr (addr sp (4+4*i))]

structure Copies (s u : State) (n : Nat) : Prop where
  rd : u.rd = s.rd
  wr : u.wr = (allocated s).wr
  regs : ∀ r, r ≠ .eax → u.gpr r = (allocated s).gpr r
  frame : Frame [region s] s.mem u.mem
  slots : ∀ j<n, u.mem.readW (addr (SP s) (4+4*j)) 32 = arg s (sourceSlot j)

theorem copies_run {s : State} (h : Gather.Lay s) (n : Nat) (hn : n≤11) :
    ∃ u, execBlock isa ((List.range n).flatMap copySlot) (allocated s) =
      some (u,copiesTrace (SP s) n) ∧ Copies s u n := by
  induction n with
  | zero => exact ⟨_,rfl,rfl,rfl,fun _ _ => rfl,Frame.refl _ _,fun j hj => by omega⟩
  | succ n ih =>
    obtain ⟨u,run,hc⟩ := ih (by omega)
    have hi : sourceSlot n < 11 := by unfold sourceSlot; split <;> (first | split <;> omega | omega)
    have eq : 2612+4*sourceSlot n-4*n+4+4*n = 2616+4*sourceSlot n := by omega
    have sp := hc.regs .esp (by decide)
    change u.gpr .esp = SP s at sp
    have rd : InRegions (u.rd++u.wr) (addr (u.gpr .esp) (2612+4*sourceSlot n-4*n+4+4*n)) 4 := by
      rw [sp,eq,hc.rd,hc.wr]; exact argRead h hi
    have wr : InRegions u.wr (addr (u.gpr .esp) (4+4*n)) 4 := by
      rw [sp,hc.wr]; exact privateWrite _ (by omega) h
    obtain r := copyArg_run rd wr
    let z := copyState (2612+4*sourceSlot n-4*n) n u
    refine ⟨z,?_,hc.rd,hc.wr,fun q hq => (copyState_gpr _ _ u hq).trans (hc.regs q hq),?_,?_⟩
    · rw [List.range_succ,List.flatMap_append,execBlock_append,run]
      simp only [Option.bind_some,List.flatMap_singleton,copySlot,r,Option.map_some,copiesTrace,List.range_succ,List.flatMap_append,sp,eq,z]
    · change Frame _ _ (u.mem.writeW _ _); rw [sp,norm h (by omega : 4+4*n+4 ≤2660)]
      exact hc.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · intro j hj
      change (u.mem.writeW _ _).readW _ _ = _
      rw [sp,eq]
      by_cases same : j=n
      · subst j; rw [Mem.readW_writeW_self32]
        refine (hc.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans ?_
        · obtain rfl := List.mem_singleton.mp hr
          rw [norm h (by omega_using [hi])]; exact Offset.disjoint_base _ (by omega) (by omega_using [hi])
        · rw [origArg]; rfl
      · rw [Mem.readW_writeW_sep, hc.slots _ (by omega)]
        · rw [norm h (by omega : 4+4*j+4 ≤2660),norm h (by omega : 4+4*n+4 ≤2660)]
          exact Offset.sep _ (by omega) (by omega) (by omega)
        · decide

def frameTrace (sp : BitVec 32) := copiesTrace sp 11 ++ [.addr (addr sp 48),.addr (w64 sp)]

structure Prepared (s t : State)  : Prop extends Copies s t 11 where
  scratch : arg t 11 = work s
  ret : t.mem.readW (w64 (SP s)) 32 = 0

theorem zeroRet_run {u : State} (hw : InRegions u.wr (w64 (u.gpr .esp)) 4) :
    ∃ v, execBlock isa zeroRet u = some (v,[.addr (w64 (u.gpr .esp))]) ∧
      v.mem = u.mem.writeW (w64 (u.gpr .esp)) (0#32) ∧ v.rd=u.rd ∧ v.wr=u.wr ∧
      ∀ r, r≠.eax → v.gpr r=u.gpr r := by
  refine ⟨{ u.setReg .eax 0 with mem := u.mem.writeW (w64 (u.gpr .esp)) (0#32) }, ?_,
    rfl,rfl,rfl,fun r hr => by simp [State.setReg,hr]⟩
  simp [zeroRet, imm, at_, execBlock, isa, exec, readSrc, State.store32, ea_mk,
    addrs, srcAddrs, State.setReg, addr, w64] at *
  simp [hw]


theorem prepare_run {s : State} (h : Gather.Lay s) :
    ∃ t, execBlock isa frameArgs (allocated s) = some (t,frameTrace (SP s)) ∧ Prepared s t := by
  obtain ⟨u,run,hu⟩ := copies_run h 11 (by decide)
  have usp : u.gpr .esp=SP s := hu.regs _ (by decide)
  obtain ⟨w,tail,rd,wr,g,m⟩ := tail_run (n := 11) (w := u)
    (by rw [usp,hu.wr]; exact privateWrite _ (by decide) h)
  have wsp := (g .esp (by decide)).trans usp
  obtain ⟨t,zero,mem,rd',wr',g'⟩ := zeroRet_run (u := w) (by
    rw [wsp,wr,hu.wr]
    exact ⟨_,List.mem_cons_self ..,(by simp [Region.Contains,SP])⟩)
  rw [usp] at m tail
  rw [wsp] at mem zero
  have tsp := (g' .esp (by decide)).trans wsp
  have keep (j : Nat) (hj : j≤11) :
      t.mem.readW (addr (SP s) (4+4*j)) 32 = w.mem.readW (addr (SP s) (4+4*j)) 32 := by
    rw [mem,Mem.readW_writeW_sep]
    · rw [norm h (by omega_using [hj])]
      exact fun x hjx hbx => Offset.sep_base _ (n := 4) (e := 4+4*j) (k := 4) (by omega) (by omega) x hbx hjx
    · decide
  have wFrame : Frame [region s] s.mem w.mem := by
    rw [m,norm h (d := 4+4*11) (by decide)]
    exact hu.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine ⟨t,?_,⟨rd'.trans (rd.trans hu.rd),wr'.trans (wr.trans hu.wr),
    fun r hr => (g' r hr).trans ((g r hr).trans (hu.regs r hr)),?_,?_⟩,?_,?_⟩
  · unfold frameArgs frameTrace
    rw [execBlock_append,execBlock_append,run]
    simp only [Option.bind_some]
    change execBlock isa [.mov .eax (.reg .esp),.alu .add .eax (imm 52),.store (at_ .esp 48) .eax] u = some (w,[.addr (addr (SP s) 48)]) at tail
    rw [tail]
    simp [zero,List.append_assoc]
  · rw [mem]; exact wFrame.writeW (List.mem_singleton_self _) _ ((by simp [Region.Contains,SP]))
  · intro j hj
    rw [keep j (by omega),m,Mem.readW_writeW_sep,hu.slots _ hj]
    · rw [norm h (d := 4+4*j) (by omega),norm h (d := 4+4*11) (by decide)]
      exact Offset.sep _ (by omega) (by omega) (by decide)
    · decide
  · change t.mem.readW (addr (t.gpr .esp) (4+4*11)) 32 = _
    rw [tsp,keep 11 (by decide),m,Mem.readW_writeW_self32]
  · rw [mem,Mem.readW_writeW_self32]; rfl

end VG.Proof.AesGcm.X86.DirectGather
