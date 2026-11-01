module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Stack
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: compose descriptor recovery with the shared argument restores.
/-! # Preparing the split-seal register arguments -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather

structure RegisterArgs (s e t u : State) : Prop where
  regs : ∀ r∈[Reg.r3,.r4,.r5,.r6,.r7,.r8],u.gpr r=s.gpr r
  source : u.gpr .r9=e.mem.readW (Src s) 64
  length : u.gpr .r10=firstLen e
  base : u.gpr .r12=Pf s
  mem : u.mem=t.mem
  pres : ∀ r∈preserved,u.gpr r=s.gpr r
  sp : u.sp=Pf s
  rd : u.rd=s.rd
  wr : u.wr=FR s::s.wr


theorem registerArgs_ok {s e t : State} (h : Lay s) (he : Entered s e)
    (hcount : e.gpr .r10=s.gpr .r10) (hc : 0<Cnt s)
    (ht : TailResult e (Src s) (Dst s) (Cnt s) t) :
    WP isa (.block (Impl.AesGcm.PPC64LE.GatherSplit.firstArgs ++
        Impl.AesGcm.PPC64LE.SealGather.callArgs.take 6)) t (RegisterArgs s e t) := by
  have hg := gatherPre_of h he
  have hin {d : Nat} (hd : d+8≤Cnt s*16) :
      InRegions (t.rd++t.wr) (Src s+BitVec.ofNat 64 d) 8 := by
    rw [ht.keep.rd,ht.keep.wr]
    exact hg.dsr _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ hd (by have := hg.dw; omega)⟩
  have hread {d : Nat} (hd : d+8≤Cnt s*16) :
      t.mem.readW (Src s+BitVec.ofNat 64 d) 64=e.mem.readW (Src s+BitVec.ofNat 64 d) 64 := by
    exact (suffix_frame h he hc ht).readW
      (Offset.contains_base _ hd (by have := hg.dw; omega)) (fun r hr => by
        rw [List.mem_singleton] at hr
        subst r
        exact hg.dsd) (by decide)
  have hsrc : t.mem.readW (Src s) 64=e.mem.readW (Src s) 64 := by
    have hh := hread (d := 0) (by omega)
    simpa only [BitVec.add_zero] using hh
  have hlen : t.mem.readW (Src s+8#64) 64=firstLen e := by
    rw [hread (d := 8) (by omega)]
    rw [firstLen,he.r7]
    rfl
  refine WP.block_append (WP.mono (firstArgs_ok ht.next
    (by rw [ht.keep.gpr _ (by decide),hcount]; symm; exact BitVec.ofNat_toNat 64 (s.gpr .r10))
    (by simpa only [BitVec.add_zero] using hin (d := 0) (by omega))
    (hin (d := 8) (by omega))) fun a ha => ?_)
  subst a
  have ma : (firstArgsState t (Src s)).mem=t.mem := by
    simp only [firstArgsState,RegUpd.mem_write]
  have ba : (firstArgsState t (Src s)).gpr .r12=Pf s := by
    simp only [firstArgsState,RegUpd.gpr_write,reduceCtorEq,ite_false]
    exact (ht.keep.gpr _ (by decide)).trans he.r12
  have wa : (firstArgsState t (Src s)).wr=FR s::s.wr := by
    simp only [firstArgsState,RegUpd.wr_write]
    exact ht.keep.wr.trans he.wr
  refine WP.mono (restoreArgs_ok ba wa (by rw [ma]; exact suffix_slots h he hc ht)) fun u hu => ?_
  have gu {r : Reg} (hr : r∉restoreRegs.map Prod.fst) :
      u.gpr r=(firstArgsState t (Src s)).gpr r := hu.other r hr
  refine ⟨?_,?_,?_,?_,hu.mem.trans ma,?_,?_,?_,hu.wr.trans wa⟩
  · intro r hr
    exact hu.gpr_of (.inl hr)
  · rw [gu (by decide)]
    simp only [firstArgsState,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
    exact hsrc
  · rw [gu (by decide)]
    simp only [firstArgsState,RegUpd.gpr_write,ite_true]
    exact hlen
  · rw [gu (by decide)]
    exact ba
  · intro r hr
    have hp : ∀ r∈preserved,r∉restoreRegs.map Prod.fst ∧ r≠.r9 ∧ r≠.r10 ∧ r≠.r11 ∧
        r∉VG.Proof.Gather.PPC64LE.gatherRegs := by decide
    rw [gu (hp r hr).1]
    simp only [firstArgsState,RegUpd.gpr_write,(hp r hr).2.1,(hp r hr).2.2.1,
      (hp r hr).2.2.2.1,ite_false]
    exact (ht.keep.gpr r (hp r hr).2.2.2.2).trans (he.pres r hr)
  · rw [hu.sp]
    simp only [firstArgsState,RegUpd.sp_write]
    exact ht.keep.sp.trans he.sp
  · rw [hu.rd]
    simp only [firstArgsState,RegUpd.rd_write]
    exact ht.keep.rd.trans he.rd


theorem RegisterArgs.incoming {s e t u : State} (h : Lay s) (he : Entered s e)
    (hc : 0<Cnt s) (ht : TailResult e (Src s) (Dst s) (Cnt s) t)
    (hu : RegisterArgs s e t u) {j : Nat} (hj : j<3) :
    u.mem.readW (sa s j) 64=stackArg s j := by
  rw [hu.mem]
  have darg := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hr : (⟨sa s j,8⟩ : Region).Disjoint (dR s) := by
    apply darg.symm.sub_left
    rw [h.hargR]
    exact Offset.sub _ (by omega) (by omega)
  rw [(suffix_frame h he hc ht).readW (Region.contains_self _ _)
    (fun r hr' => by rw [List.mem_singleton] at hr'; subst r; exact hr) (by decide),he.mem,h.eArg hj]

structure Prepared (s e c : State) : Prop where
  regs : ∀ r∈[Reg.r3,.r4,.r5,.r6,.r7,.r8],c.gpr r=s.gpr r
  source : c.gpr .r9=e.mem.readW (Src s) 64
  length : c.gpr .r10=firstLen e
  args : ∀ j<3,c.mem.readW (Pf s+BitVec.ofNat 64 (96+8*j)) 64=stackArg s j
  input : Spec.Aes.bytesAt c.mem (e.mem.readW (Src s) 64) (firstLen e).toNat ++
    (Spec.Aes.bytesAt c.mem (Dst s) (L s)).drop (firstLen e).toNat=pt s (Cnt s)
  ra : c.mem.readW (slot s 6) 64=s.lr
  frame : Frame [dR s,⟨Pf s+96,24⟩] e.mem c.mem
  pres : ∀ r∈preserved,c.gpr r=s.gpr r
  sp : c.sp=Pf s
  rd : c.rd=s.rd
  wr : c.wr=FR s::s.wr


theorem prepare_ok {s e t : State} (h : Lay s) (he : Entered s e)
    (hcount : e.gpr .r10=s.gpr .r10) (hc : 0<Cnt s)
    (ht : TailResult e (Src s) (Dst s) (Cnt s) t) :
    WP isa (.block Impl.AesGcm.PPC64LE.GatherSplit.callArgs) t (Prepared s e) := by
  unfold Impl.AesGcm.PPC64LE.GatherSplit.callArgs
  refine WP.block_append (WP.mono (registerArgs_ok h he hcount hc ht) fun u hu => ?_)
  refine WP.mono (stackArgs_ok h hu.base hu.sp hu.rd hu.wr) fun c hc' => ?_
  subst c
  have fr : Frame [⟨Pf s+96,24⟩] u.mem (copiedState 160 u 3).mem := by
    have ff := stackArgs_frame u
    rw [hu.sp] at ff
    exact ff
  have g {r : Reg} (hr : r≠.r0) : (copiedState 160 u 3).gpr r=u.gpr r :=
    copiedState_gpr _ _ hr _
  refine ⟨?_,(g (by decide)).trans hu.source,(g (by decide)).trans hu.length,?_,stackArgs_plaintext h he hc ht hu.mem hu.sp,?_,?_,?_,
    (copiedState_sp _ _ _).trans hu.sp,(copiedState_rd _ _ _).trans hu.rd,
    (copiedState_wr _ _ _).trans hu.wr⟩
  · intro r hr
    have hp : ∀ r∈[Reg.r3,.r4,.r5,.r6,.r7,.r8],r≠.r0 := by decide
    exact (g (hp r hr)).trans (hu.regs r hr)
  · intro j hj
    have hv := stackArgs_values u hj
    rw [hu.sp] at hv
    exact hv.trans (hu.incoming h he hc ht hj)
  · rw [fr.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)) (by decide),hu.mem]
    exact (suffix_slots h he hc ht).ra
  · have f₁ : Frame [dR s,⟨Pf s+96,24⟩] e.mem u.mem := by
      rw [hu.mem]
      exact (suffix_frame h he hc ht).mono (fun r hr => by
        rw [List.mem_singleton] at hr
        subst r
        exact List.mem_cons_self)
    exact f₁.trans (fr.mono (fun r hr => List.mem_cons_of_mem _ hr))
  · intro r hr
    have hp : ∀ r∈preserved,r≠.r0 := by decide
    exact (g (hp r hr)).trans (hu.pres r hr)

end VG.Proof.AesGcm.PPC64LE.GatherSplit
