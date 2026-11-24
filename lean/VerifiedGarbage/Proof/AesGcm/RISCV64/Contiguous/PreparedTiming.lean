module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.HashInput
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Gcm.RISCV64.Prepared

/-! # Timing of a prepared GHASH call from a contiguous operation -/

public section
namespace VG.Proof.AesGcm.RISCV64
open VG VG.RISCV64 VG.Impl.Gcm.RISCV64.Prepared
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint)

theorem preparedSkip_rel {s t : State} : RelCT isa (Eq2 s t) (.block []) TT :=
  RelCT.mono (CT.skip (I:=fun _ => True)) (fun _ _ _ => ⟨trivial,trivial⟩) (fun _ _ _ => trivial)

theorem preparedInvocation_rel {s t : State} {H H' : Spec.Gcm.Block}
    (a : HashInput s H) (b : HashInput t H') (sp : s.sp=t.sp)
    (key : s.mem.readW (s.sp+BitVec.ofNat 64 16) 64=t.mem.readW (t.sp+BitVec.ofNat 64 16) 64)
    (regs : ∀ r∈[Reg.a1,.a2,.a3,.a4],s.gpr r=t.gpr r) :
    RelCT isa (Eq2 s t) preparedInvocation TT := by
  refine rel_seq (rel_taint [] sp (by simp) (by taint_decide)) (loadPrepared_wp a) (loadPrepared_wp b)
    fun x y ⟨a0,ax,_,sx,_,_⟩ ⟨b0,ay,_,sy,_,_⟩ => ?_
  refine rel_taint [.a0,.a1,.a2,.a3,.a4] (sx.trans (sp.trans sy.symm)) ?_ (by taint_decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · rw [a0,b0,key]
  all_goals rw [ax _ (by decide) (by decide), ay _ (by decide) (by decide)]; apply regs; simp

/-- The hash source and public key-table pointer remain pinned while setting up the call. -/
theorem preparedOne_rel {K bk c st w sp P : Addr} {rs : List Region} {s t : State}
    {yo o : Nat} {b : Reg} (y : yo=0 ∨ yo=16) (bo : (b=.s1 ∧ o=32) ∨ (b=.s0 ∧ o=96))
    (g : GhIn c st w sp b o P s) (j : GhIn c st w sp b o P t)
    (a : HashScope K bk rs s) (z : HashScope K bk rs t) :
    RelCT isa (Eq2 s t) (VG.Impl.AesGcm.RISCV64.ghash1With preparedInvocation yo b o) TT := by
  obtain ⟨⟨V,vc,vs,vw,ve⟩,vp,_⟩ := g
  obtain ⟨⟨W,wc,ws,ww,we⟩,wp,_⟩ := j
  have hb : b=.s1 ∨ b=.s0 := by rcases bo with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp
  have ho : o<2048 := by rcases bo with ⟨_,rfl⟩|⟨_,rfl⟩ <;> decide
  refine rel_seq ?_ (ghArgs_ok y ve b o hb ho vp) (ghArgs_ok y we b o hb ho wp)
    fun x v ⟨_,ay,ad,an,ascr,_,ak⟩ ⟨_,zy,zd,zn,zscr,_,zk⟩ => ?_
  · have pin := fun r (hr : r∈[Reg.s2,.s1,.s0]) =>
      EnvC.pin ⟨V,vc,vs,vw,ve⟩ ⟨W,wc,ws,ww,we⟩ (by simpa using hr)
    rcases y with rfl|rfl <;> rcases bo with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      exact rel_taint [.s2,.s1,.s0] (ve.sp.trans we.sp.symm) pin (by taint_decide)
  · have ix := (a.kept ak).now
    have iv := (z.kept zk).now
    refine preparedInvocation_rel ix.1 iv.1 (ak.sp.trans (ve.sp.trans (we.sp.symm.trans zk.sp.symm)))
      (ix.2.trans iv.2.symm) ?_
    intro r h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · rw [ay,zy,vs,ws]
    · exact ad.trans zd.symm
    · exact an.trans zn.symm
    · rw [ascr,zscr,vw,ww]

private theorem wholeCallArgs {s : State} {yo : Nat} (hyo : yo=0 ∨ yo=16) :
    WP isa (.block [.addi .a0 .s2 240, .addi .a1 .s1 yo, .addi .a4 .s0 VG.Impl.AesGcm.RISCV64.scrO]) s
      fun u => u.gpr .a1=s.gpr .s1+BitVec.ofNat 64 yo ∧ u.gpr .a4=s.gpr .s0+BitVec.ofNat 64 512 ∧
        u.gpr .a2=s.gpr .a2 ∧ u.gpr .a3=s.gpr .a3 ∧ Keeps s u := by
  have ho : yo<2048 := by omega_using [hyo]
  refine Steps.wp_addi (by decide) fun x hx => Steps.wp_addi ho fun v hv =>
    Steps.wp_addi (imm:=VG.Impl.AesGcm.RISCV64.scrO) (by decide) fun u hu => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,⟨?_,?_,?_,?_⟩⟩
  · rw [hu.other _ (by decide),hv.gpr,hx.other _ (by decide)]
  · rw [hu.gpr,hv.other _ (by decide),hx.other _ (by decide)];rfl
  · rw [hu.other _ (by decide),hv.other _ (by decide),hx.other _ (by decide)]
  · rw [hu.other _ (by decide),hv.other _ (by decide),hx.other _ (by decide)]
  · rw [hu.mem,hv.mem,hx.mem]
  · rw [hu.rd,hv.rd,hx.rd]
  · rw [hu.wr,hv.wr,hx.wr]
  · rw [hu.sp,hv.sp,hx.sp]

theorem preparedWhole_rel {K bk c st w sp D : Addr} {rs : List Region} {s t : State}
    {yo n q j : Nat} (y : yo=0 ∨ yo=16)
    (l : MidI c st w sp yo D n q j s) (r : MidI c st w sp yo D n q j t)
    (a : HashScope K bk rs s) (b : HashScope K bk rs t) :
    RelCT isa (Eq2 s t) (VG.Impl.AesGcm.RISCV64.absorbWholeWith preparedInvocation yo) TT := by
  obtain ⟨V,_,_,_,vc,vs,vw,_,v⟩ := l
  obtain ⟨W,_,_,_,wc,ws,ww,_,h⟩ := r
  have spEq := v.env.sp.trans h.env.sp.symm
  refine rel_seq (rel_taint [.s4,.s5] spEq ?_ (by taint_decide))
    (split_ok v.le v.data.lt v.s4 v.s5) (split_ok h.le h.data.lt h.s4 h.s5)
    fun x z ⟨xd,xn,_,_,xr,xk⟩ ⟨zd,zn,_,_,zr,zk⟩ => ?_
  · intro reg hr
    rcases List.mem_cons.mp hr with rfl|hp
    · rw [v.s4,h.s4]
    · obtain rfl := List.mem_singleton.mp hp; rw [v.s5,h.s5]
  · have sx := xk.sp.trans (spEq.trans zk.sp.symm)
    have nb : (n-j)/16<2^64 := by omega_using [v.data.lt]
    refine VG.Proof.Gather.RISCV64.rel_ite (eval_zero xn nb) (eval_zero zn nb)
      (fun _ => preparedSkip_rel) fun _ => ?_
    have pins : ∀ k∈[Reg.s2,.s1,.s0],x.gpr k=z.gpr k := by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl
      all_goals rw [xr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
                    zr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      · rw [v.env.s2,h.env.s2,vc,wc]
      · rw [v.env.s1,h.env.s1,vs,ws]
      · rw [v.env.s0,h.env.s0,vw,ww]
    refine rel_seq (c₁ := .block [.addi .a0 .s2 240,.addi .a1 .s1 yo,.addi .a4 .s0 VG.Impl.AesGcm.RISCV64.scrO])
      (by rcases y with rfl|rfl <;> exact rel_taint [.s2,.s1,.s0] sx pins (by taint_decide))
      (wholeCallArgs y) (wholeCallArgs y) fun u w ⟨uy,us,ud,un,uk⟩ ⟨wy,wsc,wd,wn,wk⟩ => ?_
    have au := ((a.kept xk).kept uk).now
    have bw := ((b.kept zk).kept wk).now
    refine preparedInvocation_rel au.1 bw.1 (uk.sp.trans (sx.trans wk.sp.symm)) (au.2.trans bw.2.symm) ?_
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl
    · rw [uy,wy,pins .s1 (by simp)]
    · rw [ud,wd,xd,zd]
    · rw [un,wn,xn,zn]
    · rw [us,wsc,pins .s0 (by simp)]

end VG.Proof.AesGcm.RISCV64
