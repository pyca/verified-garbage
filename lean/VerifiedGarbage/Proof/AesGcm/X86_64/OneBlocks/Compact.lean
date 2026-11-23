module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Seal
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Alias
import VerifiedGarbage.Proof.Framework.Covers

/-! # Adapting the compact two-pointer block leaf to in-place seal -/

@[expose] public section
namespace VG.Proof.AesGcm.X86_64.OneBlocks
open VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open BlocksTo

def aliasReadState (M : CtxMode) (s : State) : State :=
  (aliasState s).withRegions [kR M s,srcR s,aR s true] s.wr

theorem aliasReads (M : CtxMode) (s : State) (h : Proof.AesGcm.blocksPreM M s) :
    Covers ((aliasReadState M s).rd++(aliasReadState M s).wr) (s.rd++s.wr) := by
  obtain ⟨rd,wr,_⟩ := h
  apply Covers.of_mem
  simp only [aliasReadState, State.withRegions_rd,State.withRegions_wr,List.mem_append]
  rw [rd,wr]
  intro r hr
  rcases hr with h | h
  · rcases List.mem_cons.mp h with e | h
    · left; exact List.mem_cons.mpr (Or.inl e)
    · rcases List.mem_cons.mp h with e | h
      · right; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl e)))))
      · left; exact List.mem_cons.mpr (.inr h)
  · right; exact h

theorem alias_pre (M : CtxMode) (s : State) (h : Proof.AesGcm.blocksPreM M s)
    : BT M (aliasReadState M s) true true := by
  obtain ⟨rd,wr,kc,ky,kd,ks,cy,cd,cs,ca,yd,ys,ya,ds,da,sa,tc,ty,td,ts,bk,bc,by',bd,bs,
    wk,wc,wy,wd,ws,wsp,rounds,ok⟩ := h
  exact ⟨rfl,wr,trivial,kc,ky,kd,ks,cy,cd,cd,cs,ca,yd,yd,ys,ya,Or.inl rfl,ds,ds,da,sa,
    tc,ty,td,ts,bk,bc,by',bd,bd,bs,wk,wc,wy,wd,wd,ws,trivial,wsp,rounds,ok⟩

/-- The leaf reads the plaintext through its source register. When both
buffers coincide its read permission follows from the writable data region. -/
theorem alias_ok {M : CtxMode} {f : Impl.AesGcm.X86_64.Fn}
    (ok : ∀ u, BT M u true true → ∃ tr t, Exec isa f.code u tr t ∧
      abiPreserved u t ∧ Proof.AesGcm.blocksPostAt (Dst u true) u t)
    (s : State) (pre : Proof.AesGcm.blocksPreM M s) :
    ∃ tr t, Exec isa f.withSameDst.code s tr t ∧ abiPreserved s t ∧
      Proof.AesGcm.encryptBlocksX86_64.post s t := by
  obtain ⟨trace,t,body,habi,post⟩ := ok _ (alias_pre M s pre)
  have run := Exec.widen (rd := s.rd) (wr := s.wr) body (aliasReads M s pre) (Covers.refl _)
  have back : (aliasReadState M s).withRegions s.rd s.wr=aliasState s := rfl
  rw [back] at run
  refine ⟨_,_,Exec.seq (alias_exec s) run,⟨?_,habi.2⟩,post⟩
  intro r hr
  have keep : ∀ r ∈ calleeSaved, r ≠ .r10 := by decide
  simpa only [aliasReadState,aliasState,State.withRegions_gpr,State.setReg,
    keep r hr,ite_false] using habi.1 r hr

/-- Recover the trace from the narrower read list. Widening permissions
changes neither the instructions nor their addresses. -/
theorem alias_trace {M : CtxMode} {f : Impl.AesGcm.X86_64.Fn}
    (ok : ∀ u, BT M u true true → ∃ tr t, Exec isa f.code u tr t)
    {s t : State} {tr : List Leak} (pre : Proof.AesGcm.blocksPreM M s)
    (run : Exec isa f.withSameDst.code s tr t) : ∃ u, Exec isa f.code (aliasReadState M s) tr u := by
  obtain ⟨tr',u,e⟩ := ok _ (alias_pre M s pre)
  have e' := Exec.widen (rd := s.rd) (wr := s.wr) e (aliasReads M s pre) (Covers.refl _)
  have back : (aliasReadState M s).withRegions s.rd s.wr=aliasState s := rfl
  rw [back] at e'
  have eq := (Exec.det run (Exec.seq (alias_exec s) e')).1
  rw [List.nil_append] at eq
  exact ⟨u,eq ▸ e⟩

theorem alias_pub (M : CtxMode) {a b : State} (p : Proof.AesGcm.blocksPub a b) :
    Pub (aliasReadState M a) (aliasReadState M b) true := by
  obtain ⟨k,r,c,y,src,n,sp,sc⟩ := p
  exact ⟨k.symm,r.symm,c.symm,y.symm,src.symm,n.symm,sp.symm,src.symm,sc.symm⟩

def withAlias {M : CtxMode} (B : BlkFn M) (leaf : SealFn M) : BlkFn M := { B with
  enc := leaf.fn.withSameDst
  encOk := alias_ok (f := leaf.fn) (fun u h => by
    obtain ⟨tr,t,e,save,post⟩ := leaf.wp u h
    exact ⟨tr,t,e,abiPreserved_of_exec leaf.mx e save,post⟩)
  encCt := by
    intro a b t u x y ha hb hp ea eb
    have run (z : State) (hz : BT M z true true) : ∃ tr t, Exec isa leaf.fn.code z tr t := by
      obtain ⟨tr,t,e,_⟩ := leaf.wp z hz
      exact ⟨tr,t,e⟩
    obtain ⟨x',ea'⟩ := alias_trace run ha ea
    obtain ⟨y',eb'⟩ := alias_trace run hb eb
    exact leaf.ct _ _ _ _ _ _ (alias_pre M a ha) (alias_pre M b hb) (alias_pub M hp) ea' eb'
  encNosp := by
    intro i hi
    change i ∈ [.mov .r10 (.reg .r8)] ++ instrs leaf.fn.code at hi
    rcases List.mem_append.mp hi with x | x
    · obtain rfl := List.mem_singleton.mp x; rfl
    · exact leaf.noSp i x
  encDepth := by simp only [Impl.AesGcm.X86_64.Fn.withSameDst,Code.depth,Nat.zero_max,leaf.depth]
  encMx := by
    change (true && leaf.fn.code.allInstrs (fun i => !loadsMxcsr i))=true
    exact leaf.mx
  encSp := by
    change (true && leaf.fn.code.all (fun i => !isa.writesSp i))=true
    exact leaf.spAll
  encXd := by simpa only [Impl.AesGcm.X86_64.Fn.withSameDst,Code.x86_64Depth,Nat.zero_max] using leaf.xd }

end VG.Proof.AesGcm.X86_64.OneBlocks
