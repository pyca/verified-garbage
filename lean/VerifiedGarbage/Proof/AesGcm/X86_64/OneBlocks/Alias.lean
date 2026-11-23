module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Seal
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.TCB.X86_64.Residue
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Impl.AesGcm.X86_64

/-! # Passing an equal destination to the two-pointer seal block helper

The caller sets r10 to the source before calling the shared leaf. Its proof
can use the in-place contract for the leaf preceded by the same move. These
two executions have the same state and the same leakage trace. -/

@[expose] public section
namespace VG.Proof.AesGcm.X86_64.OneBlocks
open VG.X86_64

def aliasDst : Prog isa := .block [.mov .r10 (.reg .r8)]

def aliasState (s : State) : State := s.setReg .r10 (s.gpr .r8)

theorem alias_run (s : State) : execBlock isa [.mov .r10 (.reg .r8)] s=some (aliasState s,[]) := rfl

theorem alias_exec (s : State) : Exec isa aliasDst s [] (aliasState s) := .block (alias_run s)

theorem alias_exec_iff {s t : State} {tr : List Leak} : Exec isa aliasDst s tr t ↔ t=aliasState s ∧ tr=[] := by
  constructor
  · intro e; cases e with
    | block a => rw [alias_run] at a; cases a; exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩; exact alias_exec s

theorem alias_entry (s : State) : (aliasState s).callEntry=aliasState s.callEntry := by
  simp only [aliasState,State.callEntry,State.setReg,State.mk.injEq,reduceCtorEq,ite_false,
    and_true]
  funext r
  cases r <;> rfl

theorem alias_call {name : String} {body : Prog isa} {s t : State} {tr : List Leak} :
    Exec isa (.call name (.seq aliasDst body)) s tr t ↔
      Exec isa (.seq aliasDst (.call name body)) s tr t := by
  constructor
  · intro e
    cases e with
    | call hcall w ret =>
      cases w with
      | seq m b =>
        rw [call_callEntry] at hcall
        cases hcall
        obtain ⟨rfl,rfl⟩ := alias_exec_iff.mp m
        rw [← alias_entry] at b
        have c := Exec.call (name := name) (call_callEntry (aliasState s)) b ret
        have e := Exec.seq (alias_exec s) c
        simp only [List.nil_append] at e ⊢
        change Exec isa _ s (([s.gpr .rsp - 8].map Leak.addr ++ _) ++ _) _ at e
        exact e
  · intro e
    cases e with
    | seq m c =>
      cases c with
      | call hcall b ret =>
        obtain ⟨rfl,rfl⟩ := alias_exec_iff.mp m
        rw [call_callEntry] at hcall
        cases hcall
        rw [alias_entry] at b
        exact .call (call_callEntry _) (.seq (alias_exec _) b) ret

theorem callBlocks_iff (f : Impl.AesGcm.X86_64.Fn) {s t : State} {tr : List Leak} :
    Exec isa (.call f.name f.code) s tr t ↔ Exec isa f.callBlocks s tr t := by
  unfold Impl.AesGcm.X86_64.Fn.callBlocks
  split
  · rename_i body h
    rw [h]
    exact alias_call
  · exact Iff.rfl

theorem place_exec {c : Prog isa} {s t : State} {tr : List Leak} (target : String)
    (e : Exec isa c s tr t) : Exec isa (Impl.AesGcm.X86_64.placeSealArgs target c) s tr t := by
  induction e with
  | block h => exact .block h
  | seq _ _ a b => exact .seq a b
  | iteT x _ a => exact .iteT x a
  | iteF x _ a => exact .iteF x a
  | loopExit _ x a => exact .loopExit a x
  | loopNext _ x _ a b => exact .loopNext a x b
  | call h b r _ =>
    rw [Impl.AesGcm.X86_64.placeSealArgs]
    split
    · exact (callBlocks_iff _).mp (.call h b r)
    · exact .call h b r
  | frame i _ j b => exact .frame i b j
  | icall h c b r _ => exact .icall h c b r
  | icallNext h n b _ => exact .icallNext h n b

theorem place_verified {k : Contract isa} {bits : Nat} {p : Prog isa} (target : String)
    (h : VerifiedScrubbed VG.X86_64.target p k bits) :
    VerifiedScrubbed VG.X86_64.target (Impl.AesGcm.X86_64.placeSealArgs target p) k bits := by
  obtain ⟨⟨ok,ct,nonempty⟩,scrub⟩ := h
  have old {s t : State} {tr : List Leak} (pre : k.pre s)
      (e : Exec isa (Impl.AesGcm.X86_64.placeSealArgs target p) s tr t) : Exec isa p s tr t := by
    obtain ⟨tr',t',e',_,_⟩ := ok s pre
    obtain ⟨rfl,rfl⟩ := Exec.det e (place_exec target e')
    exact e'
  refine ⟨⟨?_,?_,nonempty⟩,?_⟩
  · intro s pre
    obtain ⟨tr,t,e,abi,post⟩ := ok s pre
    exact ⟨tr,t,place_exec target e,abi,post⟩
  · intro a b t u x y ha hb hp ea eb
    exact ct _ _ _ _ _ _ ha hb hp (old ha ea) (old hb eb)
  · change NoResidue _ k bits
    intro a b t u x y ha hb hp outside unknown ea eb
    exact scrub _ _ _ _ _ _ ha hb hp outside unknown (old ha ea) (old hb eb)

theorem place_all (target : String) (p : Prog isa) (test : Instr → Bool) :
    (Impl.AesGcm.X86_64.placeSealArgs target p).all test = p.all test := by
  induction p with
  | block => rfl
  | seq a b ha hb => simp only [Impl.AesGcm.X86_64.placeSealArgs,Code.all,ha,hb]
  | ite c a b ha hb => simp only [Impl.AesGcm.X86_64.placeSealArgs,Code.all,ha,hb]
  | loop b c h => exact h
  | call n b _ =>
    rw [Impl.AesGcm.X86_64.placeSealArgs]
    split
    · unfold Impl.AesGcm.X86_64.Fn.callBlocks
      split
      · rename_i body h; change b=_ at h; rw [h]; rfl
      · rfl
    · rfl
  | frame i b j h => simp only [Impl.AesGcm.X86_64.placeSealArgs,Code.all,h]
  | icall => rfl

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
