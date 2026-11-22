module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! The ordinary gather arguments passed into the general out-of-place path.
Only the pointers in the calling convention are copied into the local frame. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.StackScratch.AArch64

abbrev genBase (s : State) (wn : Nat) := s.sp - BitVec.ofNat 64 (wn+32)
abbrev genStack (s : State) (wn : Nat) : Region := ⟨genBase s wn,wn+32⟩
abbrev genWork (s : State) (wn : Nat) := genBase s wn + 32

/-- The entry of the unframed, general gather implementation. The
original gather layout remains the authority for all external buffers. -/
structure GeneralEntry (o s : State) (wn : Nat) : Prop where
  lay : Gather.Lay .plain o
  bound : wn ≤ 2560
  frame : Frame [⟨genBase o wn,32⟩] o.mem s.mem
  regs : ∀ r, r ≠ .x16 → r ≠ .x17 → s.gpr r = o.gpr r
  sp : s.sp = genBase o wn
  rd : s.rd = o.rd
  wr : s.wr = genStack o wn :: o.wr
  args : ∀ i < 3, s.mem.readW (s.sp+BitVec.ofNat 64 (8*i)) 64 = stackArg o i
  work : s.mem.readW (s.sp+24) 64 = genWork o wn

theorem genStack_sub (o : State) {wn : Nat} (hb : wn ≤ 2560) : (genStack o wn).Sub (stkR o) :=
  Offset.sub_below _ (by omega) (by omega)

theorem genArgAddr (o : State) (wn i : Nat) :
    genBase o wn + BitVec.ofNat 64 ((wn+32)+8*i) = stackArgAddr o i := by
  unfold genBase stackArgAddr
  rw [← Offset.add_add,BitVec.sub_add_cancel]

theorem generalEntry_run (o : State) (l : Gather.Lay .plain o) {wn : Nat} (hb : wn ≤ 2560)
    (align : wn % 16 = 0) :
    let a := allocated (wn+32) o
    execBlock isa (setArgs (wn+32) 3) a =
      some (setArgsState (wn+32) 3 a,setArgsTrace (wn+32) a.sp 3) ∧
      GeneralEntry o (setArgsState (wn+32) 3 a) wn := by
  let a := allocated (wn+32) o
  have hr (i : Nat) (hi : i < 3) : InRegions (a.rd ++ a.wr) (a.sp+BitVec.ofNat 64 ((wn+32)+8*i)) 8 := by
    change InRegions (o.rd ++ a.wr) (genBase o wn + BitVec.ofNat 64 ((wn+32)+8*i)) 8
    rw [genArgAddr,l.hA]; exact l.inArg _ (by omega) (by omega) _
  have hw (i : Nat) (hi : i ≤ 3) : InRegions a.wr (a.sp+BitVec.ofNat 64 (8*i)) 8 :=
    ⟨_,List.mem_cons_self ..,Offset.contains_base _ (by change 8*i+8 ≤ wn+32; omega) (by omega)⟩
  obtain ⟨run,frame,args,work⟩ := setArgs_run (bytes := wn+32) (m := 3) (u := a)
    (by omega) (by omega) (by change 32 ≤ wn+32; omega) hr hw
  refine ⟨run,l,hb,frame,fun r h j => setArgsState_gpr _ _ _ h j,setArgsState_sp ..,
    setArgsState_rd ..,setArgsState_wr ..,?_,?_⟩
  · intro i hi
    rw [setArgsState_sp,args i hi]
    change o.mem.readW (genBase o wn + BitVec.ofNat 64 ((wn+32)+8*i)) 64 = _
    rw [genArgAddr]; rfl
  · rw [setArgsState_sp]; exact work

theorem generalFramed_wp (o : State) (l : Gather.Lay .plain o) {wn : Nat} (hb : wn ≤ 2560)
    (align : wn % 16 = 0) (body : Prog isa)
    (proved : ∀ s, GeneralEntry o s wn → WP isa body s fun t => gatherPost o t ∧ GprAbi s t) :
    WP isa (withStackArgScratch (wn+32) 3 body) o fun t => gatherPost o t ∧ GprAbi o t := by
  let a := allocated (wn+32) o
  obtain ⟨run,entry⟩ := generalEntry_run o l hb align
  refine AArch64.WP.alloc ⟨by omega,by omega,by omega⟩ (by have := l.w₁; omega)
    (WP.seq ⟨_,_,Exec.block run,?_⟩)
  refine (proved _ entry).mono ?_
  intro t ⟨post,g,sp⟩ m u fr
  have p : ∀ r ∈ preserved, r ≠ .x16 ∧ r ≠ .x17 := by decide
  have ds := l.bd.sub_left (genStack_sub o hb)
  have ts := l.bt.sub_left (genStack_sub o hb)
  refine ⟨?_,fun r hr => (g r hr).trans (entry.regs r (p r hr).1 (p r hr).2),?_⟩
  · unfold gatherPost at post ⊢
    simpa only [freed,bytesAt_frame fr (p := Dst o) (n := L o) (by
      simpa only [List.mem_singleton,forall_eq] using ds.symm) (Nat.le_of_lt (stackArg o 1).isLt),
      bytesAt_frame fr (p := Tg o) (n := 16) (by
      simpa only [List.mem_singleton,forall_eq] using ts.symm) (by decide)] using post
  · change t.sp + BitVec.ofNat 64 (wn+32) = o.sp
    rw [sp,entry.sp,genBase,BitVec.sub_add_cancel]


theorem generalFramed_rel {a b : State} (la : Gather.Lay .plain a) (lb : Gather.Lay .plain b)
    (pub : gatherPub a b) {wn : Nat} (hb : wn ≤ 2560) (align : wn % 16 = 0) (body : Prog isa)
    (run : ∀ u v, GeneralEntry a u wn → GeneralEntry b v wn → u.dit = v.dit →
      RelCT isa (Eq2 u v) body TT) :
    RelCT isa (Eq2 a b) (withStackArgScratch (wn+32) 3 body) TT := by
  have sp := pub.2.2.2.2.2.2.2.2.1
  have dit := pub.2.2.2.2.2.2.2.2.2.1
  obtain ⟨xa,ea⟩ := generalEntry_run a la hb align
  obtain ⟨xb,eb⟩ := generalEntry_run b lb hb align
  let u := setArgsState (wn+32) 3 (allocated (wn+32) a)
  let v := setArgsState (wn+32) 3 (allocated (wn+32) b)
  have eq : u.dit = v.dit := dit
  apply RelCT.alloc (P := Eq2 a b) (R := TT)
  apply RelCT.seq (R := Eq2 u v)
  · rintro x y tx ty x' y' ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩ ex ey
    obtain ⟨rfl,rfl⟩ := Exec.det ex (Exec.block xa)
    obtain ⟨rfl,rfl⟩ := Exec.det ey (Exec.block xb)
    exact ⟨by simp only [allocated,sp],rfl,rfl⟩
  · exact run u v ea eb eq

end VG.Proof.AesGcm.AArch64.DirectGather
