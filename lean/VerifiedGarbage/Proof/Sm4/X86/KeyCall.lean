module

public import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
import VerifiedGarbage.Proof.Sm4.X86.Lit
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Scrub
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
meta import VerifiedGarbage.Spec.Sm4.Contract
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
meta import VerifiedGarbage.Proof.Sm4.X86.Lit
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/-! # The shared x86 SM4 key schedule within its existing stack budget

The call's return address occupies the old unused word. Its three arguments
and scratch buffer keep their previous addresses, so the raw schedule's
correctness proof applies without changing its contract. The frame and call
use at most 1448 bytes. The setup and wipe have traces determined by the
stack pointer; the call reuses the raw schedule's constant-time proof.
-/

namespace VG.Proof.Sm4.X86.KeyCall

open VG VG.X86
structure FramePre (s : State) : Prop where
  sp : 1448 ≤ (s.gpr .esp).toNat
  fitSp : (s.gpr .esp).toNat + 12 ≤ 2^32
  rd : s.rd = [⟨(arg s 0).setWidth 64,16⟩,⟨argAddr s 0,8⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64,128⟩]
  retSchedule : Region.Disjoint ⟨(s.gpr .esp).setWidth 64,4⟩ ⟨(arg s 1).setWidth 64,128⟩
  frameKey : (below (s.gpr .esp) 1448).Disjoint ⟨(arg s 0).setWidth 64,16⟩
  frameSchedule : (below (s.gpr .esp) 1448).Disjoint ⟨(arg s 1).setWidth 64,128⟩

theorem framePre_of {s : State} (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s) : FramePre s := by
  sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, abi, argVal,
    argBytes, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceDiv, List.sum_cons, List.sum_nil,
    Nat.reduceAdd, Nat.reduceMul] at hs
  obtain ⟨h1,h2,h3,h4,_,_,_,h8,_,h10,h11,_,_,_⟩ := hs
  have hb : below (s.gpr .esp) 1448 = ⟨(s.gpr .esp).setWidth 64 - 1448#64,1448⟩ :=
    congrArg (fun a : Addr => (⟨a,1448⟩ : Region))
      (Taint.sub_setWidth (e := s.gpr .esp) (m := 1448) h1)
  refine ⟨h1,?_,h3,h4,h8,?_,?_⟩
  · omega_using [h2]
  · rw [hb]; exact h10
  · rw [hb]; exact h11


open VG.Impl.StackScratch.X86

def copyArg0 (bytes j : Nat) : List Instr :=
  [.mov .eax (.mem ⟨.esp,bytes + 4*j⟩), .store ⟨.esp,4*j⟩ .eax]

def copyState0 (bytes j : Nat) (u : State) : State :=
  {u.setReg .eax (u.mem.readW (addr (u.gpr .esp) (bytes + 4*j)) 32) with
   mem := u.mem.writeW (addr (u.gpr .esp) (4*j))
     (u.mem.readW (addr (u.gpr .esp) (bytes + 4*j)) 32)}

theorem copyArg0_run {bytes j : Nat} {u : State}
    (hr : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes+4*j)) 4)
    (hw : InRegions u.wr (addr (u.gpr .esp) (4*j)) 4) :
    execBlock isa (copyArg0 bytes j) u = some (copyState0 bytes j u,
      [.addr (addr (u.gpr .esp) (bytes+4*j)), .addr (addr (u.gpr .esp) (4*j))]) := by
  have hesp : (u.setReg .eax (u.mem.readW (addr (u.gpr .esp) (bytes+4*j)) 32)).gpr .esp =
      u.gpr .esp := RegUpd.gpr_setReg_of_ne u _ (by decide)
  simp only [copyArg0,execBlock,isa,exec,readSrc,State.load32,ea_mk,hr,ite_true,
    Option.map_some,addrs,srcAddrs,State.store32,hesp]
  simp only [RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg_self,hw,ite_true,Option.map_some,List.append_nil,copyState0]
  rfl

@[simp] theorem copyState0_esp (bytes j : Nat) (u : State) :
    (copyState0 bytes j u).gpr .esp = u.gpr .esp :=
  RegUpd.gpr_setReg_of_ne u (r := .eax) (r' := .esp) (u.mem.readW (addr (u.gpr .esp) (bytes + 4*j)) 32) (by decide)
@[simp] theorem copyState0_rd (bytes j : Nat) (u : State) : (copyState0 bytes j u).rd = u.rd := rfl
@[simp] theorem copyState0_wr (bytes j : Nat) (u : State) : (copyState0 bytes j u).wr = u.wr := rfl
theorem copyState0_gpr (bytes j : Nat) (u : State) {r : Reg} (hr : r ≠ .eax) :
    (copyState0 bytes j u).gpr r = u.gpr r := RegUpd.gpr_setReg_of_ne u _ hr

def setupTrace (bytes : Nat) (E : BitVec 32) : List Leak :=
  [.addr (addr E bytes),.addr (addr E 0)] ++
  [.addr (addr E (bytes+4)),.addr (addr E 4)] ++ [.addr (addr E 8)]

def setupArgs (bytes : Nat) : List Instr :=
  copyArg0 bytes 0 ++ copyArg0 bytes 1 ++
    [.mov .eax (.reg .esp),.alu .add .eax (.imm 12),.store ⟨.esp,8⟩ .eax]

theorem setupArgs_run {bytes : Nat} {u : State}
    (hfit : (u.gpr .esp).toNat + bytes + 8 ≤ 2^32) (hb : 12 ≤ bytes)
    (hr : ∀ j < 2, InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes+4*j)) 4)
    (hw : ∀ j ≤ 2, InRegions u.wr (addr (u.gpr .esp) (4*j)) 4) :
    ∃ w t, execBlock isa (setupArgs bytes) u = some (w,t) ∧
      w.rd = u.rd ∧ w.wr = u.wr ∧
      (∀ r, r ≠ .eax → w.gpr r = u.gpr r) ∧
      Frame [⟨(u.gpr .esp).setWidth 64,12⟩] u.mem w.mem ∧
      (∀ j < 2, w.mem.readW (addr (u.gpr .esp) (4*j)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes+4*j)) 32) ∧
      w.mem.readW (addr (u.gpr .esp) 8) 32 = u.gpr .esp + 12#32 ∧
      t = setupTrace bytes (u.gpr .esp) := by
  let u0 := copyState0 bytes 0 u
  let u1 := copyState0 bytes 1 u0
  have e0 := copyArg0_run (bytes := bytes) (j := 0) (u := u) (hr 0 (by decide)) (hw 0 (by decide))
  have e1 := copyArg0_run (bytes := bytes) (j := 1) (u := u0)
    (by simpa only [u0,copyState0_rd,copyState0_wr,copyState0_esp] using hr 1 (by decide))
    (by simpa only [u0,copyState0_wr,copyState0_esp] using hw 1 (by decide))
  obtain ⟨w,ew,rw,ww,gw,mw⟩ := tail_run (n := 1) (w := u1)
    (by simpa only [u1,u0,copyState0_wr,copyState0_esp] using hw 2 (by decide))
  have sp0 : u0.gpr .esp = u.gpr .esp := copyState0_esp _ _ _
  have sp1 : u1.gpr .esp = u.gpr .esp := (copyState0_esp _ _ _).trans sp0
  change execBlock isa [.mov .eax (.reg .esp),.alu .add .eax (.imm 12),.store ⟨.esp,8⟩ .eax] u1 =
    some (w,[.addr (addr (u1.gpr .esp) 8)]) at ew
  change w.mem = u1.mem.writeW (addr (u1.gpr .esp) 8) (u1.gpr .esp + 12) at mw
  change execBlock isa (copyArg0 bytes 0) u = some (u0,
    [.addr (addr (u.gpr .esp) bytes),.addr (addr (u.gpr .esp) 0)]) at e0
  change execBlock isa (copyArg0 bytes 1) u0 = some (u1,
    [.addr (addr (u0.gpr .esp) (bytes+4)),.addr (addr (u0.gpr .esp) 4)]) at e1
  have e : execBlock isa (setupArgs bytes) u = some (w,
      [.addr (addr (u.gpr .esp) bytes),.addr (addr (u.gpr .esp) 0)] ++
      [.addr (addr (u.gpr .esp) (bytes+4)),.addr (addr (u.gpr .esp) 4)] ++
      [.addr (addr (u.gpr .esp) 8)]) := by
    rw [setupArgs,execBlock_append,execBlock_append,e0]
    simp only [Option.bind_some]
    rw [e1]
    simp only [Option.map_some,Option.bind_some]
    rw [ew]
    simp only [Option.map_some,sp0,sp1]

  have hA (d : Nat) (hd : d ≤ bytes+4) : addr (u.gpr .esp) d =
      (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := addr_eq (by omega_using [hfit,hd])
  have sep (d k : Nat) (hh : d+4 ≤ k ∨ k+4 ≤ d) (hd : d ≤ bytes+4) (hk : k ≤ bytes+4) :
      Mem.Sep (addr (u.gpr .esp) d) 4 (addr (u.gpr .esp) k) 4 := by
    rw [hA d hd,hA k hk]
    exact VG.Offset.sep _ hh (by omega_using [hfit,hd]) (by omega_using [hfit,hk])
  have m0 : u0.mem = u.mem.writeW (addr (u.gpr .esp) 0)
      (u.mem.readW (addr (u.gpr .esp) bytes) 32) := rfl
  have s1 : u0.mem.readW (addr (u.gpr .esp) (bytes+4)) 32 =
      u.mem.readW (addr (u.gpr .esp) (bytes+4)) 32 := by
    rw [m0,Mem.readW_writeW_sep (sep (bytes+4) 0 (Or.inr (by omega_using [hb])) (by omega_using []) (by omega_using [hb])) (by decide)]
  have m1 : u1.mem = u0.mem.writeW (addr (u.gpr .esp) 4)
      (u.mem.readW (addr (u.gpr .esp) (bytes+4)) 32) := by
    have hm : u1.mem = u0.mem.writeW (addr (u0.gpr .esp) 4)
      (u0.mem.readW (addr (u0.gpr .esp) (bytes+4)) 32) := rfl
    rw [hm,sp0,s1]
  refine ⟨w,_,e,rw.trans ((copyState0_rd bytes 1 u0).trans (copyState0_rd bytes 0 u)),
    ww.trans ((copyState0_wr bytes 1 u0).trans (copyState0_wr bytes 0 u)),fun r hr => ?_,?_,?_,?_,rfl⟩
  · rw [gw r hr,copyState0_gpr _ _ _ hr,copyState0_gpr _ _ _ hr]
  · have c (d : Nat) (hd : d+4 ≤ 12) :
        (⟨(u.gpr .esp).setWidth 64,12⟩ : Region).Contains (addr (u.gpr .esp) d) 4 := by
      rw [hA d (by omega_using [hb,hd])]
      exact VG.Offset.contains_base _ hd (by omega_using [hfit,hd])
    rw [mw,sp1]
    have f0 : Frame [⟨(u.gpr .esp).setWidth 64,12⟩] u.mem u0.mem := by
      rw [m0]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))
    have f1 : Frame [⟨(u.gpr .esp).setWidth 64,12⟩] u0.mem u1.mem := by
      rw [m1]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 4 (by decide))
    exact (f0.trans f1).writeW (List.mem_singleton_self _) _ (c 8 (by decide))
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega_using [hj]
    rcases hj' with rfl | rfl
    · rw [mw,sp1]
      simp only [Nat.mul_zero,Nat.add_zero]
      rw [Mem.readW_writeW_sep (sep 0 8 (Or.inl (by decide)) (by omega_using [hb]) (by omega_using [hb])) (by decide),m1,
        Mem.readW_writeW_sep (sep 0 4 (Or.inl (by decide)) (by omega_using [hb]) (by omega_using [hb])) (by decide),m0,Mem.readW_writeW_self32]
    · rw [mw,sp1]
      simp only [Nat.mul_one]
      rw [Mem.readW_writeW_sep (sep 4 8 (Or.inl (by decide)) (by omega_using [hb]) (by omega_using [hb])) (by decide),m1,Mem.readW_writeW_self32]
  · rw [mw,sp1,Mem.readW_writeW_self32]
    rfl


theorem scratch_pre_congr {s t : State}
    (hs : (Proof.Sm4.expandKeyScratchContract abi 179).pre s)
    (he : t.gpr .esp = s.gpr .esp) (ha : ∀ j < 3, arg t j = arg s j)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    (Proof.Sm4.expandKeyScratchContract abi 179).pre t := by
  sig_pre [Proof.Sm4.expandKeyScratchContract,Proof.Sm4.expandKeyScratchSig,
    Spec.Sm4.expandKeySig,abi,argVal,argBytes,↓reduceIte,Nat.reduceEqDiff,
    Nat.reduceDiv,List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul] at hs ⊢
  have h0 := ha 0 (by decide)
  have h1 := ha 1 (by decide)
  have h2 := ha 2 (by decide)
  rw [he,hr,hw,h0,h1,h2,show argAddr t 0 = argAddr s 0 by rw [argAddr,he]; rfl]
  exact hs


theorem frame_setup_run {s : State} (hs : FramePre s) :
    let u := allocFrame 1444 s
    ∃ w t, execBlock isa (setupArgs 1448) u = some (w,t) ∧
      w.rd = s.rd ∧ w.wr = u.wr ∧
      (∀ r, r ≠ .eax → w.gpr r = u.gpr r) ∧
      Frame [⟨(u.gpr .esp).setWidth 64,12⟩] s.mem w.mem ∧
      (∀ j < 2, arg w.callEntry j = arg s j) ∧
      arg w.callEntry 2 = u.gpr .esp + 12#32 ∧ t = setupTrace 1448 (u.gpr .esp) := by
  intro u
  have hE : (u.gpr .esp).toNat = (s.gpr .esp).toNat - 1444 :=
    sub_toNat (by omega_using [hs.sp])
  have hfit : (u.gpr .esp).toNat + 1448 + 8 ≤ 2^32 := by
    rw [hE]
    omega_using [hs.sp,hs.fitSp]
  have hsrc (j : Nat) : addr (u.gpr .esp) (1448+4*j) = argAddr s j := by
    rw [allocFrame_esp,addr,argAddr]
    apply congrArg (BitVec.setWidth 64)
    rw [show 1448+4*j = 1444+(4+4*j) by omega_using [],BitVec.ofNat_add,
      ← BitVec.add_assoc,BitVec.sub_add_cancel]
  have hr (j : Nat) (hj : j < 2) :
      InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (1448+4*j)) 4 := by
    rw [hsrc j,allocFrame_rd,hs.rd]
    refine ⟨⟨argAddr s 0,8⟩,List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),?_⟩
    unfold argAddr
    rw [show 4+4*0 = 4 from rfl,← addr,← addr,
      addr_eq (x := s.gpr .esp) (k := 4) (by omega_using [hs.fitSp]),
      addr_eq (x := s.gpr .esp) (k := 4+4*j) (by omega_using [hs.fitSp,hj])]
    exact VG.Offset.contains _ (by omega_using []) (by omega_using [hj]) (by omega_using [hs.fitSp])
  have hw (j : Nat) (hj : j ≤ 2) : InRegions u.wr (addr (u.gpr .esp) (4*j)) 4 := by
    refine ⟨_,List.mem_cons_self,?_⟩
    rw [addr_eq (x := u.gpr .esp) (k := 4*j) (by omega_using [hfit,hj])]
    exact VG.Offset.contains_base _ (by omega_using [hj]) (by omega_using [hfit,hj])
  obtain ⟨w,t,e,rd,wr,g,f,v,b,tr⟩ := setupArgs_run hfit (by decide) hr hw
  have he : w.gpr .esp = u.gpr .esp := g _ (by decide)
  refine ⟨w,t,e,rd,wr,g,f,?_,?_,tr⟩
  · intro j hj
    rw [arg_callEntry (by rw [he,hE]; omega_using [hs.sp])
      (by rw [he,hE]; omega_using [hs.sp,hs.fitSp,hj]),he]
    change w.mem.readW (addr (u.gpr .esp) (4*j)) 32 = _
    rw [v j hj,hsrc j]
    rfl
  · rw [arg_callEntry (by rw [he,hE]; omega_using [hs.sp])
      (by rw [he,hE]; omega_using [hs.sp,hs.fitSp]),he]
    exact b


def oldEntry (s : State) : State := narrow Spec.Sm4.expandKeySig .u64 179 1448 false s

theorem oldEntry_facts {s : State} (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s) :
    (Proof.Sm4.expandKeyScratchContract abi 179).pre (oldEntry s) ∧
    (oldEntry s).gpr .esp = s.gpr .esp - 1448#32 ∧
    (∀ j < 2, arg (oldEntry s) j = arg s j) ∧
    arg (oldEntry s) 2 = s.gpr .esp - 1448#32 + 16#32 := by
  have hpre : (Proof.Sm4.expandKeyScratchContract abi 179).pre (oldEntry s) :=
    narrow_pre (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64) (n := 179)
      (bytes := 1448) (stack := 0)
      (pre := Curry.const (fun _ : Mem => True) (Spec.Sm4.expandKeySig.words abi.ptrBits)) (by decide)
      (fun _ _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) hs
  have nf := narrow_facts (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64) (n := 179)
    (bytes := 1448) (stack := 0) (by decide) hs
  obtain ⟨_,_,_,_,_,ha,hb⟩ := argsState_run (sig := Spec.Sm4.expandKeySig) (e := .u64) (n := 179)
    (bytes := 1448) (stack := 0) hs (by decide)
  exact ⟨hpre,nf.1,fun j hj => ha j hj,hb⟩

theorem oldEntry_regions {s : State} (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s) :
    (oldEntry s).rd = [⟨(arg s 0).setWidth 64,16⟩,⟨(s.gpr .esp - 1444#32).setWidth 64,12⟩] ∧
    (oldEntry s).wr = [⟨(arg s 1).setWidth 64,128⟩,⟨(s.gpr .esp - 1432#32).setWidth 64,1432⟩] := by
  obtain ⟨hp,he,ha,hb⟩ := oldEntry_facts hs
  generalize hn : oldEntry s = n at hp he ha hb ⊢
  sig_pre [Proof.Sm4.expandKeyScratchContract,Proof.Sm4.expandKeyScratchSig,
    Spec.Sm4.expandKeySig,abi,argVal,argBytes,↓reduceIte,Nat.reduceEqDiff,
    Nat.reduceDiv,List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul] at hp
  have h0 := ha 0 (by decide)
  have h1 := ha 1 (by decide)
  have hA : argAddr n 0 = (s.gpr .esp - 1444#32).setWidth 64 := by
    rw [argAddr,he]
    apply congrArg (BitVec.setWidth 64)
    exact (VG.Offset.sub_ofNat_eq (s.gpr .esp) (a := 1444) (b := 1448) (by decide)).symm
  have hB : s.gpr .esp - 1448#32 + 16#32 = s.gpr .esp - 1432#32 := by
    exact (VG.Offset.sub_ofNat_eq (s.gpr .esp) (a := 1432) (b := 1448) (by decide)).symm
  exact ⟨by rw [hp.2.1,h0,hA],by rw [hp.2.2.1,h1,hb,hB]⟩


theorem shared_call_pre {s w : State} (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s)
    (he : w.gpr .esp = s.gpr .esp - 1444#32)
    (ha : ∀ j < 2, arg w.callEntry j = arg s j)
    (hb : arg w.callEntry 2 = s.gpr .esp - 1444#32 + 12#32)
    (hr : w.rd = s.rd) (hw : w.wr = (allocFrame 1444 s).wr) :
    let n := oldEntry s
    (Proof.Sm4.expandKeyScratchContract abi 179).pre (w.callEntry.withRegions n.rd n.wr) ∧
    Covers (n.rd ++ n.wr) (w.rd ++ w.wr) ∧ Covers n.wr w.wr := by
  intro n
  obtain ⟨np,ne,na,nb⟩ := oldEntry_facts hs
  obtain ⟨nr,nw⟩ := oldEntry_regions hs
  have hp := framePre_of hs
  have p : (Proof.Sm4.expandKeyScratchContract abi 179).pre (w.callEntry.withRegions n.rd n.wr) := by
    refine scratch_pre_congr np ?_ ?_ rfl rfl
    · rw [State.withRegions_gpr,State.callEntry_esp,he,ne,BitVec.sub_sub]
      rfl
    · intro j hj
      rw [arg_withRegions]
      by_cases h2 : j < 2
      · exact (ha j h2).trans (na j h2).symm
      · obtain rfl : j = 2 := by omega_using [hj,h2]
        rw [hb,nb]
        have b1 := VG.Offset.sub_ofNat_eq (s.gpr .esp) (a := 1432) (b := 1444) (by decide)
        have b2 := VG.Offset.sub_ofNat_eq (s.gpr .esp) (a := 1432) (b := 1448) (by decide)
        exact b1.symm.trans b2
  have frame_cover {a : Addr} {k : Nat} (h : (below (s.gpr .esp) 1444).Contains a k) :
      Covers [⟨a,k⟩] w.wr :=
    Covers.one ⟨_,by rw [hw]; exact List.mem_cons_self,h⟩
  have buffer_cover : Covers [⟨(s.gpr .esp - 1432#32).setWidth 64,1432⟩] w.wr := by
    apply frame_cover
    show (⟨(s.gpr .esp - 1444#32).setWidth 64,1444⟩ : Region).Contains
      ((s.gpr .esp - 1432#32).setWidth 64) 1432
    have e1 := Taint.sub_setWidth (e := s.gpr .esp) (m := 1444) (by omega_using [hp.sp])
    have e2 := Taint.sub_setWidth (e := s.gpr .esp) (m := 1432) (by omega_using [hp.sp])
    rw [e1,e2]
    exact VG.Offset.contains_below _ (by decide) (by decide) (by decide)
  have args_cover : Covers [⟨(s.gpr .esp - 1444#32).setWidth 64,12⟩] w.wr := by
    apply frame_cover
    simpa only [BitVec.add_zero] using VG.Offset.contains_base
      ((s.gpr .esp - 1444#32).setWidth 64) (d := 0) (n := 12) (k := 1444) (by decide) (by decide)
  have sched_cover : Covers [⟨(arg s 1).setWidth 64,128⟩] w.wr := Covers.of_mem (by
    intro r hr'
    simp only [List.mem_singleton] at hr'
    subst hr'
    rw [hw,allocFrame_wr,hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have key_cover : Covers [⟨(arg s 0).setWidth 64,16⟩] w.rd := Covers.of_mem (by
    intro r hr'
    simp only [List.mem_singleton] at hr'
    subst hr'
    rw [hr,hp.rd]
    exact List.mem_cons_self)
  have write_cover : Covers n.wr w.wr := by
    rw [nw]
    exact Covers.pair sched_cover buffer_cover
  refine ⟨p,?_,write_cover⟩
  apply Covers.append_left
  · rw [nr]
    exact Covers.pair (Covers.left key_cover) (Covers.right args_cover)
  · exact Covers.right write_cover


theorem scratch_post {s t : State} (hp : (Proof.Sm4.expandKeyScratchContract abi 179).post s t) :
    Spec.Sm4.scheduleAt t.mem ((arg s 1).setWidth 64) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64)) := by
  sig_post [Proof.Sm4.expandKeyScratchContract,Proof.Sm4.expandKeyScratchSig,
    Spec.Sm4.expandKeySig,Proof.Sm4.expandKeyPost,abi,argVal,argBytes,↓reduceIte,Nat.reduceEqDiff,
    Nat.reduceDiv,List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul] at hp
  exact hp

theorem public_post {s t : State}
    (h : Spec.Sm4.scheduleAt t.mem ((arg s 1).setWidth 64) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64))) :
    (Spec.Sm4.expandKeyContract abi 1448).post s t := by
  sig_post [Spec.Sm4.expandKeyContract,Spec.Sm4.expandKeySig,abi,argVal,argBytes,↓reduceIte,Nat.reduceEqDiff,
    Nat.reduceDiv,List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul]
  exact h

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p,16⟩ r) :
    Spec.Sm4.blockAt m' p = Spec.Sm4.blockAt m p := by
  apply Vector.ext
  intro i hi
  simpa only [Spec.Sm4.blockAt,Vector.getElem_ofFn] using
    hf.bytes (R := ⟨p,16⟩) hd (by show 16 ≤ 2^64; decide) hi

theorem entry_frame {s w : State} (hs : FramePre s)
    (he : w.gpr .esp = s.gpr .esp - 1444#32)
    (hf : Frame [⟨(s.gpr .esp - 1444#32).setWidth 64,12⟩] s.mem w.mem) :
    Frame [below (s.gpr .esp) 1448] s.mem w.callEntry.mem := by
  have f0 : Frame [below (s.gpr .esp) 1448] s.mem w.mem := hf.sub (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨_,List.mem_singleton_self _,?_⟩
    exact fun a ha => below_sub (a := 1444) (b := 1448) (by decide) hs.sp a
      (Region.sub_prefix (by decide) a ha))
  rw [State.callEntry_mem]
  apply f0.writeW (List.mem_singleton_self _)
  rw [he,BitVec.sub_sub]
  change (below (s.gpr .esp) 1448).Contains ((s.gpr .esp - 1448#32).setWidth 64) 4
  simpa only [BitVec.add_zero] using VG.Offset.contains_base
    ((s.gpr .esp - 1448#32).setWidth 64) (d := 0) (n := 4) (k := 1448) (by decide) (by decide)


def keyBody : Prog isa := .seq (.block (setupArgs 1448))
  (.seq (.call "vg_sm4_expand_key_shared" Impl.Sm4.X86.expandKey)
    (.block (wipe 12 358)))

theorem raw_nosp : NoSp Impl.Sm4.X86.expandKey := NoSp.of_all (by lit_decide)
theorem raw_depth : stackUse Impl.Sm4.X86.expandKey = 0 := rfl

theorem keyBody_nosp : NoSp keyBody := by
  intro i hi
  simp only [keyBody,instrs,List.mem_append] at hi
  rcases hi with hi | hi | hi
  · exact NoSp.of_all (c := .block (setupArgs 1448)) (by lit_decide) i hi
  · exact raw_nosp i hi
  · exact wipe_noSp 12 358 i hi

theorem keyBody_depth : stackUse keyBody = 4 := by
  show max 0 (max (stackUse Impl.Sm4.X86.expandKey + 4) 0) = 4
  rw [raw_depth]
  rfl

theorem framed_code : Impl.Sm4.X86.expandKeyFramed =
    .frame (.alloc 1444) keyBody (.free 1444) := by kernel_rfl

theorem framed_nosp : NoSp Impl.Sm4.X86.expandKeyFramed := by
  intro i hi
  rw [framed_code] at hi
  simp only [instrs,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact keyBody_nosp i hi
  · rfl

theorem framed_depth : stackUse Impl.Sm4.X86.expandKeyFramed = 1448 := by
  rw [framed_code,stackUse,keyBody_depth]
  rfl


def Finished (s t : State) : Prop :=
  (∀ r ∈ calleeSaved,t.gpr r = s.gpr r) ∧
    Spec.Sm4.scheduleAt t.mem ((arg s 1).setWidth 64) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64))

theorem framed_wipe_run {s u : State} (hp : FramePre s)
    (he : u.gpr .esp = s.gpr .esp - 1444#32)
    (hw : u.wr = (allocFrame 1444 s).wr) :
    ∃ mW, execBlock isa (wipe 12 358) u =
      some ({wipeRegs u with mem := mW},wipeTrace (u.gpr .esp) 12 358) ∧
      Frame [below (s.gpr .esp) 1444] u.mem mW := by
  let R := below (s.gpr .esp) 1444
  have heN : (u.gpr .esp).toNat = (s.gpr .esp).toNat - 1444 := by
    rw [he]
    exact sub_toNat (by omega_using [hp.sp])
  have hR : R ∈ u.wr := by rw [hw]; exact List.mem_cons_self
  have hc (d n : Nat) (hd : d+n ≤ 1444) :
      R.Contains ((u.gpr .esp + BitVec.ofNat 32 d).setWidth 64) n := by
    have e : (u.gpr .esp).setWidth 64 = (s.gpr .esp - 1444#32).setWidth 64 := congrArg _ he
    change R.Contains (addr (u.gpr .esp) d) n
    rw [addr_eq (by omega_using [heN,hp.sp,hp.fitSp,hd]),e]
    exact VG.Offset.contains_base _ hd (by omega_using [heN,hp.fitSp,hd])
  exact wipe_run R u 12 358 hR
    (fun k hk => hc _ _ (by omega_using [hk]))
    (fun k hk => hc _ _ (by omega_using [hk]))

theorem wipe_finish {s u : State} (hp : FramePre s)
    (he : u.gpr .esp = s.gpr .esp - 1444#32)
    (hw : u.wr = (allocFrame 1444 s).wr)
    (hg : ∀ r ∈ calleeSaved,u.gpr r = (allocFrame 1444 s).gpr r)
    (hs : Spec.Sm4.scheduleAt u.mem ((arg s 1).setWidth 64) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64))) :
    WP isa (.block (wipe 12 358)) u fun v => ∀ m U,
      Frame [below (s.gpr .esp) 1444] v.mem m →
      Finished s {freed 1444 v with mem := m,unknowns := U} := by
  let R := below (s.gpr .esp) 1444
  obtain ⟨mW,eW,fW⟩ := framed_wipe_run hp he hw
  refine ⟨_,_,Exec.block eW,?_⟩
  intro m U fm
  have notCx : ∀ r ∈ calleeSaved,r ≠ Reg.ecx := by decide
  refine ⟨?_,?_⟩
  · intro r hr
    by_cases hsp : r = Reg.esp
    · subst hsp
      change (freed 1444 {wipeRegs u with mem := mW}).gpr .esp = _
      rw [freed_esp]
      change (wipeRegs u).gpr .esp + 1444#32 = _
      rw [wipeRegs_gpr (by decide),he]
      exact BitVec.sub_add_cancel _ _
    · change (freed 1444 {wipeRegs u with mem := mW}).gpr r = _
      rw [freed_gpr _ _ hsp]
      change (wipeRegs u).gpr r = _
      rw [wipeRegs_gpr (notCx r hr),hg r hr,allocFrame_gpr _ _ hsp]
  · change Spec.Sm4.scheduleAt m ((arg s 1).setWidth 64) = _
    have dS : Region.Disjoint ⟨(arg s 1).setWidth 64,128⟩ R :=
      (hp.frameSchedule.sub_left (below_sub (by decide) hp.sp)).symm
    rw [Proof.Sm4.scheduleAt_frame (fW.trans fm) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact dS),hs]


theorem framed_wp {s : State} (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s) :
    WP isa Impl.Sm4.X86.expandKeyFramed s (Finished s) := by
  have hp := framePre_of hs
  rw [framed_code]
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega_using [hp.sp]) keyBody_nosp ?_
  obtain ⟨w,t,e,rd,wr,g,hf,a,b,_tr⟩ := frame_setup_run hp
  have he : w.gpr .esp = s.gpr .esp - 1444#32 :=
    (g .esp (by decide)).trans (allocFrame_esp _ _)
  have hb : arg w.callEntry 2 = s.gpr .esp - 1444#32 + 12#32 := b
  obtain ⟨pre,cov,covw⟩ := shared_call_pre hs he a hb rd wr
  have fi := entry_frame hp he (by simpa only [allocFrame_esp] using hf)
  have ki : Spec.Sm4.blockAt w.callEntry.mem ((arg s 0).setWidth 64) =
      Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64) := blockAt_frame fi (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hp.frameKey.symm)
  have noAx : ∀ r ∈ calleeSaved,r ≠ Reg.eax := by decide
  have hd : stackUse Impl.Sm4.X86.expandKey + 4 ≤ (w.gpr .esp).toNat := by
    rw [raw_depth,he,sub_toNat (by omega_using [hp.sp])]
    omega_using [hp.sp]
  unfold keyBody
  refine WP.seq ⟨t,w,Exec.block e,?_⟩
  refine WP.seq (WP.call Proof.Sm4.X86.expandKey_verified.1 raw_nosp hd pre cov covw ?_)
  intro u _rd uwr ucs _fr _keep ⟨v,vm,_vg,vp⟩
  have heU : u.gpr .esp = s.gpr .esp - 1444#32 := (ucs .esp (by decide)).trans he
  have hwU : u.wr = (allocFrame 1444 s).wr := uwr.trans wr
  have hgU : ∀ r ∈ calleeSaved,u.gpr r = (allocFrame 1444 s).gpr r :=
    fun r hr => (ucs r hr).trans (g r (noAx r hr))
  have sched := scratch_post vp
  simp only [State.withRegions_mem,arg_withRegions] at sched
  rw [vm,a 1 (by decide),a 0 (by decide),ki] at sched
  exact wipe_finish hp heU hwU hgU sched

theorem framed_correct (s : State) (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s) :
    ∃ t u, Exec isa Impl.Sm4.X86.expandKeyFramed s t u ∧ abiPreserved s u ∧
      (Spec.Sm4.expandKeyContract abi 1448).post s u := by
  obtain ⟨t,u,he,hg,hp⟩ := framed_wp hs
  have hs' := framePre_of hs
  have ff := Exec.frameSp he framed_nosp (by rw [framed_depth]; exact hs'.sp)
  rw [framed_depth,hs'.wr] at ff
  refine ⟨t,u,he,⟨hg,?_⟩,public_post hp⟩
  apply ff.readW (r := ⟨(s.gpr .esp).setWidth 64,4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hs'.retSchedule
  · exact Scrub.ret_slot_disjoint hs'.sp _ (List.mem_singleton_self _)


theorem framed_pub {s t : State} (hp : (Spec.Sm4.expandKeyContract abi 1448).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ j < 2,arg s j = arg t j := by
  sig_pub [Spec.Sm4.expandKeyContract,Spec.Sm4.expandKeySig,abi,argVal,argBytes,↓reduceIte,Nat.reduceEqDiff,
    Nat.reduceDiv,List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul] at hp
  obtain ⟨he,h0,h1⟩ := hp
  refine ⟨he,fun j hj => ?_⟩
  have h : j = 0 ∨ j = 1 := by omega_using [hj]
  rcases h with rfl | rfl
  · exact h0
  · exact h1

structure CallSetup (s w : State) : Prop where
  sp : w.gpr .esp = s.gpr .esp - 1444#32
  args : ∀ j < 2,arg w.callEntry j = arg s j
  scratch : arg w.callEntry 2 = s.gpr .esp - 1444#32 + 12#32
  rd : w.rd = s.rd
  wr : w.wr = (allocFrame 1444 s).wr

theorem scratch_pub_of {s t : State} (he : s.gpr .esp = t.gpr .esp)
    (ha : ∀ j < 3,arg s j = arg t j) : (Proof.Sm4.expandKeyScratchContract abi 179).pub s t := by
  sig_pub [Proof.Sm4.expandKeyScratchContract,Proof.Sm4.expandKeyScratchSig,
    Spec.Sm4.expandKeySig,abi,argVal,argBytes,↓reduceIte,Nat.reduceEqDiff,
    Nat.reduceDiv,List.sum_cons,List.sum_nil,Nat.reduceAdd,Nat.reduceMul]
  exact ⟨he,ha 0 (by decide),ha 1 (by decide),ha 2 (by decide)⟩

theorem shared_call_ct {s t a b : State}
    (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s)
    (ht : (Spec.Sm4.expandKeyContract abi 1448).pre t)
    (hp : (Spec.Sm4.expandKeyContract abi 1448).pub s t)
    (hA : CallSetup s a) (hB : CallSetup t b) :
    RelCT isa (fun x y => x = a ∧ y = b)
      (.call "vg_sm4_expand_key_shared" Impl.Sm4.X86.expandKey) (fun _ _ => True) := by
  obtain ⟨he,ha⟩ := framed_pub hp
  obtain ⟨pa,ca,wa⟩ := shared_call_pre hs hA.sp hA.args hA.scratch hA.rd hA.wr
  obtain ⟨pb,cb,wb⟩ := shared_call_pre ht hB.sp hB.args hB.scratch hB.rd hB.wr
  have er : (oldEntry t).rd = (oldEntry s).rd := by
    rw [(oldEntry_regions ht).1,(oldEntry_regions hs).1,he,ha 0 (by decide)]
  have ew : (oldEntry t).wr = (oldEntry s).wr := by
    rw [(oldEntry_regions ht).2,(oldEntry_regions hs).2,he,ha 1 (by decide)]
  rw [er,ew] at pb cb
  rw [ew] at wb
  have esp : a.gpr .esp = b.gpr .esp := by rw [hA.sp,hB.sp,he]
  have pub : (Proof.Sm4.expandKeyScratchContract abi 179).pub
      (a.callEntry.withRegions (oldEntry s).rd (oldEntry s).wr)
      (b.callEntry.withRegions (oldEntry s).rd (oldEntry s).wr) := by
    apply scratch_pub_of
    · simp only [State.withRegions_gpr,State.callEntry_esp,esp]
    · intro j hj
      simp only [arg_withRegions]
      by_cases hj2 : j < 2
      · rw [hA.args j hj2,hB.args j hj2]
        exact ha j hj2
      · obtain rfl : j = 2 := by omega_using [hj,hj2]
        rw [hA.scratch,hB.scratch,he]
  refine RelCT.call Proof.Sm4.X86.expandKey_verified.1 Proof.Sm4.X86.expandKey_verified.2.1
    (oldEntry s).rd (oldEntry s).wr ?_
  intro x y hxy
  rcases hxy with ⟨rfl,rfl⟩
  exact ⟨pa,pb,pub,ca,wa,cb,wb,esp⟩


theorem framed_ct : ConstantTime isa (Spec.Sm4.expandKeyContract abi 1448).pre
    (Spec.Sm4.expandKeyContract abi 1448).pub Impl.Sm4.X86.expandKeyFramed := by
  apply RelCT.constantTime
  rw [framed_code]
  apply RelCT.frameAlloc (R := fun _ _ => True)
  intro a b ta tb ua ub hab ea eb
  obtain ⟨s,t,⟨hs,ht,hpub⟩,rfl,rfl⟩ := hab
  have ps := framePre_of hs
  have pt := framePre_of ht
  obtain ⟨w1,p1,e1,rd1,wr1,g1,f1,args1,buf1,tr1⟩ := frame_setup_run ps
  obtain ⟨w2,p2,e2,rd2,wr2,g2,f2,args2,buf2,tr2⟩ := frame_setup_run pt
  have setup1 : CallSetup s w1 :=
    ⟨(g1 .esp (by decide)).trans (allocFrame_esp _ _),args1,buf1,rd1,wr1⟩
  have setup2 : CallSetup t w2 :=
    ⟨(g2 .esp (by decide)).trans (allocFrame_esp _ _),args2,buf2,rd2,wr2⟩
  have he := (framed_pub hpub).1
  unfold keyBody at ea eb
  cases ea with
  | seq prefix1 rest1 =>
    cases eb with
    | seq prefix2 rest2 =>
      obtain ⟨dt1,ds1⟩ := Exec.det prefix1 (Exec.block e1)
      obtain ⟨dt2,ds2⟩ := Exec.det prefix2 (Exec.block e2)
      subst dt1 ds1 dt2 ds2
      cases rest1 with
      | @seq _ _ _ cOut1 _ tc1 tw1 call1 wipe1 =>
        cases rest2 with
        | @seq _ _ _ cOut2 _ tc2 tw2 call2 wipe2 =>
          have cc := shared_call_ct hs ht hpub setup1 setup2
          have ctrace : tc1 = tc2 := (cc _ _ _ _ _ _ ⟨rfl,rfl⟩ call1 call2).1
          have sp1 : cOut1.gpr .esp = s.gpr .esp - 1444#32 :=
            (Exec.gpr (c := .call "vg_sm4_expand_key_shared" Impl.Sm4.X86.expandKey) raw_nosp call1).trans setup1.sp
          have sp2 : cOut2.gpr .esp = t.gpr .esp - 1444#32 :=
            (Exec.gpr (c := .call "vg_sm4_expand_key_shared" Impl.Sm4.X86.expandKey) raw_nosp call2).trans setup2.sp
          have cw1 : cOut1.wr = (allocFrame 1444 s).wr := (Exec.rdwr call1).2.trans wr1
          have cw2 : cOut2.wr = (allocFrame 1444 t).wr := (Exec.rdwr call2).2.trans wr2
          obtain ⟨m1,ew1,_⟩ := framed_wipe_run ps sp1 cw1
          obtain ⟨m2,ew2,_⟩ := framed_wipe_run pt sp2 cw2
          have wt1 := (Exec.det wipe1 (Exec.block ew1)).1
          have wt2 := (Exec.det wipe2 (Exec.block ew2)).1
          have es : cOut1.gpr .esp = cOut2.gpr .esp := by rw [sp1,sp2,he]
          have wtrace : tw1 = tw2 := wt1.trans ((congrArg (fun E => wipeTrace E 12 358) es).trans wt2.symm)
          have ea : (allocFrame 1444 s).gpr .esp = (allocFrame 1444 t).gpr .esp := by
            simp only [allocFrame_esp,he]
          have ptrace := tr1.trans ((congrArg (setupTrace 1448) ea).trans tr2.symm)
          exact ⟨by rw [ptrace,ctrace,wtrace],trivial⟩

public theorem framed_verified : Verified target Impl.Sm4.X86.expandKeyFramed (Spec.Sm4.expandKeyContract abi 1448) :=
  ⟨framed_correct,framed_ct,Proof.Sm4.X86.expandKeyFrameSat_pre⟩

def headerStore : Prog isa := .block [.movdquStore ⟨.esp,0⟩ .xmm0]

theorem header_nosp : NoSp headerStore := NoSp.of_all (by decide)

theorem clean_nosp : NoSp Impl.Sm4.X86.expandKeyClean := by
  intro i hi
  simp only [Impl.Sm4.X86.expandKeyClean,instrs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with hi | ((rfl | hi) | rfl)
  · exact framed_nosp i hi
  · rfl
  · subst hi; rfl
  · rfl

theorem header_run (u : State) (h : InRegions u.wr ((u.gpr .esp).setWidth 64) 16) :
    execBlock isa [.movdquStore ⟨.esp,0⟩ .xmm0] u =
      some ({u with mem := u.mem.writeW ((u.gpr .esp).setWidth 64) (u.xmm .xmm0)},
        [.addr ((u.gpr .esp).setWidth 64)]) := by
  simp only [execBlock,isa,exec,State.store128,ea_mk,addr,BitVec.add_zero,h,
    ite_true,Option.map_some,addrs,List.append_nil,List.map_cons,List.map_nil]

theorem header_wp {s u : State} (hp : FramePre s) (hu : Finished s u) :
    WP isa (.frame (.alloc 1448) headerStore (.free 1448)) u (Finished s) := by
  have sp : u.gpr .esp = s.gpr .esp := hu.1 .esp (by decide)
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [sp]; exact hp.sp) header_nosp ?_
  let a := allocFrame 1448 u
  let R := below (s.gpr .esp) 1448
  have hc : R.Contains ((a.gpr .esp).setWidth 64) 16 := by
    simp only [a,R,allocFrame_esp,sp,below]
    simpa only [BitVec.add_zero] using VG.Offset.contains_base ((s.gpr .esp - 1448#32).setWidth 64) (d := 0) (n := 16) (k := 1448) (by decide) (by decide)
  have hin : InRegions a.wr ((a.gpr .esp).setWidth 64) 16 :=
    ⟨R,by simp only [a,R,allocFrame_wr,sp,below]; exact List.mem_cons_self,hc⟩
  refine ⟨_,_,Exec.block (header_run a hin),?_⟩
  intro m U fm
  have fw : Frame [R] u.mem (a.mem.writeW ((a.gpr .esp).setWidth 64) (a.xmm .xmm0)) :=
    (Frame.refl [R] u.mem).writeW (List.mem_singleton_self _) _ hc
  have ft : Frame [R] u.mem m := fw.trans (by simpa only [sp,R] using fm)
  refine ⟨?_,?_⟩
  · intro r hr
    by_cases he : r = .esp
    · subst he
      change (freed 1448 {a with mem := _}).gpr .esp = _
      rw [freed_esp]
      change (u.gpr .esp - 1448#32) + 1448#32 = _
      rw [BitVec.sub_add_cancel,sp]
    · change (freed 1448 {a with mem := _}).gpr r = _
      rw [freed_gpr _ _ he]
      exact (allocFrame_gpr 1448 u he).trans (hu.1 r hr)
  · change Spec.Sm4.scheduleAt m ((arg s 1).setWidth 64) = _
    rw [Proof.Sm4.scheduleAt_frame ft (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.frameSchedule.symm)]
    exact hu.2

theorem clean_wp {s : State} (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s) :
    WP isa Impl.Sm4.X86.expandKeyClean s (Finished s) := by
  exact WP.seq (WP.mono (framed_wp hs) fun _ hu => header_wp (framePre_of hs) hu)

theorem clean_depth : stackUse Impl.Sm4.X86.expandKeyClean = 1448 := by
  rw [Impl.Sm4.X86.expandKeyClean,stackUse,framed_depth]
  rfl

theorem clean_correct (s : State) (hs : (Spec.Sm4.expandKeyContract abi 1448).pre s) :
    ∃ t u, Exec isa Impl.Sm4.X86.expandKeyClean s t u ∧ abiPreserved s u ∧
      (Spec.Sm4.expandKeyContract abi 1448).post s u := by
  obtain ⟨t,u,he,hg,hp⟩ := clean_wp hs
  have hs' := framePre_of hs
  have ff := Exec.frameSp he clean_nosp (by rw [clean_depth]; exact hs'.sp)
  rw [clean_depth,hs'.wr] at ff
  refine ⟨t,u,he,⟨hg,?_⟩,public_post hp⟩
  apply ff.readW (r := ⟨(s.gpr .esp).setWidth 64,4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hs'.retSchedule
  · exact Scrub.ret_slot_disjoint hs'.sp _ (List.mem_singleton_self _)

theorem header_ct : RelCT isa (fun s t => s.gpr .esp = t.gpr .esp)
    (.frame (.alloc 1448) headerStore (.free 1448)) (fun _ _ => True) := by
  apply RelCT.frameAlloc (R := fun _ _ => True)
  rintro a b ta tb ua ub ⟨s,t,he,rfl,rfl⟩ ea eb
  cases ea with
  | block ea =>
    cases eb with
    | block eb =>
      have trace {x y : State} {tt : List Leak}
          (ee : execBlock isa [.movdquStore ⟨.esp,0⟩ .xmm0] x = some (y,tt)) :
          tt = [.addr ((x.gpr .esp).setWidth 64)] := by
        simp only [execBlock,isa,exec,State.store128,ea_mk,addr,BitVec.add_zero] at ee
        split at ee
        · contradiction
        · simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,addrs,ea_mk,addr,
            BitVec.add_zero,List.map_cons,List.map_nil,List.append_nil] at ee
          exact ee.2.symm
      exact ⟨(trace ea).trans (by rw [trace eb,allocFrame_esp,allocFrame_esp,he]),trivial⟩

theorem clean_ct : ConstantTime isa (Spec.Sm4.expandKeyContract abi 1448).pre
    (Spec.Sm4.expandKeyContract abi 1448).pub Impl.Sm4.X86.expandKeyClean := by
  intro s t ts tt us ut ps pt pub es et
  cases es with
  | seq es1 es2 =>
    cases et with
    | seq et1 et2 =>
      have e1 := framed_ct _ _ _ _ _ _ ps pt pub es1 et1
      have sp : _ := (Exec.gpr framed_nosp es1).trans ((framed_pub pub).1.trans (Exec.gpr framed_nosp et1).symm)
      have e2 := (header_ct _ _ _ _ _ _ sp es2 et2).1
      rw [e1,e2]

public theorem clean_verified : Verified target Impl.Sm4.X86.expandKeyClean (Spec.Sm4.expandKeyContract abi 1448) :=
  ⟨clean_correct,clean_ct,Proof.Sm4.X86.expandKeyFrameSat_pre⟩

end VG.Proof.Sm4.X86.KeyCall
