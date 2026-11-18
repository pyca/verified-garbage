module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
import VerifiedGarbage.Proof.Sm4.Arm.BatchLoop
import VerifiedGarbage.Proof.Sm4.Arm.Group
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
public import VerifiedGarbage.Proof.Sm4.Arm.BatchCT
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Sm4.Arm.BatchBody`, which only this module used -/

section

/-! # Functional composition of the prepared, eight-block SM4-CTR implementation -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchBody

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4.Arm.BatchXor
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchEntry VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchLoop VG.Proof.Sm4.Arm.BatchGroup
open VG.Spec.Aes (bytesAt)

structure Post (s₀ s : State) : Prop where
  regs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  data : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) =
    Spec.Ctr.crypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))))
      (bytesAt s₀.mem (State.addr (Iv s₀)) 16) (Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀))
  iv : bytesAt s.mem (State.addr (Iv s₀)) 16 =
    Spec.Ctr.next (bytesAt s₀.mem (State.addr (Iv s₀)) 16) (N s₀)
  sp : s.sp = s₀.sp

theorem body_wp {s₀ : State} (hp : Pre s₀) : WP isa BatchCtr.ctr s₀ (Post s₀) := by
  have hw := hp.writable (r := wsR s₀) (by simp)
  have hd := hp.writable (r := dataR s₀) (by simp)
  have hi := hp.writable (r := ivR s₀) (by simp)
  refine WP.seq (WP.mono (prologue_wp hp) fun s₁ p => ?_)
  have blocks₁ : Spec.Cbc.blocksAt s₁.mem (State.addr (Dp s₀)) (N s₀) =
      Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀) := by
    unfold Spec.Cbc.blocksAt
    apply List.map_congr_left
    intro j hj
    apply bytes_frame (P := dataAddr (Dp s₀) j) p.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ds.sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; change 16 * j + 16 ≤ 16 * N s₀; omega_using [this]))
  refine WP.seq (WP.mono (loopOrEmpty_wp (s₀.gpr .r3).isLt p.base p.data p.left p.z hp.fitB hp.fitD
    (by rw [p.wr]; exact hw) (by rw [p.wr]; exact hd) hp.ds p.table p.counter) fun s₂ l => ?_)
  have base₂ : s₂.gpr sb = Sc s₀ := (l.regs _ (by simp [sb])).trans p.base
  have iv₂ : s₂.gpr .r5 = Iv s₀ := (l.regs _ (by simp)).trans p.iv
  have saved₂ := p.saved.frame mode_slots l.frame (fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (d := 1456) (n := 36) (k := 4 * slots) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact hp.ds.symm.sub_left (Offset.sub_base _ (by decide)))
  have cp : ChainPre s₂ (Sc s₀) (Iv s₀) :=
    ⟨base₂, iv₂, hp.fitB, hp.fitI, by rw [l.wr, p.wr]; exact hw,
      by rw [l.wr, p.wr]; exact hi, hp.ivs⟩
  have output := loop_output l
  rw [blocks₁] at output
  apply (WP.block_append_iff (M := isa) (l₁ := BatchCtr.copyCounterOut)
    (l₂ := ([movR .r12 sb] : List Instr) ++ BatchCtr.restore)).mpr
  refine WP.mono (counterOut_wp cp) fun s₃ c => ?_
  have saved₃ := saved₂.frame mode_slots c.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ivs.symm.sub_left (Offset.sub_base _ (by decide)))
  have blocks₃ : Spec.Cbc.blocksAt s₃.mem (State.addr (Dp s₀)) (N s₀) =
      Spec.Cbc.blocksAt s₂.mem (State.addr (Dp s₀)) (N s₀) := by
    unfold Spec.Cbc.blocksAt
    apply List.map_congr_left
    intro j hj
    apply bytes_frame (P := dataAddr (Dp s₀) j) c.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.id.symm.sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; change 16 * j + 16 ≤ 16 * N s₀; omega_using [this]))
  refine WP.mono (restore_wp ((c.regs _ (by decide) (by decide)).trans base₂) hp.fitB
    (by rw [c.wr, l.wr, p.wr]; exact hw) saved₃) fun s₄ ⟨regs, mem, _, _, sp⟩ => ?_
  refine ⟨regs, ?_, ?_, sp.trans (c.sp.trans (l.sp.trans p.sp))⟩
  · rw [mem, blocks₃]; exact output
  · rw [mem, c.block]; exact l.counter

end VG.Proof.Sm4.Arm.BatchBody

end

end


/-! # Batched ARMv7 SM4-CTR meets the public, wiped-stack contract -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.BatchVerified

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchBody VG.Proof.Sm4.Arm.BatchCT

def ctrArm : Contract isa where
  pre := Pre
  post := Post
  pub := Pub

theorem correct (s : State) (h : ctrArm.pre s) :
    ∃ t s', Exec isa BatchCtr.ctr s t s' ∧ abiPreserved s s' ∧ ctrArm.post s s' := by
  obtain ⟨t, s', e, p⟩ := body_wp h
  exact ⟨t, s', e, ⟨p.regs, p.sp⟩, p⟩

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0, 1512⟩]

theorem implies : ctrArm.Implies (Proof.Sm4.ctrScratchContract Arm.abi 189 0) where
  pre s h := by
    sig_pre [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ds, ia, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Proof.Sm4.ctrPost, Spec.Sm4.ctrSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h.data, h.iv⟩
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem verified : Verified Arm.target BatchCtr.ctr (Proof.Sm4.ctrScratchContract Arm.abi 189 0) :=
  Verified.of_correct correct ctr_ct implies

def frameState : State := { satState with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩] }

theorem frameSat : ∃ s, (Spec.Sm4.ctrContract Arm.abi 1520).pre s := by
  implies_sat [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, State.addr] [frameState, satState] using frameState

theorem framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 BatchCtr.ctr)
    (Spec.Sm4.ctrContract Arm.abi 1520) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64) (n := 189)
    (post := Proof.Sm4.ctrPost Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1520)
    verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.ctrPost_local _)
    (Proof.Sm4.ctrPostOut_local _) frameSat

end VG.Proof.Sm4.Arm.BatchVerified
