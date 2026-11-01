module

import VerifiedGarbage.Proof.Sm4.Arm.BatchEntry
import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Sm4.Arm.BatchFill
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Sm4.Arm.BatchFill
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # The batched SM4-CTR prologue and its external precondition -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchPrologue

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchEntry VG.Proof.Sm4.Arm.BatchChain
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

abbrev Kp (s : State) : BitVec 32 := s.gpr .r0
abbrev Iv (s : State) : BitVec 32 := s.gpr .r1
abbrev Dp (s : State) : BitVec 32 := s.gpr .r2
abbrev N (s : State) : Nat := (s.gpr .r3).toNat
abbrev Sc (s : State) : BitVec 32 := stackArg s 0
abbrev keyR (s : State) : Region := ⟨State.addr (Kp s), 128⟩
abbrev ivR (s : State) : Region := ⟨State.addr (Iv s), 16⟩
abbrev dataR (s : State) : Region := ⟨State.addr (Dp s), 16 * N s⟩
abbrev wsR (s : State) : Region := ⟨State.addr (Sc s), 4 * BatchCtr.totalSlots⟩
abbrev argR (s : State) : Region := ⟨stackArgAddr s 0, 4⟩

structure Pre (s : State) : Prop where
  spFit : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [keyR s, argR s]
  wr : s.wr = [ivR s, dataR s, wsR s]
  ki : (keyR s).Disjoint (ivR s)
  kd : (keyR s).Disjoint (dataR s)
  ks : (keyR s).Disjoint (wsR s)
  id : (ivR s).Disjoint (dataR s)
  ivs : (ivR s).Disjoint (wsR s)
  ds : (dataR s).Disjoint (wsR s)
  ia : (ivR s).Disjoint (argR s)
  da : (dataR s).Disjoint (argR s)
  sa : (wsR s).Disjoint (argR s)
  fitK : (Kp s).toNat + 128 ≤ 2 ^ 32
  fitI : (Iv s).toNat + 16 ≤ 2 ^ 32
  fitD : (Dp s).toNat + 16 * N s ≤ 2 ^ 32
  fitB : (Sc s).toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32

theorem Pre.writable {s : State} (h : Pre s) {r : Region} (hr : r ∈ [ivR s, dataR s, wsR s]) :
    Covers [r] s.wr := Covers.of_mem fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'
  rw [h.wr]; exact hr

theorem Pre.key {s : State} (h : Pre s) : Covers [keyR s] (s.rd ++ s.wr) :=
  Covers.left (Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h.rd]; simp)

structure Ready (s₀ : State) (s : State) : Prop where
  base : s.gpr sb = Sc s₀
  key : s.gpr .r4 = Kp s₀
  iv : s.gpr .r5 = Iv s₀
  data : s.gpr .r6 = Dp s₀
  left : s.gpr .r7 = BitVec.ofNat 32 (N s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  saved : Spill.Saved s.mem (State.addr (Sc s₀)) s₀.gpr BatchCtr.modeSaved
  frame : Frame [wsR s₀] s₀.mem s.mem
  table : Holds layout s.mem (State.addr (Sc s₀)) (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))) .encrypt
  counter : bytesAt s.mem (counterAddr (Sc s₀)) 16 = bytesAt s₀.mem (State.addr (Iv s₀)) 16
  z : s.z = decide (N s₀ = 0)

theorem prologue_wp {s₀ : State} (hp : Pre s₀) : WP isa BatchCtr.prologue s₀ (Ready s₀) := by
  have hw := hp.writable (r := wsR s₀) (by simp)
  have hi := hp.writable (r := ivR s₀) (by simp)
  have ha : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 :=
    ⟨argR s₀, List.mem_append_left _ (by rw [hp.rd]; simp), Region.contains_self _ _⟩
  refine WP.seq (WP.mono (entry_wp rfl ha rfl hp.fitB hw) fun s₁ e₁ => ?_)
  have eWide : Frame [wsR s₀] s₀.mem s₁.mem := e₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR s₀, List.mem_singleton_self _, Offset.sub_base _ (by change 1456 + 36 ≤ 4 * BatchCtr.totalSlots; decide)⟩
  have sch₁ : Spec.Sm4.scheduleAt s₁.mem (State.addr (Kp s₀)) = Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀)) :=
    Proof.Sm4.scheduleAt_congr fun i hi => eWide.bytes
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.ks)
      (by change 128 ≤ 2 ^ 64; decide) hi
  have wc : Covers [⟨State.addr (Sc s₀), 4 * slots⟩] s₁.wr := by
    rw [e₁.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots)
      (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega)
  refine WP.seq (WP.mono (BatchCalls.prepare_wp e₁.key e₁.base hp.fitK
    (by have h := hp.fitB; change (Sc s₀).toNat + 4 * slots ≤ 2 ^ 32; rw [slots_eq]; change (Sc s₀).toNat + 1512 ≤ 2 ^ 32 at h; omega)
    (hp.ks.sub_right (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega)))
    (by rw [e₁.rd, e₁.wr]; exact hp.key) wc) fun s₂ ⟨p₂, table₂⟩ => ?_)
  rw [sch₁] at table₂
  have base₂ : s₂.gpr sb = Sc s₀ := (p₂.regs _ (by decide) (by decide)).trans e₁.base
  have iv₂ : s₂.gpr .r5 = Iv s₀ := (p₂.regs _ (by decide) (by decide)).trans e₁.iv
  have pWide : Frame [wsR s₀] s₁.mem s₂.mem := p₂.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR s₀, List.mem_singleton_self _, Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega)⟩
  have prefixFrame := eWide.trans pWide
  have saved₂ := e₁.saved.frame mode_slots p₂.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (d := 1456) (n := 36) (k := 4 * slots) (by decide) (by decide))
  have counterPre : ChainPre s₂ (Sc s₀) (Iv s₀) :=
    ⟨base₂, iv₂, hp.fitB, hp.fitI, by rw [p₂.wr, e₁.wr]; exact hw,
      by rw [p₂.wr, e₁.wr]; exact hi, hp.ivs⟩
  have n₂ : s₂.gpr .r7 = BitVec.ofNat 32 (N s₀) := by
    rw [p₂.regs _ (by decide) (by decide), e₁.left]
    exact (BitVec.ofNat_toNat 32 (s₀.gpr .r3)).symm
  refine WP.mono (setup_wp counterPre (s₀.gpr .r3).isLt n₂ table₂) fun s₃ u₃ => ?_
  have uWide : Frame [wsR s₀] s₂.mem s₃.mem := u₃.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
  have saved₃ := saved₂.frame mode_slots u₃.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  refine ⟨?_, ?_, ?_, ?_, ?_, u₃.rd.trans (p₂.rd.trans e₁.rd), u₃.wr.trans (p₂.wr.trans e₁.wr),
    u₃.sp.trans (p₂.sp.trans e₁.sp), saved₃, prefixFrame.trans uWide, u₃.table, ?_, u₃.z⟩
  · rw [u₃.regs _ (by decide) (by decide)]; exact base₂
  · rw [u₃.regs _ (by decide) (by decide), p₂.regs _ (by decide) (by decide)]; exact e₁.key
  · rw [u₃.regs _ (by decide) (by decide)]; exact iv₂
  · rw [u₃.regs _ (by decide) (by decide), p₂.regs _ (by decide) (by decide)]; exact e₁.data
  · rw [u₃.regs _ (by decide) (by decide)]; exact n₂
  · rw [u₃.counter]
    apply bytes_frame prefixFrame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ivs

end VG.Proof.Sm4.Arm.BatchPrologue
