module

public import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-! # RISC-V contiguous seal argument setup -/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64.Contiguous

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.Contiguous (entry payloadArgs)

/-- Scratch, tag and length slots remain outside the register save area. -/
structure EntryArgs (s : State) (w tag : Addr) : Prop where
  work : Covers [⟨w,2560⟩] s.wr
  workAlign : w.toNat % 8 = 0
  spAlign : s.sp.toNat % 16 = 0
  slot : ∀ i < 4, InRegions (s.rd++s.wr) (s.sp + BitVec.ofNat 64 (8*i)) 8
  apart : ∀ i < 4, (⟨s.sp + BitVec.ofNat 64 (8*i),8⟩ : Region).Disjoint (oneR w)
  scratch : stackArg s 3 = w
  tagPtr : stackArg s 1 = tag

/-- Embed the existing nonce and AAD state. The two additional assignments retain
the destination in s8 and the shared length in s11. -/
def Started (w tag : Addr) (s t : State) : Prop :=
  ∃ u, SO1 w tag s u ∧ t = (u.write .s8 (s.gpr .a7)).write .s11 (stackArg s 0)

theorem entry_wp {s : State} (a : EntryArgs s w tag) :
    WP isa (.block entry) s (Started w tag s) := by
  unfold entry
  rw [WP.block_append_iff]
  refine WP.mono (one1At_args_wp (off := 24) (tagO := 8) (by decide) (by decide)
    a.work a.workAlign a.spAlign (a.slot 3 (by decide)) a.scratch
    (a.slot 1 (by decide)) a.tagPtr (a.apart 1 (by decide))) fun u ⟨hu, _, a7⟩ => ?_
  have align : s.sp.toNat % 8 = 0 := by have := a.spAlign; omega_using [this]
  have read : InRegions (u.rd ++ u.wr) s.sp 8 := by
    rw [hu.keeps.rd,hu.keeps.wr]
    simpa using a.slot 0 (by decide)
  have val : u.mem.readW s.sp 64 = stackArg s 0 := by
    have kept : u.mem.readW s.sp 64 = s.mem.readW s.sp 64 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      simpa using a.apart 0 (by decide)
    simpa [stackArg,stackArgAddr] using kept
  refine Steps.WP.cons (s' := u.write .s8 (u.gpr .a7)) ?_ ?_
  · simp [mov,exec_addi (by decide : imm12 0)]
  apply Steps.WP.cons (s' := ((u.write .s8 (u.gpr .a7)).write .s11 (u.mem.readW s.sp 64)))
  · have ptr : (u.write .s8 (u.gpr .a7)).gpr .t1 + BitVec.ofNat 64 0 = s.sp := by
      simp [RegUpd.gpr_write_of_ne,hu.t1]
    rw [exec_load_d (by decide) (by rw [ptr]; exact align) (by rw [ptr]; exact read),ptr]
    rfl
  · exact WP.block_nil ⟨u,hu,by rw [a7,val]⟩

/-- The public argument registers after loading the bitsliced keys and preparing
the payload. The tag pass reads from the destination retained in the workspace. -/
def payloadState (s : State) : State :=
  let slot := s.gpr .s0 + BitVec.ofNat 64 dataO
  let src := s.mem.readW slot 64
  let dst := s.gpr .s8
  let t := (s.write .t2 s.sp).write .s7 (s.mem.readW (s.sp+16) 64)
  let t := (t.write .s4 src).write .s5 (s.gpr .s11)
  let t := (t.write .s6 0).write .s9 (dst-src)
  { t with mem := s.mem.writeW slot dst }

theorem payloadArgs_wp {s : State}
    (aligned : (s.gpr .s0+BitVec.ofNat 64 dataO).toNat % 8 = 0)
    (slot : InRegions s.wr (s.gpr .s0+BitVec.ofNat 64 dataO) 8)
    (spAligned : (s.sp+BitVec.ofNat 64 16).toNat % 8 = 0)
    (bk : InRegions (s.rd++s.wr) (s.sp+BitVec.ofNat 64 16) 8) :
    WP isa (.block payloadArgs) s (· = payloadState s) := by
  have ro := in_left slot (rd := s.rd)
  apply WP.of_runBlock
  refine ⟨payloadState s, ?_, rfl⟩
  simp only [payloadArgs,bkLoad,dataArgs,List.cons_append,List.nil_append,runBlock_cons,
    exec_addSp (by decide : 0 < 2048), runStep_some, add_ofNat_zero]
  rw [exec_load_d (off := 16) (by decide) (by exact spAligned) (by exact bk)]
  simp only [runStep_some,runBlock_cons,RegUpd.gpr_write_self]
  rw [exec_load_d (off := dataO) (by decide) (by exact aligned) (by exact ro)]
  simp only [runStep_some,runBlock_cons,mov,exec_addi (by decide : imm12 0),
    exec_li (by decide : imm12 0),exec_sub]
  rw [exec_store_d (off := dataO) (by decide) (by exact aligned) (by exact slot)]
  simp [runStep_some, runBlock_nil, payloadState, State.write]

end VG.Proof.AesGcm.RISCV64.Contiguous
