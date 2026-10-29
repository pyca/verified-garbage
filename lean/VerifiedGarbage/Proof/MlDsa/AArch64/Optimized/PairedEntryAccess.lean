module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedKernelReady
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSaved

import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedProlog.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

def argumentMoves : List Instr :=
  [mov .x13 .x0,mov .x14 .x1,mov .x15 .x2,mov .x16 .x3,mov .x8 .x6,mov .x17 .x5,mov .x0 .x4]

structure Arguments (s t : State) : Prop where
  common : t.gpr .x13=s.gpr .x0
  secret : t.gpr .x14=s.gpr .x1
  data : t.gpr .x15=s.gpr .x2
  aux : t.gpr .x16=s.gpr .x3
  bound : t.gpr .x8=s.gpr .x6
  gamma : t.gpr .x17=s.gpr .x5
  work : t.gpr .x0=s.gpr .x4

theorem argumentMoves_ok (s : State) : WP isa (.block argumentMoves) s fun t =>
    ((Arguments s t ∧ t.mem=s.mem) ∧ Keep [.x0,.x8,.x13,.x14,.x15,.x16,.x17] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold argumentMoves mov
  arun
  constructor <;> rfl

theorem tableAddress_ok (s : State) :
    WP isa (.block [.adrSym .x1 "VG_MLDSA_INV_PAIR"]) s fun t =>
      ((t.gpr .x1=s.syms "VG_MLDSA_INV_PAIR" ∧ t.mem=s.mem) ∧ Keep [.x1] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [exec_adrSym]


theorem prolog_ok (s : State)
    (hw : ∀p∈extraSlots 2048,InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 p.2) 16) :
    WP isa (.block pro) s fun t =>
      Keep [.x0,.x1,.x8,.x13,.x14,.x15,.x16,.x17] s t ∧ Arguments s t ∧
      t.gpr .x1=s.syms "VG_MLDSA_INV_PAIR" ∧ t.v=s.v ∧
      Saved t.mem (s.gpr .x4) s.v ∧
      Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem t.mem := by
  change WP isa (.block ((argumentMoves++save)++[.adrSym .x1 "VG_MLDSA_INV_PAIR"])) s _
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono_syms (argumentMoves_ok s) fun a ⟨⟨⟨ha,hma⟩,hka⟩,hva⟩ hya => ?_
  have hwa : ∀p∈extraSlots 2048,InRegions a.wr (a.gpr .x0+BitVec.ofNat 64 p.2) 16 := by
    intro p hp
    rw [hka.wr,ha.work]
    exact hw p hp
  have hsave : WP isa (.block save) a fun b =>
      VG.Proof.MlKem.AArch64.VMem a b (writeSlice (extraSlots 2048) (a.gpr .x0) a.v a.mem) ∧
      Saved b.mem (a.gpr .x0) a.v ∧
      Frame [⟨a.gpr .x0+BitVec.ofNat 64 2048,128⟩] a.mem b.mem := by
    simpa only [List.append_nil] using (save_saved (rest := []) hwa fun b hb hs hf =>
      WP.block_nil_iff.mpr ⟨hb,hs,hf⟩)
  rw [WP.block_append_iff]
  refine WP.mono_syms hsave fun b ⟨hb,hs,hf⟩ hyb => ?_
  refine WP.mono (tableAddress_ok b) fun t ⟨⟨⟨ht,hmt⟩,hkt⟩,hvt⟩ => ?_
  have hmid : Keep [] a b := hb.keep
  have hall := (hka.trans hmid).trans hkt
  refine ⟨hall.mono,?_,?_,hvt.trans (hb.v.trans hva),?_,?_⟩
  · constructor
    · rw [hkt.get .x13 (by decide),hb.gpr,ha.common]
    · rw [hkt.get .x14 (by decide),hb.gpr,ha.secret]
    · rw [hkt.get .x15 (by decide),hb.gpr,ha.data]
    · rw [hkt.get .x16 (by decide),hb.gpr,ha.aux]
    · rw [hkt.get .x8 (by decide),hb.gpr,ha.bound]
    · rw [hkt.get .x17 (by decide),hb.gpr,ha.gamma]
    · rw [hkt.get .x0 (by decide),hb.gpr,ha.work]
  · exact ht.trans (congrFun (hyb.trans hya) _)
  · simpa only [hmt,ha.work,hva] using hs
  · simpa only [hmt,ha.work,hma] using hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure EntryAccess (s : State) : Prop where
  table : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 off) 16
  common : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16
  secret : ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16
  workRead : ∀off,off+16≤2176 → InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 off) 16
  workWrite : ∀off,off+16≤2176 → InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 off) 16
  dataRead : ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16
  dataWrite : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16

theorem EntryAccess.kernel {s t : State} (h : EntryAccess s) {rs : List Reg}
    (hk : Keep rs s t) (ha : Arguments s t)
    (ht : t.gpr .x1=s.syms "VG_MLDSA_INV_PAIR") : KernelAccess t := by
  constructor
  · simpa only [hk.rd,hk.wr,ht] using h.table
  · simpa only [hk.rd,hk.wr,ha.common] using h.common
  · simpa only [hk.rd,hk.wr,ha.secret] using h.secret
  · simpa only [hk.rd,hk.wr,ha.work] using h.workRead
  · intro off ho
    rw [hk.wr,ha.work]
    exact h.workWrite off (by omega)
  · simpa only [hk.rd,hk.wr,ha.data] using h.dataRead
  · simpa only [hk.wr,ha.data] using h.dataWrite

theorem EntryAccess.save {s : State} (h : EntryAccess s) :
    ∀p∈extraSlots 2048,InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 p.2) 16 := by
  intro p hp
  obtain ⟨i,rfl⟩ := (extraSlots_mem _ _).mp hp
  exact h.workWrite _ (by omega)

theorem KernelAccess.gamma {s t : State} (h : KernelAccess s)
    (hk : Keep [.x17,.x7] s t) : KernelAccess t := by
  constructor
  · simpa only [hk.rd,hk.wr,hk.get .x1 (by decide)] using h.table
  · simpa only [hk.rd,hk.wr,hk.get .x13 (by decide)] using h.common
  · simpa only [hk.rd,hk.wr,hk.get .x14 (by decide)] using h.secret
  · simpa only [hk.rd,hk.wr,hk.get .x0 (by decide)] using h.workRead
  · simpa only [hk.wr,hk.get .x0 (by decide)] using h.workWrite
  · simpa only [hk.rd,hk.wr,hk.get .x15 (by decide)] using h.dataRead
  · simpa only [hk.wr,hk.get .x15 (by decide)] using h.dataWrite

end VG.Proof.MlDsa.AArch64.Optimized.Paired
