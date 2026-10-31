module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: CTR initialization builds masks and loads the counter without changing memory.
/-! # POWER8 AES CTR initialization -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto (mask byteMask counterBase counterMask counterControl)

def icb_lo_word (s : State) : BitVec 64 := (rev32 (s.mem.readW (s.gpr .r5 + 12) 32)).setWidth 64

theorem counter_load_ok (s : State) (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hr : (⟨s.gpr .r5, 16⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (([.li .r11 12, .loadRev .w .r8 .r5 .r11] : List Instr) ++ Impl.Aes.PPC64LE.Crypto.load counterBase .r5)) s fun t =>
      t.gpr .r8 = (icb_lo_word s) ∧ t.gpr .r11 = 12 ∧
      t.vpr counterBase = Spec.Gcm.blockAt s.mem (s.gpr .r5) ∧ Local [.r8, .r11] [counterBase] s t := by
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨s.write .r11 12, ?_, ?_⟩
  · simp only [reduceExec, show 12 < 2^15 by decide, ite_true]
    rfl
  have hread : InRegions ((s.write .r11 12).rd ++ (s.write .r11 12).wr)
      ((s.write .r11 12).gpr .r5 + (s.write .r11 12).gpr .r11) 4 := by
    simp only [RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    exact ⟨⟨s.gpr .r5, 16⟩, hr, Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide)⟩
  have hload : WP isa (.block [.loadRev .w .r8 .r5 .r11]) (s.write .r11 12)
      (· = (s.write .r11 12).write .r8 (icb_lo_word s)) := by
    apply WP.of_runBlock
    rw [runBlock_cons, exec_loadRev_w (by decide) hread, runStep_some, runBlock_nil]
    simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      Option.some.injEq, exists_eq_left']
    rfl
  refine WP.mono hload fun u hu => ?_
  subst u
  have he := (Local.write s .r11 12).trans (Local.write _ .r8 (icb_lo_word s))
  have hin : InRegions (((s.write .r11 12).write .r8 (icb_lo_word s)).rd ++
      ((s.write .r11 12).write .r8 (icb_lo_word s)).wr)
      (((s.write .r11 12).write .r8 (icb_lo_word s)).gpr .r5) 16 := by
    rw [he.keep.2.1, he.keep.2.2, he.keep.gpr (by decide)]
    exact ⟨⟨s.gpr .r5, 16⟩, hr, Region.contains_self _ _⟩
  refine WP.mono (load_ok counterBase .r5 _ (by decide) (by decide)
    ((he.keep.gpr (by decide)).trans h0) ((he.v mask (by simp)).trans hm) hin) fun t ⟨hv, ho⟩ => ?_
  refine ⟨?_, ?_, ?_, (he.trans (Local.of_vector ho)).weaken (by simp [or_comm]) (by simp)⟩
  · rw [congrFun ho.gpr .r8, RegUpd.gpr_write_self]
  · rw [congrFun ho.gpr .r11, RegUpd.gpr_write, ite_eq_right (by decide), RegUpd.gpr_write_self]
  · rw [hv, he.mem, he.keep.gpr (by decide), read_blockAt]

structure CtrSetup (s t : State) : Prop where
  effects : Local [.r0, .r8, .r11, .r12] [.v0, .v1, mask, counterMask, counterBase] s t
  zero : t.gpr .r0 = 0
  mask : t.vpr Impl.Aes.PPC64LE.Crypto.mask = byteMask
  control : t.vpr counterMask = counterControl
  baseValue : t.vpr counterBase = Spec.Gcm.blockAt s.mem (s.gpr .r5)
  word : (t.gpr .r8).setWidth 32 = (Spec.Gcm.blockAt s.mem (s.gpr .r5)).extractLsb' 0 32
  offset : t.gpr .r11 = 12

theorem ctr_setup_ok (s : State) (hr : (⟨s.gpr .r5, 16⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.setup ++
      Impl.Aes.PPC64LE.Crypto.setMask counterMask counterControl ++
      ([.li .r11 12, .loadRev .w .r8 .r5 .r11] : List Instr) ++ Impl.Aes.PPC64LE.Crypto.load counterBase .r5)) s (CtrSetup s) := by
  repeat rw [WP.block_append_iff]
  refine WP.mono (setup_ok s) fun u ⟨hz, hm, hv0, he⟩ => ?_
  refine WP.mono (setMask_ok counterMask counterControl u (by decide) (by decide) hv0) fun v ⟨hctrl, hf⟩ => ?_
  have hzero : v.gpr .r0 = 0 := (hf.keep.gpr (by decide)).trans hz
  have hmask : v.vpr mask = byteMask := (hf.v mask (by decide)).trans hm
  have ho := he.trans hf
  have hrv : (⟨v.gpr .r5, 16⟩ : Region) ∈ v.rd ++ v.wr := by
    rw [ho.keep.gpr (by decide), ho.keep.2.1, ho.keep.2.2]
    exact hr
  rw [← WP.block_append_iff]
  refine WP.mono (counter_load_ok v hzero hmask hrv) fun t ⟨hw, hoff, hb, hg⟩ => ?_
  refine ⟨(ho.trans hg).weaken (by simp [or_left_comm]) (by simp [or_left_comm]),
    (hg.keep.gpr (by decide)).trans hzero, (hg.v mask (by decide)).trans hmask,
    (hg.v counterMask (by decide)).trans hctrl, ?_, ?_, hoff⟩
  · rw [hb, ho.mem, ho.keep.gpr (by decide)]
  · rw [hw, icb_lo_word, BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat, icb_lo, ho.mem, ho.keep.gpr (by decide)]

end VG.Proof.Aes.PPC64LE.Crypto
