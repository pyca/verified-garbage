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
open VG.Impl.Aes.PPC64LE.Crypto (mask byteMask counterBase counterStep counterOne)

structure CtrSetup (s t : State) : Prop where
  effects : Local [.r0, .r11, .r12] [.v0, .v1, mask, counterStep, counterBase] s t
  zero : t.gpr .r0 = 0
  mask : t.vpr Impl.Aes.PPC64LE.Crypto.mask = byteMask
  control : t.vpr counterStep = counterOne
  baseValue : t.vpr counterBase = Spec.Gcm.blockAt s.mem (s.gpr .r5)

theorem ctr_setup_ok (s : State) (hr : (⟨s.gpr .r5, 16⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block Impl.Aes.PPC64LE.Crypto.ctrSetup) s (CtrSetup s) := by
  rw [Impl.Aes.PPC64LE.Crypto.ctrSetup]
  repeat rw [WP.block_append_iff]
  refine WP.mono (setup_ok s) fun u ⟨hz, hm, hv0, he⟩ => ?_
  refine WP.mono (setMask_ok counterStep counterOne u (by decide) (by decide) hv0) fun v ⟨hctrl, hf⟩ => ?_
  have hzero : v.gpr .r0 = 0 := (hf.keep.gpr (by decide)).trans hz
  have hmask : v.vpr mask = byteMask := (hf.v mask (by decide)).trans hm
  have ho := he.trans hf
  have hin : InRegions (v.rd ++ v.wr) (v.gpr .r5) 16 := by
    rw [ho.keep.gpr (by decide), ho.keep.2.1, ho.keep.2.2]
    exact ⟨⟨s.gpr .r5, 16⟩, hr, Region.contains_self _ _⟩
  refine WP.mono (load_ok counterBase .r5 v (by decide) (by decide) hzero hmask hin) fun t ⟨hb, hg⟩ => ?_
  refine ⟨(ho.trans (Local.of_vector hg)).weaken (by simp [or_left_comm]) (by simp [or_left_comm]),
    (congrFun hg.gpr .r0).trans hzero, (hg.v mask (by decide)).trans hmask,
    (hg.v counterStep (by decide)).trans hctrl, ?_⟩
  rw [hb, read_blockAt, ho.mem, ho.keep.gpr (by decide)]

end VG.Proof.Aes.PPC64LE.Crypto
