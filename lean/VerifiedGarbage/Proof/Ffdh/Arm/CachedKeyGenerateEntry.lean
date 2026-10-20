module

public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Preserve all existing arguments and retain the appended read-only context pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem cachedKeyGenerateEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : KeyIncoming p s) (cache : IncomingWord p.cachedContext 156 s)
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry) s fun t =>
      Context p [52, 0, 48, 44, 32, 28, 24, 4, 36, 40] t ∧
      Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry, WP.block_append_iff]
  refine WP.mono (withAllRest (keyEntry_ok s h incoming privateValue publicValue outputY privateLength)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  refine wp_stackAddr (by decide) fun v moved => ?_
  have restV : Rest [.r12] u v := moved.rest (by simp)
  have contextV := contextU.of_mem moved.mem restV ((restV.gpr .r0 (by simp)).trans contextU.ptr)
  have cacheU := cache.after (by decide) frameU restU
  have cacheV : IncomingWord p.cachedContext 156 v :=
    ⟨by rw [moved.sp]; exact cacheU.fits,
      by rw [moved.rd, moved.wr, moved.sp]; exact cacheU.readable,
      by rw [moved.mem, moved.sp]; exact cacheU.word⟩
  refine wp_retain_incoming .r3 (by decide) contextV.toArgumentMemory (by decide)
    cacheV (by decide) (by decide) (by decide)
    (by rw [moved.gpr, moved.sp]; exact BitVec.add_zero _) fun t args frameT restT _ _ => ?_
  apply WP.block_nil
  refine ⟨⟨args, (restT.gpr .r0 (by simp)).trans contextV.ptr⟩, ?_⟩
  rw [moved.mem, moved.sp, restU.sp] at frameT
  exact frameU.trans frameT

end VG.Proof.Ffdh.Arm
