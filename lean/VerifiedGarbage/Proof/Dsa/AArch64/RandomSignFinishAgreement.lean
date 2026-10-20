module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishResult
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! Connect saved wrapper arguments to the return-path leakage proof. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomFinishPublic (s : State) (status : BitVec 64) : RandomFinishPublic :=
  ⟨randomBase s, s.gpr .x0, (s.gpr .x1).toNat, s.gpr .x2, status⟩

theorem random_finish_public_pre {extra : Nat} {s t : State} {used : Nat} {status : BitVec 64}
    (h : RandomSignABI extra s) (hr : RandomSignFinishPre s used t)
    (hz : word t.mem (randomBase s) Random.oStatus = status) :
    RandomFinishPre (randomFinishPublic s status) t := by
  refine ⟨hr.scr, hr.sp,
    hr.saved (40, s.gpr .x0) (by simp [randomSavedValues]), ?_,
    hr.saved (56, s.gpr .x2) (by simp [randomSavedValues]), hz, ?_, (s.gpr .x1).isLt, ?_, ?_⟩
  · change word t.mem (randomBase s) Random.oOutLen = BitVec.ofNat 64 (s.gpr .x1).toNat
    simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .x1) (by simp [randomSavedValues])
  · change 0 < (s.gpr .x1).toNat
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega
  · intro j hj
    exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .x1).isLt)⟩
  · intro d hd
    exact ((h.stackOut.sub_left (random_frame_sub h)).sub_left (Offset.sub_base _ hd)).sep
      (Region.contains_self _ _) (Region.contains_self _ _)

theorem RandomSignRunning.finishPre {extra : Nat} {s t : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) : RandomSignFinishPre s used t := by
  obtain ⟨_, _, hready⟩ := hr.ready
  exact ⟨hready.scr, hready.sp, hr.saved, hready.usedWord, hr.rd, hr.wr, hr.callee, hr.vectors⟩

theorem random_finish_agreement {extra : Nat} {s t a b : State} {useda usedb : Nat} {status : BitVec 64}
    (hs : RandomSignABI extra s) (ht : RandomSignABI extra t)
    (ha : RandomSignFinishPre s useda a) (hb : RandomSignFinishPre t usedb b)
    (hpub : RandomSignPublicAgree s t)
    (hsa : word a.mem (randomBase s) Random.oStatus = status)
    (hsb : word b.mem (randomBase t) Random.oStatus = status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa RandomSign.finish a tsa u) (eb : Exec isa RandomSign.finish b tsb w) : tsa = tsb := by
  have hpa := random_finish_public_pre hs ha hsa
  have hpb := random_finish_public_pre ht hb hsb
  have he : randomFinishPublic s status = randomFinishPublic t status := by
    unfold randomFinishPublic
    rw [hpub.base, hpub.regs .x0 (by decide), hpub.regs .x1 (by decide), hpub.regs .x2 (by decide)]
  rw [← he] at hpb
  exact (random_finish_ct _ _ _ _ _ _ ⟨_, hpa, hpb, hpa.sp.trans hpb.sp.symm⟩ ea eb).1

end VG.Proof.Dsa.AArch64
