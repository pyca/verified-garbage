module

import VerifiedGarbage.Proof.Bignum.Arm.CrtLinkStep
import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLinksMemory
public import VerifiedGarbage.Impl.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Block

/-! # All CRT buffer links come from public lengths and addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_links_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 244 ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa links s fun t =>
      t.mem = crtLinkMem s.mem (State.addr base)
        (base + BitVec.ofNat 32 (pOffset w)) (base + BitVec.ofNat 32 (qOffset w))
        (base + BitVec.ofNat 32 (productOffset w)) (base + BitVec.ofNat 32 (compareOffset w))
        (base + BitVec.ofNat 32 (modulusOffset w)) ∧ Rest [.r7, .r1, .r2] s t := by
  rw [links, linksTail, WP.seq_iff]
  refine WP.mono (crt_linkStride_ok s ws (by omega) ptr count) ?_
  rintro u ⟨widthU, stepU, currentU, memU, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans ptr
  rw [WP.seq_iff]
  refine WP.mono (crt_linkStep_ok u (ws.congr restU.wr) (by omega : 224 + 4 ≤ size) (by decide) ptrU
    (currentU.trans (BitVec.add_zero base).symm)
    stepU widthU (by simp [pOffset] : pOffset w = 0 + stride w)) ?_
  rintro v ⟨ptrV, currentV, stepV, widthV, memV, restV⟩
  have restSV := restU.trans (restV.mono (by simp))
  rw [WP.seq_iff]
  refine WP.mono (crt_linkStep_ok v (ws.congr restSV.wr) (by omega : 228 + 4 ≤ size) (by decide) ptrV
    currentV stepV widthV (by simp only [qOffset, pOffset]; omega : qOffset w = pOffset w + stride w)) ?_
  rintro z ⟨ptrZ, currentZ, stepZ, widthZ, memZ, restZ⟩
  have restSZ := restSV.trans (restZ.mono (by simp))
  rw [WP.seq_iff]
  refine WP.mono (crt_linkStep_ok z (ws.congr restSZ.wr) (by omega : 232 + 4 ≤ size) (by decide) ptrZ
    currentZ stepZ widthZ (by simp only [productOffset, qOffset]; omega : productOffset w = qOffset w + stride w)) ?_
  rintro q ⟨ptrQ, currentQ, _, widthQ, memQ, restQ⟩
  have restSQ := restSZ.trans (restQ.mono (by simp))
  rw [WP.seq_iff]
  refine WP.mono (crt_productStride_ok q widthQ) ?_
  rintro r ⟨stepR, memR, restR⟩
  have restSR := restSQ.trans (restR.mono (by simp))
  have ptrR := (restR.gpr .r0 (by simp)).trans ptrQ
  have currentR := (restR.gpr .r2 (by simp)).trans currentQ
  have widthR := (restR.gpr .r7 (by simp)).trans widthQ
  rw [WP.seq_iff]
  refine WP.mono (crt_linkStep_ok r (ws.congr restSR.wr) (by omega : 236 + 4 ≤ size) (by decide) ptrR
    currentR stepR widthR (rfl : compareOffset w = productOffset w + productBytes w)) ?_
  rintro v2 ⟨ptrV2, currentV2, stepV2, widthV2, memV2, restV2⟩
  have restSV2 := restSR.trans (restV2.mono (by simp))
  refine WP.mono (crt_linkStep_ok v2 (ws.congr restSV2.wr) (by omega : 240 + 4 ≤ size) (by decide) ptrV2
    currentV2 stepV2 widthV2 (rfl : modulusOffset w = compareOffset w + productBytes w)) ?_
  rintro t ⟨_, _, _, _, memT, restT⟩
  refine ⟨?_, restSV2.trans (restT.mono (by simp))⟩
  rw [memT, memV2, memR, memQ, memZ, memV, memU]
  rfl

end VG.Proof.Bignum.Arm
