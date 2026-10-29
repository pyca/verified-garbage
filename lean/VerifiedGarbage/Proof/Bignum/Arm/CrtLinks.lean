module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtLayout
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Bignum.Arm.CrtLinkStep
import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! # All CRT buffer links come from public lengths and addresses -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtLinksMemory.lean`, which only this module imported.
section

/-! # Exact header writes for the five CRT buffer links -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

def crtLinkMem (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) : Mem :=
  ((((m.writeW (off base 224) p).writeW (off base 228) q).writeW (off base 232) prod).writeW
    (off base 236) cmp).writeW (off base 240) pad

theorem crtLinkMem_ok (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) :
    let m' := crtLinkMem m base p q prod cmp pad
    m'.readW (off base 224) 32 = p ∧ m'.readW (off base 228) 32 = q ∧
    m'.readW (off base 232) 32 = prod ∧ m'.readW (off base 236) 32 = cmp ∧
    m'.readW (off base 240) 32 = pad ∧ Outside base 224 20 m m' := by
  let m1 := m.writeW (off base 224) p
  let m2 := m1.writeW (off base 228) q
  let m3 := m2.writeW (off base 232) prod
  let m4 := m3.writeW (off base 236) cmp
  have a := writeW32_outside m base (d := 224) p (by decide)
  have b := writeW32_outside m1 base (d := 228) q (by decide)
  have c := writeW32_outside m2 base (d := 232) prod (by decide)
  have d := writeW32_outside m3 base (d := 236) cmp (by decide)
  have e := writeW32_outside m4 base (d := 240) pad (by decide)
  change (m4.writeW (off base 240) pad).readW (off base 224) 32 = p ∧ _
  refine ⟨?_, ?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _, ?_⟩
  · rw [outside_read32 e (d := 224) (by decide) (by decide),
      outside_read32 d (d := 224) (by decide) (by decide),
      outside_read32 c (d := 224) (by decide) (by decide),
      outside_read32 b (d := 224) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 240) pad).readW (off base 228) 32 = _
    rw [outside_read32 e (d := 228) (by decide) (by decide),
      outside_read32 d (d := 228) (by decide) (by decide),
      outside_read32 c (d := 228) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 240) pad).readW (off base 232) 32 = _
    rw [outside_read32 e (d := 232) (by decide) (by decide), outside_read32 d (d := 232) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 240) pad).readW (off base 236) 32 = _
    rw [outside_read32 e (d := 236) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact (a.mono (by decide) (by decide)).trans ((b.mono (by decide) (by decide)).trans
      ((c.mono (by decide) (by decide)).trans ((d.mono (by decide) (by decide)).trans (e.mono (by decide) (by decide)))))

end VG.Proof.Bignum.Arm
end

end

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
  have ptrU := (restU.gpr .r0 (by decide)).trans ptr
  rw [WP.seq_iff]
  refine WP.mono (crt_linkStep_ok u (ws.congr restU.wr) (by omega : 224 + 4 ≤ size) (by decide) ptrU
    (currentU.trans (BitVec.add_zero base).symm)
    stepU widthU (by simp [pOffset] : pOffset w = 0 + stride w)) ?_
  rintro v ⟨ptrV, currentV, stepV, widthV, memV, restV⟩
  have restSV := restU.trans (restV.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (crt_linkStep_ok v (ws.congr restSV.wr) (by omega : 228 + 4 ≤ size) (by decide) ptrV
    currentV stepV widthV (by simp only [qOffset, pOffset]; omega : qOffset w = pOffset w + stride w)) ?_
  rintro z ⟨ptrZ, currentZ, stepZ, widthZ, memZ, restZ⟩
  have restSZ := restSV.trans (restZ.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (crt_linkStep_ok z (ws.congr restSZ.wr) (by omega : 232 + 4 ≤ size) (by decide) ptrZ
    currentZ stepZ widthZ (by simp only [productOffset, qOffset]; omega : productOffset w = qOffset w + stride w)) ?_
  rintro q ⟨ptrQ, currentQ, _, widthQ, memQ, restQ⟩
  have restSQ := restSZ.trans (restQ.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (crt_productStride_ok q widthQ) ?_
  rintro r ⟨stepR, memR, restR⟩
  have restSR := restSQ.trans (restR.mono (by decide))
  have ptrR := (restR.gpr .r0 (by decide)).trans ptrQ
  have currentR := (restR.gpr .r2 (by decide)).trans currentQ
  have widthR := (restR.gpr .r7 (by decide)).trans widthQ
  rw [WP.seq_iff]
  refine WP.mono (crt_linkStep_ok r (ws.congr restSR.wr) (by omega : 236 + 4 ≤ size) (by decide) ptrR
    currentR stepR widthR (rfl : compareOffset w = productOffset w + productBytes w)) ?_
  rintro v2 ⟨ptrV2, currentV2, stepV2, widthV2, memV2, restV2⟩
  have restSV2 := restSR.trans (restV2.mono (by decide))
  refine WP.mono (crt_linkStep_ok v2 (ws.congr restSV2.wr) (by omega : 240 + 4 ≤ size) (by decide) ptrV2
    currentV2 stepV2 widthV2 (rfl : modulusOffset w = compareOffset w + productBytes w)) ?_
  rintro t ⟨_, _, _, _, memT, restT⟩
  refine ⟨?_, restSV2.trans (restT.mono (by decide))⟩
  rw [memT, memV2, memR, memQ, memZ, memV, memU]
  rfl

end VG.Proof.Bignum.Arm
