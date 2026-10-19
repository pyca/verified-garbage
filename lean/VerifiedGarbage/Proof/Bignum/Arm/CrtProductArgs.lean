module

import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyChildPointer
import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyHeaderPointer
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductCount
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductMemory
public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Block

/-! # Prepare the verified full-width factor multiplication -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_productArgs_ok (s : State) {base p q out : BitVec 32} {size cp cq w : Nat} {coefficient : Bool}
    (ws : Workspace s base size) (fit : 236 ≤ size) (hq : 256 ≤ cq)
    (pFit : cp + productOperandSlot coefficient + 4 ≤ size) (qFit : cq + 68 ≤ size) (ptr : s.gpr .r0 = base)
    (pLink : s.mem.readW (off (State.addr base) 224) 32 = base + BitVec.ofNat 32 cp)
    (qLink : s.mem.readW (off (State.addr base) 228) 32 = base + BitVec.ofNat 32 cq)
    (pArray : s.mem.readW (off (State.addr base) (cp + productOperandSlot coefficient)) 32 = p)
    (qArray : s.mem.readW (off (State.addr base) (cq + 64)) 32 = q)
    (product : s.mem.readW (off (State.addr base) 232) 32 = out)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (productArgs coefficient) s fun t =>
      t.mem = crtProductMem s.mem (State.addr base) p q out (BitVec.ofNat 32 (2 * w)) (BitVec.ofNat 32 (2 * w)) ∧
      Rest [.r1] s t := by
  rw [productArgs, WP.seq_iff]
  refine WP.mono (crt_copyChildPointer_ok s ws (by omega : 224 + 4 ≤ size) (by omega : 128 + 4 ≤ size)
    (by decide) (by decide) (by cases coefficient <;> decide) pFit ptr pLink pArray) ?_
  rintro u ⟨memU, restU⟩
  have outsideU := writeW32_outside s.mem (State.addr base) (d := 128) p (by decide)
  rw [← memU] at outsideU
  rw [WP.seq_iff]
  refine WP.mono (crt_copyChildPointer_ok (value := q) u (ws.congr restU.wr) (by omega : 228 + 4 ≤ size) (by omega : 132 + 4 ≤ size)
    (by decide) (by decide) (by decide) qFit ((restU.gpr .r0 (by simp)).trans ptr)
    (by rw [outside_read32 outsideU (d := 228) (by decide) (by decide)]; exact qLink)
    (by rw [outside_read32 outsideU (d := cq + 64) (by omega) (by have := ws.nowrap; omega)]; exact qArray)) ?_
  rintro v ⟨memV, restV⟩
  have outsideV := writeW32_outside u.mem (State.addr base) (d := 132) q (by decide)
  rw [← memV] at outsideV
  have restSV := restU.trans restV
  rw [WP.seq_iff]
  refine WP.mono (crt_copyHeaderPointer_ok (value := out) v (ws.congr restSV.wr) (by omega : 232 + 4 ≤ size) (by omega : 136 + 4 ≤ size)
    (by decide) (by decide) ((restSV.gpr .r0 (by simp)).trans ptr)
    (by rw [outside_read32 outsideV (d := 232) (by decide) (by decide),
            outside_read32 outsideU (d := 232) (by decide) (by decide)]; exact product)) ?_
  rintro z ⟨memZ, restZ⟩
  have outsideZ := writeW32_outside v.mem (State.addr base) (d := 136) out (by decide)
  rw [← memZ] at outsideZ
  have restSZ := restSV.trans restZ
  refine WP.mono (crt_productCount_ok (w := w) z (ws.congr restSZ.wr) (by omega) ((restSZ.gpr .r0 (by simp)).trans ptr)
    (by rw [outside_read32 outsideZ (d := 48) (by decide) (by decide),
            outside_read32 outsideV (d := 48) (by decide) (by decide),
            outside_read32 outsideU (d := 48) (by decide) (by decide)]; exact count)) ?_
  rintro t ⟨memT, restT⟩
  refine ⟨?_, restSZ.trans restT⟩
  rw [memT, memZ, memV, memU]
  rfl

end VG.Proof.Bignum.Arm
