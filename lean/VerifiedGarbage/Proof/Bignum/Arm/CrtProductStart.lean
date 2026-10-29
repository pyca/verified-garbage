module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState

import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyChildPointer
import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyHeaderPointer
import VerifiedGarbage.Proof.Framework.Block
/-! # Product arguments establish the full schoolbook-loop invariant -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductCount.lean`, which only this module imported.
section

/-! # Two native words represent each shared 64-bit RSA limb -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_reg dpVal)

theorem crt_productCount_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block productCount) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 140) (BitVec.ofNat 32 (2 * w))).writeW
        (off (State.addr base) 144) (BitVec.ofNat 32 (2 * w)) ∧ Rest [.r1] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ size) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold productCount
  refine wp_ldr (a := off (State.addr base) 48) (by decide) (addr 48 (by omega)) (ws.read (by omega)) fun u a => ?_
  refine wp_dp (op2_reg _ _) fun v b => ?_
  have doubled : v.gpr .r1 = BitVec.ofNat 32 (2 * w) := by
    rw [b.gpr, dpVal, a.gpr, count, ← BitVec.ofNat_add, show w + w = 2 * w by omega]
  refine wp_str (a := off (State.addr base) 140) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 140 (by omega))
    (by rw [b.wr, a.wr]; exact ws.write (by omega)) fun z c => ?_
  have restC : Rest [] v z := c.rest []
  refine wp_str (a := off (State.addr base) 144) (by decide)
    (by rw [restC.gpr .r0 (by simp), b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 144 (by omega))
    (by rw [restC.wr, b.wr, a.wr]; exact ws.write (by omega)) fun t d => WP.block_nil ?_
  refine ⟨?_, (a.rest (by simp)).trans ((b.rest (by simp)).trans ((restC.mono (by simp)).trans (d.rest _)))⟩
  rw [d.mem, restC.gpr .r1 (by simp), c.mem, doubled, b.mem, a.mem]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductMemory.lean`, which only this module imported.
section

/-! # Exact header writes for the factor-product loop controls -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

def crtProductMem (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) : Mem :=
  ((((m.writeW (off base 128) p).writeW (off base 132) q).writeW (off base 136) prod).writeW
    (off base 140) cmp).writeW (off base 144) pad

theorem crtProductMem_ok (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) :
    let m' := crtProductMem m base p q prod cmp pad
    m'.readW (off base 128) 32 = p ∧ m'.readW (off base 132) 32 = q ∧
    m'.readW (off base 136) 32 = prod ∧ m'.readW (off base 140) 32 = cmp ∧
    m'.readW (off base 144) 32 = pad ∧ Outside base 128 20 m m' := by
  let m1 := m.writeW (off base 128) p
  let m2 := m1.writeW (off base 132) q
  let m3 := m2.writeW (off base 136) prod
  let m4 := m3.writeW (off base 140) cmp
  have a := writeW32_outside m base (d := 128) p (by decide)
  have b := writeW32_outside m1 base (d := 132) q (by decide)
  have c := writeW32_outside m2 base (d := 136) prod (by decide)
  have d := writeW32_outside m3 base (d := 140) cmp (by decide)
  have e := writeW32_outside m4 base (d := 144) pad (by decide)
  change (m4.writeW (off base 144) pad).readW (off base 128) 32 = p ∧ _
  refine ⟨?_, ?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _, ?_⟩
  · rw [outside_read32 e (d := 128) (by decide) (by decide),
      outside_read32 d (d := 128) (by decide) (by decide),
      outside_read32 c (d := 128) (by decide) (by decide),
      outside_read32 b (d := 128) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 132) 32 = _
    rw [outside_read32 e (d := 132) (by decide) (by decide),
      outside_read32 d (d := 132) (by decide) (by decide),
      outside_read32 c (d := 132) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 136) 32 = _
    rw [outside_read32 e (d := 136) (by decide) (by decide), outside_read32 d (d := 136) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 140) 32 = _
    rw [outside_read32 e (d := 140) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact (a.mono (by decide) (by decide)).trans ((b.mono (by decide) (by decide)).trans
      ((c.mono (by decide) (by decide)).trans ((d.mono (by decide) (by decide)).trans (e.mono (by decide) (by decide)))))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductArgs.lean`, which only this module imported.
section

/-! # Prepare the verified full-width factor multiplication -/

section

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
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtProductStart (base : BitVec 32) (size o a b w : Nat) (s : State) : Prop where
  context : WideProductCtx s base size o a b (2 * w) (2 * w)
  initial : WideProductInv s base o a b (2 * w) (2 * w) 0 s

theorem crt_productArgs_ready (s : State) {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool}
    (h : CrtProductInput base size o a b cp cq w s coefficient)
    (zero : val32 s.mem (State.addr base) o (2 * w + 2 * w + 2) = 0) :
    WP isa (productArgs coefficient) s fun t => CrtProductStart base size o a b w t ∧
      Outside (State.addr base) 128 20 s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  have outFit := h.outFits
  have beforeP := h.pBeforeOut
  have beforeQ := h.qBeforeOut
  refine WP.mono (crt_productArgs_ok s h.workspace h.parentFit h.qHeader (by omega) (by omega)
    h.ptr h.pLink h.qLink h.pArray h.qArray h.product h.count) ?_
  rintro t ⟨memT, rest⟩
  have result := crtProductMem_ok s.mem (State.addr base)
    (base + BitVec.ofNat 32 a) (base + BitVec.ofNat 32 b) (base + BitVec.ofNat 32 o)
    (BitVec.ofNat 32 (2 * w)) (BitVec.ofNat 32 (2 * w))
  dsimp only at result
  rw [← memT] at result
  obtain ⟨p, q, out, count, width, outside⟩ := result
  have frame := outside_workspace outside (size := size) h.headerFit
  have ctx := h.toWideProductCtx.after_frame rest frame
  have zeroT : val32 t.mem (State.addr base) o (2 * w + 2 * w + 2) = 0 := by
    rw [outside.val32 (by have := h.oHeader; omega) (by have := h.workspace.nowrap; omega), zero]
  refine ⟨⟨ctx, ?_⟩, outside, frame, rest⟩
  refine ⟨by omega, (rest.gpr .r0 (by simp)).trans h.ptr, ?_, q, ?_, ?_, width,
    Outs.refl _ _ _, ?_, Rest.refl _ _⟩
  · simpa only [Nat.mul_zero, Nat.add_zero] using p
  · simpa only [Nat.mul_zero, Nat.add_zero] using out
  · simpa only [Nat.sub_zero] using count
  · simp only [val32, Nat.zero_mul]; exact zeroT

end VG.Proof.Bignum.Arm
