module

public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductState

import VerifiedGarbage.Proof.Bignum.Arm.WideProductRow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Bignum.Arm.HeaderControl
import VerifiedGarbage.Proof.Framework.Arm.Exec
/-! # The product loop maintains its exact prefix product and public counters -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/WideProductMemory.lean`, which only this module imported.
section

/-! # Product-loop controls change only their dedicated header slots -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem wideProductNext_memory {m m' : Mem} {base : Addr} {ap op : BitVec 32} {c : Nat}
    (mem : m' = ((m.writeW (off base 128) (ap + 4)).writeW
      (off base 136) (op + 4)).writeW (off base 140) (BitVec.ofNat 32 (c - 1))) :
    Outside base 128 16 m m' ∧
      m'.readW (off base 128) 32 = ap + 4 ∧
      m'.readW (off base 136) 32 = op + 4 ∧
      m'.readW (off base 140) 32 = BitVec.ofNat 32 (c - 1) ∧
      m'.readW (off base 132) 32 = m.readW (off base 132) 32 ∧
      m'.readW (off base 144) 32 = m.readW (off base 144) 32 := by
  have a := writeW32_outside m base (d := 128) (ap + 4) (by decide)
  have b := writeW32_outside (m.writeW (off base 128) (ap + 4)) base (d := 136) (op + 4) (by decide)
  have c' := writeW32_outside ((m.writeW (off base 128) (ap + 4)).writeW (off base 136) (op + 4))
    base (d := 140) (BitVec.ofNat 32 (c - 1)) (by decide)
  have outside : Outside base 128 16 m m' := by
    rw [mem]
    exact (a.mono (by decide) (by decide)).trans
      ((b.mono (by decide) (by decide)).trans (c'.mono (by decide) (by decide)))
  refine ⟨outside, ?_, ?_, ?_, ?_, outside_read32 outside (by decide) (by decide)⟩
  · rw [mem, outside_read32 c' (d := 128) (by decide) (by decide),
      outside_read32 b (d := 128) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem, outside_read32 c' (d := 136) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem, Mem.readW_writeW_self32]
  · rw [mem, outside_read32 c' (d := 132) (by decide) (by decide),
      outside_read32 b (d := 132) (by decide) (by decide),
      outside_read32 a (d := 132) (by decide) (by decide)]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/HeaderIncrement.lean`, which only this module imported.
section

/-! # Increment a fixed-offset workspace pointer or counter -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_imm dpVal)

theorem headerIncrement_ok (s : State) {base : BitVec 32} {size d k : Nat} {value : BitVec 32}
    (ws : Workspace s base size) (fits : d + 4 ≤ size) (hd : d < 4096) (hk : encodable k = true)
    (ptr : s.gpr .r0 = base) (word : s.mem.readW (off (State.addr base) d) 32 = value) :
    WP isa (.block (headerIncrement d k)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) d) (value + BitVec.ofNat 32 k) ∧ Rest [.r1] s t := by
  have address : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold headerIncrement
  refine wp_ldr (a := off (State.addr base) d) hd address (ws.read fits) fun u h => ?_
  refine wp_dp (op2_imm hk) fun v j => ?_
  refine wp_str (a := off (State.addr base) d) hd
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide)]; exact address)
    (by rw [j.wr, h.wr]; exact ws.write fits) fun t l => WP.block_nil ?_
  refine ⟨?_, (h.rest (by simp)).trans ((j.rest (by simp)).trans (l.rest _))⟩
  rw [l.mem, j.mem, h.mem, j.gpr, dpVal, h.gpr, word, BitVec.natCast_eq_ofNat]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/HeaderDecrement.lean`, which only this module imported.
section

/-! # Decrement a fixed-offset public loop counter -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str wp_subs op2_reg op2_imm dpVal ofNat_beq_zero)

theorem headerDecrement_ok (s : State) {base : BitVec 32} {size c d : Nat}
    (ws : Workspace s base size) (fits : d + 4 ≤ size) (hd : d < 4096) (ptr : s.gpr .r0 = base)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (count : s.mem.readW (off (State.addr base) d) 32 = BitVec.ofNat 32 c) :
    WP isa (.block (headerDecrement d)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) d) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  have addr : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by omega)
  unfold headerDecrement
  refine wp_ldr (a := off (State.addr base) d) hd addr (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  refine wp_str_z (a := off (State.addr base) d) hd
    (by rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact addr)
    (by rw [u2.wr, u1.wr]; exact ws.write (by omega)) fun t u3 z3 => WP.block_nil ?_
  have value : s2.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [u2.gpr, u1.gpr, count]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  refine ⟨?_, ?_, (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest _))⟩
  · rw [u3.mem, u2.mem, u1.mem, value]
  · rw [z3, z2, ← u2.gpr, value, ofNat_beq_zero (by omega)]
    simp only [show c - 1 = 0 ↔ c = 1 by omega]


end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/WideProductNext.lean`, which only this module imported.
section

/-! # Advance both product pointers and the public row count -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProductNext_ok (s : State) {base ap op : BitVec 32} {size c : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (ptr : s.gpr .r0 = base)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = ap)
    (oPtr : s.mem.readW (off (State.addr base) 136) 32 = op)
    (count : s.mem.readW (off (State.addr base) 140) 32 = BitVec.ofNat 32 c) :
    WP isa wideProductNext s fun t =>
      t.mem = ((s.mem.writeW (off (State.addr base) 128) (ap + 4)).writeW
        (off (State.addr base) 136) (op + 4)).writeW (off (State.addr base) 140) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  rw [wideProductNext, WP.seq_iff]
  refine WP.mono (headerIncrement_ok s ws (by omega) (by decide) (by decide) ptr aPtr) ?_
  rintro u ⟨memU, restU⟩
  have outsideU : Outside (State.addr base) 128 4 s.mem u.mem := by
    rw [memU]; exact writeW32_outside s.mem (State.addr base) (d := 128) (ap + 4) (by decide)
  have oPtrU := (outside_read32 outsideU (d := 136) (by decide) (by decide)).trans oPtr
  have countU := (outside_read32 outsideU (d := 140) (by decide) (by decide)).trans count
  rw [WP.seq_iff]
  refine WP.mono (headerIncrement_ok u (ws.congr restU.wr) (by omega) (by decide) (by decide)
    ((restU.gpr .r0 (by simp)).trans ptr) oPtrU) ?_
  rintro v ⟨memV, restV⟩
  have outsideV : Outside (State.addr base) 136 4 u.mem v.mem := by
    rw [memV]; exact writeW32_outside u.mem (State.addr base) (d := 136) (op + 4) (by decide)
  have countV := (outside_read32 outsideV (d := 140) (by decide) (by decide)).trans countU
  refine WP.mono (headerDecrement_ok v (ws.congr (restV.wr.trans restU.wr)) (by omega) (by decide)
    ((restV.gpr .r0 (by simp)).trans ((restU.gpr .r0 (by simp)).trans ptr)) hc hc' countV) ?_
  rintro t ⟨memT, zero, restT⟩
  exact ⟨by rw [memT, memV, memU]; rfl, zero, restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProductBody_ok (s : State) {s0 : State} {base : BitVec 32} {size o a b m n i : Nat}
    (ctx : WideProductCtx s0 base size o a b m n) (h : WideProductInv s0 base o a b m n i s) (hi : i < m) :
    WP isa wideProductBody s fun t => WideProductInv s0 base o a b m n (i + 1) t ∧
      t.z = decide (i + 1 = m) := by
  have nowrap := ctx.workspace.nowrap
  have outFits := ctx.outFits
  have oHeader := ctx.oHeader
  have aFits := ctx.aFits
  rw [wideProductBody, WP.seq_iff]
  refine WP.mono (wideProductRow_ok s ctx h hi) ?_
  rintro u ⟨value, outside, ptr, rest⟩
  have header (d : Nat) (hd : d + 4 ≤ 148) :
      u.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32 :=
    outside_read32 outside (by omega) (by omega)
  have outsideRow : Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s.mem u.mem :=
    Outs.of_outside (outside.mono (o' := o) (n' := 4 * (m + n + 2)) (by omega) (by omega)) (by simp)
  have restU := h.rest.trans rest
  refine WP.mono (wideProductNext_ok u (ctx.workspace.congr restU.wr) ctx.headerFit ptr
    (by omega) (by omega) ((header 128 (by decide)).trans h.aPtr)
    ((header 136 (by decide)).trans h.oPtr) ((header 140 (by decide)).trans h.count)) ?_
  rintro t ⟨mem, zero, restT⟩
  obtain ⟨outsideT, aPtr, oPtr, count, bPtr, width⟩ := wideProductNext_memory mem
  have outsideAll := h.outside.trans (outsideRow.trans (Outs.of_outside outsideT (by simp)))
  refine ⟨⟨by omega, (restT.gpr .r0 (by decide)).trans ptr, ?_, ?_, ?_, ?_, ?_, outsideAll, ?_,
    restU.trans (restT.mono (by decide))⟩, ?_⟩
  · rw [aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · exact bPtr.trans ((header 132 (by decide)).trans h.bPtr)
  · rw [oPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count]; congr 1
  · exact width.trans ((header 144 (by decide)).trans h.width)
  · rw [outsideT.val32 (d := o) (k := m + n + 2) (by omega) (by omega)]
    exact value
  · rw [zero]; exact decide_eq_decide.mpr (by omega)

end VG.Proof.Bignum.Arm
