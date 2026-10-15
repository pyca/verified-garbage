module

public import VerifiedGarbage.Proof.Bignum.Arm.WideProductRow
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The product loop maintains its exact prefix product and public counters -/

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
  refine ⟨⟨by omega, (restT.gpr .r0 (by simp)).trans ptr, ?_, ?_, ?_, ?_, ?_, outsideAll, ?_,
    restU.trans (restT.mono (by simp [roundClobbers]))⟩, ?_⟩
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
