module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Scalar loads and stores preserve the recovery stage -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.readSlot (h : KS g s0 A live AW liveW V ls s) {d : Nat} (hd : d ∈ ls) :
    readSrc s (.mem (VG.Impl.Mont.X86.sc d)) = some (BitVec.ofNat 32 (V d)) := by
  have limit := (h.ls_ok d hd).2.1
  have header := h.ws.hdr_le
  rw [readSrc_sc h.ws.workspace (by omega), ← h.sl d hd]
  simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem KS.loadSlot (h : KS g s0 A live AW liveW V ls s) {d : Nat} (hd : d ∈ ls)
    {r : Reg} (hr : r ∈ opRegs) :
    WP isa (.block [.mov r (.mem (VG.Impl.Mont.X86.sc d))]) s fun t =>
      KS g s0 A live AW liveW V ls t ∧ t.gpr r = BitVec.ofNat 32 (V d) ∧ Keeps [r] s t := by
  refine wp_movS (h.readSlot hd) fun t T _ => WP.block_nil ?_
  exact ⟨h.of_rest T.keeps (by simpa using hr) T.mem, T.gpr, T.keeps⟩

theorem KS.storeSlot (h : KS g s0 A live AW liveW V ls s) {d : Nat} (hd : SlotOk d) (r : Reg) :
    WP isa (.block [.store (VG.Impl.Mont.X86.sc d) r]) s fun t =>
      KS g s0 A live AW liveW (upd V d (s.gpr r).toNat) (d :: ls) t ∧
      t.zf = s.zf ∧ Keeps [] s t := by
  have header := h.ws.hdr_le
  have limit := hd.2.1
  refine wp_storeS (h.ws.workspace.ea (by omega)) (h.ws.workspace.write (by omega))
    fun t T => WP.block_nil ?_
  have frame : Keep g.B g.w [] [d] s.mem t.mem := by
    rw [T.mem]
    exact Keep.of_slot (writeW32_outside _ _ _ (by unfold hdr at limit; omega)) (by simp)
  exact ⟨h.slot1 frame hd ((T.keeps []).mono (by decide)) (by
    unfold slot; rw [T.mem, w32_write_self]), T.zf, T.keeps []⟩

end
end VG.Proof.Rsa.X86.Recover
