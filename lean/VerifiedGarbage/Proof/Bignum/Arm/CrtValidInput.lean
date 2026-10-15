module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtValid
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckedState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Inputs to the private RSA path after checking the public modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtValidInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  buffers : CrtBuffers g bs s
  stack : CrtCallStack g s
  ptr : s.gpr .r0 = g.base
  count : s.gpr .r6 = BitVec.ofNat 32 g.length
  saved : s.mem.readW (State.addr s.sp) 32 = g.base
  modulusPtr : s.mem.readW (off (State.addr s.sp) 8) 32 = g.modulus
  valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true

theorem CrtValidInput.prepare_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtValidInput g bs s) : CrtPrepareInput g.base g.modulus g.size g.words g.length (bs 0) s := by
  have mainSub : (⟨State.addr g.base, 8 * workspaceWords g.words⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])
  have source : SavedOperand g.base g.modulus (workspaceWords g.words) g.length 8 12 (bs 0) s :=
    ⟨h.stack.nowrap, ⟨h.stack.read (by decide), h.stack.read (by decide)⟩, h.stack.separate.sub_right mainSub, by decide, by decide,
      h.modulusPtr, h.stack.count, h.buffers.source 0, (h.buffers.sourceSeparate 0).sub_right mainSub⟩
  exact ⟨h.buffers.workspace, h.buffers.context, h.buffers.storageFits, source, h.stack.separate, h.buffers.sourceSeparate 0,
    by simpa only [off, BitVec.add_zero] using h.stack.read (d := 0) (by decide),
    h.stack.write (by decide), h.saved, h.ptr, h.count, h.buffers.lengthValid, rfl⟩

theorem crt_begin_selected (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtValidInput g bs s) : WP isa CrtFn.prepare s (CrtSelected g bs g.base) :=
  (crt_begin_ok s h.buffers h.stack h.ptr h.count h.saved h.modulusPtr h.valid).mono (fun _ j => ⟨j.1, j.2.1⟩)

theorem crt_validate_checked (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtSelected g bs g.base s) : WP isa CrtFn.validate s (CrtCheckedState g bs) :=
  (crt_validateStage_ok s h.1 h.2).mono (fun _ j => ⟨⟨j.1, j.2.1⟩, j.2.2.1, j.2.2.2.1, j.2.2.2.2.1⟩)

end VG.Proof.Bignum.Arm
