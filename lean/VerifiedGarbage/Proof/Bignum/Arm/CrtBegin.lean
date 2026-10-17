module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Enter private CRT computation with immutable arguments and three valid layouts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_begin_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (buffers : CrtBuffers g bs s) (stack : CrtCallStack g s)
    (ptr : s.gpr .r0 = g.base) (count : s.gpr .r6 = BitVec.ofNat 32 g.length)
    (saved : s.mem.readW (State.addr s.sp) 32 = g.base)
    (modulusPtr : s.mem.readW (off (State.addr s.sp) 8) 32 = g.modulus)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true) :
    WP isa CrtFn.prepare s fun t => CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      Frame (crtMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have mainSub : (⟨State.addr g.base, 8 * workspaceWords g.words⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace buffers.workspace buffers.storageFits (by simp [crtRegions])
  have source : SavedOperand g.base g.modulus (workspaceWords g.words) g.length 8 12 (bs 0) s :=
    ⟨stack.nowrap, ⟨stack.read (by decide), stack.read (by decide)⟩, stack.separate.sub_right mainSub, by decide, by decide,
      modulusPtr, stack.count, buffers.source 0, (buffers.sourceSeparate 0).sub_right mainSub⟩
  have input : CrtPrepareInput g.base g.modulus g.size g.words g.length (bs 0) s :=
    ⟨buffers.workspace, buffers.context, buffers.storageFits, source, stack.separate, buffers.sourceSeparate 0,
      by simpa only [off, BitVec.add_zero] using stack.read (d := 0) (by decide),
      stack.write (by decide), saved, ptr, count, buffers.lengthValid, rfl⟩
  refine WP.mono (crt_prepare_ok s input) ?_
  rintro t ⟨loaded, mainSaved, modulus, frame, rest⟩
  have frame' : Frame (crtMutable g s.sp) s.mem t.mem := frame.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [crtMutable])
  exact ⟨⟨buffers.after_mutable frame' rest, stack.after_frame frame' rest,
    loaded.main, loaded.p.toCrtLayoutState, loaded.q.toCrtLayoutState, modulus, valid, mainSaved⟩,
    loaded.ready, frame', rest⟩

end VG.Proof.Bignum.Arm
