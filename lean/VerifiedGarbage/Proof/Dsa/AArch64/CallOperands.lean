module

public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
public import VerifiedGarbage.Proof.Dsa.AArch64.LocalCallFrame
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import Batteries.Logic

/-! # Reading and preserving operands across the DSA arithmetic schedule -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem CallResult.localFrame {L : ExecutionLayout} {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult L side d value s t) (hend : d + side.length L ≤ usedBytes) :
    Frm L.base (localCallRanges side.offset (side.words L) d (side.length L)) s.mem t.mem := by
  have hi := (side.bounds L).2.2.2.2.1
  have hn := h.ready.scratch.nowrap
  have : activeBytes ≤ usedBytes := by decide
  exact callFrame_local h.frame (by omega) (by omega)

theorem CallResult.fields {L : ExecutionLayout} {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult L side d value s t) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes)
    (f : Field) : word t.mem L.base f.offset = word s.mem L.base f.offset := by
  have ho : pWorkspace ≤ side.offset := by cases side <;> decide
  exact localCall_field (h.localFrame hend) ho (Nat.le_trans (by decide) hd) f

theorem CallResult.pointer {L : ExecutionLayout} {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult L side d value s t) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes)
    (p : Pointer) : pointerValue t.mem L.base p = pointerValue s.mem L.base p := by
  cases p with
  | input f => exact h.fields hd hend f
  | «local» _ => rfl
  | signatureS => exact congrArg₂ (· + ·) (h.fields hd hend .signature) (h.fields hd hend .qLen)

theorem CallResult.preserve {L : ExecutionLayout} {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult L side d value s t) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes)
    {a : Operand} {bs : List Byte} (hs : OperandBytes s L.base activeBytes a bs)
    (hsep : ∀ i < bs.length, ∀ j < side.length L,
      pointerValue s.mem L.base a.pointer + BitVec.ofNat 64 i ≠ off L.base d + BitVec.ofNat 64 j) :
    OperandBytes t L.base activeBytes a bs := by
  refine ⟨(h.fields hd hend a.length).trans hs.length, ?_⟩
  rw [h.pointer hd hend a.pointer]
  exact callFrame_source h.frame h.keep (by decide) (side.bounds L).2.2.2.2.1 (by decide) hs.source hsep

theorem CallResult.output {L : ExecutionLayout} {side : ModulusSide} {d value : Nat} {s t : State}
    (h : CallResult L side d value s t) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    OperandBytes t L.base activeBytes ⟨.local d, side.lengthField⟩ (Spec.Dsa.encodeBE (side.length L) value) := by
  apply output_operand (h.ready.length side) h.bytes _ (h.ready.local_out hd hend)
  intro i hi
  rcases h.ready.local_write hend i hi with ⟨region, hr, hc⟩
  exact ⟨region, List.mem_append_right _ hr, hc⟩

theorem operand_bytesAt {s : State} {B : Addr} {Z : Nat} {a : Operand} {bs : List Byte}
    (h : OperandBytes s B Z a bs) :
    Spec.Rsa.bytesAt s.mem (pointerValue s.mem B a.pointer) bs.length = bs := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro i hi hj
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.source.val i hj

end VG.Proof.Dsa.AArch64
