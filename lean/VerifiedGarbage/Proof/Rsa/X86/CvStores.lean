module
public import VerifiedGarbage.Proof.Rsa.X86.CvInputs
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Release all three CRT values under their common acceptance mask -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

theorem storeFrame_body {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 3)
    {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.base (arr (2 * g.n) j), S (2 * g.n)⟩, g.buffer (2 * i.val)] m m') :
    Frame (bodyWrites g) m m' := by
  apply f.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨⟨off g.base 16, g.size - 16⟩, by simp [bodyWrites], Offset.sub g.base ?_ ?_⟩
    · have : hdr ≤ arr (2 * g.n) j := Nat.le_add_right _ _
      unfold hdr at this; omega
    · have := h.ws.arr_fit hj
      have := h.ws.hdr_le
      unfold hdr at this; omega
  · refine ⟨g.buffer (2 * i.val), ?_, fun _ hx => hx⟩
    have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases cases with e | e | e <;> simp [bodyWrites, e]

theorem output_preserved {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i k : Fin 3)
    (ne : k ≠ i) {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.base (arr (2 * g.n) j), S (2 * g.n)⟩, g.buffer (2 * i.val)] m m') :
    Spec.Rsa.bytesAt m' (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len =
      Spec.Rsa.bytesAt m (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame f (by have := h.outputBound k; have := h.upper; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.outputScratch k).sub_right (Offset.sub_base g.base (h.ws.arr_fit hj))
  · exact h.outputSeparate k i ne

def resultBytes (g : CallGeometry) (m : Mem) (accept : Bool) (i : Fin 3) (j : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then num m g.base (2 * g.n) j else 0) %
    2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len

end VG.Proof.Rsa.X86.CrtValues
