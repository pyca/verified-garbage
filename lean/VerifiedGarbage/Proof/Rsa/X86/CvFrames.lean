module

public import VerifiedGarbage.Proof.Rsa.X86.CvLoad

/-! # Scratch frames preserve CRT input bytes and saved registers -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

theorem Inputs.keepOutside {g : CallGeometry} {s : State} {m : Mem} {js ds : List Nat}
    (h : Inputs g s) (keep : Keep g.base (2 * g.n) js ds s.mem m)
    (hj : ∀ j ∈ js, j < nArr) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    Outside g.base 0 g.size s.mem m := by
  intro a ha
  apply keep.out (fun j hj' => h.ws.arr_fit (hj j hj')) (fun d hd' => Nat.le_trans (hd d hd') h.ws.hdr_le)
  omega

theorem Inputs.keepBody {g : CallGeometry} {s : State} {m : Mem} {js ds : List Nat}
    (h : Inputs g s) (keep : Keep g.base (2 * g.n) js ds s.mem m)
    (hj : ∀ j ∈ js, j < nArr) (hd : ∀ d ∈ ds, 16 ≤ d ∧ d + 4 ≤ hdr) :
    Outside g.base 16 (g.size - 16) s.mem m := by
  have header := h.ws.hdr_le
  intro a ha
  apply keep a
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, jmem, rfl⟩ | ⟨d, dmem, rfl⟩
  · have bound := h.ws.arr_fit (hj j jmem)
    have lower : hdr ≤ arr (2 * g.n) j := Nat.le_add_right _ _
    dsimp only
    unfold hdr at header lower
    omega
  · have bound := hd d dmem
    dsimp only
    unfold hdr at header bound
    omega

def inputBytes (g : CallGeometry) (m : Mem) (i : Fin 4) : List Byte :=
  Spec.Rsa.bytesAt m (g.buffer (6 + 2 * i.val)).base (g.buffer (6 + 2 * i.val)).len

theorem Inputs.inputFrame {g : CallGeometry} {s : State} {m : Mem} (h : Inputs g s)
    (frame : Outside g.base 0 g.size s.mem m) (i : Fin 4) : inputBytes g m i = inputBytes g s.mem i := by
  exact scratch_bytes frame (by have := h.inputBound i; have := h.upper; omega)
    (h.inputApart i _ (by simp [CallGeometry.writes]))

end VG.Proof.Rsa.X86.CrtValues
