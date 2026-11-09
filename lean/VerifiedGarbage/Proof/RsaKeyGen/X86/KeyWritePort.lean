module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWriteArray
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Output one key component while retaining the remaining output context -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def portResult (g : OutputGeometry) (m : Mem) (accept : Bool) (i : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then num m g.base g.n (outputIndex i) else 0) %
    2 ^ (8 * g.length i)) (g.length i)

def portWrites (g : OutputGeometry) (i : Nat) : List Region :=
  [⟨off g.base (arr g.n (outputIndex i)), S g.n⟩, g.region i]

theorem portFrame_global {g : OutputGeometry} {s : State} {m m' : Mem} {i : Nat}
    (h : OutputInput g s) (hi : i < 7) (F : Frame (portWrites g i) m m') : Frame g.writes m m' := by
  apply F.sub
  intro r hr
  simp only [portWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨g.scratch, List.mem_cons_self,
      Offset.sub_base g.base (h.ws.arr_fit (outputIndex_bound hi))⟩
  · exact ⟨g.region i, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
      fun _ H => H⟩

theorem portFrame_other {g : OutputGeometry} {s : State} {m m' : Mem} {i j : Nat}
    (h : OutputInput g s) (hi : i < 7) (hj : j < 7) (ne : j ≠ i)
    (F : Frame (portWrites g i) m m') :
    Spec.Rsa.bytesAt m' (g.region j).base (g.region j).len =
      Spec.Rsa.bytesAt m (g.region j).base (g.region j).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by change g.length j < 2 ^ 64; have H := h.valid.fit j hj; omega)
  intro r hr
  simp only [portWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.valid.scratchApart j hj).symm.sub_right
      (Offset.sub_base g.base (h.ws.arr_fit (outputIndex_bound hi)))
  · exact h.valid.separate j hj i hi ne

end VG.Proof.RsaKeyGen.X86.Key
