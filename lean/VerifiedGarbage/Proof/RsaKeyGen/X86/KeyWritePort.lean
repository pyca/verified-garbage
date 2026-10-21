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

theorem writePort_ok {g : OutputGeometry} {s : State} {i : Nat} (h : OutputInput g s) (hi : i < 7)
    (zero : num s.mem g.base g.n aZero = 0) (accept : Bool)
    (mask : slot s.mem g.base kOk = if accept then 1 else 0) :
    WP isa (writePort g.n i) s fun t =>
      OutputInput g t ∧ Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = portResult g s.mem accept i ∧
      Frame (portWrites g i) s.mem t.mem ∧
      (∀ d, d + 4 ≤ hdr → slot t.mem g.base d = slot s.mem g.base d) ∧
      (∀ k, k < 32 → k ≠ outputIndex i → num t.mem g.base g.n k = num s.mem g.base g.n k) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have pointer : s.mem.readW (off g.base (8 * i)) 32 = g.pointer i := by
    have H := h.arguments (2 * i) (by omega)
    rw [show 4 * (2 * i) = 8 * i by omega] at H
    exact H
  have length : s.mem.readW (off g.base (8 * i + 4)) 32 = BitVec.ofNat 32 (g.length i) := by
    have H := h.arguments (2 * i + 1) (by omega)
    rw [show 4 * (2 * i + 1) = 8 * i + 4 by omega] at H
    simpa only [OutputGeometry.length, BitVec.ofNat_toNat, BitVec.setWidth_eq] using H
  refine WP.mono (writeArray_ok h.ws (outputIndex_bound hi)
    (by unfold hdr; omega) (by unfold hdr; omega) pointer length
    (h.valid.lengthPositive i hi) (h.valid.lengthBound i hi) (h.valid.fit i hi)
    (h.writable i hi) (h.valid.scratchApart i hi) zero accept mask)
    fun t ⟨ht, value, F, header, other, K⟩ => ?_
  exact ⟨h.after ht K header, value, F, header, other, K⟩

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
