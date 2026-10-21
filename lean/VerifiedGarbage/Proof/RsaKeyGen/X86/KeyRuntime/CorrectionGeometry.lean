module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.WordRanges

/-! # The fixed 128-bit correction bank fits every native RSA workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def correctionScratch : List (Nat × Nat) := [(kProduct, 28), (hdr, 96)]

theorem correction_preserves_exponent {m m' : Mem} {B : Addr} (O : Outs B correctionScratch m m') :
    val32 m' B kEv 2 = val32 m B kEv 2 := by
  apply O.val32 _ (by decide)
  intro r hr
  simp only [correctionScratch, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> decide

theorem correction_scratch_arr {m m' : Mem} {B : Addr} {j : Nat} (hj : j < 4)
    (O : Outside B (arr 4 j) (S 4) m m') : Outs B correctionScratch m m' := by
  intro x hx
  apply O x
  have H := hx (hdr, 96) (by simp [correctionScratch])
  simp only [arr, S, hdr] at H ⊢
  omega

theorem correction_scratch_keep {m m' : Mem} {B : Addr} {js : List Nat}
    (indices : ∀ j ∈ js, j < 4) (O : Keep B 4 js [] m m') : Outs B correctionScratch m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at hr
  obtain ⟨j, hj, rfl⟩ := hr
  refine ⟨(hdr, 96), by simp [correctionScratch], ?_, ?_⟩
  · unfold arr
    omega
  · have bound := indices j hj
    simp only [arr, S, hdr]
    omega

theorem correction_scratch_outside {m m' : Mem} {B : Addr} {out len : Nat}
    (low : hdr ≤ out) (high : out + len ≤ hdr + 96) (O : Outside B out len m m') :
    Outs B correctionScratch m m' := by
  intro x hx
  apply O x
  have H := hx (hdr, 96) (by simp [correctionScratch])
  simp only at H
  omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
