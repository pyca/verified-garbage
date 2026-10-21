module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! # Scratch-local steps preserve the encoded primes and public exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem outs_scratch_frame {B : Addr} {Z : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (size : Z ≤ 2 ^ 64) (O : Outs B rs m m') (fit : ∀ r ∈ rs, r.1 + r.2 ≤ Z) :
    Frame [⟨B, Z⟩] m m' := by
  have outside : Outside B 0 Z m m' := by
    intro a ha
    apply O a
    intro r hr
    have H := fit r hr
    omega
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    VG.Proof.Bignum.outside_frame outside (by simpa only [Nat.zero_add] using size)

theorem stage_scratch_frame {s : State} {B : Addr} {Z n : Nat} {js : List Nat} {m m' : Mem}
    (h : Ws s B Z n 32) (indices : ∀ j ∈ js, j < 32) (O : Outs B (stageRanges n js) m m') :
    Frame [⟨B, Z⟩] m m' := by
  have head := h.hdr_le
  apply outs_scratch_frame (by have := h.workspace.nowrap; omega) O
  intro r hr
  rcases List.mem_append.mp hr with temp | output
  · simp only [exponentTemps, List.mem_cons, List.not_mem_nil, or_false] at temp
    rcases temp with rfl | rfl
    · unfold kOk hdr at *
      omega
    · exact Nat.le_trans (arr_mono (by decide : 15 ≤ 32)) h.fits
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at output
    obtain ⟨j, hj, rfl⟩ := output
    exact h.arr_fit (indices j hj)

theorem Input.output_preserved {E : Environment} {s : State} {m m' : Mem} {i : Nat}
    (h : Input E s) (hi : i < 7) (F : Frame [E.workspaceRegion] m m') :
    Spec.Rsa.bytesAt m' (E.outputRegion i).base (E.outputRegion i).len =
      Spec.Rsa.bytesAt m (E.outputRegion i).base (E.outputRegion i).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by change E.outputLength i < 2 ^ 64; have H := h.valid.outFit i hi; omega)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h.valid.outputScratch i hi

theorem Input.exponent_preserved {E : Environment} {s : State} {m m' : Mem}
    (h : Input E s) (F : Frame [E.workspaceRegion] m m') :
    Spec.Rsa.bytesAt m' E.exponentRegion.base E.exponentRegion.len =
      Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by change E.exponentLength < 2 ^ 64; have H := h.valid.exponentLength; omega)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h.valid.exponentScratch

end VG.Proof.RsaKeyGen.X86.Key
