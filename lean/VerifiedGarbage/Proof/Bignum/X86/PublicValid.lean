module

public import VerifiedGarbage.Proof.Bignum.X86.PublicSized
public import VerifiedGarbage.Proof.Bignum.X86.PublicControls
public import VerifiedGarbage.Proof.Bignum.X86.PublicDispatch

/-! # A validated public key reaches the correctly sized RSA operation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

theorem publicValid_ok {s : State} {base : Addr} {bytes len e : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true)
    (he : e < 2 ^ 33) (lo : s.gpr .ebx = BitVec.ofNat 32 (e % 2 ^ 32))
    (hi : s.gpr .edx = BitVec.ofNat 32 (exponentHigh e)) :
    WP isa PublicFn.valid s fun t => PublicResult base bytes len args s.mem e t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have space := h.space
  have nw := h.scratch.nowrap
  unfold PublicFn.valid
  refine WP.seq (WP.mono (saveExponent_ok h.scratch (by omega) he lo hi)
    fun v ⟨E, O, K⟩ => ?_)
  have hv := h.keep K (by decide) (by decide) (O.mono (by omega) (by omega))
  refine WP.seq (WP.mono (widthArgs_ok h.upper (by rw [← h.nLen]; exact (hv.stack 3 (by decide)).readSrc))
    fun w ⟨Width, M, T⟩ => ?_)
  refine publicDispatch_ok PublicFn.widths (publicWidths_member h.lower h.upper) ?_ Width ?_
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
    have := List.mem_range.mp hi
    omega
  · intro u Ku Mu
    have Ksu : Keeps [.eax] s u := ((K.mono (by decide)).trans T).trans (Ku.mono (by decide))
    have Osu : Outside base 128 8 s.mem u.mem := by rw [Mu, M]; exact O
    have Osu' : Outside base 0 bytes s.mem u.mem := Osu.mono (by omega) (by omega)
    have hu := h.keep Ksu (by decide) (by decide) Osu'
    have ns := scratch_bytes Osu' (by have := h.upper; omega) h.nApart
    have xs := scratch_bytes Osu' (by have := h.upper; omega) h.inApart
    refine WP.mono (publicSized_ok (e := e) hu (by rw [ns]; exact valid) (by rw [Mu, M, E]))
      fun t ⟨R, B, F, Kt⟩ => ?_
    refine ⟨⟨?_, ?_, ?_⟩, (Ksu.mono (by decide)).trans Kt⟩
    · simpa only [ns, xs] using R
    · simpa only [ns, xs] using B
    · have Osaved : Outside base 16 (bytes - 16) s.mem u.mem := Osu.mono (by omega) (by omega)
      exact ((outside_frame Osaved (by omega)).mono (by simp)).trans F

end VG.Proof.Bignum.X86.PublicContext
