module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacStart
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfUpdate
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfFinalize

/-! # HMAC calls preserve the PRF key and previously produced blocks -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem macInit_bytes {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d n : Nat}
    (h : Context g bs s) (lower : 192 ≤ d) (upper : d + n ≤ sHash)
    (F : Frame ((macInitWr g ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (g.scratch d n).base n = Spec.Rsa.bytesAt s.mem (g.scratch d n).base n := by
  have fit : d + n ≤ 8448 := by unfold sHash at upper; omega
  apply VG.Proof.Rsa.rsa_bytes_frame F (by omega)
  intro r hr
  simp only [List.mem_append, macInitWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl) | rfl) | rfl
  · exact scratchDisjoint g (Or.inr (by unfold sSt; omega)) fit (by decide)
  · exact scratchDisjoint g (Or.inr (by unfold sOuter; omega)) fit (by decide)
  · exact scratchDisjoint g (Or.inl upper) fit (by decide)
  · exact (h.argsScratch (by decide : 20 ≤ 160) fit).symm
  · exact (h.calleeScratch fit).symm
  · exact (h.argsScratch (by decide : 80 ≤ 160) fit).symm

theorem macUpdate_bytes {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d n : Nat}
    (h : Context g bs s) (lower : 96 ≤ d) (upper : d + n ≤ sHash)
    (F : Frame ((updateWr g ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (g.scratch d n).base n = Spec.Rsa.bytesAt s.mem (g.scratch d n).base n := by
  have fit : d + n ≤ 8448 := by unfold sHash at upper; omega
  apply VG.Proof.Rsa.rsa_bytes_frame F (by omega)
  intro r hr
  simp only [List.mem_append, updateWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | rfl) | rfl
  · exact scratchDisjoint g (Or.inr (by unfold sSt; omega)) fit (by decide)
  · exact scratchDisjoint g (Or.inl upper) fit (by decide)
  · exact (h.argsScratch (by decide : 24 ≤ 160) fit).symm
  · exact (h.calleeScratch fit).symm
  · exact (h.argsScratch (by decide : 80 ≤ 160) fit).symm

theorem macFinalize_bytes {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d n dst : Nat}
    (h : Context g bs s) (lower : 96 ≤ d) (upper : d + n ≤ sHash)
    (dstUpper : dst + 32 ≤ sHash) (apart : d + n ≤ dst ∨ dst + 32 ≤ d)
    (F : Frame ((macFinalizeWr g dst ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (g.scratch d n).base n = Spec.Rsa.bytesAt s.mem (g.scratch d n).base n := by
  have fit : d + n ≤ 8448 := by unfold sHash at upper; omega
  have dstFit : dst + 32 ≤ 8448 := by unfold sHash at dstUpper; omega
  apply VG.Proof.Rsa.rsa_bytes_frame F (by omega)
  intro r hr
  simp only [List.mem_append, macFinalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl) | rfl) | rfl
  · exact scratchDisjoint g (Or.inr (by unfold sSt; omega)) fit (by decide)
  · exact scratchDisjoint g apart fit dstFit
  · exact scratchDisjoint g (Or.inl upper) fit (by decide)
  · exact (h.argsScratch (by decide : 24 ≤ 160) fit).symm
  · exact (h.calleeScratch fit).symm
  · exact (h.argsScratch (by decide : 80 ≤ 160) fit).symm

end VG.Proof.RsaPkcs1Enc.X86.Dec
