module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptDCopy
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptDClear
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Bytes

/-! # The fixed-width private exponent is its given bytes after zero padding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem paddedD_bytes {g : Geometry} {bs : Fin 9 → List Byte} {s t : State}
    (h : Context g bs s)
    (zero : Spec.Rsa.bytesAt s.mem (g.scratch sD g.length).base g.length = List.replicate g.length 0)
    (frame : Frame [g.scratch (dOffset g) g.privateLength] s.mem t.mem)
    (copied : Spec.Rsa.bytesAt t.mem (g.scratch (dOffset g) g.privateLength).base g.privateLength = bs 2) :
    Spec.Rsa.bytesAt t.mem (g.scratch sD g.length).base g.length =
      List.replicate (g.length - g.privateLength) 0 ++ bs 2 := by
  have len := h.valid.privateFits
  have max := h.valid.maxLength
  have fit : dOffset g + g.privateLength ≤ 8448 := by unfold dOffset sD; omega
  have prefixFit : sD + (g.length - g.privateLength) ≤ 8448 := by unfold sD; omega
  have sep : (g.scratch sD (g.length - g.privateLength)).Disjoint (g.scratch (dOffset g) g.privateLength) :=
    scratchDisjoint g (Or.inl (by unfold dOffset; omega)) prefixFit fit
  have prefixBytes : Spec.Rsa.bytesAt t.mem (g.scratch sD g.length).base (g.length - g.privateLength) =
      List.replicate (g.length - g.privateLength) 0 := by
    have same : Spec.Rsa.bytesAt t.mem (g.scratch sD g.length).base (g.length - g.privateLength) =
        Spec.Rsa.bytesAt s.mem (g.scratch sD g.length).base (g.length - g.privateLength) := by
      apply VG.Proof.Rsa.rsa_bytes_frame frame (by omega)
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact sep
    rw [same, VG.Proof.RsaPkcs1Enc.bytesAt_take s.mem _ (Nat.sub_le _ _), zero]
    simp only [List.take_replicate, Nat.min_eq_left (Nat.sub_le _ _)]
  have tail : (g.scratch sD g.length).base + BitVec.ofNat 64 (g.length - g.privateLength) =
      (g.scratch (dOffset g) g.privateLength).base := by
    change byteAddr g.workspace + BitVec.ofNat 64 sD + BitVec.ofNat 64 (g.length - g.privateLength) = _
    rw [Offset.add_add]
    change byteAddr g.workspace + BitVec.ofNat 64 (sD + (g.length - g.privateLength)) =
      byteAddr g.workspace + BitVec.ofNat 64 (dOffset g)
    rw [show sD + (g.length - g.privateLength) = dOffset g by unfold dOffset; omega]
  calc
    _ = Spec.Rsa.bytesAt t.mem (g.scratch sD g.length).base
        ((g.length - g.privateLength) + g.privateLength) := by rw [Nat.sub_add_cancel len]
    _ = _ := VG.Proof.RsaPkcs1Enc.bytesAt_add _ _ _ _
    _ = _ := by rw [prefixBytes, tail, copied]

theorem dCopyAll_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s)
    (zero : Spec.Rsa.bytesAt s.mem (g.scratch sD g.length).base g.length = List.replicate g.length 0) :
    WP isa (.seq (.block dCopy) VG.Impl.Bignum.X86.copyBytes) s fun t => Context g bs t ∧
      Frame [g.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .esi] s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sD g.length).base g.length =
        List.replicate (g.length - g.privateLength) 0 ++ bs 2 := by
  refine WP.seq (WP.mono (dCopy_ok h) ?_)
  rintro u ⟨hu, M, K, dst, src, count⟩
  refine WP.mono (copyD_ok hu src dst count) ?_
  rintro t ⟨ht, F, Kt, bytes⟩
  have fit : dOffset g + g.privateLength ≤ 8448 := by
    have := h.valid.privateFits
    have := h.valid.maxLength
    unfold dOffset sD
    omega
  have Ffull : Frame [g.workspaceRegion] s.mem t.mem := by
    rw [M] at F
    apply F.sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, h.valid.scratchSub fit⟩
  refine ⟨ht, Ffull, K.trans (Kt.mono (by decide)), ?_⟩
  have zu : Spec.Rsa.bytesAt u.mem (g.scratch sD g.length).base g.length = List.replicate g.length 0 := by rw [M]; exact zero
  exact paddedD_bytes hu zu F bytes

end VG.Proof.RsaPkcs1Enc.X86.Dec
