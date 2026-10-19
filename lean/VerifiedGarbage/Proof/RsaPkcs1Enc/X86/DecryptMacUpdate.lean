module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacState
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashUpdate

/-! # Absorb the ciphertext or one PRF message into an initialized HMAC -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem macRepr_args {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {key text : List Byte}
    (h : Context g bs s) (F : Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem) (repr : MacRepr g key text s) :
    MacRepr g key text t := by
  constructor
  · apply repr_frame F ?_ repr.1
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.argsScratch (by decide : 80 ≤ 160) (by decide : sSt + 96 ≤ 8448)).symm
  · apply repr_frame F ?_ repr.2
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.argsScratch (by decide : 80 ≤ 160) (by decide : sOuter + 96 ≤ 8448)).symm

theorem macUpdate_call (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {data : BitVec 32} {len : Nat} {key : List Byte}
    (h : Context g bs s) (a : Arguments g (updateValues g data len 64) 6 s)
    (dataFit : data.toNat + len ≤ 2 ^ 32) (lengthBound : len < 2 ^ 32)
    (dataState : (⟨byteAddr data, len⟩ : Region).Disjoint (g.scratch sSt 96))
    (dataScratch : (⟨byteAddr data, len⟩ : Region).Disjoint (g.scratch sHash 608))
    (calleeData : g.calleeRegion.Disjoint ⟨byteAddr data, len⟩)
    (dataArgs : (⟨byteAddr data, len⟩ : Region).Disjoint ⟨byteAddr g.stack, 24⟩)
    (dataRead : InRegions (s.rd ++ s.wr) (byteAddr data) len)
    (keyFits : key.length ≤ 64) (repr : MacRepr g key [] s) :
    WP isa (.call (hashFns v).updN (hashFns v).updC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Frame (updateWr g ++ [g.calleeRegion]) s.mem t.mem ∧
      Keeps callClobbers s t ∧ MacRepr g key (Spec.Rsa.bytesAt s.mem (byteAddr data) len) t := by
  have inner : Spec.Sha256.Repr s.mem (g.scratch sSt 96).base
      (Spec.Hmac.xorPad (macKey key) Spec.Hmac.ipad) := by
    simpa only [List.append_nil] using repr.1
  have count : (Spec.Hmac.xorPad (macKey key) Spec.Hmac.ipad).length = 64 := by
    rw [Spec.Hmac.xorPad, List.length_map]
    exact macKey_length keyFits
  refine WP.mono (shaUpdate_call v h a dataFit lengthBound (by decide : 64 < 2 ^ 32)
    dataState dataScratch calleeData dataArgs dataRead inner count) ?_
  rintro t ⟨ht, F, Ffine, K, innerT⟩
  refine ⟨ht, F, Ffine, K, innerT, ?_⟩
  apply repr_frame Ffine ?_ repr.2
  intro r hr
  simp only [List.mem_append, updateWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact scratchDisjoint g (Or.inr (by decide : sSt + 96 ≤ sOuter)) (by decide : sOuter + 96 ≤ 8448) (by decide : sSt + 96 ≤ 8448)
  · exact scratchDisjoint g (Or.inl (by decide : sOuter + 96 ≤ sHash)) (by decide : sOuter + 96 ≤ 8448) (by decide : sHash + 608 ≤ 8448)
  · exact (h.argsScratch (by decide : 24 ≤ 160) (by decide : sOuter + 96 ≤ 8448)).symm
  · exact (h.calleeScratch (by decide : sOuter + 96 ≤ 8448)).symm

end VG.Proof.RsaPkcs1Enc.X86.Dec
