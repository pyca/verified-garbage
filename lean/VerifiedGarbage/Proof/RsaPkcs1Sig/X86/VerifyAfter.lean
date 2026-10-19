module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyTail

/-! # Padding checks retain the RSA result and the saved status -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify

def checkedResult (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : BitVec 32 :=
  match encodeId g.hash (bs 2) g.length with
  | none => 0
  | some em => BitVec.ofNat 32 (decide (Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length = em)).toNat &&& s.gpr .eax

theorem Context.em1Status {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    (⟨byteAddr g.em1, g.length⟩ : Region).Disjoint (localRegion g statusOffset 4) := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint _ (Or.inr (by decide : statusOffset + 4 ≤ em1Offset))
    (by have := h.valid.maxLength; simp only [em1Offset]; omega) (by decide)

theorem Context.statusEm2 {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    (localRegion g statusOffset 4).Disjoint ⟨byteAddr g.em2, g.length⟩ := by
  rw [Geometry.em2, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint _ (Or.inl (by decide : statusOffset + 4 ≤ em2Offset)) (by decide)
    (by have := h.valid.maxLength; simp only [em2Offset]; omega)

theorem afterPub_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    WP isa afterPub s fun t => Context g bs t ∧ t.gpr .eax = checkedResult g bs s ∧
      Frame [g.innerRegion] s.mem t.mem ∧ Keeps clobbers s t := by
  unfold afterPub
  refine WP.seq (WP.mono (save_ok h) ?_)
  rintro a ⟨ha, saved, Fa, Ka⟩
  refine WP.seq (WP.mono (encArgs_ok ha) ?_)
  rintro b ⟨hb, Mb, Kb, dst, len, hash, src, count⟩
  refine WP.seq (WP.mono (encoding_ok hb dst len hash src count) ?_)
  rintro c ⟨hc, Fc, Kc, enc⟩
  refine WP.mono (tail_ok hc enc) ?_
  rintro t ⟨ht, Mt, Kt, value⟩
  have first : Spec.Rsa.bytesAt a.mem (byteAddr g.em1) g.length =
      Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length :=
    VG.Proof.Rsa.rsa_bytes_frame Fa (by have := h.valid.maxLength; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.em1Status)
  have next : Spec.Rsa.bytesAt c.mem (byteAddr g.em1) g.length =
      Spec.Rsa.bytesAt b.mem (byteAddr g.em1) g.length :=
    VG.Proof.Rsa.rsa_bytes_frame Fc (by have := h.valid.maxLength; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.encodingsSeparate)
  have status : savedStatus g c = savedStatus g b :=
    Fc.readW (r := localRegion g statusOffset 4) (Region.contains_self _ _)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.statusEm2) (by decide)
  have statusS : savedStatus g c = s.gpr .eax := by
    rw [status, savedStatus, Mb]
    exact saved
  have bytesS : Spec.Rsa.bytesAt c.mem (byteAddr g.em1) g.length =
      Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length := by rw [next, Mb, first]
  refine ⟨ht, ?_, ?_, (Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans
    ((Kc.mono (by decide)).trans Kt))⟩
  · rw [value]
    unfold paddingResult checkedResult
    rw [bytesS, statusS]
    rfl
  · have fa : Frame [g.innerRegion] s.mem a.mem := Fa.sub (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, localSub (by decide)⟩)
    have fc : Frame [g.innerRegion] a.mem c.mem := by
      rw [Mb] at Fc
      apply Fc.sub
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, h.em2Sub⟩
    rw [Mt]
    exact fa.trans fc

end VG.Proof.RsaPkcs1Sig.X86.Ver
