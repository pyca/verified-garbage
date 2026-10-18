module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT

/-! # Seed hashing's trace depends only on its public location and width -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem seedHash_ct {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Calls.StreamOK G1.stream) (h256 : Calls.StreamOK G256.stream)
    {F S rp : Addr} {len : Nat} (hlen : len < 2 ^ 64) :
    RelCT isa (LR F S (fun W s => LabAt s F S W rp len))
      (Impl.Dsa.AArch64.Generation.seedHash G1 G256) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.seedHash
  refine (lr_wp (X' := fun W s => LabAt s F S W rp len ∧ s.gpr .x0 = BitVec.ofNat 64 len - 20)
    (lr_taint [] (by taint_decide) nopin) ?_).seq ?_
  · intro s V W L R A
    exact WP.mono (hashTest_ok L R A.hll) fun t ⟨hx, hm, hk⟩ =>
      ⟨V, W, L.congr hk.sp hk.wr (by rw [hm]), hm ▸ R,
        A.congr hk.rd hk.wr rfl rfl, hx⟩
  · refine RelCT.ite ?_ ?_ ?_
    · intro a b h
      obtain ⟨⟨_, _, _, _, _, ha⟩, ⟨_, _, _, _, _, hb⟩⟩ := h
      simp only [eval, State.read, ha, hb]
    · apply (hashLabel_tr h1 hlen (Or.inl rfl) (X := fun W s => LabAt s F S W rp len)
        (fun _ _ h => h)).mono
      · intro a b h
        obtain ⟨⟨Va, Wa, La, Ra, Aa, _⟩, ⟨Vb, Wb, Lb, Rb, Ab, _⟩⟩ := h.1
        exact ⟨⟨Va, Wa, La, Ra, Aa⟩, ⟨Vb, Wb, Lb, Rb, Ab⟩⟩
      · intro _ _ _
        trivial
    · apply (hashLabel_tr h256 hlen (Or.inl rfl) (X := fun W s => LabAt s F S W rp len)
        (fun _ _ h => h)).mono
      · intro a b h
        obtain ⟨⟨Va, Wa, La, Ra, Aa, _⟩, ⟨Vb, Wb, Lb, Rb, Ab, _⟩⟩ := h.1
        exact ⟨⟨Va, Wa, La, Ra, Aa⟩, ⟨Vb, Wb, Lb, Rb, Ab⟩⟩
      · intro _ _ _
        trivial

end VG.Proof.Dsa.AArch64.Generation
