import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the tag
copied out to `tag` and the restore compute `encryptWith` (RFC 8452 §4) of
the arguments (`seal_wp`), given that the tag input computed with GHASH is
the RFC's (`Proof.GcmSiv.Words.tagInputG`, related to it by
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`). Each
piece writes only `mutR`, which keeps the slots, our caller's registers,
the return address, the key schedule, the nonce and the additional data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.X86 (w64 SavedAt GcmImpl covers_left)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

/-- The end: our caller's registers restored. -/
theorem exit_ok {p : Prm} (L : Lay p) {s₀ t : State} (E : Env p t) (hsp : p.SP = s₀.gpr .esp)
    (hs : SavedAt t.mem p.W s₀) (hret : t.mem.readW (w64 p.SP) 32 = s₀.mem.readW (w64 p.SP) 32) :
    WP isa (.block Impl.AesGcm.X86.restore) t fun s' => abiPreserved s₀ s' ∧ s'.mem = t.mem ∧
      s'.gpr .eax = t.gpr .eax :=
  WP.mono (Proof.AesGcm.X86.exit_ok E.ebp (by rw [E.esp, hsp]) (covers_left E.perm.w2560)
    (by have := L.ww; omega) hs (by rw [← hsp]; exact hret)) fun _ ⟨a, m, r, _⟩ => ⟨a, m, r⟩

/-- What the entry wrote is in our caller's registers and the slots. -/
theorem entered_mut {s : State} {p : Prm} {s₁ : State} (L : Lay p) (En : Entered s p s₁) :
    s₁.mem.readW (w64 p.SP) 32 = s.mem.readW (w64 p.SP) 32 ∧
      Spec.GcmSiv.ctxCiph s₁.mem (w64 p.K) p.R = Spec.GcmSiv.ctxCiph s.mem (w64 p.K) p.R ∧
      bytesAt s₁.mem (w64 p.N) 12 = bytesAt s.mem (w64 p.N) 12 ∧
      bytesAt s₁.mem (w64 p.A) p.al = bytesAt s.mem (w64 p.A) p.al ∧
      bytesAt s₁.mem (w64 p.D) p.n = bytesAt s.mem (w64 p.D) p.n ∧
      bytesAt s₁.mem (w64 p.W) 16 = bytesAt s.mem (w64 p.W) 16 := by
  have f := En.frame
  have d : ∀ {P : Addr} {k : Nat}, (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 128, 48⟩ : Region)], (⟨P, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  refine ⟨Proof.AesGcm.X86.ret_kept f (d L.retW), ?_, Proof.AesGcm.X86.bytesAt_frame f (d L.n_w) (by decide),
    Proof.AesGcm.X86.bytesAt_frame f (d L.a_w) (by have := L.al32; omega),
    Proof.AesGcm.X86.bytesAt_frame f (d L.d_w) (by have := L.n32; omega),
    Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := p.W) (a := 0) (n := 16) (d := 128) (k := 48) (.inl (by decide)) (by decide)
        (by decide)) (by decide)⟩
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame f (d (L.k_w.sub_left (Region.sub_prefix L.rounds_le)))
    (by have := L.rounds_le; omega)]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (hs : sealPre s) :
    WP isa («seal» v.callees) s fun s' => abiPreserved s s' ∧ sealX86.post s s' := by
  have h := onePre_seal hs
  have tW : Covers [⟨w64 (prmOf s).T, 16⟩] s.wr := covers_of_mem (by rw [hs.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have L := lay_of h
  have hRb := L.rounds_le
  have hn := L.n32
  refine WP.seq (WP.mono (entry_ok h) fun s₁ En => ?_)
  obtain ⟨ret₁, hK₁, n₁, a₁, d₁, -⟩ := entered_mut L En
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L En.env) fun s₂ Ky => ?_)
  have f₂ := frame_toMut Ky.frame (inMut_keyR _)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  have f₃ := frame_toMut Po.frame (inMut_polyR _)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  have f₄ := frame_toMut Tg.frame (inMut_tagWr _ (by decide))
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  have f₅ := frame_toMut Cr.frame (inMut_cryR _)
  have f₂₅ := (f₂.trans f₃).trans (f₄.trans f₅)
  -- The tag copied out.
  have tW₅ : Covers [⟨w64 (prmOf s).T, 16⟩] s₅.wr := by rw [Cr.wr, Tg.wr, Po.wr, Ky.wr, En.wr]; exact tW
  refine WP.seq (WP.mono (tagOut_ok L Cr.env tW₅) fun s₆ ⟨tg₆, f₆, bp₆, sp₆, _, rd₆, wr₆⟩ => ?_)
  have E₆ := Cr.env.tag L bp₆ sp₆ rd₆ wr₆ f₆
  have sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (SavedAt.mut L f₂₅ En.saved).frame f₆ (w_t L (d := 128) (k := 16) (by decide))
  have rT : ∀ q ∈ [(⟨w64 (prmOf s).T, 16⟩ : Region)], (⟨w64 (prmOf s).SP, 4⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.retT
  have ret₆ : s₆.mem.readW (w64 (prmOf s).SP) 32 = s.mem.readW (w64 (prmOf s).SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept f₆ rT, ret_mut L f₂₅, ret₁]
  have d₆ : bytesAt s₆.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.t_d.symm) (by omega)
  -- `restore`.
  refine WP.mono (exit_ok L E₆ rfl sv₆ ret₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
      (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)
      (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al) =
    (bytesAt s'.mem (w64 (prmOf s).D) (prmOf s).n, bytesAt s'.mem (w64 (prmOf s).T) 16)
  rw [hm, d₆, tg₆]
  -- What the pieces read.
  have n₂ : bytesAt s₂.mem (w64 (prmOf s).N) 12 = bytesAt s.mem (w64 (prmOf s).N) 12 := by
    rw [nonce_mut L f₂, n₁]
  have a₂ : bytesAt s₂.mem (w64 (prmOf s).A) (prmOf s).al = bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al := by
    rw [aad_mut L f₂, a₁]
  have dk₂ : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).D, (prmOf s).n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  have d₂ : bytesAt s₂.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame dk₂ (by omega), d₁]
  have d₄ : bytesAt s₄.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.bd.symm) (by omega),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.d_w' (by decide)
        · exact absorbR_buf L.d_w L.bd r hr) (by omega), d₂]
  have dS : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 (prmOf s).W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' → Spec.GcmSiv.ctxCiph m' (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
        Spec.GcmSiv.ctxCiph m (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := fun hd m m' hf => by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    refine dS (fun r hr => ?_) Po.frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    refine (dS (fun r hr => ?_) Tg.frame).trans key₃
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  have t₅ : bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 := by
    refine Proof.AesGcm.X86.bytesAt_frame Cr.frame (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.d_w' (by decide)).symm
    · exact (L.bw' (by decide)).symm
  rw [BitVec.add_zero] at t₅
  have tg := Tg.out
  rw [BitVec.add_zero] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.X86
