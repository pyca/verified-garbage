import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Fn

/-!
# AES-GCM-SIV on AArch64: `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, and
the restore compute `encryptWith` (RFC 8452 §4) of the arguments
(`seal_wp`), given that the tag input computed with GHASH is the RFC's
(`Proof.GcmSiv.Words.tagInputG`, related to it in `Verified.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.AesGcm.AArch64.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (h : onePre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  have L := lay_of h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok h) fun s₁ ⟨E₁, sv₁, f₁, rd₁, wr₁⟩ => ?_)
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L E₁) fun s₂ Ky => ?_)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  -- `restore`.
  have sv₅ : SavedAt s₅.mem (prmOf s).W s :=
    ((((sv₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L))
  refine WP.mono (exit_ok (s₀ := s) Cr.env.x19 Cr.env.sp Cr.env.w2560R sv₅) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R) (Spec.GcmSiv.keyLen (prmOf s).R)
      (bytesAt s.mem (prmOf s).N 12) (bytesAt s.mem (prmOf s).D (prmOf s).n) (bytesAt s.mem (prmOf s).A (prmOf s).al) =
    (bytesAt s'.mem (prmOf s).D (prmOf s).n, bytesAt s'.mem (prmOf s).W 16)
  rw [hm]
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (prmOf s).K (prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := bytesAt_keep f₁ (by disj_tac L) (by decide)
  have n₂ : bytesAt s₂.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₂ : bytesAt s₂.mem (prmOf s).A (prmOf s).al = bytesAt s.mem (prmOf s).A (prmOf s).al := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega), bytesAt_keep f₁ (by disj_tac L) (by omega)]
  have d₄ : bytesAt s₄.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by omega), bytesAt_keep Po.frame (by disj_tac L) (by omega), d₂]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem ((prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R :=
    ciph_keep Po.frame (by disj_tac L) hRb
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    rw [ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  have t₅ : bytesAt s₅.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  rw [L.w0] at t₅
  have tg := Tg.out
  rw [L.w0] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.AArch64
