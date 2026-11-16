module

public import VerifiedGarbage.Proof.AesGcmSiv.X86.Seal
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Contract
import VerifiedGarbage.Proof.Aes.X86.AesNi.Context

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the received tag
copied to `W`, the keys, counter mode on the data from it, POLYVAL of the
result and the tag input, its tag at `W + 240`, the comparison, the mask and
the restore compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.X86 (w64 SavedAt GcmImpl covers_left length_bytesAt)

theorem decrypt_eq (hti : TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-- Counter mode after the keys keeps what POLYVAL starts from. -/
theorem keys_crypt {p : Prm} (L : Lay p) {σ s₂ s₃ : State} (Ky : KeysPost p σ s₂) (Cr : CryptPost p s₂ s₃) :
    Spec.Gcm.blockAt s₃.mem (w64 p.W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16)) ∧
    Spec.Gcm.blockAt s₃.mem (w64 p.W + BitVec.ofNat 64 80) = 0 ∧
    bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 := by
  obtain dCr : ∀ {d : Nat}, 16 ≤ d → d + 16 ≤ 96 → ∀ r ∈ cryR p,
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact (L.d_w' (by omega_using [h₂])).symm
    · exact (L.bw' (by omega_using [h₂])).symm
  obtain a₃ : bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86.bytesAt_frame Cr.frame (dCr (by decide) (by decide)) (by decide)
  refine ⟨?_, ?_, a₃⟩
  · rw [Proof.AesGcm.X86.blockAt_frame Cr.frame (dCr (by decide) (by decide)), Ky.hkey, a₃]
  · rw [Proof.AesGcm.X86.blockAt_frame Cr.frame (dCr (by decide) (by decide)), Ky.acc]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (hs : openPre s) :
    WP isa («open» v.callees) s fun s' => abiPreserved s s' ∧ openX86.post s s' := by
  obtain h := onePre_open hs
  obtain L := lay_of h
  have hRb := L.rounds_le
  have hn := L.n32
  refine WP.seq (WP.mono (entry_ok h) fun s₀ En => ?_)
  obtain ⟨ret₀, hK₀, n₀, a₀, d₀, -⟩ := entered_mut L En
  -- The received tag.
  refine WP.seq (WP.mono (recvTag_ok L En.env) fun s₁ ⟨E₁, tg₁, fr₁, _, _⟩ => ?_)
  obtain fr₁' : Frame (mutR (prmOf s)) s₀.mem s₁.mem := frame_toMut fr₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    simpa using inMut_w (prmOf s) (d := 0) (k := 16) (.inl (by decide))
  obtain ret₁ : s₁.mem.readW (w64 (prmOf s).SP) 32 = s.mem.readW (w64 (prmOf s).SP) 32 := by
    rw [ret_mut L fr₁', ret₀]
  obtain hK₁ := (ciph_mut L fr₁').trans hK₀
  obtain n₁ := (nonce_mut L fr₁').trans n₀
  obtain a₁ := (aad_mut L fr₁').trans a₀
  obtain d₁ : bytesAt s₁.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n :=
    (Proof.AesGcm.X86.bytesAt_frame fr₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.d_w.sub_right (Region.sub_prefix (by decide)))
      (by omega_using [hn])).trans d₀
  obtain tag₁ : bytesAt s₁.mem (w64 (prmOf s).W) 16 = bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [tg₁]
    exact Proof.AesGcm.X86.bytesAt_frame En.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.t_w.sub_right (Lay.wSub (by decide))) (by decide)
  obtain sv₁ := SavedAt.mut L fr₁' En.saved
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L E₁) fun s₂ Ky => ?_)
  obtain f₂ := frame_toMut Ky.frame (inMut_keyR _)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok v L Ky.env) fun s₃ Cr => ?_)
  obtain f₃ := frame_toMut Cr.frame (inMut_cryR _)
  obtain ⟨hG₃, hY₃, a₃⟩ := keys_crypt L Ky Cr
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Cr.env hG₃ hY₃) fun s₄ Po => ?_)
  obtain f₄ := frame_toMut Po.frame (inMut_polyR _)
  -- Its tag at `W + 240`.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 240) (by decide)) fun s₅ Tg => ?_)
  obtain f₅ := frame_toMut Tg.frame (inMut_tagWr _ (by decide))
  -- The comparison.
  obtain ⟨s₆, run₆, ax₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := cmp_ok L Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env (prmOf s) s₆ := Tg.env.keep (by rw [bp₆, Tg.env.ebp]) (by rw [sp₆, Tg.env.esp]) rd₆ wr₆ hm₆
  obtain ax₆' : s₆.gpr .eax = BitVec.ofNat 32 (if decide (bytesAt s₅.mem (w64 (prmOf s).W) 16 =
      bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 240) 16) then 1 else 0) := by
    rw [ax₆]; simp only [okVal, decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ ax₆') fun s₇ Mk => ?_)
  obtain fM : Frame (mutR (prmOf s)) s₆.mem s₇.mem := by
    rw [Mk.mem]
    exact frame_toMut (writeBytes_frame _ _ _ (by
      split <;> simp only [length_bytesAt, Spec.GcmSiv.zeros, List.length_replicate] <;>
        exact Region.contains_self _ _) : Frame [⟨w64 (prmOf s).D, (prmOf s).n⟩] _ _) fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact inMut_d _
  obtain f₂₇ : Frame (mutR (prmOf s)) s₁.mem s₇.mem := ((f₂.trans f₃).trans (f₄.trans f₅)).trans (hm₆ ▸ fM)
  -- The restore.
  refine WP.mono (exit_ok L Mk.env rfl (SavedAt.mut L f₂₇ sv₁) (by rw [ret_mut L f₂₇, ret₁]))
    fun s' ⟨ga, hm, hax⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  obtain n₃ : bytesAt s₃.mem (w64 (prmOf s).N) 12 = bytesAt s.mem (w64 (prmOf s).N) 12 := by
    rw [nonce_mut L (f₂.trans f₃), n₁]
  obtain a₃' : bytesAt s₃.mem (w64 (prmOf s).A) (prmOf s).al = bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al := by
    rw [aad_mut L (f₂.trans f₃), a₁]
  obtain dK : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).D, (prmOf s).n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  obtain d₂ : bytesAt s₂.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame dK (by omega_using [hn]), d₁]
  obtain tK : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).W + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain tag₂ : bytesAt s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame tK (by decide), BitVec.add_zero, tag₁]
  obtain tag₅ : bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm) (by decide),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm) (by decide),
      Proof.AesGcm.X86.bytesAt_frame Cr.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.d_w' (by decide)).symm
        · exact (L.bw' (by decide)).symm) (by decide), tag₂]
  rw [BitVec.add_zero] at tag₂ tag₅
  obtain dS : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 (prmOf s).W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' → Spec.GcmSiv.ctxCiph m' (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
        Spec.GcmSiv.ctxCiph m (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := fun hd m m' hf => by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])]
  obtain ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    rw [dS (fun r hr => ?_) Po.frame, ciph_cryR L Cr.frame]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain d₅ : bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s₃.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.bd.symm) (by omega_using [hn]),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.d_w' (by decide)
        · exact absorbR_buf L.d_w L.bd r hr) (by omega_using [hn])]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.mem
  rw [hm₆, tg, tag₅] at md
  obtain ax : s'.gpr .eax = s₆.gpr .eax := by rw [hax, Mk.eax]
  rw [ax₆', tg, tag₅] at ax
  show openPost (openResult s) s' (w64 (prmOf s).D) (prmOf s).n
  obtain hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (w64 (prmOf s).N) 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
            (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) =
          bytesAt s.mem (w64 (prmOf s).T) 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
          (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  obtain hD₅ : bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n = Spec.GcmSiv.ctr
      (Spec.GcmSiv.aes (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)).2)
      (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16)) (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) := by
    rw [d₅, pt₃]
  obtain hl : ∀ c : Bool, (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n
      else Spec.GcmSiv.zeros (prmOf s).n).length = (prmOf s).n := fun c => by
    cases c <;> simp [length_bytesAt, Spec.GcmSiv.zeros]
  obtain mD : ∀ c : Bool, bytesAt (writeBytes s₅.mem (w64 (prmOf s).D) (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n
      else Spec.GcmSiv.zeros (prmOf s).n)) (w64 (prmOf s).D) (prmOf s).n =
      if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n else Spec.GcmSiv.zeros (prmOf s).n := fun c => by
    obtain e := Proof.AesGcm.X86.bytesAt_writeBytes_self s₅.mem (w64 (prmOf s).D)
      (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n else Spec.GcmSiv.zeros (prmOf s).n)
      (by rw [hl]; omega_using [hn])
    rwa [hl] at e
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12) = dk at ax hdec md hD₅
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (w64 (prmOf s).N) 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
        (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) =
      bytesAt s.mem (w64 (prmOf s).T) 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax, ite_eq_left (decide_eq_true hc.symm)]; rfl
    · rw [hm, md, mD, hD₅, ite_eq_left (decide_eq_true hc.symm)]
  · have hc' : ¬bytesAt s.mem (w64 (prmOf s).T) 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1
        (bytesAt s.mem (w64 (prmOf s).N) 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
          (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) :=
      Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax, ite_eq_right (fun h => hc' (of_decide_eq_true h))]; rfl
    · rw [hm, md, mD, ite_eq_right (fun h => hc' (of_decide_eq_true h))]

end VG.Proof.AesGcmSiv.X86
