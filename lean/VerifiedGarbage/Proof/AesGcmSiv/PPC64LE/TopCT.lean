module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.KeysCT
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.PolyCT
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.CryptCT
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Entry
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Fn
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Seal
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Fn
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.KeysCT
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.PolyCT
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.CryptCT
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Entry
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Fn
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Seal
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Fn
import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp

/-!
# AES-GCM-SIV on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments have the same public values (`args_two`). The entry loads `work`
from the stack, which the taint analysis takes as secret (it reads memory):
the block is split after the load, and the rest runs from `r11` and `r12`,
which hold `work` and the stack pointer in both runs (`entry_rel`). The keys,
POLYVAL, the tag and counter mode are related by `KeysCT.lean`, `PolyCT.lean`
and `CryptCT.lean`, the code between them by the taint analysis (`seal_rel`,
`open_rel`). `open` compares the tags and masks the plaintext without a
branch: whether it succeeds is not leaked.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_ld)
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (wp_addSp)
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_taint ct_of in_off)
open VG.Proof.AesCcm.PPC64LE (Runs Runs.of_wp rel_seqR)
open VG.Spec.Aes (bytesAt)

/-- Two runs with the same public arguments: both from the public values of
the first. -/
theorem args_two {σ₁ σ₂ : State} (A₂ : Args (cxOf σ₂) σ₂) (hq : onePub σ₁ σ₂) : Args (cxOf σ₁) σ₂ := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, -, qa⟩ := hq
  have hcx : cxOf σ₂ = cxOf σ₁ := by simp only [cxOf, q3, q4, q5, q6, q7, q8, q9, q10, qa]
  rw [hcx] at A₂
  exact A₂

/-- `work` and the stack pointer. -/
theorem entryLd_wp {c : Cx} {s : State} (Ar : Args c s) :
    WP isa (.block [.addSp .r12 0, .load .d .r11 .r12 96]) s fun s' =>
      s'.gpr .r11 = c.W ∧ s'.gpr .r12 = s.sp ∧ s'.sp = s.sp := by
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have r12₁ : s₁.gpr .r12 = s.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 0) (by decide) (by decide) (by rw [r12₁]; rfl)
    (by rw [u₁.rd, u₁.wr]; simpa using in_off Ar.argsC (d := 0) (n := 8) (by decide) (by decide))
    fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u₁.mem, ← Ar.w]; rfl, by rw [u₂.other _ (by decide), r12₁],
      by rw [u₂.sp, u₁.sp]⟩

/-- The entry in two runs. -/
theorem entry_rel {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have e : entry = [.addSp .r12 0, .load .d .r11 .r12 96] ++ entry.drop 2 := rfl
  rw [e]
  refine RelCT.block_append (rel_seqR (rel_taint [] hsp (by simp) (by taint_decide))
    (Runs.of_wp (entryLd_wp A₁)) (Runs.of_wp (entryLd_wp A₂)) fun τ₁ τ₂ ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ => ?_)
  refine rel_taint [.r11, .r12] (by rw [c₁, c₂, hsp]) (fun r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂, hsp]

/-- `vg_aes_gcm_siv_seal` in two runs. -/
theorem seal_rel [VG.Proof.Gcm.PPC64LE.GhashLaw] {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) «seal» TT := by
  have L := A₁.lay
  unfold «seal»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  have h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (keys_rel L En.env En'.env h₁) (Runs.of_wp (keys_wp L En.env))
    (Runs.of_wp (keys_wp L En'.env)) fun s₂ t₂ K K' => ?_
  have E₂ := En.env.of_pk K.pk
  have E₂' := En'.env.of_pk K'.pk
  have h₂ : s₂.sp = t₂.sp := by rw [K.pk.sp, K'.pk.sp, h₁]
  refine rel_seqR (polyval_rel L E₂ E₂' h₂) (Runs.of_wp (polyval_wp L E₂ K.hkey K.acc))
    (Runs.of_wp (polyval_wp L E₂' K'.hkey K'.acc)) fun s₃ t₃ P P' => ?_
  have E₃ := E₂.of_pk P.pk
  have E₃' := E₂'.of_pk P'.pk
  have h₃ : s₃.sp = t₃.sp := by rw [P.pk.sp, P'.pk.sp, h₂]
  refine rel_seqR (tag_rel L E₃ E₃' h₃ (o := 0) (.inl rfl)) (Runs.of_wp (tag_wp L E₃ (o := 0) (.inl rfl)))
    (Runs.of_wp (tag_wp L E₃' (o := 0) (.inl rfl))) fun s₄ t₄ T T' => ?_
  have E₄ := E₃.of_pk T.pk
  have E₄' := E₃'.of_pk T'.pk
  have h₄ : s₄.sp = t₄.sp := by rw [T.pk.sp, T'.pk.sp, h₃]
  refine rel_seqR (crypt_rel L E₄ E₄' h₄) (Runs.of_wp (crypt_wp L E₄)) (Runs.of_wp (crypt_wp L E₄'))
    fun s₅ t₅ C C' => ?_
  exact rel_env [] (E₄.of_pk C.pk) (E₄'.of_pk C'.pk) (by rw [C.pk.sp, C'.pk.sp, h₄]) (by simp) ⟨_, by taint_decide⟩

/-- `vg_aes_gcm_siv_open` in two runs. -/
theorem open_rel [VG.Proof.Gcm.PPC64LE.GhashLaw] {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) «open» TT := by
  have L := A₁.lay
  unfold «open»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  have h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (rel_env [] En.env En'.env h₁ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (recv_wp En.env))
    (Runs.of_wp (recv_wp En'.env)) fun s₂ t₂ ⟨pk₂, _⟩ ⟨pk₂', _⟩ => ?_
  have E₂ := En.env.of_pk pk₂
  have E₂' := En'.env.of_pk pk₂'
  have h₂ : s₂.sp = t₂.sp := by rw [pk₂.sp, pk₂'.sp, h₁]
  refine rel_seqR (keys_rel L E₂ E₂' h₂) (Runs.of_wp (keys_wp L E₂)) (Runs.of_wp (keys_wp L E₂'))
    fun s₃ t₃ K K' => ?_
  have E₃ := E₂.of_pk K.pk
  have E₃' := E₂'.of_pk K'.pk
  have h₃ : s₃.sp = t₃.sp := by rw [K.pk.sp, K'.pk.sp, h₂]
  refine rel_seqR (crypt_rel L E₃ E₃' h₃) (Runs.of_wp (crypt_wp L E₃)) (Runs.of_wp (crypt_wp L E₃'))
    fun s₄ t₄ C C' => ?_
  have E₄ := E₃.of_pk C.pk
  have E₄' := E₃'.of_pk C'.pk
  have h₄ : s₄.sp = t₄.sp := by rw [C.pk.sp, C'.pk.sp, h₃]
  -- What POLYVAL needs of the key: as the keys left it.
  have hP : ∀ {s₂ s₃ s₄ : State}, KeysPost c s₂ s₃ → CryptPost c s₃ s₄ →
      Spec.Gcm.blockAt s₄.mem (c.W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₄.mem (c.W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt s₄.mem (c.W + BitVec.ofNat 64 80) = 0 := fun {s₂ s₃ s₄} K C => by
    have dC : ∀ {d : Nat}, d + 16 ≤ 96 → ∀ r ∈ cryR c.W c.D c.n,
        (⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.d_w' (by omega)).symm
    have a₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 16) 16 = bytesAt s₃.mem (c.W + BitVec.ofNat 64 16) 16 :=
      bytesAt_keep C.frame (dC (by decide)) (by decide)
    exact ⟨by rw [blockAt_frame C.frame (dC (by decide)), K.hkey, a₄],
      by rw [blockAt_frame C.frame (dC (by decide)), K.acc]⟩
  refine rel_seqR (polyval_rel L E₄ E₄' h₄) (Runs.of_wp (polyval_wp L E₄ (hP K C).1 (hP K C).2))
    (Runs.of_wp (polyval_wp L E₄' (hP K' C').1 (hP K' C').2)) fun s₅ t₅ P P' => ?_
  have E₅ := E₄.of_pk P.pk
  have E₅' := E₄'.of_pk P'.pk
  have h₅ : s₅.sp = t₅.sp := by rw [P.pk.sp, P'.pk.sp, h₄]
  refine rel_seqR (tag_rel L E₅ E₅' h₅ (o := 240) (.inr rfl)) (Runs.of_wp (tag_wp L E₅ (o := 240) (.inr rfl)))
    (Runs.of_wp (tag_wp L E₅' (o := 240) (.inr rfl))) fun s₆ t₆ T T' => ?_
  exact rel_env [] (E₅.of_pk T.pk) (E₅'.of_pk T'.pk) (by rw [T.pk.sp, T'.pk.sp, h₅]) (by simp) ⟨_, by taint_decide⟩

theorem seal_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub «seal» :=
  ct_of fun _ _ h₁ h₂ hq => seal_rel (args_of_seal h₁).1 (args_two (args_of_seal h₂).1 hq) hq.2.2.2.2.2.2.2.2.1

theorem open_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa openPPC64LE.pre openPPC64LE.pub «open» :=
  ct_of fun _ _ h₁ h₂ hq => open_rel (args_of_open h₁) (args_two (args_of_open h₂) hq) hq.2.2.2.2.2.2.2.2.1

end VG.Proof.AesGcmSiv.PPC64LE
