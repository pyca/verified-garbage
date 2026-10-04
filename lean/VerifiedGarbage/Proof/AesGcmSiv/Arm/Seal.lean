import VerifiedGarbage.Proof.AesGcmSiv.Arm.Fn

/-!
# AES-GCM-SIV on ARMv7: `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, and
the restore compute `encryptWith` (RFC 8452 §4) of the arguments
(`seal_wp`), given that the tag input computed with GHASH is the RFC's
(`Proof.GcmSiv.Words.tagInputG`, related to it in `Verified.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.Arm (SavedAt savedR restore_ok)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.AesGcm.Arm.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- The end: our caller's registers restored. -/
theorem exit_ok {p : Prm} (L : Lay p) {s₀ t : State} (E : Env p t) (hsp : p.SP = s₀.sp)
    (hs : SavedAt t.mem p.W s₀) :
    WP isa (.block Impl.AesGcm.Arm.restore) t fun s' => abiPreserved s₀ s' ∧ s'.mem = t.mem ∧
      s'.gpr .r0 = t.gpr .r0 :=
  WP.mono (restore_ok E.r11 (by have := L.ww; omega) (covers_left (covers_prefix E.perm.w (by decide))) hs
    (by rw [E.sp, hsp])) fun _ ⟨a, m, r, _⟩ => ⟨a, m, r⟩
where
  covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := Proof.AesGcm.Arm.covers_left h
  covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
      Covers [⟨p, n⟩] rs := Proof.AesGcm.Arm.covers_prefix h hn

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (hti : TagInputEq) {s : State} (h : onePre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' := by
  have L := lay_of h
  have hRb := L.rounds_le
  have hn := L.n_lt
  have A₀ := args_of s
  refine WP.seq (WP.mono (entry_ok h) fun s₁ En => ?_)
  have A₁ : Args (prmOf s) s₁.mem := A₀.frame L En.frame (by disj_tac L)
  -- The keys.
  refine WP.seq (WP.mono (keys_ok L En.env) fun s₂ Ky => ?_)
  have A₂ : Args (prmOf s) s₂.mem := A₁.frame L Ky.frame (by disj_tac L)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok L Ky.env A₂ Ky.hkey Ky.acc) fun s₃ Po => ?_)
  have A₃ : Args (prmOf s) s₃.mem := A₂.frame L Po.frame (by disj_tac L)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  have A₄ : Args (prmOf s) s₄.mem := A₃.frame L Tg.frame (by disj_tac L)
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok L Tg.env A₄) fun s₅ Cr => ?_)
  -- `restore`.
  have sv₅ : SavedAt s₅.mem (prmOf s).W s :=
    ((((En.saved.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L))
  refine WP.mono (exit_ok L Cr.env rfl sv₅) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
      (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12)
      (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al) =
    (bytesAt s'.mem (State.addr (prmOf s).D) (prmOf s).n, bytesAt s'.mem (State.addr (prmOf s).W) 16)
  rw [hm]
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (State.addr (prmOf s).K) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R :=
    ciph_keep En.frame (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 :=
    bytesAt_keep En.frame (by disj_tac L) (by decide)
  have n₂ : bytesAt s₂.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₂ : bytesAt s₂.mem (State.addr (prmOf s).A) (prmOf s).al = bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep En.frame (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega), bytesAt_keep En.frame (by disj_tac L) (by omega)]
  have d₄ : bytesAt s₄.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by omega), bytesAt_keep Po.frame (by disj_tac L) (by omega), d₂]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R :=
    ciph_keep Po.frame (by disj_tac L) hRb
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    rw [ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  have t₅ : bytesAt s₅.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
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
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.Arm
