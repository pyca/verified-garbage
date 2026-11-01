module

import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Fn
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Keys
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Polyval
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Tag
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Crypt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Entry
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env

/-!
# AES-GCM-SIV on RISC-V: `vg_aes_gcm_siv_seal`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Seal.lean`): `seal` is `entry`, the keys
(`keys`), POLYVAL and the tag input (`polyval`), the tag at `W` (`tag 0`),
counter mode over the data from it (`crypt`), the tag copied to `tag`
(`tagOut`) and `restore` (`seal_wp`), computing `encryptWith` (RFC 8452 §4)
given that the tag input computed with GHASH is RFC 8452's (`TagInputEq`,
proven in `Verified.lean`). The lemmas about what each piece writes serve
`open` too.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcmSiv.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.RISCV64 (SavedAt savedR restore_ok covers_prefix)
open VG.Proof.GcmSiv.Words (tagInputG)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

/-- Regions of `W` as offsets and lengths. -/
abbrev wRs (W : Addr) (rs : List (Nat × Nat)) : List Region := rs.map fun q => ⟨W + BitVec.ofNat 64 q.1, q.2⟩

theorem keyR_eq (W : Addr) : keyR W = wRs W [(16, 112), (240, 16), (256, 240), (1792, 2048)] := rfl

theorem polyR_eq (c : Cx) :
    polyR c = wRs c.W [(96, 16), (240, 16), (80, 16), (496, 1024), (1536, 256)] ++ [below c.SP 2048] := rfl

theorem tagR_eq (W : Addr) (o : Nat) : tagR W o = wRs W [(112, 16), (o, 16), (1792, 2048)] := rfl

/-- Parts of `W` the pieces write are within `mutR`. -/
theorem wRs_mut {c : Cx} {rs : List (Nat × Nat)} (h : ∀ q ∈ rs, q.1 + q.2 ≤ 128 ∨ (240 ≤ q.1 ∧ q.1 + q.2 ≤ 3840)) :
    ∀ r ∈ wRs c.W rs, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  rcases h q hq with h₁ | ⟨h₁, h₂⟩
  · exact sub_lo h₁
  · exact sub_hi h₁ h₂

/-- And the stack below `sp`. -/
theorem wRsB_mut {c : Cx} {rs : List (Nat × Nat)} (h : ∀ q ∈ rs, q.1 + q.2 ≤ 128 ∨ (240 ≤ q.1 ∧ q.1 + q.2 ≤ 3840)) :
    ∀ r ∈ wRs c.W rs ++ [below c.SP 2048], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact wRs_mut h r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact sub_below

theorem cryR_mut (c : Cx) : ∀ r ∈ cryR c.W c.D c.n, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)
  · exact sub_hi (by decide) (by decide)
  · exact sub_data

/-- A part of `W` missing the parts `rs` of `W`. -/
theorem w_keep {c : Cx} (L : Lay c) {rs : List (Nat × Nat)} {d k : Nat}
    (h : ∀ q ∈ rs, (d + k ≤ q.1 ∨ q.1 + q.2 ≤ d) ∧ q.1 + q.2 ≤ 3840) (hd : d + k ≤ 3840) :
    ∀ r ∈ wRs c.W rs, (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact L.w_w (h q hq).1 hd (h q hq).2

/-- And the stack below `sp`. -/
theorem w_keepB {c : Cx} (L : Lay c) {rs : List (Nat × Nat)} {d k : Nat}
    (h : ∀ q ∈ rs, (d + k ≤ q.1 ∨ q.1 + q.2 ≤ d) ∧ q.1 + q.2 ≤ 3840) (hd : d + k ≤ 3840) :
    ∀ r ∈ wRs c.W rs ++ [below c.SP 2048], (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact w_keep L h hd r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (L.b_w' hd).symm

/-- A buffer missing `W` misses the parts `rs` of `W`. -/
theorem buf_keep {c : Cx} {P : Addr} {len : Nat} (hP : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 3840⟩)
    {rs : List (Nat × Nat)} (h : ∀ q ∈ rs, q.1 + q.2 ≤ 3840) :
    ∀ r ∈ wRs c.W rs, (⟨P, len⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact hP.sub_right (Lay.wSub (h q hq))

/-- And the stack below `sp`, for a buffer missing it. -/
theorem buf_keepB {c : Cx} {P : Addr} {len : Nat} (hP : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 3840⟩)
    (hb : (below c.SP 2048).Disjoint ⟨P, len⟩) {rs : List (Nat × Nat)} (h : ∀ q ∈ rs, q.1 + q.2 ≤ 3840) :
    ∀ r ∈ wRs c.W rs ++ [below c.SP 2048], (⟨P, len⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact buf_keep hP h r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact hb.symm

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.Cmac.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- The entry keeps a buffer missing `W`. -/
theorem entry_buf {c : Cx} {s s₁ : State} (hf : Frame [savedR c.W, ⟨nP c.W, 12⟩] s.mem s₁.mem) {P : Addr}
    {len : Nat} (hP : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 3840⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt s₁.mem P len = bytesAt s.mem P len :=
  bytesAt_keep hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hP.sub_right (Lay.wSub (by decide))) hl

/-- The registers `restore` reloads from, at the exit. -/
theorem exit_covers {c : Cx} {s : State} (E : Env c s) : Covers [⟨c.W, 2560⟩] (s.rd ++ s.wr) :=
  covers_prefix (Covers.right E.perm.w) (by decide)

/-- `vg_aes_gcm_siv_seal`, for its arguments. -/
theorem seal_wp' (hti : TagInputEq) {c : Cx} {s : State} (Ar : Args c s) (hTw : Covers [⟨c.T, 16⟩] s.wr) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem c.K c.R) (Spec.GcmSiv.keyLen c.R) (bytesAt s.mem c.N 12)
        (bytesAt s.mem c.D c.n) (bytesAt s.mem c.A c.al) = (bytesAt s'.mem c.D c.n, bytesAt s'.mem c.T 16) := by
  have L := Ar.lay
  have hRb := L.rb
  have hn := L.n_lt
  have hal := L.al_lt
  unfold «seal»
  refine WP.seq (WP.mono (entry_wp Ar) fun s₁ En => ?_)
  -- The keys.
  refine WP.seq (WP.mono (keys_wp L En.env) fun s₂ Ky => ?_)
  have E₂ := En.env.of_pk Ky.pk
  have fK := Ky.frame
  rw [keyR_eq] at fK
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem c.K c.R = Spec.GcmSiv.ctxCiph s.mem c.K c.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [entry_buf En.frame (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega)]
  have n₁ : bytesAt s₁.mem c.N 12 = bytesAt s.mem c.N 12 := entry_buf En.frame L.n_w (by decide)
  have n₂ : bytesAt s₂.mem c.N 12 = bytesAt s.mem c.N 12 := by
    rw [bytesAt_keep fK (buf_keep L.n_w (by decide)) (by decide), n₁]
  have nP₂ : bytesAt s₂.mem (nP c.W) 12 = bytesAt s₂.mem c.N 12 := by
    rw [n₂, ← En.nonce]
    exact bytesAt_keep fK (w_keep L (d := 1520) (k := 12) (by decide) (by decide)) (by decide)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_wp L E₂ Ky.hkey Ky.acc nP₂) fun s₃ Po => ?_)
  have E₃ := E₂.of_pk Po.pk
  -- The tag.
  refine WP.seq (WP.mono (tag_wp L E₃ (o := 0) (by decide)) fun s₄ Tg => ?_)
  have E₄ := E₃.of_pk Tg.pk
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_wp L E₄) fun s₅ Cr => ?_)
  have E₅ := E₄.of_pk Cr.pk
  have pk₅ : PK s₁ s₅ := Ky.pk.trans (Po.pk.trans (Tg.pk.trans Cr.pk))
  -- The copy of the tag, and `restore`.
  have fP := Po.frame
  have fT := Tg.frame
  rw [polyR_eq] at fP
  rw [tagR_eq] at fT
  have f₅ : Frame (mutR c) s₁.mem s₅.mem :=
    (((fK.sub (wRs_mut (by decide))).trans (fP.sub (wRsB_mut (by decide)))).trans
      (fT.sub (wRs_mut (by decide)))).trans (Cr.frame.sub (cryR_mut c))
  refine WP.block_append (WP.mono (tagOut_wp L E₅ (by rw [pk₅.wr, En.wr]; exact hTw)) fun s₆ ⟨pk₆, tO, fO⟩ => ?_)
  have sv₆ : SavedAt s₆.mem c.W s :=
    (saved_mut L f₅ En.saved).frame fO fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.t_w.sub_right (Lay.wSub (by decide))).symm
  have pk₁₆ : PK s₁ s₆ := pk₅.trans pk₆
  have E₆ := E₅.of_pk pk₆
  refine WP.mono (restore_ok E₆.s0 L.wal (exit_covers E₆) sv₆ (by rw [pk₁₆.sp, En.sp]))
    fun s' ⟨abi, hm, _⟩ => ⟨abi, ?_⟩
  have a₂ : bytesAt s₂.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [bytesAt_keep fK (buf_keep L.a_w (by decide)) (by omega), entry_buf En.frame L.a_w (by omega)]
  have d₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [bytesAt_keep fK (buf_keep L.d_w (by decide)) (by omega), entry_buf En.frame L.d_w (by omega)]
  have d₄ : bytesAt s₄.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [bytesAt_keep fT (buf_keep L.d_w (by decide)) (by omega),
      bytesAt_keep fP (buf_keepB L.d_w L.b_d (by decide)) (by omega), d₂]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (c.W + BitVec.ofNat 64 256) c.R =
      Spec.GcmSiv.ctxCiph s₂.mem (c.W + BitVec.ofNat 64 256) c.R :=
    ciph_keep fP (w_keepB L (by decide) (by decide)) hRb
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (c.W + BitVec.ofNat 64 256) c.R =
      Spec.GcmSiv.ctxCiph s₂.mem (c.W + BitVec.ofNat 64 256) c.R := by
    rw [ciph_keep fT (w_keep L (by decide) (by decide)) hRb, key₃]
  have t₅ : bytesAt s₅.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s₄.mem (c.W + BitVec.ofNat 64 0) 16 :=
    bytesAt_keep Cr.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.d_w' (by decide)).symm) (by decide)
  rw [BitVec.add_zero] at t₅
  have tg := Tg.out
  rw [BitVec.add_zero] at tg
  have d₆ : bytesAt s₆.mem c.D c.n = bytesAt s₅.mem c.D c.n :=
    bytesAt_keep fO (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by omega)
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, En.nonce] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [hm, d₆, tO, Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
    (bytesAt s.mem c.N 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (hti : TagInputEq) {s : State} (h : sealRISCV64.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealRISCV64.post s s' := by
  have A := args_of_seal h
  refine WP.mono (seal_wp' hti A.1 A.2) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  simp only [sealRISCV64]
  simpa only [cxOf] using hp

end VG.Proof.AesGcmSiv.RISCV64
