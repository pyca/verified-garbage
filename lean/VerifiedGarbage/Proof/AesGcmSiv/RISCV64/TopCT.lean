module

import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.KeysCT
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.PolyCT
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.CryptCT
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Entry
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Keys
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Open
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Open
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.KeysCT
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.PolyCT
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.CryptCT
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Entry
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Fn
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Seal
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
meta import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
meta import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-!
# AES-GCM-SIV on RISC-V: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/TopCT.lean`): two runs with the same public
arguments have the same public values (`args_two`). The entry loads `work`
from the stack, which the taint analysis takes as secret (it reads memory):
the block is split after the load, and the rest runs from `t1`, which holds
`work` in both runs, and the arguments (`entry_rel`). The keys, POLYVAL, the
tag and counter mode are related by `KeysCT.lean`, `PolyCT.lean` and
`CryptCT.lean`, the code between them by the taint analysis (`seal_rel`,
`open_rel`). `open` compares the tags and masks the plaintext without a
branch: whether it succeeds is not leaked.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.RISCV64.Steps (wp_addSp wp_ld)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint ct_of)
open VG.Proof.AesGcm.RISCV64 (in_off)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp rel_seqR)
open VG.Spec.Aes (bytesAt)

/-- Two runs with the same public arguments: both from the public values of
the first. -/
theorem args_two {σ₁ σ₂ : State} (A₂ : Args (cxOf σ₂) σ₂) (hq : onePub σ₁ σ₂) : Args (cxOf σ₁) σ₂ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qs, qa⟩ := hq
  have hcx : cxOf σ₂ = cxOf σ₁ := by simp only [cxOf, q0, q1, q2, q3, q4, q5, q6, q7, qs, qa]
  rw [hcx] at A₂
  exact A₂

/-- The arguments' registers. -/
abbrev argRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

theorem Args.agree {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂) :
    ∀ r ∈ argRegs, σ₁.gpr r = σ₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [A₁.a0, A₂.a0]
  · rw [A₁.a1, A₂.a1]
  · rw [A₁.a2, A₂.a2]
  · rw [A₁.a3, A₂.a3]
  · rw [A₁.a4, A₂.a4]
  · rw [A₁.a5, A₂.a5]
  · rw [A₁.a6, A₂.a6]
  · rw [A₁.a7, A₂.a7]

/-- `work` loaded. -/
theorem entryLd_wp {c : Cx} {s : State} (Ar : Args c s) :
    WP isa (.block [.addSp .t1 0, .load .d .t1 .t1 0]) s fun s' =>
      s'.gpr .t1 = c.W ∧ (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  have L := Ar.lay
  refine wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_
  refine wp_ld (a := stackArgAddr s 0) (by decide) (by rw [u₁.gpr, stackArgAddr, Nat.mul_zero, BitVec.add_zero, BitVec.add_zero])
    (by rw [stackArgAddr, Ar.sp]; exact Spill.al8 (by have := L.spal; omega) (by decide))
    (by rw [u₁.rd, u₁.wr]; simpa using in_off Ar.argsC (d := 0) (n := 8) (by decide) (by decide))
    fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u₁.mem, ← Ar.w]; rfl,
      fun r hr => by rw [u₂.other _ hr, u₁.other _ hr], by rw [u₂.sp, u₁.sp]⟩

/-- The entry in two runs. -/
theorem entry_rel {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have e : entry = [.addSp .t1 0, .load .d .t1 .t1 0] ++ entry.drop 2 := rfl
  rw [e]
  refine RelCT.block_append (rel_seqR (rel_taint [] hsp (by simp) (by taint_decide))
    (Runs.of_wp (entryLd_wp A₁)) (Runs.of_wp (entryLd_wp A₂)) fun τ₁ τ₂ ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ => ?_)
  refine rel_taint (.t1 :: argRegs) (by rw [c₁, c₂, hsp]) (fun r hr => ?_) (by taint_decide)
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]
  · have h : r ≠ .t1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [b₁ r h, b₂ r h, A₁.agree A₂ r hr]

/-- The nonce's copy, after the entry and the keys. -/
theorem nP_keys {c : Cx} {s s₁ s₂ : State} (Ar : Args c s) (En : Entered c s s₁) (K : KeysPost c s₁ s₂) :
    bytesAt s₂.mem (nP c.W) 12 = bytesAt s₂.mem c.N 12 := by
  have L := Ar.lay
  have fK := K.frame
  rw [keyR_eq] at fK
  rw [bytesAt_keep (P := nP c.W) fK (w_keep L (d := 1520) (k := 12) (by decide) (by decide)) (by decide),
    bytesAt_keep fK (buf_keep L.n_w (by decide)) (by decide), En.nonce, entry_buf En.frame L.n_w (by decide)]

/-- `vg_aes_gcm_siv_seal` in two runs. -/
theorem seal_rel {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂) (hsp : σ₁.sp = σ₂.sp) :
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
  refine rel_seqR (polyval_rel L E₂ E₂' h₂) (Runs.of_wp (polyval_wp L E₂ K.hkey K.acc (nP_keys A₁ En K)))
    (Runs.of_wp (polyval_wp L E₂' K'.hkey K'.acc (nP_keys A₂ En' K'))) fun s₃ t₃ P P' => ?_
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
theorem open_rel {c : Cx} {σ₁ σ₂ : State} (A₁ : Args c σ₁) (A₂ : Args c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) «open» TT := by
  have L := A₁.lay
  unfold «open»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  have h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (rel_env [] En.env En'.env h₁ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (recv_wp L En.env))
    (Runs.of_wp (recv_wp L En'.env)) fun s₂ t₂ R R' => ?_
  have E₂ := En.env.of_pk R.1
  have E₂' := En'.env.of_pk R'.1
  have h₂ : s₂.sp = t₂.sp := by rw [R.1.sp, R'.1.sp, h₁]
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
  -- What POLYVAL needs: the key as the keys left it, and the nonce's copy.
  have hP : ∀ {s s₁ s₂ s₃ s₄ : State}, Args c s → Entered c s s₁ →
      (PK s₁ s₂ ∧ bytesAt s₂.mem c.W 16 = bytesAt s₁.mem c.T 16 ∧ Frame [⟨c.W, 16⟩] s₁.mem s₂.mem) →
      KeysPost c s₂ s₃ → CryptPost c s₃ s₄ →
      Spec.Gcm.blockAt s₄.mem (c.W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₄.mem (c.W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt s₄.mem (c.W + BitVec.ofNat 64 80) = 0 ∧
      bytesAt s₄.mem (nP c.W) 12 = bytesAt s₄.mem c.N 12 := fun {s s₁ s₂ s₃ s₄} Ar En R K C => by
    have dC : ∀ {d : Nat}, d + 16 ≤ 96 → ∀ r ∈ cryR c.W c.D c.n,
        (⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.d_w' (by omega)).symm
    have dN : ∀ r ∈ cryR c.W c.D c.n, (⟨nP c.W, 12⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.d_w' (by decide)).symm
    have a₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 16) 16 = bytesAt s₃.mem (c.W + BitVec.ofNat 64 16) 16 :=
      bytesAt_keep C.frame (dC (by decide)) (by decide)
    have fK := K.frame
    rw [keyR_eq] at fK
    have fR : Frame (wRs c.W [(0, 16)]) s₁.mem s₂.mem := by
      simp only [wRs, List.map_cons, List.map_nil, BitVec.add_zero]; exact R.2.2
    refine ⟨by rw [blockAt_frame C.frame (dC (by decide)), K.hkey, a₄],
      by rw [blockAt_frame C.frame (dC (by decide)), K.acc], ?_⟩
    rw [bytesAt_keep (P := nP c.W) C.frame dN (by decide),
      bytesAt_keep (P := nP c.W) fK (w_keep L (d := 1520) (k := 12) (by decide) (by decide)) (by decide),
      bytesAt_keep (P := nP c.W) fR (w_keep L (d := 1520) (k := 12) (by decide) (by decide)) (by decide), En.nonce,
      bytesAt_keep C.frame (buf_cryR L.n_w L.n_d) (by decide),
      bytesAt_keep fK (buf_keep L.n_w (by decide)) (by decide),
      bytesAt_keep fR (buf_keep L.n_w (by decide)) (by decide), entry_buf En.frame L.n_w (by decide)]
  have Q := hP A₁ En R K C
  have Q' := hP A₂ En' R' K' C'
  refine rel_seqR (polyval_rel L E₄ E₄' h₄) (Runs.of_wp (polyval_wp L E₄ Q.1 Q.2.1 Q.2.2))
    (Runs.of_wp (polyval_wp L E₄' Q'.1 Q'.2.1 Q'.2.2)) fun s₅ t₅ P P' => ?_
  have E₅ := E₄.of_pk P.pk
  have E₅' := E₄'.of_pk P'.pk
  have h₅ : s₅.sp = t₅.sp := by rw [P.pk.sp, P'.pk.sp, h₄]
  refine rel_seqR (tag_rel L E₅ E₅' h₅ (o := 240) (.inr rfl)) (Runs.of_wp (tag_wp L E₅ (o := 240) (.inr rfl)))
    (Runs.of_wp (tag_wp L E₅' (o := 240) (.inr rfl))) fun s₆ t₆ T T' => ?_
  exact rel_env [] (E₅.of_pk T.pk) (E₅'.of_pk T'.pk) (by rw [T.pk.sp, T'.pk.sp, h₅]) (by simp) ⟨_, by taint_decide⟩

theorem seal_ct : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» :=
  ct_of fun _ _ h₁ h₂ hq => seal_rel (args_of_seal h₁).1 (args_two (args_of_seal h₂).1 hq) hq.2.2.2.2.2.2.2.2.1

theorem open_ct : ConstantTime isa openRISCV64.pre openRISCV64.pub «open» :=
  ct_of fun _ _ h₁ h₂ hq => open_rel (args_of_open h₁) (args_two (args_of_open h₂) hq) hq.2.2.2.2.2.2.2.2.1

end VG.Proof.AesGcmSiv.RISCV64
