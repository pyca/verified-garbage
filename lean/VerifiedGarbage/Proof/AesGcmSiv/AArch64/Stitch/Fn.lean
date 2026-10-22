module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Open
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Fn
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.AesGcm.AArch64.Tag
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `seal_wp` is
`Proof.AesGcmSiv.AArch64.seal_wp` with the interleaved `polyval` and
`crypt`; `open_wp` is `Proof.AesGcmSiv.AArch64.open_wp` with the additional
data absorbed first and the data decrypted and absorbed by `openData`
(`openMid_ok`), which leaves what `crypt` then `polyval` did.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG hkeyOf)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs cryR polyR absorbR absR absorbR_H absorbR_buf Absorbed
  AbsPost absorb_ok lens_ok tagIn_ok tagInMem_frame tagInMem_bytes TagInputEq bytesAt_keep ciph_keep TagSlot
  prmOf args_of_seal args_of_open entry_ok keys_ok tag_ok tagOut_ok recv_ok cmp_ok mask_ok entryR ciph_cryR
  decrypt_eq sealPre openPre)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok Others length_bytesAt)
open VG.Proof.Gcm.AArch64.Pmull (PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

theorem forall_app {l₁ l₂ : List Region} {P : Region → Prop} (h₁ : ∀ r ∈ l₁, P r) (h₂ : ∀ r ∈ l₂, P r) :
    ∀ r ∈ l₁ ++ l₂, P r := fun r hr => (List.mem_append.mp hr).elim (h₁ r) (h₂ r)

/-! ## `seal` -/

theorem seal_wp (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) (hti : TagInputEq) {s : State} (h : sealPre s) :
    WP isa (Impl.AesGcmSiv.AArch64.Stitch.«seal» v.callees) s fun s' =>
      GprAbi s s' ∧ Proof.AesGcmSiv.AArch64.sealAArch64.post s s' := by
  obtain ⟨L, P, hTw, hA⟩ := args_of_seal h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok P hA) fun s₁ ⟨E₁, sv₁, f₁, sl₁, rd₁, wr₁⟩ => ?_)
  -- The keys.
  refine WP.seq (WP.mono (Proof.AesGcmSiv.AArch64.WP.rdwr (keys_ok v L E₁)) fun s₂ ⟨Ky, _, kw⟩ => ?_)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok hP gh v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  -- The copy of the tag, and `restore`.
  have sl₅ : TagSlot (prmOf s) s₅.mem :=
    (((sl₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L)
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, kw, wr₁]
  obtain ⟨s₆, run₆, fT, hT₆, -, ho₆, sp₆, rd₆, wr₆⟩ := tagOut_ok L Cr.env sl₅ (by rw [w₅]; exact hTw)
  have E₆ : Env (prmOf s) s₆ := Cr.env.keep (fun r hr => ho₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  have sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (((((sv₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L))).frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.t_w' (show 128 + 88 ≤ 3808 by decide)).symm
  refine WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  refine WP.mono (exit_ok (s₀ := s) E₆.x19 E₆.sp E₆.w2560R sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R) (Spec.GcmSiv.keyLen (prmOf s).R)
      (bytesAt s.mem (prmOf s).N 12) (bytesAt s.mem (prmOf s).D (prmOf s).n) (bytesAt s.mem (prmOf s).A (prmOf s).al) =
    (bytesAt s'.mem (prmOf s).D (prmOf s).n, bytesAt s'.mem (prmOf s).T 16)
  rw [hm, hT₆, bytesAt_keep fT (by disj_tac L) (by omega)]
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
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R :=
    ciph_keep Po.frame (by disj_tac L) hRb
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R := by
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

/-! ## `open` -/

/-- What the additional data absorbed, `openData`, the lengths and the tag
input leave, from `t`: what `crypt` then `polyval` leave. -/
structure OpenMid (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR p.W p.D p.n ++ polyR p.W) t.mem t'.mem
  data : bytesAt t'.mem p.D p.n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n)
  out : bytesAt t'.mem (p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem p.N 12) (bytesAt t'.mem p.D p.n)
      (bytesAt t.mem p.A p.al)

theorem openMid_ok (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hG : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0) {k : Prog isa} {Q : State → Prop}
    (hk : ∀ t', OpenMid p t t' → WP isa k t' Q) :
    WP isa (.seq (.block [Impl.AesGcm.AArch64.mov .x27 .x23, Impl.AesGcm.AArch64.mov .x28 .x24])
      (.seq (Impl.AesGcmSiv.AArch64.absorb v.callees) (.seq (Impl.AesGcmSiv.AArch64.Stitch.openData v.callees)
      (.seq (Impl.AesGcmSiv.AArch64.lens v.callees) (.seq (.block Impl.AesGcmSiv.AArch64.tagIn) k))))) t Q := by
  have hn := L.n_lt
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok v L ((E.write (by decide) _).write (by decide) _)
    (by simp only [rd_write, wr_write]; exact E.perm.aad) L.al_lt L.aw L.a_w
    (by simp [gpr_write, E.x23]) (by simp [gpr_write, E.x24])) fun t₂ P₂ => ?_)
  simp only [mem_write] at P₂
  have P₂' := P₂.of_eq (t := t) rfl rfl rfl
  -- The data.
  refine WP.seq (WP.mono (openData_ok hP gh v L P₂.env) fun t₄ O => ?_)
  have hH : ∀ r ∈ cryR p.W p.D p.n ++ absorbR p.W, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
    forall_app (by disj_tac L) (absorbR_H L)
  have sA : ∀ r ∈ absorbR p.W, ∃ r' ∈ cryR p.W p.D p.n ++ absorbR p.W, Region.Sub r r' :=
    fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  have P₂₄ := Absorbed.trans hH (P₂'.sub sA) ⟨O.env, O.rd, O.wr, O.frame, O.out⟩
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  have P₂₅ := Absorbed.trans hH P₂₄ (P₅.sub sA)
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := tagIn_ok P₂₅.env
  refine WP.seq (WP.of_runBlock ⟨t₆, run₆, hk t₆ ?_⟩)
  have E₆ : Env p t₆ := P₂₅.env.keep (fun q hq => ho₆ q (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  -- What the absorbing of the additional data kept.
  have dA : ∀ {Q : Addr} {k : Nat}, (⟨Q, k⟩ : Region).Disjoint ⟨p.W, 3808⟩ → k ≤ 2 ^ 64 →
      bytesAt t₂.mem Q k = bytesAt t.mem Q k := fun hd hk' => by
    rw [Proof.AesGcm.AArch64.bytesAt_frame P₂'.frame (absorbR_buf hd) hk']
  have fT : Frame [⟨p.W + BitVec.ofNat 64 96, 16⟩] t₅.mem t₆.mem := by rw [hm₆]; exact tagInMem_frame _ _ _
  have d₆ : bytesAt t₆.mem p.D p.n = bytesAt t₄.mem p.D p.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame fT (by disj_tac L) (Nat.le_of_lt hn),
      Proof.AesGcm.AArch64.bytesAt_frame P₅.frame (absorbR_buf L.d_w) (Nat.le_of_lt hn)]
  refine ⟨E₆, by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => ?_).trans (fT.mono fun q hq => ?_)
    · rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
    · simp only [List.mem_singleton] at hq; subst hq
      exact List.mem_append_right _ List.mem_cons_self
  · have hk : Spec.GcmSiv.ctxCiph t₂.mem (p.W + BitVec.ofNat 64 240) p.R =
        Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R :=
      ciph_keep P₂'.frame (by disj_tac L) L.rounds_le
    have hw0 := bytesAt_keep P₂'.frame (P := p.W + BitVec.ofNat 64 0) (n := 16) (by disj_tac L) (by decide)
    rw [L.w0] at hw0
    rw [d₆, O.data, hw0, hk, dA L.d_w (Nat.le_of_lt hn)]
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
    have nN : bytesAt t₅.mem p.N 12 = bytesAt t.mem p.N 12 :=
      Proof.AesGcm.AArch64.bytesAt_frame P₂₅.frame (forall_app (by disj_tac L) (absorbR_buf L.n_w)) (by decide)
    rw [d₆, hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) (hti : TagInputEq) {s : State} (h : openPre s) :
    WP isa (Impl.AesGcmSiv.AArch64.Stitch.«open» v.callees) s fun s' =>
      GprAbi s s' ∧ Proof.AesGcmSiv.AArch64.openAArch64.post s s' := by
  obtain ⟨L, P, hA⟩ := args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok P hA) fun s₀ ⟨E₀, sv₀, f₀, sl₀, _, _⟩ => ?_)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, -, ho₁, sp₁, rd₁, wr₁⟩ := recv_ok L E₀ sl₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env (prmOf s) s₁ := E₀.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fR' : Frame [⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by rw [L.w0]; exact fR
  have sv₁ : SavedAt s₁.mem (prmOf s).W s := sv₀.frame fR' (by disj_tac L)
  have f₁ : Frame [entryR (prmOf s).W, ⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩, by simp, fun _ h => h⟩)
  have hT₁ : bytesAt s₁.mem (prmOf s).W 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [hR₁, bytesAt_keep f₀ (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L E₁) fun s₂ Ky => ?_)
  -- The additional data, then the data decrypted and absorbed, the lengths and the tag input.
  refine openMid_ok hP gh v L Ky.env Ky.hkey Ky.acc fun s₄ Md => ?_
  have dMd : ∀ {R' : Region}, (∀ r ∈ cryR (prmOf s).W (prmOf s).D (prmOf s).n, R'.Disjoint r) →
      (∀ r ∈ polyR (prmOf s).W, R'.Disjoint r) → ∀ r ∈ cryR (prmOf s).W (prmOf s).D (prmOf s).n ++ polyR (prmOf s).W,
        R'.Disjoint r := fun h₁ h₂ => forall_app h₁ h₂
  -- Its tag at `W + 224`.
  refine WP.seq (WP.mono (tag_ok v L Md.env (o := 224) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, x27₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : Env (prmOf s) s₆ := Tg.env.keep (fun r hr => ho₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ x27₆) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  refine WP.block_append (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  have sv₇ : SavedAt s₇.mem (prmOf s).W s := by
    have := (((sv₁.frame Ky.frame (by disj_tac L)).frame Md.frame (dMd (by disj_tac L) (by disj_tac L))).frame
      Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (exit_ok (s₀ := s) (Mk.env.write (by decide) _).x19 (Mk.env.write (by decide) _).sp
    (Mk.env.write (by decide) _).w2560R (by simp only [mem_write]; exact sv₇)) fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
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
  have tag₂ : bytesAt s₂.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), L.w0, hT₁]
  have tag₅ : bytesAt s₅.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by decide),
      bytesAt_keep Md.frame (dMd (by disj_tac L) (by disj_tac L)) (by decide), tag₂]
  rw [L.w0] at tag₂ tag₅
  have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R :=
    ciph_keep Md.frame (dMd (by disj_tac L) (by disj_tac L)) hRb
  have d₆ : bytesAt s₆.mem (prmOf s).D (prmOf s).n = bytesAt s₄.mem (prmOf s).D (prmOf s).n := by
    rw [hm₆, bytesAt_keep Tg.frame (by disj_tac L) (by omega)]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Md.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Md.out
  rw [← au, n₂, a₂, pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.data
  rw [hm₆, tg, tag₅] at md
  rw [← hm₆, d₆, pt₃] at md
  have ax : s'.gpr .x0 = s₆.gpr .x27 := by
    rw [hx0]; simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero]; exact Mk.x27
  rw [x27₆, tg, tag₅] at ax
  show openPost (openResult s) s' (prmOf s).D (prmOf s).n
  have hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
            (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) =
          bytesAt s.mem (prmOf s).T 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
          (bytesAt s.mem (prmOf s).D (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
        (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) =
      bytesAt s.mem (prmOf s).T 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (prmOf s).T 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
          (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) := Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.AArch64.Stitch
