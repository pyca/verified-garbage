module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Open.lean`): `open` checks the tag length; if it is
allowed, it computes the tag of the ciphertext into `W + 112` (`oneAad`,
`oneTag 112`), copies the received tag to `W + 256` and compares the first
`tag_len` bytes of each (`recv`, `cmp 112`), and decrypts the data in place
only if they are equal; `r3` is the result (`open_wp`). Until the data is
decrypted, everything `open` writes is in the working space `W`
(`Frame [⟨W, 2560⟩]`), which every buffer is apart from.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag zeros padLen j0 inc32 gctr decryptWith openResult)

/-- What `open` promises, given the result `r3` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r3 = 1 ∧ bytesAt s.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = pt
  | none => s.gpr .r3 = 0 ∧ bytesAt s.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .r3 = 0)
    (hd : bytesAt s.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .r3 = 1)
    (hd : bytesAt s.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- What the end of `open` leaves for `restore`. -/
structure OpenOut (s₀ s : State) : Prop where
  r31 : s.gpr .r31 = stackArg s₀ 2
  sp : s.sp = s₀.sp
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 2) s₀
  post : OpenPost s₀ s

/-- An environment for a state's own registers, after a step that changes
only `r19` among those the environment pins. -/
theorem Env.self {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (he : Env V sp s)
    (hg : ∀ r, r ≠ .r19 → s'.gpr r = s.gpr r) (hk : Keeps s s') : Env s'.gpr sp s' :=
  ⟨fun _ _ => rfl, hk.sp.trans he.sp, by
    rw [hg _ (by decide), hg _ (by decide), hg _ (by decide), he.fr _ (by decide), he.fr _ (by decide),
      he.fr _ (by decide)]
    exact he.perm.of_eq hk.rd hk.wr⟩

section
variable {W : Addr}

/-- What `oneAad`, `oneTag 112`, `recv` and `cmp 112` write is in `W`. -/
theorem inW_j0 : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, ∃ r' ∈ [(⟨W, 2560⟩ : Region)], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Lay.wSub (by decide)⟩

theorem inW_ot : ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112, ∃ r' ∈ [(⟨W, 2560⟩ : Region)], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Lay.wSub (by decide)⟩

theorem inW_at {d : Nat} (hd : d + 16 ≤ 2560) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ [(⟨W, 2560⟩ : Region)], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Lay.wSub hd⟩

theorem inW_saved : ∀ r ∈ [savedR W], ∃ r' ∈ [(⟨W, 2560⟩ : Region)], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Lay.wSub (by decide)⟩

/-- The first counter block is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem cb_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.st_st (st := W + BitVec.ofNat 64 16) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide))
      (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)

end

/-- A buffer apart from `W` is as it was. -/
theorem bytes_W {m m' : Mem} {W p : Addr} {n : Nat} (hf : Frame [(⟨W, 2560⟩ : Region)] m m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hn

/-- `open` from the comparison of the tags on, once the tag length is allowed. -/
theorem open_good {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄)
    (h19 : s₄.gpr .r19 = stackArg s₀ 1) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3])
      (.seq (.ite (.zero .d .r19) (.block []) oneCrypt) (.block [mov .r3 .r19]))))))) s₄ (OpenOut s₀) := by
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hR⟩ := hh
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  have L₀ := oneLay fc fW dcW
  have hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have he₄ := one_env h4 hC hW
  have L := L₀.v h4.r29 h4.r30 h4.r31
  have hk₄ := h4.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ [(⟨stackArg s₀ 2, 2560⟩ : Region)], (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact dcW
  have F₄ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₄.mem := h4.en.frame.sub inW_saved
  -- `oneAad`
  have hN : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₀.gpr .r5) (s₀.gpr .r6).toNat := by
    rw [h4.r30, h4.r31]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .r6).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  have hAd : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r21) (s₄.gpr .r22).toNat := by
    rw [h4.r30, h4.r31, h4.r21, h4.r22]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .r8).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.r24 (by rw [h4.r25]; exact toN)
    (by rw [h4.r18]; exact toN) hN hAd)) fun s₅ ⟨oa, rd₅, wr₅, _⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.r30, h4.r31] at f₅
  have F₅ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `oneTag 112`
  have hDw₄ : Covers [⟨s₀.gpr .r9, (s₀.gpr .r10).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  have hd₄ : DataW (s₄.gpr .r29) (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r27) (s₄.gpr .r23).toNat := by
    rw [h4.r29, h4.r30, h4.r31, h4.r27, h4.r23]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .r10).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw₄, dcd⟩
  have h28 : s₄.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat := by rw [h4.r28]; exact toN
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L (o := 112) (.inr rfl) oa.env h28 hR oa.hH
    (length_bytesAt _ _ _).symm oa.abs (hd₄.ok.of_eq rd₅ wr₅))) fun s₆ ⟨ot, rd₆, wr₆, _⟩ => ?_)
  have f₆ := ot.frame
  rw [h4.r30, h4.r31] at f₆
  have F₆ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  have h19' : s₄.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; exact toN
  have hTr : Covers [⟨s₄.gpr .r20, (stackArg s₀ 1).toNat⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.r20]
    exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hTd : (⟨s₄.gpr .r20, (stackArg s₀ 1).toNat⟩ : Region).Disjoint ⟨s₄.gpr .r31 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.r20, h4.r31]; exact dtW.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (recv_ok ot.env h19' t1 t16 hTr hTd) fun s₇ ⟨hb₇, hf₇, g₇, k₇⟩ => ?_)
  have he₇ := ot.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr
  rw [h4.r31] at hf₇ hb₇
  have F₇ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₇.mem := F₆.trans (hf₇.sub (inW_at (by decide)))
  -- `cmp 112`
  refine WP.seq (WP.mono (cmp_ok he₇ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_)
  have he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  rw [h4.r31] at hf₈ h3₈
  have F₈ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₈.mem := F₇.trans (hf₈.sub (inW_at (by decide)))
  -- what the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat
  let a := bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat
  let tg := bytesAt s₀.mem (stackArg s₀ 0) (stackArg s₀ 1).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat
  let H := ctxH s₀.mem (s₀.gpr .r3)
  have hH₄ : blockAt s₄.mem (s₄.gpr .r29 + BitVec.ofNat 64 240) = H := by
    rw [h4.r29]; exact ctxH_keep F₄ dcF
  have iv₄ : bytesAt s₄.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat = iv :=
    bytes_W F₄ dnW (by have := (s₀.gpr .r6).isLt; omega)
  have a₄ : bytesAt s₄.mem (s₄.gpr .r21) (s₄.gpr .r22).toNat = a := by
    rw [h4.r21, h4.r22]; exact bytes_W F₄ daW (by have := (s₀.gpr .r8).isLt; omega)
  have ct₅ : bytesAt s₅.mem (s₄.gpr .r27) (s₄.gpr .r23).toNat = ct := by
    rw [h4.r27, h4.r23]; exact bytes_W F₅ ddW (by have := (s₀.gpr .r10).isLt; omega)
  have hc₅ : ciphOf s₅.mem (s₄.gpr .r29) (s₀.gpr .r4).toNat = ciph := by rw [h4.r29]; exact ciph_keep F₅ dcF hR
  have hj₅ : blockAt s₅.mem (s₄.gpr .r30) = j0 H iv := by rw [oa.j, hH₄, iv₄]
  have hT₆ : bytesAt s₆.mem (stackArg s₀ 2 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    have ho := ot.out
    rw [h4.r31, hc₅, hj₅, ct₅, ← h4.r31, hH₄, a₄, ← Proof.Gcm.fullTag_eq] at ho
    rw [← h4.r31]; exact ho
  have hT₇ : bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    rw [bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hT₆
  have hr₇ : bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 1).toNat) := by
    rw [hb₇, h4.r20]; congr 1; exact bytes_W F₆ dtW (by omega)
  let X := (fullTag ciph H iv a ct).take (stackArg s₀ 1).toNat = tg
  have hX : (bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 112) (stackArg s₀ 1).toNat ++
      zeros (16 - (stackArg s₀ 1).toNat) = bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  have r3₈ : s₈.gpr .r3 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  have dat₈ : bytesAt s₈.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = ct :=
    bytes_W F₈ ddW (by have := (s₀.gpr .r10).isLt; omega)
  have cb₈ : blockAt s₈.mem (stackArg s₀ 2 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    have f₆₈ : Frame (otFrame (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) 112 ++
        [⟨stackArg s₀ 2 + BitVec.ofNat 64 256, 16⟩, ⟨stackArg s₀ 2 + BitVec.ofNat 64 272, 16⟩]) s₅.mem s₈.mem :=
      ((f₆.mono fun r hr => List.mem_append_left _ hr).trans (hf₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp)).trans (hf₈.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp)
    rw [blockAt_frame f₆₈ (cb_ot L₀), ← h4.r30, oa.cb, hH₄, iv₄]
  have sv₈ : SavedAt s₈.mem (stackArg s₀ 2) s₀ :=
    (((h4.en.saved.frame f₅ (saved_j0Frame L₀)).frame f₆ (saved_otFrame L₀ (.inr rfl))).frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame hf₈
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  -- the result into `r19`
  obtain ⟨s₉, run₉, h19₉, g₉, k₉⟩ : ∃ s₉, runBlock isa [mov .r19 .r3] s₈ = some s₉ ∧ s₉.gpr .r19 = s₈.gpr .r3 ∧
      (∀ r, r ≠ .r19 → s₉.gpr r = s₈.gpr r) ∧ Keeps s₈ s₉ := by
    refine ⟨_, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · simp [State.write]
    · intro r hr; simp [State.write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have he₉ := Env.self he₈ g₉ k₉
  have e : ∀ r ∈ frozen, r ≠ .r19 → s₉.gpr r = s₄.gpr r := fun r hf hr => (g₉ r hr).trans (he₈.fr r hf)
  have rd₉ : s₉.rd = s₄.rd := k₉.rd.trans (k₈.rd.trans (k₇.rd.trans (rd₆.trans rd₅)))
  have wr₉ : s₉.wr = s₄.wr := k₉.wr.trans (k₈.wr.trans (k₇.wr.trans (wr₆.trans wr₅)))
  have sv₉ : SavedAt s₉.mem (stackArg s₀ 2) s₀ := k₉.mem ▸ sv₈
  have F₉ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₉.mem := k₉.mem ▸ F₈
  have hd₉₀ : DataW (s₀.gpr .r3) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₉ (s₀.gpr .r9)
      (s₀.gpr .r10).toNat := by
    have := hd₄.of_eq rd₉ wr₉
    rwa [h4.r29, h4.r30, h4.r31, h4.r27, h4.r23] at this
  -- the data decrypted only if the tags are equal
  have mid : WP isa (.ite (.zero .d .r19) (.block []) oneCrypt) s₉ fun s₁₀ =>
      Env s₉.gpr s₀.sp s₁₀ ∧ SavedAt s₁₀.mem (stackArg s₀ 2) s₀ ∧ s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      (X → bytesAt s₁₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = gctr ciph (inc32 (j0 H iv)) ct) ∧
      (¬X → bytesAt s₁₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = ct) := by
    have h19n : s₉.gpr .r19 = BitVec.ofNat 64 (if X then 1 else 0) := by
      rw [h19₉, r3₈]; split <;> rfl
    refine WP.ite _ (eval_zero h19n (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬X := fun x => by simp [x] at ht
      exact WP.block_nil ⟨he₉, sv₉, rd₉, wr₉, fun x => absurd x hx, fun _ => k₉.mem ▸ dat₈⟩
    · have hx : X := Classical.byContradiction fun x => by simp [x] at hf
      have L₉ : Lay (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r29, h4.r30,
          h4.r31]
        exact L₀
      have hd₉ : DataW (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) s₉ (s₉.gpr .r27) (s₉.gpr .r23).toNat := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
          e _ (by decide) (by decide), e _ (by decide) (by decide)]
        exact hd₄.of_eq rd₉ wr₉
      have h28₉ : s₉.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat := by rw [e _ (by decide) (by decide)]; exact h28
      have cb₉ : blockAt s₉.mem (s₉.gpr .r30 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [e _ (by decide) (by decide), h4.r30, k₉.mem]; exact cb₈
      refine WP.mono (WP.with_rdwr (oneCrypt_ok L₉ he₉ h28₉ hR hd₉ cb₉)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      have cf := oc.frame
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
        e _ (by decide) (by decide), h4.r30, h4.r31, h4.r27, h4.r23] at cf
      refine ⟨oc.env, sv₉.frame cf (saved_crFrame L₀ hd₉₀), rd₁₀.trans rd₉, wr₁₀.trans wr₉, fun _ => ?_,
        fun x => absurd hx x⟩
      have ho := oc.out
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r27, h4.r23,
        h4.r29, ciph_keep F₉ dcF hR, k₉.mem, dat₈] at ho
      exact ho
  refine WP.seq (WP.mono mid fun s₁₀ ⟨he₁₀, sv₁₀, rd₁₀, wr₁₀, hd₁, hd₂⟩ => ?_)
  -- the result back into `r3`
  refine WP.of_runBlock ⟨_, rfl, ?_⟩
  have g₁₁ : ∀ r, r ≠ .r3 → (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr r = s₁₀.gpr r := fun r hr => by
    simp [State.write, hr]
  have r3₁₁ : (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr .r3 = if X then 1 else 0 := by
    have : (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr .r3 = s₁₀.gpr .r19 := by simp [State.write]
    rw [this, he₁₀.fr _ (by decide), h19₉, r3₈]
  have hres : openRes s₀ = if X then some (gctr ciph (inc32 (j0 H iv)) ct) else none := by
    simp only [openRes, openResult, hok, ite_true, decryptWith]; rfl
  refine ⟨by rw [g₁₁ _ (by decide), he₁₀.fr _ (by decide), e _ (by decide) (by decide), h4.r31],
    by simp only [State.write]; exact he₁₀.sp, fun r hr => ?_, by simp only [State.write]; rw [rd₁₀, hk₄.rd],
    by simp only [State.write]; rw [wr₁₀, hk₄.wr], by simp only [State.write]; exact sv₁₀, ?_⟩
  · have hf : r ∈ frozen := by revert hr; revert r; decide
    rw [g₁₁ r (by revert hr; revert r; decide), he₁₀.fr r hf, e r hf (by revert hr; revert r; decide)]
    exact h4.en.low r hr
  · by_cases hx : X
    · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true hx)))
        (r3₁₁.trans (ite_eq_left_of_eq_true _ _ (eq_true hx))) (hd₁ hx)
    · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false hx)))
        (r3₁₁.trans (ite_eq_right_of_eq_false _ _ (eq_false hx))) (hd₂ hx)

/-- The contract's postcondition, from `OpenPost`, through `restore`. -/
theorem openPost_out {s₀ s s' : State} (op : OpenPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .r3 = s.gpr .r3) :
    openPPC64LE.post s₀ s' := by
  unfold OpenPost at op
  unfold openPPC64LE
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op <;> exact ⟨by rw [op.1]; rfl, op.2⟩

theorem open_wp {s₀ : State} (h : openPPC64LE.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openPPC64LE.post s₀ s' := by
  have h' : openPre s₀ := h
  have hh := h'
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hR⟩ := hh
  have hW : Covers [⟨stackArg s₀ 2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 3] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have dA : (args s₀ 3).Disjoint (savedR (stackArg s₀ 2)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  have hTd : (⟨s₀.sp + BitVec.ofNat 64 96, 8⟩ : Region).Disjoint (savedR (stackArg s₀ 2)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 3 by decide))
  have hLd : (⟨s₀.sp + BitVec.ofNat 64 104, 8⟩ : Region).Disjoint (savedR (stackArg s₀ 2)) := by
    have hs := Offset.sub_base (s₀.sp + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 24) (by decide)
    rw [add_ofNat_assoc] at hs
    exact dA.sub_left hs
  unfold «open» openEntry
  refine WP.seq (WP.block_append (WP.mono (one1_wp (off := 112) (W := stackArg s₀ 2) (T := stackArg s₀ 0)
    (.inr rfl) hW (args_in hA (by decide) (i := 2) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide))
    rfl hTd) fun s₁ h1 => ?_))
  -- `tag_len` into `r19`
  have hi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r12 + BitVec.ofNat 64 104) 8 := by
    rw [h1.r12, h1.en.keeps.rd, h1.en.keeps.wr]; exact args_in hA (by decide) (i := 1) (by decide)
  have hv : s₁.mem.readW (s₁.gpr .r12 + BitVec.ofNat 64 104) 64 = stackArg s₀ 1 := by
    rw [h1.r12, Frame.readW h1.en.frame (r := ⟨s₀.sp + BitVec.ofNat 64 104, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hLd) (by decide)]
    rfl
  refine WP.mono (ld_ok (t := .r19) (by decide) (by decide) (by decide) hi hv) fun s₂ ⟨h19, g₂, k₂⟩ => ?_
  have h2 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₂ := h1.keep (fun r _ hr => g₂ r hr) k₂
  -- the tag length
  have h19' : s₂.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 1).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  have F₂ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₂.mem := h2.en.frame.sub inW_saved
  have mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) openGood) s₃ (OpenOut s₀) := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat
        · rfl
        · simp [e] at ht
      have h₀ : WP isa (.block [.li .r3 0]) s₃ fun s' => s'.gpr .r3 = 0 ∧
          (∀ r, r ≠ .r3 → s'.gpr r = s₃.gpr r) ∧ Keeps s₃ s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₀ fun s' ⟨z3, g, k⟩ => ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
      · rw [g _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.r31
      · rw [k.sp, k₃.sp]; exact h2.en.keeps.sp
      · rw [g r (by revert hr; revert r; decide), g₃ r (by revert hr; revert r; decide)
          (by revert hr; revert r; decide)]
        exact h2.en.low r hr
      · rw [k.rd, k₃.rd]; exact h2.en.keeps.rd
      · rw [k.wr, k₃.wr]; exact h2.en.keeps.wr
      · rw [k.mem, k₃.mem]; exact h2.en.saved
      · refine openPost_none (by simp only [openRes, openResult, hbad]; rfl) z3 ?_
        rw [k.mem, k₃.mem]
        exact bytes_W F₂ ddW (by have := (s₀.gpr .r10).isLt; omega)
    · have hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat
        · simp [e] at hf
        · rfl
      refine WP.seq (WP.of_runBlock ⟨_, rfl, ?_⟩)
      let s₄ := s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)
      have g₄ : ∀ r, r ≠ .r0 → r ≠ .r19 → s₄.gpr r = s₂.gpr r := fun r h0 h19 => by
        by_cases e : r = .r25
        · subst e
          have : s₄.gpr .r25 = s₃.gpr .r18 := by simp [s₄, State.write]
          rw [this, g₃ _ (by decide) (by decide), h2.r18, h2.r25]
        · have : s₄.gpr r = s₃.gpr r := by simp [s₄, State.write, e]
          rw [this, g₃ r h0 e]
      have h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄ := h2.keep g₄ ⟨k₃.mem, k₃.rd, k₃.wr, k₃.sp, k₃.lr⟩
      have e19 : s₄.gpr .r19 = s₃.gpr .r19 := by simp [s₄, State.write]
      exact open_good h' h4 (by rw [e19, g₃ _ (by decide) (by decide)]; exact h19) hok
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.r31 (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp oo.low)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, openPost_out oo.post hm h3⟩

end VG.Proof.AesGcm.PPC64LE
