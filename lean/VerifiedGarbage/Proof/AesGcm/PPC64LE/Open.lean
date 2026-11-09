module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
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
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

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

The proof is of `openWith dec` for any decryption `dec` (`openWith_wp`,
`goodWith`, `tailWith`): `open` is its instance in place (`open_dec`), and
`vg_aes_gcm_open_split` (`OpenTo/Split.lean`) the one to a destination.
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

/-- What the end of `openWith` leaves for `restore`, with `Post` what it
promises given the result `r3`. -/
structure OutWith (Post : State → State → Prop) (s₀ s : State) : Prop where
  r31 : s.gpr .r31 = stackArg s₀ 2
  sp : s.sp = s₀.sp
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 2) s₀
  post : Post s₀ s

/-- What the end of `open` leaves for `restore`. -/
abbrev OpenOut := OutWith OpenPost

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

/-- What `open`'s entry and the computation and comparison of the tags need of
the state, as `openPre` gives it but with the data only read: the buffers
read (the data among them) and `W` written, `W` apart from them. Both `open`
(`HeadPre.of_open`) and `vg_aes_gcm_open_split`, whose data is the source,
satisfy it. -/
structure HeadPre (s : State) : Prop where
  ctx : Covers [⟨s.gpr .r3, 256⟩] (s.rd ++ s.wr)
  nonce : Covers [⟨s.gpr .r5, (s.gpr .r6).toNat⟩] (s.rd ++ s.wr)
  aad : Covers [⟨s.gpr .r7, (s.gpr .r8).toNat⟩] (s.rd ++ s.wr)
  data : Covers [⟨s.gpr .r9, (s.gpr .r10).toNat⟩] (s.rd ++ s.wr)
  tag : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr)
  stk : Covers [VG.Proof.AesGcm.PPC64LE.args s 3] (s.rd ++ s.wr)
  w : Covers [⟨stackArg s 2, 2560⟩] s.wr
  dcW : (⟨s.gpr .r3, 256⟩ : Region).Disjoint ⟨stackArg s 2, 2560⟩
  dnW : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region).Disjoint ⟨stackArg s 2, 2560⟩
  daW : (⟨s.gpr .r7, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨stackArg s 2, 2560⟩
  ddW : (⟨s.gpr .r9, (s.gpr .r10).toNat⟩ : Region).Disjoint ⟨stackArg s 2, 2560⟩
  dtW : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 2, 2560⟩
  dWA : (⟨stackArg s 2, 2560⟩ : Region).Disjoint (VG.Proof.AesGcm.PPC64LE.args s 3)
  fc : (s.gpr .r3).toNat + 256 ≤ 2 ^ 64
  fn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  fa : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  fd : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  ft : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  fW : (stackArg s 2).toNat + 2560 ≤ 2 ^ 64
  hR : rounds (s.gpr .r4)

theorem HeadPre.of_open {s : State} (h : openPre s) : HeadPre s := by
  obtain ⟨hrd, hwr, _, dcW, _, dnW, _, daW, _, ddW, _, dtW, dWA, fc, fn, fa, fd, ft, fW, _, hR⟩ := h
  have r : ∀ x, x ∈ s.rd → Covers [x] (s.rd ++ s.wr) := fun x hx => covers_mem (List.mem_append_left _ hx)
  refine ⟨r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp),
    covers_mem (List.mem_append_right _ (by rw [hwr]; simp)), r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp),
    by rw [hwr]; exact covers_mem (by simp), dcW, dnW, daW, ddW, dtW, dWA, fc, fn, fa, fd, ft, fW, hR⟩

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) (ctxH s₀.mem (s₀.gpr .r3))
      (bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat) (bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat)
      (bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat)).take (stackArg s₀ 1).toNat =
    bytesAt s₀.mem (stackArg s₀ 0) (stackArg s₀ 1).toNat

/-- After the tags are compared, with the result in `r19`, from `s₄` (after
the entry). -/
structure OpenMid (s₀ s₄ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  regs : ∀ r ∈ frozen, r ≠ .r19 → s.gpr r = s₄.gpr r
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr
  saved : SavedAt s.mem (stackArg s₀ 2) s₀
  frame : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem
  cb : blockAt s.mem (stackArg s₀ 2 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat))
  r19 : s.gpr .r19 = BitVec.ofNat 64 (if openTagOk s₀ then 1 else 0)

/-- `open`, once the tag length is allowed, up to the comparison of the tags,
followed by any `T`. -/
theorem open_head [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ s₄ : State} (h : HeadPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄)
    (h19 : s₄.gpr .r19 = stackArg s₀ 1) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true) {T : Prog isa}
    {Q : State → Prop} (k : ∀ s₉, OpenMid s₀ s₄ s₉ → WP isa T s₉ Q) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3]) T))))) s₄ Q := by
  have dcW := h.dcW; have dnW := h.dnW; have daW := h.daW; have ddW := h.ddW; have dtW := h.dtW
  have fn := h.fn; have fa := h.fa; have fd := h.fd; have hR := h.hR
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  have L₀ := oneLay h.fc h.fW dcW
  have hC := h.ctx
  have hW := h.w
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
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.nonce,
      (s₀.gpr .r6).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  have hAd : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r21) (s₄.gpr .r22).toNat := by
    rw [h4.r30, h4.r31, h4.r21, h4.r22]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.aad,
      (s₀.gpr .r8).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.r24 (by rw [h4.r25]; exact toN)
    (by rw [h4.r18]; exact toN) hN hAd)) fun s₅ ⟨oa, rd₅, wr₅, _⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.r30, h4.r31] at f₅
  have F₅ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `oneTag 112`
  have hd₄ : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r27) (s₄.gpr .r23).toNat := by
    rw [h4.r30, h4.r31, h4.r27, h4.r23]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.data, (s₀.gpr .r10).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩
  have h28 : s₄.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat := by rw [h4.r28]; exact toN
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L (o := 112) (.inr rfl) oa.env h28 hR oa.hH
    (length_bytesAt _ _ _).symm oa.abs (hd₄.of_eq rd₅ wr₅))) fun s₆ ⟨ot, rd₆, wr₆, _⟩ => ?_)
  have f₆ := ot.frame
  rw [h4.r30, h4.r31] at f₆
  have F₆ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  have h19' : s₄.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; exact toN
  have hTr : Covers [⟨s₄.gpr .r20, (stackArg s₀ 1).toNat⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.r20]
    exact h.tag
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
    bytes_W F₄ dnW (by have := (s₀.gpr .r6).isLt; omega_arith)
  have a₄ : bytesAt s₄.mem (s₄.gpr .r21) (s₄.gpr .r22).toNat = a := by
    rw [h4.r21, h4.r22]; exact bytes_W F₄ daW (by have := (s₀.gpr .r8).isLt; omega_arith)
  have ct₅ : bytesAt s₅.mem (s₄.gpr .r27) (s₄.gpr .r23).toNat = ct := by
    rw [h4.r27, h4.r23]; exact bytes_W F₅ ddW (by have := (s₀.gpr .r10).isLt; omega_arith)
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
    rw [hb₇, h4.r20]; congr 1; exact bytes_W F₆ dtW (by omega_arith)
  let X := (fullTag ciph H iv a ct).take (stackArg s₀ 1).toNat = tg
  have hX : (bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 112) (stackArg s₀ 1).toNat ++
      zeros (16 - (stackArg s₀ 1).toNat) = bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  have r3₈ : s₈.gpr .r3 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  have dat₈ : bytesAt s₈.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = ct :=
    bytes_W F₈ ddW (by have := (s₀.gpr .r10).isLt; omega_arith)
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
  refine k s₉ ⟨he₉, e, rd₉, wr₉, k₉.mem ▸ sv₈, k₉.mem ▸ F₈, by rw [k₉.mem]; exact cb₈, ?_⟩
  rw [h19₉, r3₈]
  show _ = BitVec.ofNat 64 (if X then 1 else 0)
  by_cases hx : X
  · simp only [eq_true hx, ite_true]; rfl
  · simp only [eq_false hx, ite_false]; rfl

/-- The plaintext, if the tag is right. -/
abbrev openPt (s₀ : State) : List Byte :=
  gctr (ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat)
    (inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat)))
    (bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat)

theorem openRes_eq {s₀ : State} (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true) :
    openRes s₀ = if openTagOk s₀ then some (openPt s₀) else none := by
  simp only [openRes, openResult, hok, ite_true, decryptWith]

/-- What `openWith`'s decryption leaves, from `s₉` after the comparison
(`OpenMid`): `Out` holds of the memory. -/
def DecOut (s₀ s₄ s₉ : State) (Out : Mem → Prop) (s : State) : Prop :=
  Env s₉.gpr s₀.sp s ∧ SavedAt s.mem (stackArg s₀ 2) s₀ ∧ s.rd = s₄.rd ∧ s.wr = s₄.wr ∧ Out s.mem

/-- The registers after the comparison of the tags, and the first counter block. -/
structure MidAt (s₀ s : State) : Prop where
  lay : Lay (s.gpr .r29) (s.gpr .r30) (s.gpr .r31)
  r23 : s.gpr .r23 = s₀.gpr .r10
  r27 : s.gpr .r27 = s₀.gpr .r9
  r28 : s.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat
  r29 : s.gpr .r29 = s₀.gpr .r3
  r30 : s.gpr .r30 = stackArg s₀ 2 + BitVec.ofNat 64 16
  r31 : s.gpr .r31 = stackArg s₀ 2
  cb : blockAt s.mem (s.gpr .r30 + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat))

theorem OpenMid.at {s₀ s₄ s₉ : State} (h : HeadPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄)
    (om : OpenMid s₀ s₄ s₉) : MidAt s₀ s₉ := by
  have e := om.regs
  have r29 : s₉.gpr .r29 = s₀.gpr .r3 := by rw [e _ (by decide) (by decide), h4.r29]
  have r30 : s₉.gpr .r30 = stackArg s₀ 2 + BitVec.ofNat 64 16 := by rw [e _ (by decide) (by decide), h4.r30]
  have r31 : s₉.gpr .r31 = stackArg s₀ 2 := by rw [e _ (by decide) (by decide), h4.r31]
  refine ⟨by rw [r29, r30, r31]; exact oneLay h.fc h.fW h.dcW, by rw [e _ (by decide) (by decide), h4.r23],
    by rw [e _ (by decide) (by decide), h4.r27], ?_, r29, r30, r31, by rw [r30]; exact om.cb⟩
  rw [e _ (by decide) (by decide), h4.r28]; simp

/-- `openWith dec` from the comparison's result on: `dec` only if the tags
are equal, leaving `Out`; the memory but `W` as it was otherwise. -/
theorem tailWith {dec : Prog isa} {Post : State → State → Prop} {Out : Mem → Prop} {s₀ s₄ s₉ : State}
    (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true)
    (om : OpenMid s₀ s₄ s₉) (hdec : openTagOk s₀ → WP isa dec s₉ (DecOut s₀ s₄ s₉ Out))
    (hsome : ∀ s, openRes s₀ = some (openPt s₀) → s.gpr .r3 = 1 → Out s.mem → Post s₀ s)
    (hnone : ∀ s, openRes s₀ = none → s.gpr .r3 = 0 →
      Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem → Post s₀ s) :
    WP isa (.seq (.ite (.zero .d .r19) (.block []) dec) (.block [mov .r3 .r19])) s₉ (OutWith Post s₀) := by
  have hk₄ := h4.en.keeps
  have e := om.regs
  -- the data decrypted only if the tags are equal
  have mid : WP isa (.ite (.zero .d .r19) (.block []) dec) s₉ fun s₁₀ =>
      Env s₉.gpr s₀.sp s₁₀ ∧ SavedAt s₁₀.mem (stackArg s₀ 2) s₀ ∧ s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      (openTagOk s₀ → Out s₁₀.mem) ∧
      (¬openTagOk s₀ → Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₁₀.mem) := by
    refine WP.ite _ (eval_zero om.r19 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬(openTagOk s₀) := fun x => by simp [x] at ht
      exact WP.block_nil ⟨om.env, om.saved, om.rd, om.wr, fun x => absurd x hx, fun _ => om.frame⟩
    · have hx : (openTagOk s₀) := Classical.byContradiction fun x => by simp [x] at hf
      exact WP.mono (hdec hx) fun s ⟨a, b, c, d, o⟩ => ⟨a, b, c, d, fun _ => o, fun x => absurd hx x⟩
  refine WP.seq (WP.mono mid fun s₁₀ ⟨he₁₀, sv₁₀, rd₁₀, wr₁₀, hd₁, hd₂⟩ => ?_)
  -- the result back into `r3`
  refine WP.of_runBlock ⟨_, rfl, ?_⟩
  have g₁₁ : ∀ r, r ≠ .r3 → (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr r = s₁₀.gpr r := fun r hr => by
    simp [State.write, hr]
  have r3₁₁ : (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr .r3 = if (openTagOk s₀) then 1 else 0 := by
    have : (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr .r3 = s₁₀.gpr .r19 := by simp [State.write]
    rw [this, he₁₀.fr _ (by decide), om.r19]
    by_cases hx : openTagOk s₀
    · simp only [eq_true hx, ite_true]; rfl
    · simp only [eq_false hx, ite_false]; rfl
  have hres := openRes_eq hok
  refine ⟨by rw [g₁₁ _ (by decide), he₁₀.fr _ (by decide), e _ (by decide) (by decide), h4.r31],
    by simp only [State.write]; exact he₁₀.sp, fun r hr => ?_, by simp only [State.write]; rw [rd₁₀, hk₄.rd],
    by simp only [State.write]; rw [wr₁₀, hk₄.wr], by simp only [State.write]; exact sv₁₀, ?_⟩
  · have hf : r ∈ frozen := by revert hr; revert r; decide
    rw [g₁₁ r (by revert hr; revert r; decide), he₁₀.fr r hf, e r hf (by revert hr; revert r; decide)]
    exact h4.en.low r hr
  · by_cases hx : (openTagOk s₀)
    · exact hsome _ (hres.trans (ite_eq_left hx)) (r3₁₁.trans (ite_eq_left hx)) (hd₁ hx)
    · exact hnone _ (hres.trans (ite_eq_right hx)) (r3₁₁.trans (ite_eq_right hx)) (hd₂ hx)

/-- `openWith dec`, once the tag length is allowed: `open_head`, then `tailWith`. -/
theorem goodWith [VG.Proof.Gcm.PPC64LE.GhashLaw] {dec : Prog isa} {Post : State → State → Prop}
    {Out : Mem → Prop} {s₀ s₄ : State} (hp : HeadPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄)
    (h19 : s₄.gpr .r19 = stackArg s₀ 1) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true)
    (hdec : ∀ s₉, OpenMid s₀ s₄ s₉ → openTagOk s₀ → WP isa dec s₉ (DecOut s₀ s₄ s₉ Out))
    (hsome : ∀ s, openRes s₀ = some (openPt s₀) → s.gpr .r3 = 1 → Out s.mem → Post s₀ s)
    (hnone : ∀ s, openRes s₀ = none → s.gpr .r3 = 0 →
      Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem → Post s₀ s) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3])
      (.seq (.ite (.zero .d .r19) (.block []) dec) (.block [mov .r3 .r19]))))))) s₄ (OutWith Post s₀) :=
  open_head hp h4 h19 hok fun s₉ om => tailWith h4 hok om (hdec s₉ om) hsome hnone

/-- `open`'s decryption, in place: the data is then the plaintext. -/
theorem open_dec {s₀ s₄ s₉ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄)
    (om : OpenMid s₀ s₄ s₉) :
    WP isa oneCrypt s₉ (DecOut s₀ s₄ s₉ fun m => bytesAt m (s₀.gpr .r9) (s₀.gpr .r10).toNat = openPt s₀) := by
  have hp := HeadPre.of_open h
  obtain ⟨_, hwr, dcd, dcW, _, _, _, _, _, ddW, _, _, _, fc, _, _, fd, _, fW, _, hR⟩ := h
  have M := om.at hp h4
  have hk₄ := h4.en.keeps
  have dcF : ∀ r ∈ [(⟨stackArg s₀ 2, 2560⟩ : Region)], (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact dcW
  have dat₉ : bytesAt s₉.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat :=
    bytes_W om.frame ddW (by have := (s₀.gpr .r10).isLt; omega_arith)
  have hd₉₀ : DataW (s₀.gpr .r3) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₉ (s₀.gpr .r9)
      (s₀.gpr .r10).toNat := by
    have hw : Covers [⟨s₀.gpr .r9, (s₀.gpr .r10).toNat⟩] s₉.wr := by
      rw [om.wr, hk₄.wr, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hw, (s₀.gpr .r10).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hw, dcd⟩
  have hd₉ : DataW (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) s₉ (s₉.gpr .r27) (s₉.gpr .r23).toNat := by
    rw [M.r29, M.r30, M.r31, M.r27, M.r23]; exact hd₉₀
  refine WP.mono (WP.with_rdwr (oneCrypt_ok M.lay om.env M.r28 hR hd₉ M.cb)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
  have cf := oc.frame
  rw [M.r30, M.r31, M.r27, M.r23] at cf
  refine ⟨oc.env, om.saved.frame cf (saved_crFrame (oneLay fc fW dcW) hd₉₀), rd₁₀.trans om.rd,
    wr₁₀.trans om.wr, ?_⟩
  have ho := oc.out
  rw [M.r27, M.r23, M.r29, ciph_keep om.frame dcF hR, dat₉] at ho
  exact ho

/-- If the tag is wrong, or its length is not allowed, the data is as it was. -/
theorem open_none {s₀ : State} (h : openPre s₀) : ∀ s, openRes s₀ = none → s.gpr .r3 = 0 →
    Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem → OpenPost s₀ s :=
  fun _ hr h0 hf => openPost_none hr h0 (bytes_W hf (HeadPre.of_open h).ddW
    (by have := (s₀.gpr .r10).isLt; omega_arith))

theorem open_good [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄)
    (h19 : s₄.gpr .r19 = stackArg s₀ 1) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3])
      (.seq (.ite (.zero .d .r19) (.block []) oneCrypt) (.block [mov .r3 .r19]))))))) s₄ (OpenOut s₀) :=
  goodWith (HeadPre.of_open h) h4 h19 hok (fun _ om _ => open_dec h h4 om)
    (fun _ hr h1 hd => openPost_some hr h1 hd) (open_none h)

/-- The contract's postcondition, from `OpenPost`, through `restore`. -/
theorem openPost_out {s₀ s s' : State} (op : OpenPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .r3 = s.gpr .r3) :
    openPPC64LE.post s₀ s' := by
  unfold OpenPost at op
  unfold openPPC64LE
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op <;> exact ⟨by rw [op.1]; rfl, op.2⟩

/-- The entry of `open`, and `tag_len` in `r19`. -/
theorem openEntry_wp {s₀ : State} (h : HeadPre s₀) :
    WP isa (.block openEntry) s₀ fun s₂ =>
      SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₂ ∧ s₂.gpr .r19 = stackArg s₀ 1 := by
  have hW := h.w
  have hA := h.stk
  have dA : (args s₀ 3).Disjoint (savedR (stackArg s₀ 2)) :=
    (h.dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  have hTd : (⟨s₀.sp + BitVec.ofNat 64 96, 8⟩ : Region).Disjoint (savedR (stackArg s₀ 2)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 3 by decide))
  have hLd : (⟨s₀.sp + BitVec.ofNat 64 104, 8⟩ : Region).Disjoint (savedR (stackArg s₀ 2)) := by
    have hs := Offset.sub_base (s₀.sp + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 24) (by decide)
    rw [add_ofNat_assoc] at hs
    exact dA.sub_left hs
  unfold openEntry
  refine WP.block_append (WP.mono (one1_wp (off := 112) (W := stackArg s₀ 2) (T := stackArg s₀ 0)
    (.inr rfl) hW (args_in hA (by decide) (i := 2) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide))
    rfl hTd) fun s₁ h1 => ?_)
  -- `tag_len` into `r19`
  have hi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r12 + BitVec.ofNat 64 104) 8 := by
    rw [h1.r12, h1.en.keeps.rd, h1.en.keeps.wr]; exact args_in hA (by decide) (i := 1) (by decide)
  have hv : s₁.mem.readW (s₁.gpr .r12 + BitVec.ofNat 64 104) 64 = stackArg s₀ 1 := by
    rw [h1.r12, Frame.readW h1.en.frame (r := ⟨s₀.sp + BitVec.ofNat 64 104, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hLd) (by decide)]
    rfl
  refine WP.mono (ld_ok (t := .r19) (by decide) (by decide) (by decide) hi hv) fun s₂ ⟨h19, g₂, k₂⟩ => ?_
  exact ⟨h1.keep (fun r _ hr => g₂ r hr) k₂, h19⟩

/-- `openWith dec`, from `HeadPre`: `dec` decrypts the data, leaving `Out`,
once the tag is right; `Post` holds of the end in every case, and `Q`
after `restore`. -/
theorem openWith_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {dec : Prog isa} {Post : State → State → Prop}
    {Out : Mem → Prop} {Q : State → Prop} {s₀ : State} (hp : HeadPre s₀)
    (hdec : ∀ s₄ s₉, SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄ → OpenMid s₀ s₄ s₉ → openTagOk s₀ →
      WP isa dec s₉ (DecOut s₀ s₄ s₉ Out))
    (hsome : ∀ s, openRes s₀ = some (openPt s₀) → s.gpr .r3 = 1 → Out s.mem → Post s₀ s)
    (hnone : ∀ s, openRes s₀ = none → s.gpr .r3 = 0 →
      Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem → Post s₀ s)
    (hout : ∀ s s', Post s₀ s → s'.mem = s.mem → s'.gpr .r3 = s.gpr .r3 → Q s') :
    WP isa (openWith dec) s₀ fun s' => abiPreserved s₀ s' ∧ Q s' := by
  have hW := hp.w
  unfold openWith
  refine WP.seq (WP.mono (openEntry_wp hp) fun s₂ ⟨h2, h19⟩ => ?_)
  -- the tag length
  have h19' : s₂.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 1).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  have F₂ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₂.mem := h2.en.frame.sub inW_saved
  have mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) (openGoodWith dec)) s₃ (OutWith Post s₀) := by
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
      · exact hnone s' (by simp only [openRes, openResult, hbad]; rfl) z3 (by rw [k.mem, k₃.mem]; exact F₂)
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
      exact goodWith hp h4 (by rw [e19, g₃ _ (by decide) (by decide)]; exact h19) hok
        (fun s₉ om => hdec s₄ s₉ h4 om) hsome hnone
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.r31 (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp oo.low)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, hout _ _ oo.post hm h3⟩

theorem open_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : openPPC64LE.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openPPC64LE.post s₀ s' :=
  have h' : openPre s₀ := h
  openWith_wp (HeadPre.of_open h') (fun _ _ h4 om _ => open_dec h' h4 om)
    (fun _ hr h1 hd => openPost_some hr h1 hd) (open_none h') (fun _ _ op hm h3 => openPost_out op hm h3)

end VG.Proof.AesGcm.PPC64LE
