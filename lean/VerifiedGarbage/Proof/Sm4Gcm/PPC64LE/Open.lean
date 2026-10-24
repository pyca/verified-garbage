module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.OneShot
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Seal
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/Open.lean`), with SM4's counter mode: `open` checks
the tag length; if it is allowed, it computes the tag of the ciphertext into
`W + 112` (`oneAad`, `oneTag 112`), copies the received tag to `W + 256` and
compares the first `tag_len` bytes of each (`recv`, `cmp 112`), and decrypts
the data in place only if they are equal; `r3` is the result (`open_wp`).
Until the data is decrypted, everything `open` writes is in the working
space `W` and SM4's (`Frame (WX W X)`), which every buffer is apart from.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov recv cmp tagLenOk oneAad)
open VG.Proof.AesGcm.PPC64LE (Env Env.self Keeps Lay DataW DataOk SavedAt savedR frozen restore_ok covers_mem covers_left
  covers_off covers_prefix bytesAt_frame blockAt_frame ctxH_keep saved_w WP.with_rdwr saved_j0Frame oneAad_ok
  oneLay args_in j0Frame length_bytesAt tagLenOk_bounds recv_ok cmp_ok tagLenOk_ok eval_zero ld_ok bytesAt_take
  add_ofNat_assoc)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH fullTag zeros padLen j0 inc32 gctr decryptWith openResult)
open VG.Spec.Sm4.Gcm (ctxCiph)

/-- What `open` promises, given the result `r3` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r3 = 1 ∧ bytesAt s.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = pt
  | none => s.gpr .r3 = 0 ∧ bytesAt s.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .r3 = 0)
    (hd : bytesAt s.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .r3 = 1)
    (hd : bytesAt s.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- What the end of `open` leaves for `restore`. -/
structure OpenOut (s₀ s : State) : Prop where
  r31 : s.gpr .r31 = stackArg s₀ 1
  sp : s.sp = s₀.sp
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 1) s₀
  post : OpenPost s₀ s

/-- The working spaces, AES-GCM's `W` and SM4's `X`. -/
abbrev WX (W X : Addr) : List Region := [⟨W, scrBytes⟩, ⟨X, xBytes⟩]

section
variable {W x : Addr}

/-- What `oneAad`, `oneTag 112`, `recv` and `cmp 112` write is in the working spaces. -/
theorem inW_j0 : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, ∃ r' ∈ WX W x, Region.Sub r r' := by
  intro r hr
  simp only [j0Frame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩

theorem inW_ot : ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W x 112, ∃ r' ∈ WX W x, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

theorem inW_at {d : Nat} (hd : d + 16 ≤ scrBytes) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ WX W x, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ hd⟩

theorem inW_saved : ∀ r ∈ [savedR W], ∃ r' ∈ WX W x, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩

/-- The first counter block is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem cb_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) (X : XOk c (W + BitVec.ofNat 64 16) W x) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W x 112 ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.st_st (st := W + BitVec.ofNat 64 16) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide))
      (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact X.sx.sub_left (Lay.stSub (by decide))
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)

end

/-- A buffer apart from the working spaces is as it was. -/
theorem bytes_W {m m' : Mem} {W X p : Addr} {n : Nat} (hf : Frame (WX W X) m m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨W, scrBytes⟩) (hx : (⟨p, n⟩ : Region).Disjoint ⟨X, xBytes⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hx) hn

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3))
      (bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat) (bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat)
      (bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat)).take (stackArg s₀ 0).toNat =
    bytesAt s₀.mem (s₀.gpr .r10) (stackArg s₀ 0).toNat

/-- After the tags are compared, with the result in `r19`, from `s₄` (after
the entry). -/
structure OpenMid (s₀ s₄ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  regs : ∀ r ∈ frozen, r ≠ .r19 → s.gpr r = s₄.gpr r
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr
  saved : SavedAt s.mem (stackArg s₀ 1) s₀
  frame : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s.mem
  cb : blockAt s.mem (stackArg s₀ 1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat))
  r19 : s.gpr .r19 = BitVec.ofNat 64 (if openTagOk s₀ then 1 else 0)

/-- `open`, once the tag length is allowed, up to the comparison of the tags,
followed by any `T`. -/
theorem open_head {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₄)
    (h19 : s₄.gpr .r19 = stackArg s₀ 0) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) {T : Prog isa}
    {Q : State → Prop} (k : ∀ s₉, OpenMid s₀ s₄ s₉ → WP isa T s₉ Q) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3]) T))))) s₄ Q := by
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, dcx, dnx,
    dax, ddx, dtx, dwx, dxA, fx⟩ := hh
  have hW' : Covers [⟨stackArg s₀ 1, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hXw : Covers [xR (stackArg s₀ 2)] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  have L₀ := oneLay fc fW dcW
  have hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := covers_prefix hW' (by decide)
  have he₄ := one_env h4 hC hW
  have L := L₀.v h4.r29 h4.r30 h4.r31
  have X₀ := oneX fx dcx dwx
  have X : XOk (s₄.gpr .r29) (s₄.gpr .r30) (s₄.gpr .r31) (s₄.gpr .r28) := by
    rw [h4.r29, h4.r30, h4.r31, h4.r28]; exact X₀
  have hk₄ := h4.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ WX (stackArg s₀ 1) (stackArg s₀ 2), (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact dcx
  have F₄ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₄.mem := h4.en.frame.sub inW_saved
  -- `oneAad`
  have hN : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₀.gpr .r4) (s₀.gpr .r5).toNat := by
    rw [h4.r30, h4.r31]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .r5).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  have hAd : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r21) (s₄.gpr .r22).toNat := by
    rw [h4.r30, h4.r31, h4.r21, h4.r22]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .r7).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.r24 (by rw [h4.r25]; exact toN)
    (by rw [h4.r18]; exact toN) hN hAd)) fun s₅ ⟨oa, rd₅, wr₅, _⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.r30, h4.r31] at f₅
  have F₅ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `oneTag 112`
  have hDw₄ : Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  have hd₄ : DataW (s₄.gpr .r29) (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r27) (s₄.gpr .r23).toNat := by
    rw [h4.r29, h4.r30, h4.r31, h4.r27, h4.r23]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .r9).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw₄, dcd⟩
  have hxw₅ : Covers [xR (s₄.gpr .r28)] s₅.wr := by
    rw [wr₅, hk₄.wr, h4.r28]; exact hXw
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L X (o := 112) (.inr rfl) oa.env hxw₅ oa.hH
    (length_bytesAt _ _ _).symm oa.abs (hd₄.ok.of_eq rd₅ wr₅))) fun s₆ ⟨ot, rd₆, wr₆, _⟩ => ?_)
  have f₆ := ot.frame
  rw [h4.r30, h4.r31, h4.r28] at f₆
  have F₆ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  have h19' : s₄.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 0).toNat := by rw [h19]; exact toN
  have hTr : Covers [⟨s₄.gpr .r20, (stackArg s₀ 0).toNat⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.r20]
    exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hTd : (⟨s₄.gpr .r20, (stackArg s₀ 0).toNat⟩ : Region).Disjoint ⟨s₄.gpr .r31 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.r20, h4.r31]; exact dtW.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (recv_ok ot.env h19' t1 t16 hTr hTd) fun s₇ ⟨hb₇, hf₇, g₇, k₇⟩ => ?_)
  have he₇ := ot.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr
  rw [h4.r31] at hf₇ hb₇
  have F₇ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₇.mem := F₆.trans (hf₇.sub (inW_at (by decide)))
  -- `cmp 112`
  refine WP.seq (WP.mono (cmp_ok he₇ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_)
  have he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  rw [h4.r31] at hf₈ h3₈
  have F₈ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₈.mem := F₇.trans (hf₈.sub (inW_at (by decide)))
  -- what the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat
  let a := bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat
  let tg := bytesAt s₀.mem (s₀.gpr .r10) (stackArg s₀ 0).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .r3)
  let H := ctxH s₀.mem (s₀.gpr .r3)
  have hH₄ : blockAt s₄.mem (s₄.gpr .r29 + BitVec.ofNat 64 240) = H := by
    rw [h4.r29]; exact ctxH_keep F₄ dcF
  have iv₄ : bytesAt s₄.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat = iv :=
    bytes_W F₄ dnW dnx (by have := (s₀.gpr .r5).isLt; omega)
  have a₄ : bytesAt s₄.mem (s₄.gpr .r21) (s₄.gpr .r22).toNat = a := by
    rw [h4.r21, h4.r22]; exact bytes_W F₄ daW dax (by have := (s₀.gpr .r7).isLt; omega)
  have ct₅ : bytesAt s₅.mem (s₄.gpr .r27) (s₄.gpr .r23).toNat = ct := by
    rw [h4.r27, h4.r23]; exact bytes_W F₅ ddW ddx (by have := (s₀.gpr .r9).isLt; omega)
  have hc₅ : ciphOf s₅.mem (s₄.gpr .r29) = ciph := by rw [h4.r29]; exact ciph_keep F₅ dcF
  have hj₅ : blockAt s₅.mem (s₄.gpr .r30) = j0 H iv := by rw [oa.j, hH₄, iv₄]
  have hT₆ : bytesAt s₆.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    have ho := ot.out
    rw [h4.r31, hc₅, hj₅, ct₅, ← h4.r31, hH₄, a₄, ← Proof.Gcm.fullTag_eq] at ho
    rw [← h4.r31]; exact ho
  have hT₇ : bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    rw [bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hT₆
  have hr₇ : bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 0).toNat) := by
    rw [hb₇, h4.r20]; congr 1; exact bytes_W F₆ dtW dtx (by omega)
  let X := (fullTag ciph H iv a ct).take (stackArg s₀ 0).toNat = tg
  have hX : (bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) (stackArg s₀ 0).toNat ++
      zeros (16 - (stackArg s₀ 0).toNat) = bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  have r3₈ : s₈.gpr .r3 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  have dat₈ : bytesAt s₈.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = ct :=
    bytes_W F₈ ddW ddx (by have := (s₀.gpr .r9).isLt; omega)
  have cb₈ : blockAt s₈.mem (stackArg s₀ 1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    have f₆₈ : Frame (otFrame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) (stackArg s₀ 2) 112 ++
        [⟨stackArg s₀ 1 + BitVec.ofNat 64 256, 16⟩, ⟨stackArg s₀ 1 + BitVec.ofNat 64 272, 16⟩]) s₅.mem s₈.mem :=
      ((f₆.mono fun r hr => List.mem_append_left _ hr).trans (hf₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp)).trans (hf₈.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp)
    rw [blockAt_frame f₆₈ (cb_ot L₀ X₀), ← h4.r30, oa.cb, hH₄, iv₄]
  have sv₈ : SavedAt s₈.mem (stackArg s₀ 1) s₀ :=
    (((h4.en.saved.frame f₅ (saved_j0Frame L₀)).frame f₆ (saved_otFrame L₀ X₀ (.inr rfl))).frame hf₇ (fun r hr => by
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

/-- `open` from the comparison's result on. -/
theorem open_tail {s₀ s₄ s₉ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₄)
    (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) (om : OpenMid s₀ s₄ s₉) :
    WP isa (.seq (.ite (.zero .d .r19) (.block []) oneCrypt) (.block [mov .r3 .r19])) s₉ (OpenOut s₀) := by
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, dcx, dnx,
    dax, ddx, dtx, dwx, dxA, fx⟩ := hh
  have hW' : Covers [⟨stackArg s₀ 1, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hXw : Covers [xR (stackArg s₀ 2)] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have L₀ := oneLay fc fW dcW
  have hk₄ := h4.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ WX (stackArg s₀ 1) (stackArg s₀ 2), (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact dcx
  have hDw₄ : Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  have hd₄ : DataW (s₄.gpr .r29) (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r27) (s₄.gpr .r23).toNat := by
    rw [h4.r29, h4.r30, h4.r31, h4.r27, h4.r23]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .r9).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw₄, dcd⟩
  have X₀ := oneX fx dcx dwx
  let iv := bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .r3)
  let H := ctxH s₀.mem (s₀.gpr .r3)
  have he₉ := om.env
  have e := om.regs
  have rd₉ := om.rd
  have wr₉ := om.wr
  have sv₉ := om.saved
  have F₉ := om.frame
  have dat₉ : bytesAt s₉.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = ct :=
    bytes_W F₉ ddW ddx (by have := (s₀.gpr .r9).isLt; omega)
  have hd₉₀ : DataW (s₀.gpr .r3) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₉ (s₀.gpr .r8)
      (s₀.gpr .r9).toNat := by
    have := hd₄.of_eq rd₉ wr₉
    rwa [h4.r29, h4.r30, h4.r31, h4.r27, h4.r23] at this
  -- the data decrypted only if the tags are equal
  have mid : WP isa (.ite (.zero .d .r19) (.block []) oneCrypt) s₉ fun s₁₀ =>
      Env s₉.gpr s₀.sp s₁₀ ∧ SavedAt s₁₀.mem (stackArg s₀ 1) s₀ ∧ s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      ((openTagOk s₀) → bytesAt s₁₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = gctr ciph (inc32 (j0 H iv)) ct) ∧
      (¬(openTagOk s₀) → bytesAt s₁₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = ct) := by
    refine WP.ite _ (eval_zero om.r19 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬(openTagOk s₀) := fun x => by simp [x] at ht
      exact WP.block_nil ⟨he₉, sv₉, rd₉, wr₉, fun x => absurd x hx, fun _ => dat₉⟩
    · have hx : (openTagOk s₀) := Classical.byContradiction fun x => by simp [x] at hf
      have L₉ : Lay (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r29, h4.r30,
          h4.r31]
        exact L₀
      have hd₉ : DataW (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) s₉ (s₉.gpr .r27) (s₉.gpr .r23).toNat := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
          e _ (by decide) (by decide), e _ (by decide) (by decide)]
        exact hd₄.of_eq rd₉ wr₉
      have X₉ : XOk (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) (s₉.gpr .r28) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
          e _ (by decide) (by decide), h4.r29, h4.r30, h4.r31, h4.r28]
        exact X₀
      have hxw₉ : Covers [xR (s₉.gpr .r28)] s₉.wr := by
        rw [e _ (by decide) (by decide), h4.r28, wr₉, hk₄.wr]; exact hXw
      have hdx₉ : (⟨s₉.gpr .r27, (s₉.gpr .r23).toNat⟩ : Region).Disjoint (xR (s₉.gpr .r28)) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r27, h4.r23,
          h4.r28]
        exact ddx
      have cb₉ : blockAt s₉.mem (s₉.gpr .r30 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [e _ (by decide) (by decide), h4.r30]; exact om.cb
      refine WP.mono (WP.with_rdwr (oneCrypt_ok L₉ X₉ he₉ hd₉ hxw₉ hdx₉ cb₉)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      have cf := oc.frame
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
        e _ (by decide) (by decide), h4.r30, h4.r28, h4.r27, h4.r23] at cf
      refine ⟨oc.env, sv₉.frame cf (saved_crFrame L₀ X₀ hd₉₀), rd₁₀.trans rd₉, wr₁₀.trans wr₉, fun _ => ?_,
        fun x => absurd hx x⟩
      have ho := oc.out
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r27, h4.r23,
        h4.r29, ciph_keep F₉ dcF, dat₉] at ho
      exact ho
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
  have hres : openRes s₀ = if (openTagOk s₀) then some (gctr ciph (inc32 (j0 H iv)) ct) else none := by
    simp only [openRes, openResult, hok, ite_true, decryptWith]; rfl
  refine ⟨by rw [g₁₁ _ (by decide), he₁₀.fr _ (by decide), e _ (by decide) (by decide), h4.r31],
    by simp only [State.write]; exact he₁₀.sp, fun r hr => ?_, by simp only [State.write]; rw [rd₁₀, hk₄.rd],
    by simp only [State.write]; rw [wr₁₀, hk₄.wr], by simp only [State.write]; exact sv₁₀, ?_⟩
  · have hf : r ∈ frozen := by revert hr; revert r; decide
    rw [g₁₁ r (by revert hr; revert r; decide), he₁₀.fr r hf, e r hf (by revert hr; revert r; decide)]
    exact h4.en.low r hr
  · by_cases hx : (openTagOk s₀)
    · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true hx)))
        (r3₁₁.trans (ite_eq_left_of_eq_true _ _ (eq_true hx))) (hd₁ hx)
    · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false hx)))
        (r3₁₁.trans (ite_eq_right_of_eq_false _ _ (eq_false hx))) (hd₂ hx)


theorem open_good {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₄)
    (h19 : s₄.gpr .r19 = stackArg s₀ 0) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3])
      (.seq (.ite (.zero .d .r19) (.block []) oneCrypt) (.block [mov .r3 .r19]))))))) s₄ (OpenOut s₀) :=
  open_head h h4 h19 hok fun _ om => open_tail h h4 hok om

/-- The contract's postcondition, from `OpenPost`, through `restore`. -/
theorem openPost_out {s₀ s s' : State} (op : OpenPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .r3 = s.gpr .r3) :
    openPPC64LE.post s₀ s' := by
  unfold OpenPost at op
  unfold openPPC64LE
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op <;> exact ⟨by rw [op.1]; rfl, op.2⟩

/-- `tag_len` into `r19`. -/
theorem tl_ok {s : State} {v : BitVec 64} (hi : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96) 8)
    (hv : s.mem.readW (s.sp + BitVec.ofNat 64 96) 64 = v) :
    WP isa (.block [.addSp .r12 0, .load .d .r19 .r12 96]) s fun s' =>
      s'.gpr .r19 = v ∧ (∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r19 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.write, Size.bytes,
    hi, Proof.Gcm.PPC64LE.read_8, hv, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ne_eq, not_false_eq_true, Nat.reduceLT, Nat.reducePow, Nat.reduceMod, ↓reduceIte,
    and_self, implies_true, BitVec.setWidth_eq, BitVec.add_zero]
  exact ⟨trivial, fun r a b c => by simp [b, c], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The entry of `open`, and `tag_len` in `r19`. -/
theorem openEntry_wp {s₀ : State} (h : openPre s₀) :
    WP isa (.block openEntry) s₀ fun s₂ =>
      SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₂ ∧ s₂.gpr .r19 = stackArg s₀ 0 := by
  have hh := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, dXA, -⟩ := hh
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 3] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have dA : (args s₀ 3).Disjoint (savedR (stackArg s₀ 1)) :=
    (dXA.sub_left (VG.Offset.sub_base _ (d := 128) (n := 120) (by decide))).symm
  have hTd : (⟨s₀.sp + BitVec.ofNat 64 96, 8⟩ : Region).Disjoint (savedR (stackArg s₀ 1)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 3 by decide))
  have hXd : (⟨s₀.sp + BitVec.ofNat 64 (104 + 8), 8⟩ : Region).Disjoint (savedR (stackArg s₀ 1)) := by
    have hs := VG.Offset.sub_base (s₀.sp + BitVec.ofNat 64 96) (d := 16) (n := 8) (k := 24) (by decide)
    rw [add_ofNat_assoc] at hs
    exact dA.sub_left hs
  unfold openEntry
  refine WP.block_append (WP.mono (one1_wp (off := 104) (W := stackArg s₀ 1) (X := stackArg s₀ 2) (.inr rfl) hW
    (args_in hA (by decide) (i := 1) (by decide)) rfl (args_in hA (by decide) (i := 2) (by decide)) rfl hXd)
    fun s₁ h1 => ?_)
  have hi : InRegions (s₁.rd ++ s₁.wr) (s₁.sp + BitVec.ofNat 64 96) 8 := by
    rw [h1.en.keeps.sp, h1.en.keeps.rd, h1.en.keeps.wr]; exact args_in hA (by decide) (i := 0) (by decide)
  have hv : s₁.mem.readW (s₁.sp + BitVec.ofNat 64 96) 64 = stackArg s₀ 0 := by
    rw [h1.en.keeps.sp, Frame.readW h1.en.frame (r := ⟨s₀.sp + BitVec.ofNat 64 96, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd) (by decide)]
    rfl
  refine WP.mono (tl_ok hi hv) fun s₂ ⟨h19, g₂, k₂⟩ => ?_
  exact ⟨h1.keep g₂ k₂, h19⟩

theorem open_wp {s₀ : State} (h : openPPC64LE.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openPPC64LE.post s₀ s' := by
  have h' : openPre s₀ := h
  have hh := h'
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, dcx, dnx,
    dax, ddx, dtx, dwx, dxA, fx⟩ := hh
  have hW' : Covers [⟨stackArg s₀ 1, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hXw : Covers [xR (stackArg s₀ 2)] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := covers_prefix hW' (by decide)
  unfold «open»
  refine WP.seq (WP.mono (openEntry_wp h') fun s₂ ⟨h2, h19⟩ => ?_)
  -- the tag length
  have h19' : s₂.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 0).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 0).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  have F₂ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₂.mem := h2.en.frame.sub inW_saved
  have mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) openGood) s₃ (OpenOut s₀) := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat
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
        exact bytes_W F₂ ddW ddx (by have := (s₀.gpr .r9).isLt; omega)
    · have hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat
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
      have h4 : SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₄ := h2.keep (fun r h0 _ h19 => g₄ r h0 h19) ⟨k₃.mem, k₃.rd, k₃.wr, k₃.sp, k₃.lr⟩
      have e19 : s₄.gpr .r19 = s₃.gpr .r19 := by simp [s₄, State.write]
      exact open_good h' h4 (by rw [e19, g₃ _ (by decide) (by decide)]; exact h19) hok
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.r31 (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp oo.low)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, openPost_out oo.post hm h3⟩

end VG.Proof.Sm4Gcm.PPC64LE
