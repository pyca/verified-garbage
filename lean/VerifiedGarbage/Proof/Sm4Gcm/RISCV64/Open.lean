module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.OneShot
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.OneEntry
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. AES-GCM's
(`Proof/AesGcm/RISCV64/Open.lean`) with SM4's pieces: `open` checks the tag
length; if it is allowed, it computes the tag of the ciphertext into
`W + 112` (`oneAad`, `oneTag 112`), copies the received tag to `W + 256` and
compares the first `tag_len` bytes of each (`recv`, `cmp 112`), and decrypts
the data in place only if they are equal; `a0` is the result (`open_wp`).
Until the data is decrypted, everything `open` writes is in the working
space `W` or the stack below `sp` (`Frame (wF W sp)`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov oneAad recv cmp tagLenOk restore dataO)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel stp_crFrame saved_crFrame ciph_keep tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT
  oneTag_ok SO1 one1_wp one_env saved_otFrame openPre openRes openRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH fullTag zeros padLen j0 inc32 gctr decryptWith openResult)
open VG.Spec.Sm4.Gcm (ctxCiph)

/-- What `open` promises, given the result `a0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .a0 = 1 ∧ bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = pt
  | none => s.gpr .a0 = 0 ∧ bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .a0 = 0)
    (hd : bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .a0 = 1)
    (hd : bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- What the end of `open` leaves for `restore`. -/
structure OpenOut (s₀ s : State) : Prop where
  s0 : s.gpr .s0 = stackArg s₀ 1
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 1) s₀
  post : OpenPost s₀ s

/-- An environment for a state's own registers, after a step that changes
only `s8` among those the environment pins. -/
theorem Env.self {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (he : Env V sp s)
    (hg : ∀ r, r ≠ .s8 → s'.gpr r = s.gpr r) (hk : Keeps s s') : Env s'.gpr sp s' :=
  ⟨fun _ _ => rfl, hk.sp.trans he.sp, by
    rw [hg _ (by decide), hg _ (by decide), hg _ (by decide), he.fr _ (by decide), he.fr _ (by decide),
      he.fr _ (by decide)]
    exact he.perm.of_eq hk.rd hk.wr, by
    rw [hg _ (by decide), hg _ (by decide), hg _ (by decide), he.fr _ (by decide), he.fr _ (by decide),
      he.fr _ (by decide), hk.sp]
    exact he.stk⟩

/-- `W` and the stack below `sp`. -/
abbrev wF (W sp : Addr) : List Region := [⟨W, 2560⟩, below sp 3232]

section
variable {W sp : Addr}

/-- What `oneAad`, `oneTag 112`, `recv` and `cmp 112` write is in `W` or below `sp`. -/
theorem inW_j0 : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W sp, ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, below_sub⟩

theorem inW_ot : ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp, ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem inW_at {d : Nat} (hd : d + 16 ≤ 2560) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Lay.wSub hd⟩

theorem inW_one : ∀ r ∈ [oneR W], ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

/-- The first counter block is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem cb_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W)
    (hbs : (below sp 3232).Disjoint ⟨W + BitVec.ofNat 64 16, 80⟩) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp ++
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
  · exact hbs.symm.sub_left (Lay.stSub (by decide))
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)

/-- The slot of the data's address is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem slot_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) (hbw : (below sp 3232).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 dataO, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by decide, by decide⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact hbw.symm.sub_left (Lay.wSub (by decide))
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

end

/-- A buffer apart from `W` and the stack below `sp` is as it was. -/
theorem bytes_W {m m' : Mem} {W sp p : Addr} {n : Nat} (hf : Frame (wF W sp) m m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hs : (⟨p, n⟩ : Region).Disjoint (below sp 3232)) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hs) hn

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (s₀.gpr .a0)) (ctxH s₀.mem (s₀.gpr .a0))
      (bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat) (bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat)
      (bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat)).take (stackArg s₀ 0).toNat =
    bytesAt s₀.mem (s₀.gpr .a7) (stackArg s₀ 0).toNat

/-- After the tags are compared, with the result in `s8`, from `s₄` (after
the entry). -/
structure OpenMid (s₀ s₄ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  regs : ∀ r ∈ frozen, r ≠ .s8 → s.gpr r = s₄.gpr r
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr
  saved : SavedAt s.mem (stackArg s₀ 1) s₀
  frame : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s.mem
  cb : blockAt s.mem (stackArg s₀ 1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat))
  dat : s.mem.readW (stackArg s₀ 1 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5
  s8 : s.gpr .s8 = BitVec.ofNat 64 (if openTagOk s₀ then 1 else 0)

section
variable {s₀ : State} (h : openPre s₀)
include h

theorem openLay : Lay (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) := by
  obtain ⟨-, -, -, dcW, -, -, -, -, -, -, -, -, -, fc, -, -, -, -, fW, -, -, ca, wa⟩ := h
  exact oneLay fc fW dcW ca wa

theorem openStk : StkOk (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -⟩ := h
  exact one_stk3 hstk (by simp) (by simp)

theorem openGe : 3232 ≤ s₀.sp.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -⟩ := h
  exact hstk.2.1

theorem openWa : (stackArg s₀ 1).toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, wa⟩ := h
  exact wa

/-- A buffer of the precondition is apart from the stack below `sp`. -/
theorem openBuf {r : Region} (hr : r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a1, (s₀.gpr .a2).toNat⟩,
    ⟨s₀.gpr .a3, (s₀.gpr .a4).toNat⟩, ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩,
    ⟨s₀.gpr .a7, (stackArg s₀ 0).toNat⟩, ⟨stackArg s₀ 1, 2560⟩, args s₀ 2]) :
    r.Disjoint (below s₀.sp 2048) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -⟩ := h
  exact hstk.buf hr

/-- A buffer of the precondition is apart from the 3232 bytes below `sp`. -/
theorem openBuf3 {r : Region} (hr : r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a1, (s₀.gpr .a2).toNat⟩,
    ⟨s₀.gpr .a3, (s₀.gpr .a4).toNat⟩, ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩,
    ⟨s₀.gpr .a7, (stackArg s₀ 0).toNat⟩, ⟨stackArg s₀ 1, 2560⟩, args s₀ 2]) :
    r.Disjoint (below s₀.sp 3232) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -⟩ := h
  exact (hstk.buf3 hr).symm

/-- The registers `open` keeps after its entry, apart from the stack below `sp`. -/
theorem openBig {s : State} (h4 : SO1 (stackArg s₀ 1) s₀ s) : Big s.gpr s₀.sp :=
  ⟨openGe h, by rw [h4.s2]; exact (openBuf3 h (by simp)).symm, by
    rw [h4.s1]; exact (openBuf3 h (r := ⟨stackArg s₀ 1, 2560⟩) (by simp)).symm.sub_right (Lay.wSub (by decide)),
    by rw [h4.s0]; exact (openBuf3 h (by simp)).symm⟩

end

/-- `open`, once the tag length is allowed, up to the comparison of the tags,
followed by any `T`. -/
theorem open_head {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) s₀ s₄)
    (h19 : s₄.gpr .s8 = stackArg s₀ 0) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) {T : Prog isa}
    {Q : State → Prop} (k : ∀ s₉, OpenMid s₀ s₄ s₉ → WP isa T s₉ Q) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .s8 .a0]) T))))) s₄ Q := by
  have L₀ := openLay h
  have hk₀ := openStk h
  have wa := openWa h
  have hb₄ := openBig h h4
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, -⟩ := hh
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  have hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have he₄ := one_env h4 hC hW hk₀
  have L := L₀.v h4.s2 h4.s1 h4.s0
  have hk₄ := h4.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ wF (stackArg s₀ 1) s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact (openBuf3 h (by simp))
  have F₄ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₄.mem := h4.frame.sub inW_one
  -- `oneAad`
  have hN : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a1) (s₀.gpr .a2).toNat := by
    rw [h4.s1, h4.s0]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a2).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₄.sp]; exact openBuf h (by simp)⟩
  have hAd : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a3) (s₄.gpr .s10).toNat := by
    rw [h4.s1, h4.s0, h4.s10]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a4).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₄.sp]; exact openBuf h (by simp)⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.s4 (by rw [h4.s5]; exact toN)
    (by rw [h4.s7]; exact toN) hN hAd (by rw [h4.s0]; exact h4.aad))) fun s₅ ⟨oa, rd₅, wr₅, sp₅⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.s1, h4.s0] at f₅
  have F₅ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `oneTag 112`
  have hDw₄ : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  have hd₄ : DataW (s₄.gpr .s2) (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a5) (s₄.gpr .s11).toNat := by
    rw [h4.s2, h4.s1, h4.s0, h4.s11]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .a6).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₄.sp]; exact openBuf h (by simp)⟩, hDw₄, dcd⟩
  have dat₅ : s₅.mem.readW (s₄.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
    rw [slot_keep oa.frame (slot_j0 L he₄.stk' (by decide)), h4.s0]; exact h4.dat
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L hb₄ (o := 112) (.inr rfl) oa.env oa.hH
    (length_bytesAt _ _ _).symm oa.abs (hd₄.ok.of_eq rd₅ wr₅ sp₅) dat₅)) fun s₆ ⟨ot, rd₆, wr₆, sp₆⟩ => ?_)
  have f₆ := ot.frame
  rw [h4.s1, h4.s0] at f₆
  have F₆ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  have h19' : s₄.gpr .s8 = BitVec.ofNat 64 (stackArg s₀ 0).toNat := by rw [h19]; exact toN
  have hTr : Covers [⟨s₄.gpr .s9, (stackArg s₀ 0).toNat⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.s9]
    exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hTd : (⟨s₄.gpr .s9, (stackArg s₀ 0).toNat⟩ : Region).Disjoint ⟨s₄.gpr .s0 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.s9, h4.s0]; exact dtW.sub_right (Lay.wSub (by decide))
  have wa₄ : (s₄.gpr .s0).toNat % 8 = 0 := by rw [h4.s0]; exact wa
  refine WP.seq (WP.mono (recv_ok ot.env wa₄ h19' t1 t16 hTr hTd) fun s₇ ⟨hb₇, hf₇, g₇, k₇⟩ => ?_)
  have he₇ := ot.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr
  rw [h4.s0] at hf₇ hb₇
  have F₇ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₇.mem := F₆.trans (hf₇.sub (inW_at (by decide)))
  -- `cmp 112`
  refine WP.seq (WP.mono (cmp_ok he₇ wa₄ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_)
  have he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  rw [h4.s0] at hf₈ h3₈
  have F₈ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₈.mem := F₇.trans (hf₈.sub (inW_at (by decide)))
  -- what the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat
  let a := bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat
  let tg := bytesAt s₀.mem (s₀.gpr .a7) (stackArg s₀ 0).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0)
  let H := ctxH s₀.mem (s₀.gpr .a0)
  have hH₄ : blockAt s₄.mem (s₄.gpr .s2 + BitVec.ofNat 64 240) = H := by
    rw [h4.s2]; exact ctxH_keep F₄ dcF
  have iv₄ : bytesAt s₄.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat = iv :=
    bytes_W F₄ dnW (openBuf3 h (by simp)) (by have := (s₀.gpr .a2).isLt; omega_arith)
  have a₄ : bytesAt s₄.mem (s₀.gpr .a3) (s₄.gpr .s10).toNat = a := by
    rw [h4.s10]; exact bytes_W F₄ daW (openBuf3 h (by simp)) (by have := (s₀.gpr .a4).isLt; omega_arith)
  have ct₅ : bytesAt s₅.mem (s₀.gpr .a5) (s₄.gpr .s11).toNat = ct := by
    rw [h4.s11]; exact bytes_W F₅ ddW (openBuf3 h (by simp)) (by have := (s₀.gpr .a6).isLt; omega_arith)
  have hc₅ : ciphOf s₅.mem (s₄.gpr .s2) = ciph := by rw [h4.s2]; exact ciph_keep F₅ dcF
  have hj₅ : blockAt s₅.mem (s₄.gpr .s1) = j0 H iv := by rw [oa.j, hH₄, iv₄]
  have hT₆ : bytesAt s₆.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    have ho := ot.out
    rw [h4.s0, hc₅, hj₅, ct₅, ← h4.s0, hH₄, a₄, ← Proof.Gcm.fullTag_eq] at ho
    rw [← h4.s0]; exact ho
  have hT₇ : bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    rw [bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hT₆
  have hr₇ : bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 0).toNat) := by
    rw [hb₇, h4.s9]; congr 1; exact bytes_W F₆ dtW (openBuf3 h (by simp)) (by omega_arith)
  let X := (fullTag ciph H iv a ct).take (stackArg s₀ 0).toNat = tg
  have hX : (bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) (stackArg s₀ 0).toNat ++
      zeros (16 - (stackArg s₀ 0).toNat) = bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  have r3₈ : s₈.gpr .a0 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  have f₆₈ : Frame (otFrame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) 112 s₀.sp ++
      [⟨stackArg s₀ 1 + BitVec.ofNat 64 256, 16⟩, ⟨stackArg s₀ 1 + BitVec.ofNat 64 272, 16⟩]) s₅.mem s₈.mem :=
    ((f₆.mono fun r hr => List.mem_append_left _ hr).trans (hf₇.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)).trans (hf₈.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)
  have cb₈ : blockAt s₈.mem (stackArg s₀ 1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    rw [blockAt_frame f₆₈ (cb_ot L₀ (by rw [← h4.s1]; exact (openBig h h4).st)), ← h4.s1, oa.cb, hH₄, iv₄]
  have dat₈ : s₈.mem.readW (stackArg s₀ 1 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
    rw [slot_keep f₆₈ (slot_ot L₀ (openBuf3 h (by simp)).symm), ← h4.s0]; exact dat₅
  have sv₈ : SavedAt s₈.mem (stackArg s₀ 1) s₀ :=
    (((h4.saved.frame f₅ (saved_j0Frame L₀ hk₀)).frame f₆ (saved_otFrame L₀ (openBuf3 h (by simp)).symm (.inr rfl))).frame hf₇
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame
      hf₈ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  -- the result into `s8`
  refine WP.seq (Steps.wp_mv fun s₉ u₉ => WP.block_nil ?_)
  have k₉ : Keeps s₈ s₉ := ⟨u₉.mem, u₉.rd, u₉.wr, u₉.sp⟩
  have he₉ := Env.self he₈ u₉.other k₉
  have e : ∀ r ∈ frozen, r ≠ .s8 → s₉.gpr r = s₄.gpr r := fun r hf hr => (u₉.other r hr).trans (he₈.fr r hf)
  have rd₉ : s₉.rd = s₄.rd := k₉.rd.trans (k₈.rd.trans (k₇.rd.trans (rd₆.trans rd₅)))
  have wr₉ : s₉.wr = s₄.wr := k₉.wr.trans (k₈.wr.trans (k₇.wr.trans (wr₆.trans wr₅)))
  refine k s₉ ⟨he₉, e, rd₉, wr₉, k₉.mem ▸ sv₈, k₉.mem ▸ F₈, by rw [k₉.mem]; exact cb₈, by rw [k₉.mem]; exact dat₈,
    ?_⟩
  rw [u₉.gpr, r3₈]
  show _ = BitVec.ofNat 64 (if X then 1 else 0)
  by_cases hx : X
  · simp only [eq_true hx, ite_true]; rfl
  · simp only [eq_false hx, ite_false]; rfl

/-- `open` from the comparison's result on. -/
theorem open_tail {s₀ s₄ s₉ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) s₀ s₄)
    (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) (om : OpenMid s₀ s₄ s₉) :
    WP isa (.seq (.ite (.zero .s8) (.block []) oneCrypt) (.block [mov .a0 .s8])) s₉ (OpenOut s₀) := by
  have L₀ := openLay h
  have hk₀ := openStk h
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, -⟩ := hh
  have hk₄ := h4.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ wF (stackArg s₀ 1) s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact (openBuf3 h (by simp))
  have hDw₄ : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  have hd₄ : DataW (s₄.gpr .s2) (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a5) (s₄.gpr .s11).toNat := by
    rw [h4.s2, h4.s1, h4.s0, h4.s11]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .a6).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₄.sp]; exact openBuf h (by simp)⟩, hDw₄, dcd⟩
  let iv := bytesAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0)
  let H := ctxH s₀.mem (s₀.gpr .a0)
  have he₉ := om.env
  have e := om.regs
  have rd₉ := om.rd
  have wr₉ := om.wr
  have sv₉ := om.saved
  have F₉ := om.frame
  have sp₉ : s₉.sp = s₄.sp := he₉.sp.trans hk₄.sp.symm
  have dat₉ : bytesAt s₉.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = ct :=
    bytes_W F₉ ddW (openBuf3 h (by simp)) (by have := (s₀.gpr .a6).isLt; omega_arith)
  have hd₉₀ : DataW (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₉ (s₀.gpr .a5)
      (s₀.gpr .a6).toNat := by
    have := hd₄.of_eq rd₉ wr₉ sp₉
    rwa [h4.s2, h4.s1, h4.s0, h4.s11] at this
  -- the data decrypted only if the tags are equal
  have mid : WP isa (.ite (.zero .s8) (.block []) oneCrypt) s₉ fun s₁₀ =>
      Env s₉.gpr s₀.sp s₁₀ ∧ SavedAt s₁₀.mem (stackArg s₀ 1) s₀ ∧ s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      ((openTagOk s₀) → bytesAt s₁₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = gctr ciph (inc32 (j0 H iv)) ct) ∧
      (¬(openTagOk s₀) → bytesAt s₁₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = ct) := by
    refine WP.ite _ (eval_zero om.s8 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬(openTagOk s₀) := fun x => by simp [x] at ht
      exact WP.block_nil ⟨he₉, sv₉, rd₉, wr₉, fun x => absurd x hx, fun _ => dat₉⟩
    · have hx : (openTagOk s₀) := Classical.byContradiction fun x => by simp [x] at hf
      have L₉ : Lay (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.s2, h4.s1,
          h4.s0]
        exact L₀
      have hd₉ : DataW (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) s₉ (s₀.gpr .a5) (s₉.gpr .s11).toNat := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
          e _ (by decide) (by decide)]
        exact hd₄.of_eq rd₉ wr₉ sp₉
      have hb₉ : Big s₉.gpr s₀.sp := by
        have hb := openBig h h4
        exact ⟨hb.ge, by rw [e _ (by decide) (by decide)]; exact hb.c, by rw [e _ (by decide) (by decide)]; exact hb.st,
          by rw [e _ (by decide) (by decide)]; exact hb.w⟩
      have hbd₉ : (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a5, (s₉.gpr .s11).toNat⟩ := by
        rw [e _ (by decide) (by decide), h4.s11]; exact (openBuf3 h (by simp)).symm
      have cb₉ : blockAt s₉.mem (s₉.gpr .s1 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [e _ (by decide) (by decide), h4.s1]; exact om.cb
      have ds₉ : s₉.mem.readW (s₉.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5 := by
        rw [e _ (by decide) (by decide), h4.s0]; exact om.dat
      refine WP.mono (WP.with_rdwr (oneCrypt_ok L₉ hb₉ he₉ hd₉ hbd₉ ds₉ cb₉)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      have cf := oc.frame
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), h4.s1, h4.s11] at cf
      refine ⟨oc.env, sv₉.frame cf (saved_crFrame L₀ (openBuf3 h (by simp)).symm hd₉₀), rd₁₀.trans rd₉, wr₁₀.trans wr₉, fun _ => ?_,
        fun x => absurd hx x⟩
      have ho := oc.out
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), h4.s11, h4.s2, ciph_keep F₉ dcF, dat₉] at ho
      exact ho
  refine WP.seq (WP.mono mid fun s₁₀ ⟨he₁₀, sv₁₀, rd₁₀, wr₁₀, hd₁, hd₂⟩ => ?_)
  -- the result back into `a0`
  refine Steps.wp_mv fun s₁₁ u₁₁ => WP.block_nil ?_
  have r3₁₁ : s₁₁.gpr .a0 = if (openTagOk s₀) then 1 else 0 := by
    rw [u₁₁.gpr, he₁₀.fr _ (by decide), om.s8]
    by_cases hx : openTagOk s₀
    · simp only [eq_true hx, ite_true]; rfl
    · simp only [eq_false hx, ite_false]; rfl
  have hres : openRes s₀ = if (openTagOk s₀) then some (gctr ciph (inc32 (j0 H iv)) ct) else none := by
    simp only [openRes, openResult, hok, ite_true, decryptWith]; rfl
  refine ⟨by rw [u₁₁.other _ (by decide), he₁₀.fr _ (by decide), e _ (by decide) (by decide), h4.s0],
    by rw [u₁₁.sp]; exact he₁₀.sp, by rw [u₁₁.rd, rd₁₀, hk₄.rd], by rw [u₁₁.wr, wr₁₀, hk₄.wr],
    by rw [u₁₁.mem]; exact sv₁₀, ?_⟩
  by_cases hx : (openTagOk s₀)
  · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true hx)))
      (r3₁₁.trans (ite_eq_left_of_eq_true _ _ (eq_true hx))) (by rw [u₁₁.mem]; exact hd₁ hx)
  · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false hx)))
      (r3₁₁.trans (ite_eq_right_of_eq_false _ _ (eq_false hx))) (by rw [u₁₁.mem]; exact hd₂ hx)

theorem open_good {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) s₀ s₄)
    (h19 : s₄.gpr .s8 = stackArg s₀ 0) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .s8 .a0])
      (.seq (.ite (.zero .s8) (.block []) oneCrypt) (.block [mov .a0 .s8]))))))) s₄ (OpenOut s₀) :=
  open_head h h4 h19 hok fun _ om => open_tail h h4 hok om

/-- The contract's postcondition, from `OpenPost`, through `restore`. -/
theorem openPost_out {s₀ s s' : State} (op : OpenPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .a0 = s.gpr .a0) :
    openRISCV64.post s₀ s' := by
  unfold OpenPost at op
  unfold openRISCV64
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op <;> exact ⟨by rw [op.1]; rfl, op.2⟩

/-- After a step that changes no register the entry set but `t0` and `s8`. -/
theorem SO1.keep {W : Addr} {s₀ s₁ s₂ : State} (h1 : SO1 W s₀ s₁)
    (hg : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .s8 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 W s₀ s₂ :=
  ⟨⟨hk.rd.trans h1.keeps.rd, hk.wr.trans h1.keeps.wr, hk.sp.trans h1.keeps.sp⟩, hk.mem ▸ h1.saved,
    hk.mem ▸ h1.frame, hk.mem ▸ h1.aad, hk.mem ▸ h1.dat,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s0, by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s1,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s2,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s4, by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s5,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s7, by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s10,
    by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s11, by rw [hg _ (by decide) (by decide) (by decide)]; exact h1.s9⟩

/-- The entry of `open`, and `tag_len` in `s8`. -/
theorem openEntry_wp {s₀ : State} (h : openPre s₀) :
    WP isa (.block openEntry) s₀ fun s₂ =>
      SO1 (stackArg s₀ 1) s₀ s₂ ∧ s₂.gpr .s8 = stackArg s₀ 0 := by
  have wa := openWa h
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hstk,
    -⟩ := hh
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have dA : (args s₀ 2).Disjoint (oneR (stackArg s₀ 1)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  have hLd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 1)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 2 by decide))
  unfold openEntry
  refine WP.block_append (WP.mono (one1_wp (off := 8) (W := stackArg s₀ 1)
    (.inr rfl) hW wa hstk.1 (args_in hA (by decide) (i := 1) (by decide)) rfl) fun s₁ h1 => ?_)
  -- `tag_len` into `s8`
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  have hi : InRegions (sA.rd ++ sA.wr) (s₀.sp + BitVec.ofNat 64 0) 8 := by
    rw [uA.rd, uA.wr, h1.keeps.rd, h1.keeps.wr]; exact args_in hA (by decide) (i := 0) (by decide)
  have hv : sA.mem.readW (s₀.sp + BitVec.ofNat 64 0) 64 = stackArg s₀ 0 := by
    rw [uA.mem, Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hLd) (by decide)]
    rfl
  refine Steps.wp_ld (off := 0) (a := s₀.sp + BitVec.ofNat 64 0) (by decide)
    (by rw [uA.gpr, h1.keeps.sp, add_ofNat_zero]) (Spill.al8 (by have := hstk.1; omega) (by decide)) hi fun s₂ u₂ => WP.block_nil ?_
  exact ⟨h1.keep (fun r _ ht hr => by rw [u₂.other r hr, uA.other r ht])
    ⟨by rw [u₂.mem, uA.mem], by rw [u₂.rd, uA.rd], by rw [u₂.wr, uA.wr], by rw [u₂.sp, uA.sp]⟩,
    by rw [u₂.gpr, hv]⟩

theorem open_wp {s₀ : State} (h : openRISCV64.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openRISCV64.post s₀ s' := by
  have h' : openPre s₀ := h
  have wa := openWa h'
  have hk₀ := openStk h'
  have hh := h'
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, -⟩ := hh
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  unfold «open»
  refine WP.seq (WP.mono (openEntry_wp h') fun s₂ ⟨h2, h19⟩ => ?_)
  -- the tag length
  have h19' : s₂.gpr .s8 = BitVec.ofNat 64 (stackArg s₀ 0).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 0).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  have F₂ : Frame (wF (stackArg s₀ 1) s₀.sp) s₀.mem s₂.mem := h2.frame.sub inW_one
  have mid : WP isa (.ite (.zero .s5) (.block [.li .a0 0]) openGood) s₃ (OpenOut s₀) := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat
        · rfl
        · simp [e] at ht
      refine Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.s0
      · rw [u.sp, k₃.sp]; exact h2.keeps.sp
      · rw [u.rd, k₃.rd]; exact h2.keeps.rd
      · rw [u.wr, k₃.wr]; exact h2.keeps.wr
      · rw [u.mem, k₃.mem]; exact h2.saved
      · refine openPost_none (by simp only [openRes, openResult, hbad]; rfl) u.gpr ?_
        rw [u.mem, k₃.mem]
        exact bytes_W F₂ ddW (openBuf3 h' (by simp)) (by have := (s₀.gpr .a6).isLt; omega_arith)
    · have hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat
        · simp [e] at hf
        · rfl
      refine WP.seq (Steps.wp_mv fun s₄ u₄ => WP.block_nil ?_)
      have g₄ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .s8 → s₄.gpr r = s₂.gpr r := fun r h0 _ h19 => by
        by_cases e : r = .s5
        · subst e
          rw [u₄.gpr, g₃ _ (by decide) (by decide), h2.s7, h2.s5]
        · rw [u₄.other r e, g₃ r h0 e]
      have h4 : SO1 (stackArg s₀ 1) s₀ s₄ :=
        h2.keep g₄ ⟨by rw [u₄.mem, k₃.mem], by rw [u₄.rd, k₃.rd], by rw [u₄.wr, k₃.wr], by rw [u₄.sp, k₃.sp]⟩
      exact open_good h' h4 (by rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h19) hok
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.s0 wa (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, openPost_out oo.post hm h3⟩

end VG.Proof.Sm4Gcm.RISCV64
