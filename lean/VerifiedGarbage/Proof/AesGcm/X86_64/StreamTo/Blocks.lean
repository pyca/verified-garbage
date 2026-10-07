import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall

/-!
# AES-GCM streaming encryption out of place, x86-64: the whole blocks

Untrusted: everything here is checked by Lean. `blocks` from `Mid s 0`: if
the text so far ends a block, and is not empty or follows additional data of
whole blocks (`Sel`, the length the code tests), and there are `q ≥ 1` whole
blocks of plaintext (and the text so far and they do not exceed 2⁶⁴ bytes),
the call of `vg_aes_gcm_encrypt_blocks_to` leaves `Mid s (16 q)`
(`call_mid`, from `Proof.Gcm.streamRepr_blocksTo`); otherwise nothing is
done (`blocks_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt StreamRepr gctr inc32 j0)

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The regions the call writes are apart from the slots kept. -/
theorem kR'_blk {q : Nat} (hq : 16 * q ≤ L s) : ∀ r ∈ blkWr s q ++ [tR s], (kR' s).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact (hp.st_w.symm.sub_left kR'_sub).sub_right ctr_sub
  · exact (hp.st_w.symm.sub_left kR'_sub).sub_right y_sub
  · exact (hp.d_w.symm.sub_left kR'_sub).sub_right (dst_sub (s := s) hq)
  · exact kR'_scR
  · exact hp.b_w.symm.sub_left kR'_sub

omit hp in
/-- The regions the call writes are among those the code may write. -/
theorem blk_wR {q : Nat} (hq : 16 * q ≤ L s) {m m' : Mem} (hf : Frame (blkWr s q ++ [tR s]) m m') :
    Frame (wR s ++ [tR s]) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl
    · exact ⟨stR s, by simp, ctr_sub⟩
    · exact ⟨stR s, by simp, y_sub⟩
    · exact ⟨dR s, by simp, dst_sub (s := s) hq⟩
    · exact ⟨wkR s, by simp, scR_sub⟩
    · exact ⟨tR s, by simp, fun _ h => h⟩

/-- `J₀`, the first 16 bytes of the state, is apart from what the call writes. -/
theorem j0_blk {q : Nat} (hq : 16 * q ≤ L s) : ∀ r ∈ blkWr s q ++ [tR s], (⟨St s, 16⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨St s, 16⟩ (stR s) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact Offset.base_disjoint _ (by decide) (by have := hp.w_st; omega)
  · exact Offset.base_disjoint _ (by decide) (by have := hp.w_st; omega)
  · exact (hp.st_d.sub_left hs).sub_right (dst_sub (s := s) hq)
  · exact (hp.st_w.sub_left hs).sub_right scR_sub
  · exact hp.b_st.symm.sub_left hs

omit hp in
/-- The length whose remainder modulo 16 decides whether the whole blocks
can be taken: `aad_len` after no text, and `text_len` otherwise. -/
abbrev Sel (s : State) : BitVec 64 := if TL s = 0 then AL s else TL s

omit hp in
/-- Whether `Sel` is a multiple of 16: the text so far ends a block, and is
not empty or follows additional data of whole blocks. -/
theorem sel_mod {s : State} (h : (Sel s).toNat % 16 = 0) :
    (TL s).toNat % 16 = 0 ∧ (TL s ≠ 0 ∨ (AL s).toNat % 16 = 0) := by
  by_cases ht : TL s = 0
  · simp only [Sel, ht, ite_true] at h; exact ⟨by rw [ht]; rfl, Or.inr h⟩
  · simp only [Sel, ht, ite_false] at h; exact ⟨h, Or.inl ht⟩

/-- What the call of the whole blocks leaves: `Mid s (16 q)`, from the
state `st₄` it starts from (with nothing done but the bytes done kept). -/
theorem call_mid {q : Nat} (hq0 : q ≠ 0) (hq : 16 * q ≤ L s) (htl : (TL s).toNat + 16 * q < 2 ^ 64)
    (ht0 : TL s ≠ 0 ∨ (AL s).toNat % 16 = 0) (ht16 : (TL s).toNat % 16 = 0) {st₄ st' : State}
    (f₄ : Frame (wR s ++ [tR s]) s.mem st₄.mem) (sem₄ : Sem s 0 st₄.mem) (hk₄ : Kept s (16 * q) st₄.mem)
    (hsp₄ : st₄.gpr .rsp = SP s) (hcs₄ : ∀ r ∈ calleeSaved, st₄.gpr r = s.gpr r) (hrd₄ : st₄.rd = s.rd)
    (hwr₄ : st₄.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st₄.gpr r) (hrd : st'.rd = st₄.rd) (hwr : st'.wr = st₄.wr)
    (hf : Frame (blkWr s q ++ [tR s]) st₄.mem st'.mem)
    (o₁ : blocksAt st'.mem (Dst s) q =
      Spec.Gcm.ctr32 (ciph s) (blockAt st₄.mem (St s + BitVec.ofNat 64 48)) (blocksAt st₄.mem (Src s) q))
    (o₂ : blockAt st'.mem (St s + BitVec.ofNat 64 48) =
      Nat.repeat inc32 q (blockAt st₄.mem (St s + BitVec.ofNat 64 48)))
    (o₃ : blockAt st'.mem (St s + BitVec.ofNat 64 16) =
      Spec.Gcm.ghashFrom (hk s) (blockAt st₄.mem (St s + BitVec.ofNat 64 16)) (blocksAt st'.mem (Dst s) q)) :
    Mid s (16 * q) st' := by
  have f' : Frame (wR s ++ [tR s]) s.mem st'.mem := f₄.trans (blk_wR (s := s) hq hf)
  refine ⟨hq, htl, by rw [hcs _ (by decide), hsp₄], fun r hr => by rw [hcs r hr, hcs₄ r hr],
    by rw [hrd, hrd₄], by rw [hwr, hwr₄], hk₄.frame hf (kR'_blk hp hq), f',
    fun iv a p hr hal hpl => ?_⟩
  -- The state before the call.
  have hr₄ := (sem₄ iv a p hr hal hpl).1
  have z : pt s 0 = [] := rfl
  rw [z, List.append_nil] at hr₄
  have hc : gctr (ciph s) (inc32 (j0 (hk s) iv)) p ≠ [] ∨ a.length % 16 = 0 := by
    rcases ht0 with ht0 | ha
    · refine Or.inl fun e => ?_
      have := congrArg List.length e
      rw [Proof.Gcm.length_gctr] at this; simp at this
      exact ht0 (by apply BitVec.eq_of_toNat_eq; rw [hpl, this]; rfl)
    · rw [hal, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)] at ha
      exact Or.inr ha
  have hc0 : (gctr (ciph s) (inc32 (j0 (hk s) iv)) p).length % 16 = 0 := by
    rw [Proof.Gcm.length_gctr, ← hpl]; exact ht16
  obtain ⟨e₁, hr'⟩ := Proof.Gcm.streamRepr_blocksTo hr₄ hc hc0 hq0
    (blockAt_frame hf (j0_blk hp hq)) o₁ o₂ o₃
  have hpt : bytesAt st₄.mem (Src s) (16 * q) = pt s (16 * q) := pt_eq hp f₄ hq
  rw [hpt, Proof.Gcm.length_gctr] at e₁
  have hg : gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s (16 * q)) =
      gctr (ciph s) (inc32 (j0 (hk s) iv)) p ++ bytesAt st'.mem (Dst s) (16 * q) := by
    rw [Proof.Gcm.gctr_append, e₁]
  refine ⟨by rw [hg]; exact hr', ?_⟩
  rw [hg, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

/-- `blocks`, from `Mid s 0` with the arguments in their registers and
`work` in `r11`: some bytes done. -/
theorem blocks_ok (T : BlkToFn M) {st : State} (h : Mid s 0 st) (h11 : st.gpr .r11 = W s)
    (h8 : st.gpr .r8 = TL s) (hcx : st.gpr .rcx = AL s) :
    WP isa (blocks T.fn) st fun st' => ∃ o, Mid s o st' := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  unfold blocks
  refine WP.seq (WP.mono hd1_ok fun s₁ ⟨ax₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have M₁ : Mid s 0 s₁ := h.regs m₁ (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr)) rd₁ wr₁
  -- `rax`: `aad_len` after no text, and `text_len` otherwise.
  have hsel : WP isa (.ite .e (.block [.mov .rax (.reg .rcx)]) (.block [])) s₁ fun s₂ =>
      s₂.gpr .rax = Sel s ∧ (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
    refine WP.ite (st.gpr .r8 == 0) (by simp only [eval, z₁]) (fun e => WP.mono mvc_ok fun _ ⟨ax, g, m, rd, wr⟩ =>
      ⟨by
        have hz : TL s = 0 := by rw [← h8]; simpa using e
        rw [ax, g₁ _ (by decide), hcx]; simp only [Sel, hz, ite_true], g, m, rd, wr⟩)
      (fun e => WP.block_nil ⟨by
        have hz : TL s ≠ 0 := by rw [← h8]; simpa using e
        rw [ax₁, h8]; simp only [Sel, hz, ite_false], fun _ _ => rfl, rfl, rfl, rfl⟩)
  refine WP.seq (WP.mono hsel fun s₁' ⟨ax₁', g₁', m₁', rd₁', wr₁'⟩ => ?_)
  have M₁' : Mid s 0 s₁' := M₁.regs m₁' (fun r hr => g₁' r (by rintro rfl; simp [calleeSaved] at hr)) rd₁' wr₁'
  refine WP.seq (WP.mono (hd2_ok (T := Sel s) ax₁') fun s₂ ⟨z₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have M₂ : Mid s 0 s₂ := M₁'.regs m₂ (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂
  refine WP.ite (!(BitVec.ofNat 64 ((Sel s).toNat % 16) == 0)) (by simp only [eval, z₂, Option.map_some])
    (fun _ => WP.block_nil ⟨0, M₂⟩) (fun e₂ => ?_)
  obtain ⟨ht16, ht0⟩ := sel_mod (s := s) (by
    simp only [Bool.not_eq_false', beq_iff_eq] at e₂
    have := congrArg BitVec.toNat e₂
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this)
  have h11₂ : s₂.gpr .r11 = W s := by rw [g₂ _ (by decide), g₁' _ (by decide), g₁ _ (by decide), h11]
  refine WP.seq (WP.mono (hd3_ok hp h11₂ M₂.kept M₂.rd M₂.wr) fun s₃ ⟨ax₃, z₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have M₃ : Mid s 0 s₃ := M₂.regs m₃ (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃
  refine WP.ite (decide (L s / 16 = 0)) (by simp only [eval, z₃]) (fun _ => WP.block_nil ⟨0, M₃⟩) (fun e₃ => ?_)
  have hq0 : L s / 16 ≠ 0 := by simpa using e₃
  have h8₃ : s₃.gpr .r8 = TL s := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁' _ (by decide), g₁ _ (by decide), h8]
  refine WP.seq (WP.mono (len_ok ax₃ h8₃) fun s₄ ⟨r9₄, ax₄, cf₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  have M₄ : Mid s 0 s₄ := M₃.regs m₄ (fun r hr => g₄ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₄ wr₄
  have h16 : (BitVec.ofNat 64 (16 * (L s / 16))).toNat = 16 * (L s / 16) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [h16] at cf₄
  refine WP.ite (decide (2 ^ 64 ≤ (TL s).toNat + 16 * (L s / 16))) (by simp only [eval, cf₄])
    (fun _ => WP.block_nil ⟨0, M₄⟩) (fun e₄ => ?_)
  have htl : (TL s).toNat + 16 * (L s / 16) < 2 ^ 64 := by simpa using e₄
  have h11₄ : s₄.gpr .r11 = W s := by rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide), h11₂]
  refine WP.seq (WP.mono (blocksArgs_ok hp h11₄ ax₄ M₄.kept M₄.rd M₄.wr)
    fun s₅ ⟨di, si, dx, cx, r8₅, r10₅, ax₅, g₅, k₅, f₅, rd₅, wr₅⟩ => ?_)
  have hq : 16 * (L s / 16) ≤ L s := by omega
  have sp₅ : s₅.gpr .rsp = SP s := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), M₄.rsp]
  have r9₅ : s₅.gpr .r9 = BitVec.ofNat 64 (L s / 16) := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9₄]
  have si₅ : s₅.gpr .rsi = s.gpr .rsi := si
  refine WP.mono (blkCall_ok hp T hq sp₅ (rd₅.trans M₄.rd) (wr₅.trans M₄.wr) (M₄.frame.trans (frame_kR' f₅))
    di si₅ dx cx r8₅ r9₅ r10₅ ax₅) fun s₆ ⟨cs₆, rd₆, wr₆, f₆, o₁, o₂, o₃⟩ => ⟨16 * (L s / 16), ?_⟩
  have cs₅ : ∀ r ∈ calleeSaved, s₅.gpr r = s.gpr r := fun r hr => by
    rw [g₅ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr), M₄.saved r hr]
  exact call_mid hp hq0 hq htl ht0 ht16 (M₄.frame.trans (frame_kR' f₅)) (M₄.sem.kR' hp f₅ (Nat.zero_le _)) k₅
    sp₅ cs₅ (rd₅.trans M₄.rd) (wr₅.trans M₄.wr) cs₆ rd₆ wr₆ f₆ o₁ o₂ o₃

end

end VG.Proof.AesGcm.X86_64.StreamTo
