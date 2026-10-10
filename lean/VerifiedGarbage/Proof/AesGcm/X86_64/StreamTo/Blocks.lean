import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall

/-!
# AES-GCM streaming encryption out of place, x86-64: the whole blocks

Untrusted: everything here is checked by Lean. `blocks` from `Mid s o`: if
the text so far and the `o` bytes done end a block, and are not empty or
follow additional data of whole blocks (`Sel`, the length the code tests),
and there are `q ≥ 1` whole blocks of plaintext left (and the text so far,
the bytes done and they do not exceed 2⁶⁴ bytes), the call of
`vg_aes_gcm_encrypt_blocks_to` leaves `Mid s (o + 16 q)`
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
theorem kR'_blk {o q : Nat} (hq : o + 16 * q ≤ L s) : ∀ r ∈ blkWr s o q ++ [tR s], (kR' s).Disjoint r := by
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
theorem blk_wR {o q : Nat} (hq : o + 16 * q ≤ L s) {m m' : Mem} (hf : Frame (blkWr s o q ++ [tR s]) m m') :
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
theorem j0_blk {o q : Nat} (hq : o + 16 * q ≤ L s) :
    ∀ r ∈ blkWr s o q ++ [tR s], (⟨St s, 16⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨St s, 16⟩ (stR s) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact Offset.base_disjoint _ (by decide) (by have := hp.w_st; omega)
  · exact Offset.base_disjoint _ (by decide) (by have := hp.w_st; omega)
  · exact (hp.st_d.sub_left hs).sub_right (dst_sub (s := s) hq)
  · exact (hp.st_w.sub_left hs).sub_right scR_sub
  · exact hp.b_st.symm.sub_left hs

/-- The first `o` bytes of the output are apart from what the call writes
after them. -/
theorem pre_blk {o q : Nat} (hq : o + 16 * q ≤ L s) :
    ∀ r ∈ blkWr s o q ++ [tR s], (⟨Dst s, o⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨Dst s, o⟩ (dR s) := Region.sub_prefix (by omega)
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact (hp.st_d.symm.sub_left hs).sub_right ctr_sub
  · exact (hp.st_d.symm.sub_left hs).sub_right y_sub
  · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega)
  · exact (hp.d_w.sub_left hs).sub_right scR_sub
  · exact hp.b_d.symm.sub_left hs

omit hp in
/-- The length whose remainder modulo 16 decides whether the whole blocks
can be taken: `aad_len` after no text, and the text so far and the `o`
bytes done otherwise. -/
abbrev Sel (s : State) (o : Nat) : BitVec 64 :=
  if TL s + BitVec.ofNat 64 o = 0 then AL s else TL s + BitVec.ofNat 64 o

omit hp in
/-- Whether `Sel` is a multiple of 16: the text so far and the bytes done
end a block, and are not empty or follow additional data of whole blocks. -/
theorem sel_mod {s : State} {o : Nat} (h : (Sel s o).toNat % 16 = 0) :
    (TL s + BitVec.ofNat 64 o).toNat % 16 = 0 ∧ (TL s + BitVec.ofNat 64 o ≠ 0 ∨ (AL s).toNat % 16 = 0) := by
  by_cases ht : TL s + BitVec.ofNat 64 o = 0
  · simp only [Sel, ht, ite_true] at h; exact ⟨by rw [ht]; rfl, Or.inr h⟩
  · simp only [Sel, ht, ite_false] at h; exact ⟨h, Or.inl ht⟩

omit hp in
/-- The text so far and the `o` bytes done, exact in 64 bits. -/
theorem tl_add {s : State} {o : Nat} (h : (TL s).toNat + o < 2 ^ 64) :
    (TL s + BitVec.ofNat 64 o).toNat = (TL s).toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

/-- What the call of the whole blocks leaves: `Mid s (o + 16 q)`, from the
state `st₄` it starts from (with `o` bytes done and the bytes done after the
call kept). -/
theorem call_mid {o q : Nat} (hq0 : q ≠ 0) (hq : o + 16 * q ≤ L s) (htl : (TL s).toNat + (o + 16 * q) < 2 ^ 64)
    (ht0 : TL s + BitVec.ofNat 64 o ≠ 0 ∨ (AL s).toNat % 16 = 0) (ht16 : ((TL s).toNat + o) % 16 = 0)
    {st₄ st' : State}
    (f₄ : Frame (wR s ++ [tR s]) s.mem st₄.mem) (sem₄ : Sem s o st₄.mem) (hk₄ : Kept s (o + 16 * q) st₄.mem)
    (hsp₄ : st₄.gpr .rsp = SP s) (hcs₄ : ∀ r ∈ calleeSaved, st₄.gpr r = s.gpr r) (hrd₄ : st₄.rd = s.rd)
    (hwr₄ : st₄.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st₄.gpr r) (hrd : st'.rd = st₄.rd) (hwr : st'.wr = st₄.wr)
    (hf : Frame (blkWr s o q ++ [tR s]) st₄.mem st'.mem)
    (o₁ : blocksAt st'.mem (Dst s + BitVec.ofNat 64 o) q =
      Spec.Gcm.ctr32 (ciph s) (blockAt st₄.mem (St s + BitVec.ofNat 64 48))
        (blocksAt st₄.mem (Src s + BitVec.ofNat 64 o) q))
    (o₂ : blockAt st'.mem (St s + BitVec.ofNat 64 48) =
      Nat.repeat inc32 q (blockAt st₄.mem (St s + BitVec.ofNat 64 48)))
    (o₃ : blockAt st'.mem (St s + BitVec.ofNat 64 16) =
      Spec.Gcm.ghashFrom (hk s) (blockAt st₄.mem (St s + BitVec.ofNat 64 16))
        (blocksAt st'.mem (Dst s + BitVec.ofNat 64 o) q)) :
    Mid s (o + 16 * q) st' := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have f' : Frame (wR s ++ [tR s]) s.mem st'.mem := f₄.trans (blk_wR (s := s) hq hf)
  refine ⟨hq, htl, by rw [hcs _ (by decide), hsp₄], fun r hr => by rw [hcs r hr, hcs₄ r hr],
    by rw [hrd, hrd₄], by rw [hwr, hwr₄], hk₄.frame hf (kR'_blk hp hq), f',
    fun iv a p hr hal hpl => ?_⟩
  -- The state before the call.
  obtain ⟨hr₄, dd₄⟩ := sem₄ iv a p hr hal hpl
  have hX : (p ++ pt s o).length = (TL s).toNat + o := by rw [List.length_append, length_bytesAt, hpl]
  have hc : gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o) ≠ [] ∨ a.length % 16 = 0 := by
    rcases ht0 with ht0 | ha
    · refine Or.inl fun e => ?_
      have := congrArg List.length e
      rw [Proof.Gcm.length_gctr, hX] at this; simp at this
      exact ht0 (by apply BitVec.eq_of_toNat_eq; rw [tl_add (by omega), this.1, this.2]; rfl)
    · rw [hal, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)] at ha
      exact Or.inr ha
  have hc0 : (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o)).length % 16 = 0 := by
    rw [Proof.Gcm.length_gctr, hX]; exact ht16
  obtain ⟨e₁, hr'⟩ := Proof.Gcm.streamRepr_blocksTo hr₄ hc hc0 hq0
    (blockAt_frame hf (j0_blk hp hq)) o₁ o₂ o₃
  have hsub : Region.Sub ⟨Src s + BitVec.ofNat 64 o, 16 * q⟩ (srcR s) := Offset.sub_base _ (by omega)
  have hpt : bytesAt st₄.mem (Src s + BitVec.ofNat 64 o) (16 * q) = bytesAt s.mem (Src s + BitVec.ofNat 64 o) (16 * q) :=
    bytesAt_frame f₄ (fun r hr => (r_disj hp r hr).sub_left hsub) (by omega)
  rw [hpt, Proof.Gcm.length_gctr] at e₁
  have hP : p ++ pt s (o + 16 * q) = p ++ pt s o ++ bytesAt s.mem (Src s + BitVec.ofNat 64 o) (16 * q) := by
    rw [List.append_assoc, ← bytesAt_add]
  have hg : gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s (o + 16 * q)) =
      gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o) ++ bytesAt st'.mem (Dst s + BitVec.ofNat 64 o) (16 * q) := by
    rw [hP, Proof.Gcm.gctr_append, e₁]
  refine ⟨by rw [hg]; exact hr', ?_⟩
  have hD : bytesAt st'.mem (Dst s) o = bytesAt st₄.mem (Dst s) o :=
    bytesAt_frame hf (pre_blk hp hq) (by omega)
  rw [hg, bytesAt_add, hD, dd₄, List.drop_append_of_le_length (by rw [Proof.Gcm.length_gctr]; simp)]

/-- `blocks`, from `Mid s o`: some bytes done. -/
theorem blocks_ok (T : BlkToFn M) {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (blocks T.fn) st fun st' => ∃ o', Mid s o' st' := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  have htl := h.tl
  unfold blocks
  refine WP.seq (WP.mono (blocksLoad_ok hp h) fun s₀ ⟨h11, hcx, h8, g₀, m₀, rd₀, wr₀⟩ => ?_)
  have M₀ : Mid s o s₀ := h.regs m₀ (fun r hr => g₀ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₀ wr₀
  refine WP.seq (WP.mono hd1_ok fun s₁ ⟨ax₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have M₁ : Mid s o s₁ := M₀.regs m₁ (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr)) rd₁ wr₁
  -- `rax`: `aad_len` after no text, and the text so far and the bytes done otherwise.
  have hsel : WP isa (.ite .e (.block [.mov .rax (.reg .rcx)]) (.block [])) s₁ fun s₂ =>
      s₂.gpr .rax = Sel s o ∧ (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
    refine WP.ite (s₀.gpr .r8 == 0) (by simp only [eval, z₁]) (fun e => WP.mono mvc_ok fun _ ⟨ax, g, m, rd, wr⟩ =>
      ⟨by
        have hz : TL s + BitVec.ofNat 64 o = 0 := by rw [← h8]; simpa using e
        rw [ax, g₁ _ (by decide), hcx]; simp only [Sel, hz, ite_true], g, m, rd, wr⟩)
      (fun e => WP.block_nil ⟨by
        have hz : TL s + BitVec.ofNat 64 o ≠ 0 := by rw [← h8]; simpa using e
        rw [ax₁, h8]; simp only [Sel, hz, ite_false], fun _ _ => rfl, rfl, rfl, rfl⟩)
  refine WP.seq (WP.mono hsel fun s₁' ⟨ax₁', g₁', m₁', rd₁', wr₁'⟩ => ?_)
  have M₁' : Mid s o s₁' := M₁.regs m₁' (fun r hr => g₁' r (by rintro rfl; simp [calleeSaved] at hr)) rd₁' wr₁'
  refine WP.seq (WP.mono (hd2_ok (T := Sel s o) ax₁') fun s₂ ⟨z₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have M₂ : Mid s o s₂ := M₁'.regs m₂ (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂
  refine WP.ite (!(BitVec.ofNat 64 ((Sel s o).toNat % 16) == 0)) (by simp only [eval, z₂, Option.map_some])
    (fun _ => WP.block_nil ⟨o, M₂⟩) (fun e₂ => ?_)
  obtain ⟨ht16, ht0⟩ := sel_mod (s := s) (o := o) (by
    simp only [Bool.not_eq_false', beq_iff_eq] at e₂
    have := congrArg BitVec.toNat e₂
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this)
  rw [tl_add htl] at ht16
  have h11₂ : s₂.gpr .r11 = W s := by rw [g₂ _ (by decide), g₁' _ (by decide), g₁ _ (by decide), h11]
  refine WP.seq (WP.mono (blocksCount_ok hp h11₂ M₂.kept ho M₂.rd M₂.wr) fun s₃ ⟨ax₃, z₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have M₃ : Mid s o s₃ := M₂.regs m₃ (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃
  refine WP.ite (decide ((L s - o) / 16 = 0)) (by simp only [eval, z₃]) (fun _ => WP.block_nil ⟨o, M₃⟩)
    (fun e₃ => ?_)
  have hq0 : (L s - o) / 16 ≠ 0 := by simpa using e₃
  have h8₃ : s₃.gpr .r8 = TL s + BitVec.ofNat 64 o := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁' _ (by decide), g₁ _ (by decide), h8]
  refine WP.seq (WP.mono (len_ok ax₃ h8₃) fun s₄ ⟨r9₄, ax₄, cf₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  have M₄ : Mid s o s₄ := M₃.regs m₄ (fun r hr => g₄ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₄ wr₄
  have h16 : (BitVec.ofNat 64 (16 * ((L s - o) / 16))).toNat = 16 * ((L s - o) / 16) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [h16, tl_add htl] at cf₄
  refine WP.ite (decide (2 ^ 64 ≤ (TL s).toNat + o + 16 * ((L s - o) / 16))) (by simp only [eval, cf₄])
    (fun _ => WP.block_nil ⟨o, M₄⟩) (fun e₄ => ?_)
  have htl' : (TL s).toNat + (o + 16 * ((L s - o) / 16)) < 2 ^ 64 := by simp at e₄; omega
  have h11₄ : s₄.gpr .r11 = W s := by
    rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide), h11₂]
  refine WP.seq (WP.mono (blocksArgs_ok hp h11₄ ax₄ M₄.kept M₄.rd M₄.wr)
    fun s₅ ⟨di, si, dx, cx, r8₅, r10₅, ax₅, g₅, k₅, f₅, rd₅, wr₅⟩ => ?_)
  have hq : o + 16 * ((L s - o) / 16) ≤ L s := by omega
  have sp₅ : s₅.gpr .rsp = SP s := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), M₄.rsp]
  have r9₅ : s₅.gpr .r9 = BitVec.ofNat 64 ((L s - o) / 16) := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9₄]
  have si₅ : s₅.gpr .rsi = s.gpr .rsi := si
  refine WP.mono (blkCall_ok hp T hq sp₅ (rd₅.trans M₄.rd) (wr₅.trans M₄.wr) (M₄.frame.trans (frame_kR' f₅))
    di si₅ dx cx r8₅ r9₅ r10₅ ax₅) fun s₆ ⟨cs₆, rd₆, wr₆, f₆, o₁, o₂, o₃⟩ => ⟨o + 16 * ((L s - o) / 16), ?_⟩
  have cs₅ : ∀ r ∈ calleeSaved, s₅.gpr r = s.gpr r := fun r hr => by
    rw [g₅ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr), M₄.saved r hr]
  exact call_mid hp hq0 hq htl' ht0 ht16 (M₄.frame.trans (frame_kR' f₅)) (M₄.sem.kR' hp f₅ ho) k₅
    sp₅ cs₅ (rd₅.trans M₄.rd) (wr₅.trans M₄.wr) cs₆ rd₆ wr₆ f₆ o₁ o₂ o₃

end

end VG.Proof.AesGcm.X86_64.StreamTo
