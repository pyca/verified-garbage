import VerifiedGarbage.Proof.AesOcb.X86.Calls

/-!
# AES-OCB on x86: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `callBlocks_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq)

/-- What the pieces before the data write: the parts of `W` in `mutR` and
the stack. -/
abbrev wR (p : Prm) : List Region := [wA p.W, wB p.W, wV p.W, wC p.W, stk p]

theorem wR_mut {p : Prm} {m m' : Mem} (h : Frame (wR p) m m') : Frame (mutR p) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

/-- A frame within `wR`. -/
theorem frame_wR {p : Prm} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ wR p, Region.Sub r r') : Frame (wR p) m m' := h.sub hs

theorem inW_wR (p : Prm) {d k : Nat}
    (h : d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 176 ∨ 216 ≤ d ∧ d + k ≤ 384 ∨ 384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ wR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h
  · exact ⟨wA p.W, by simp, Offset.sub_base _ h⟩
  · exact ⟨wB p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨wV p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

/-- The data, after a frame within `wR`. -/
theorem data_wR {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (wR p) m m') :
    bytesAt m' (w64 p.D) p.n = bytesAt m (w64 p.D) p.n :=
  Proof.AesGcm.X86.bytesAt_frame h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w.sub_right (Region.sub_prefix (by decide))
    · exact L.d_w.sub_right (Lay.wSub (by decide))
    · exact L.d_w.sub_right (Lay.wSub (by decide))
    · exact L.d_w.sub_right (Lay.wSub (by decide))
    · exact L.bd.symm) (by have := L.dw; omega)

/-- The key context is apart from what the pieces write. -/
theorem k_mut {p : Prm} (L : Lay p) : ∀ r ∈ mutR p, (⟨w64 p.K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.bk.symm
  · exact L.k_d

/-- The key schedule, after a frame within `mutR`. -/
theorem ctxCiph_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (mutR p) m m') :
    ctxCiph m' (w64 p.K) p.R = ctxCiph m (w64 p.K) p.R := by
  unfold ctxCiph
  have hb := L.rounds_le
  rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (k_mut L r hr).sub_left (Region.sub_prefix (by omega)))
    (by omega)]

/-- What `nonce` leaves. -/
structure NonceOk (p : Prm) (o : Block) (s s' : State) : Prop where
  env : Env p s'
  frame : Frame (wR p) s.mem s'.mem
  ofs : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 o0O) = o
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
    blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 d)
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok (v : BlocksImpl) {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa (nonce (callees v)) s
      (NonceOk p (Spec.Ocb.offset0 (ctxCiph s.mem (w64 p.K) p.R) p.tl (bytesAt s.mem (w64 p.N) p.nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E) fun s₁ P₁ => ?_)
  have F₁ : Frame (wR p) s.mem s₁.mem := frame_wR P₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact inW_wR p (.inl (by decide))
    · exact inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  have E₁ : Env p s₁ := E.mut L (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P₁.rd P₁.wr (wR_mut F₁)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₁
    (oneBlock_ok E₁ tmpO) (DReg.w L E₁ (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun s₂ P₂ => ?_)
  have a112 : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  have F₂ : Frame (wR p) s₁.mem s₂.mem := frame_wR P₂.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a112]; exact inW_wR p (.inl (by decide))
    · exact inW_wR p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact ⟨_, by simp, fun _ h => h⟩
  have ktop : blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem (w64 p.K) p.R (Proof.Ocb.nonceN p.tl (bytesAt s.mem (w64 p.N) p.nl) &&& ~~~(63 : Block)) := by
    have := P₂.enc (i := 0) (by decide)
    rw [a112, show w64 p.W + BitVec.ofNat 64 tmpO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 tmpO from
      BitVec.add_zero _] at this
    rw [this, P₁.blk, ctxCiph_mut L (wR_mut F₁)]
  have hbv : ((Proof.Ocb.nonceN p.tl (bytesAt s.mem (w64 p.N) p.nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  have bot₂ : slotv s₂.mem p.W botO =
      BitVec.ofNat 32 ((Proof.Ocb.nonceN p.tl (bytesAt s.mem (w64 p.N) p.nl)).extractLsb' 0 6).toNat := by
    rw [← P₁.bot]
    exact P₂.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a112]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  obtain ⟨s₃, run₃, P₃⟩ := offset0_ok L P₂.env hbv bot₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have F₃ : Frame (wR p) s₂.mem s₃.mem := frame_wR P₃.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact inW_wR p (.inl (by decide))
    · exact inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  have E₃ : Env p s₃ := P₂.env.mut L (by rw [P₃.gpr _ (by decide) (by decide) (by decide) (by decide), P₂.env.ebp])
    (by rw [P₃.gpr _ (by decide) (by decide) (by decide) (by decide), P₂.env.esp]) P₃.rd P₃.wr (wR_mut F₃)
  refine ⟨E₃, F₁.trans (F₂.trans F₃), ?_, ?_, fun {d} h₁ h₂ => ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_,
    by rw [P₃.rd, P₂.rd, P₁.rd], by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [Proof.Ocb.blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by simp only [ofsO, o0O, stO]; omega) (by omega) (by decide)),
      Proof.Ocb.blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a112]; exact Lay.w_w (by simp only [tmpO]; omega) (by omega) (by decide)
        · exact Lay.w_w (by simp only [scrO]; omega) (by omega) (by decide)
        · exact (L.bw' (by omega)).symm),
      Proof.Ocb.blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Lay.w_w (by simp only [tmpO, botO]; omega) (by omega) (by decide))]
  · rw [P₃.gpr r h₁ h₂ h₃ h₄, P₂.gpr r h₁ h₂ h₃ h₄, P₁.gpr r h₁ h₃ h₄ h₅]

end VG.Proof.AesOcb.X86
