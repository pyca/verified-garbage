import VerifiedGarbage.Proof.AesOcb.X86.Pass

/-!
# AES-OCB on x86: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz ctxCiph ctxInv)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left toNat_w64 add_ofNat_assoc32)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, `i`, the
working space of the functions called, the stack and the data. -/
abbrev wholeR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 ofsO, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    wC p.W, stk p, ⟨w64 p.D, p.n⟩]

theorem wholeR_mut {p : Prm} {m m' : Mem} (h : Frame (wholeR p) m m') : Frame (mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact inMut_stk p
  · exact inMut_d p

/-- The `m` blocks of the data, for a call. -/
theorem DReg.d {p : Prm} (L : Lay p) {s : State} (E : Env p s) {m : Nat} (hm : 16 * m ≤ p.n) : DReg p s p.D m := by
  have hd := L.dw
  have sub : Region.Sub ⟨w64 p.D, 16 * m⟩ ⟨w64 p.D, p.n⟩ := Region.sub_prefix hm
  refine ⟨by omega, (L.k_d.sub_left (Region.sub_prefix (by decide))).sub_right sub,
    (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide)), L.bd.sub_right sub, covers_prefix E.perm.d hm,
    fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, by simp, sub⟩

/-- `DECIPHER` with the key context, after a frame within `mutR`. -/
theorem ctxInv_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (mutR p) m m') :
    ctxInv m' (w64 p.K) p.R = ctxInv m (w64 p.K) p.R := by
  unfold ctxInv
  have hb := L.rounds_le
  rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (k_mut L r hr).sub_left (Region.sub_prefix (by omega)))
    (by omega)]

/-- `passStart`: the data, its `m` whole blocks, `i = 1`. -/
theorem passStart_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {m : Nat}
    (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m) :
    ∃ t', runBlock isa passStart t = some t' ∧ t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * 0) ∧
      t'.gpr .ebx = BitVec.ofNat 32 (m - 0) ∧ t'.gpr .edi = BitVec.ofNat 32 (0 + 1) ∧
      (∀ r, r ≠ .ebx → r ≠ .esi → r ≠ .edi → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  have hD := E.slots.data
  simp only [slotv_eq] at hD hnb
  exact ⟨_, by grun [passStart, E.ebp, L.aW, E.perm.wR, hD, hnb], by gregs [hD]; exact (BitVec.add_zero _).symm,
    by gregs [hnb, Nat.sub_zero], by gregs [], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [],
    by gmems []⟩

/-- What `whole` leaves. -/
structure WholePost (p : Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (wholeR p) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} {G : Mem → Cipher}
    (hcall : ∀ {s s' : State} {D : BitVec 32} {n : Nat}, CallPost p f D n s s' → ∀ i < n,
      blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) = G s.mem (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))))
    (hG : ∀ {m m' : Mem}, Frame (mutR p) m m' → G m' = G m)
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
    (L : Lay p) {t : State} (E : Env p t) {m : Nat} (hmn : 16 * m ≤ p.n) (hm0 : 0 < m)
    {O0 l : Block} (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m)
    (hofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i < m, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i < m, ckF2 (i + 1) = fC2 (ckF2 i)
      (G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1))) (offAt O0 l (i + 1))) :
    WP isa (whole fn pre post) t (WholePost p m O0 l
      (fun k => G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have hn := L.n32
  -- the first pass
  obtain ⟨s₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := passStart_ok L E hnb
  have E₁ : Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
    (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁
  have P₀ : PassInv p m O0 l (fun k => blockAtMem s₁.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := si₁, edi := di₁, ebx := bx₁
      ofs := by rw [m₁, hofs]; rfl
      ck := by rw [m₁, hck]
      blk := fun k _ => by simp
      l0 := by rw [m₁, hl0]
      gpr := fun _ _ _ _ _ _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i hi => by rw [hckF1 i hi, m₁]) hmn hm0 P₀) fun s₂ P₂ => ?_)
  have fP₂ : Frame (mutR p) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inl (by decide))
    · exact ⟨_, by simp, Region.sub_prefix hmn⟩
  -- the call
  have hD₂ := P₂.env.slots.data
  have hnb₂' : slotv s₂.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [← m₁] at hnb
    rw [← hnb]
    exact P₂.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub (by decide))).symm) (by decide)
  simp only [slotv_eq] at hD₂ hnb₂'
  have hargs : ∃ s₁, runBlock isa [.mov .edx (slot dataO), .mov .ebx (slot nbO)] s₂ = some s₁ ∧
      s₁.gpr .edx = p.D ∧ s₁.gpr .ebx = BitVec.ofNat 32 m ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s₂.gpr r) ∧ s₁.mem = s₂.mem ∧
      s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr :=
    ⟨_, by grun [P₂.env.ebp, L.aW, P₂.env.perm.wR, hD₂, hnb₂'], by gregs [hD₂], by gregs [hnb₂'],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  refine WP.seq (WP.mono (callBlocks_ok ok nosp stack L P₂.env hargs (DReg.d L P₂.env hmn)) fun s₃ P₃ => ?_)
  have E₃ := P₃.env
  -- what the call keeps
  have kC : ∀ {d k : Nat}, d + k ≤ scrO → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ →
      ∀ r ∈ [⟨w64 p.D, 16 * m⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p],
        (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h hD r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hD
    · exact Lay.w_w (.inl h) (by simp only [scrO] at h; omega) (by decide)
    · exact (L.bw' (by simp only [scrO] at h; omega)).symm
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ :=
    fun h => ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub h)).symm
  -- the blocks and slots of `W` the first pass and the call keep
  have kP : ∀ {d : Nat}, (d + 16 ≤ ofsO ∨ (48 ≤ d ∧ d + 16 ≤ lO) ∨ (112 ≤ d ∧ d + 16 ≤ kO) ∨ 224 ≤ d) →
      d + 16 ≤ scrO → blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => by
      rw [Proof.Ocb.blockAtMem_frame P₃.frame (kC h₂ (dW (by simp only [scrO] at h₂; omega))),
        Proof.Ocb.blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega) (by simp only [scrO] at h₂; omega) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega) (by simp only [scrO] at h₂; omega) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega) (by simp only [scrO] at h₂; omega) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO, ckO] at h₁ ⊢; omega) (by simp only [scrO] at h₂; omega)
            (by decide)
        · exact dW (by simp only [scrO] at h₂; omega))]
  have o0₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0 := by rw [kP (by decide) (by decide), m₁, ho0]
  have ck₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [Proof.Ocb.blockAtMem_frame P₃.frame (kC (by decide) (dW (by decide))), P₂.ck, hckF2₀]
  have nb₃ : slotv s₃.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [slotv_eq, ← hnb₂']
    exact P₃.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kC (by decide) (dW (by decide))) (by decide)
  -- `Offset_0` again
  obtain ⟨s₄a, run₄a, m₄a, g₄a, rd₄a, wr₄a⟩ := copy16_ok L E₃ (s := o0O) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  have f₄a : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] s₃.mem s₄a.mem := by
    rw [m₄a]; exact copyMem16_frame _ _ _ _ _
  have E₄a : Env p s₄a := E₃.mut L (by rw [g₄a _ (by decide), E₃.ebp]) (by rw [g₄a _ (by decide), E₃.esp]) rd₄a wr₄a
    (frame_toMut f₄a fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have nb₄a : slotv s₄a.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [slotv_eq, ← nb₃, slotv_eq]
    exact f₄a.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  obtain ⟨s₄, run₄, si₄, bx₄, di₄, g₄, m₄, rd₄, wr₄⟩ := passStart_ok L E₄a nb₄a
  have E₄ : Env p s₄ := E₄a.keep (by rw [g₄ _ (by decide) (by decide) (by decide)])
    (by rw [g₄ _ (by decide) (by decide) (by decide)]) rd₄ wr₄ m₄
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [m₄]; exact Proof.Ocb.blockAtMem_frame f₄a fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  have hG₂ : G s₂.mem = G t.mem := by rw [hG fP₂, m₁]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
      G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) := fun k hk => by
    have hBk := dblk L E₄ (i := k) (by omega)
    rw [← w64_add (show p.D.toNat + 16 * k < 2 ^ 32 by have := L.dw; omega), kB₄ hBk.w,
      w64_add (show p.D.toNat + 16 * k < 2 ^ 32 by have := L.dw; omega), hcall P₃ k hk, hG₂, P₂.blk k hk]
    simp only [hk, ↓reduceIte, m₁]
  have P₀' : PassInv p m O0 l (fun k => blockAtMem s₄.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := si₄, edi := di₄, ebx := bx₄
      ofs := by rw [m₄, m₄a, copyMem16_block, o0₃]; rfl
      ck := by
        rw [m₄, Proof.Ocb.blockAtMem_frame f₄a (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)),
          ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [m₄, Proof.Ocb.blockAtMem_frame f₄a (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)),
          kP (by decide) (by decide), m₁, hl0]
      gpr := fun _ _ _ _ _ _ _ => rfl }
  refine WP.seq (WP.of_runBlock ⟨s₄, runBlock_app_of run₄a run₄, ?_⟩)
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2 i hi, X₄ i hi]) hmn hm0 P₀') fun s₅ P₅ => ?_
  have subP : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
      ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩],
      ∃ r' ∈ wholeR p, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, by simp, Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.D, p.n⟩, by simp, Region.sub_prefix hmn⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, rd₄, rd₄a, P₃.rd, P₂.rd, rd₁], by rw [P₅.wr, wr₄, wr₄a, P₃.wr, P₂.wr, wr₁],
    fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← m₁]
    refine (P₂.frame.sub subP).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨w64 p.D, p.n⟩, by simp, Region.sub_prefix hmn⟩
      · exact ⟨wC p.W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨stk p, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact (f₄a.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩).trans
        (F₅.sub subP)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.X86
