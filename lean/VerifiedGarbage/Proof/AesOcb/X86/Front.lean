import VerifiedGarbage.Proof.AesOcb.X86.TagIO

/-!
# AES-OCB on x86: up to the tag (`front`)

Untrusted: everything here is checked by Lean. `front` is the entry
(`entry_ok`), `L_$`, `L_0` and the checksum (`setup_ok`), `Offset_0`
(`nonce_ok`) and `HASH` (`hash_ok`), which leave `Pre` (`pre_ok`); then the
data (`bodySeal_ok`, `bodyOpen_ok`) and the tag at `W + d` (`tag_ok`)
(`sealFront_ok`, `openFront_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar pad lDollar)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq SavedAt length_bytesAt)

/-- What the entry writes: the saved registers and the slots. -/
abbrev entryR (p : Prm) : Region := ⟨w64 p.W + BitVec.ofNat 64 128, 88⟩

/-- A buffer apart from `W` and the stack and the data keeps its bytes across
a frame of `entryR :: mutR`. -/
theorem bytes_front {p : Prm} {P : BitVec 32} {len : Nat}
    (hw : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (hb : (stk p).Disjoint ⟨w64 P, len⟩)
    (hd : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩) (hl : len ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame (entryR p :: mutR p) m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Region.sub_prefix (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hb.symm
    · exact hd) hl

/-- What the pieces before the data leave, from the state `s` at the call. -/
structure Pre (p : Prm) (s s' : State) : Prop where
  env : Env p s'
  frame : Frame (entryR p :: mutR p) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem p.W s
  ofs : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem (w64 p.K) p.R) p.tl (bytesAt s.mem (w64 p.N) p.nl)
  o0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem (w64 p.K) p.R) p.tl (bytesAt s.mem (w64 p.N) p.nl)
  ck : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K))
  l0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0
  sum : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al)
  ciph : ctxCiph s'.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R
  inv : ctxInv s'.mem (w64 p.K) p.R = ctxInv s.mem (w64 p.K) p.R
  lstar : ctxLstar s'.mem (w64 p.K) = ctxLstar s.mem (w64 p.K)
  data : bytesAt s'.mem (w64 p.D) p.n = bytesAt s.mem (w64 p.D) p.n
  tag : bytesAt s'.mem (w64 p.T) p.tl = bytesAt s.mem (w64 p.T) p.tl

/-- The key context misses `entryR :: mutR`. -/
theorem k_front {p : Prm} (L : Lay p) : ∀ r ∈ entryR p :: mutR p, (⟨w64 p.K, 256⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact L.k_w' (by decide)
  · exact k_mut L r hr

theorem front_ciph {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (entryR p :: mutR p) m m') :
    ctxCiph m' (w64 p.K) p.R = ctxCiph m (w64 p.K) p.R ∧ ctxInv m' (w64 p.K) p.R = ctxInv m (w64 p.K) p.R ∧
      ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) := by
  have hb := L.rounds_le
  refine ⟨?_, ?_, Proof.Ocb.blockAtMem_frame h fun r hr => (k_front L r hr).sub_left (Offset.sub_base _ (by decide))⟩
  · unfold ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (k_front L r hr).sub_left (Region.sub_prefix (by omega)))
      (by omega)]
  · unfold ctxInv
    rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (k_front L r hr).sub_left (Region.sub_prefix (by omega)))
      (by omega)]

theorem mut_front {p : Prm} {m m' : Mem} (h : Frame (mutR p) m m') : Frame (entryR p :: mutR p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem entry_front {p : Prm} {m m' : Mem} (h : Frame [entryR p] m m') : Frame (entryR p :: mutR p) m m' :=
  h.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..

/-- The saved registers, after a frame within `mutR`. -/
theorem saved_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (mutR p) m m') {s₀ : State}
    (S : SavedAt m p.W s₀) : SavedAt m' p.W s₀ := SavedAt.mut L h S

theorem pre_ok (v : BlocksImpl) {s : State} (h : onePre s) :
    WP isa (.seq ocbEntry (.seq (.block setup) (.seq (nonce (callees v)) (hash (callees v))))) s
      (Pre (prmOf s) s) := by
  have L := lay_of h
  generalize hp : prmOf s = p at L
  refine WP.seq (WP.mono (hp ▸ entry_ok h) fun s₁ En => ?_)
  have fr₁ := entry_front En.frame
  obtain ⟨c₁, i₁, l₁⟩ := front_ciph L fr₁
  have hN₁ := bytes_front L.n_w L.bn L.n_d (by have := L.nl15; omega) fr₁
  have hA₁ := bytes_front L.a_w L.ba L.a_d (by have := L.aw; omega) fr₁
  have hD₁ := Proof.AesGcm.X86.bytesAt_frame En.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.dw; omega)
  have hT₁ := bytes_front L.t_w L.bt L.t_d (by have := L.tl16; omega) fr₁
  -- `L_$`, `L_0` and the checksum
  obtain ⟨s₂, run₂, P₂⟩ := setup_ok L En.env
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have f₂ : Frame (mutR p) s₁.mem s₂.mem := P₂.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  have E₂ : Env p s₂ := En.env.mut L (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), En.env.ebp])
    (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), En.env.esp]) P₂.rd P₂.wr f₂
  -- `Offset_0`
  refine WP.seq (WP.mono (nonce_ok v L E₂) fun s₃ P₃ => ?_)
  have f₃ : Frame (mutR p) s₂.mem s₃.mem := wR_mut P₃.frame
  have f₁₃ := f₂.trans f₃
  obtain ⟨c₂, -, l₂⟩ := front_ciph L (mut_front f₂)
  have hN₂ := nonce_mut L f₂
  -- `HASH`
  have C : HCtx p (ctxCiph s₃.mem (w64 p.K) p.R) (ctxLstar s₃.mem (w64 p.K)) (bytesAt s₃.mem (w64 p.A) p.al) s₃ :=
    ⟨L, rfl, rfl, rfl⟩
  have hl0₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₃.mem (w64 p.K)) 0 := by
    rw [P₃.keep (by decide) (by decide), P₂.l0, (front_ciph L (mut_front f₃)).2.2, l₂]
  refine WP.mono (hash_ok v C P₃.env hl0₃) fun s₄ ⟨E₄, F₄, sum₄, rd₄, wr₄⟩ => ?_
  have f₄ : Frame (mutR p) s₃.mem s₄.mem := wR_mut (hashR_wR F₄)
  have f₁₄ := f₁₃.trans f₄
  have fr := fr₁.trans (mut_front f₁₄)
  obtain ⟨c₄, i₄, l₄⟩ := front_ciph L fr
  obtain ⟨c₃, -, l₃⟩ := front_ciph L (mut_front f₁₃)
  have k₄ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (176 ≤ d ∧ d + 16 ≤ 220) ∨
      (224 ≤ d ∧ d + 16 ≤ 264)) →
      blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => Proof.Ocb.blockAtMem_frame F₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (by simp only [sumO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [lO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [ohO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [kO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [hlO]; omega) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  have kS : ∀ {d : Nat}, d + 16 ≤ 128 → 32 ≤ d → d + 16 ≤ 112 →
      blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun _ h₁ h₂ => P₃.keep h₁ h₂
  refine ⟨E₄, fr, by rw [rd₄, P₃.rd, P₂.rd, En.rd], by rw [wr₄, P₃.wr, P₂.wr, En.wr], saved_mut L f₁₄ En.saved,
    ?_, ?_, ?_, ?_, ?_, ?_, c₄, i₄, l₄, ?_, ?_⟩
  · rw [k₄ (by decide), P₃.ofs, c₂, c₁, hN₂, hN₁, ← hp]
  · rw [k₄ (by decide), P₃.o0, c₂, c₁, hN₂, hN₁, ← hp]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.ck]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.ld, l₁]
  · rw [k₄ (by decide), kS (by decide) (by decide) (by decide), P₂.l0, l₁]
  · rw [sum₄, c₃, l₃, c₁, l₁, aad_mut L f₁₃, hA₁]
  · rw [data_wR L (hashR_wR F₄), data_wR L P₃.frame, data_wR L (P₂.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp), hD₁]
  · rw [tag_mut L f₁₄, hT₁]

theorem seq_cont3 {a b c d k : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c d))) s P) (hk : ∀ t, P t → WP isa k t Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d k)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h₁ => WP.seq (WP.mono (WP.seq_iff.mp h₁) fun _ h₂ =>
    WP.seq (WP.mono (WP.seq_iff.mp h₂) fun _ h₃ => WP.seq (WP.mono h₃ hk))))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum,
`[96, 128)` and `[144, 160)`. -/
theorem body_keep {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (bodyR p) m m') {d : Nat}
    (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (128 ≤ d ∧ d + 16 ≤ 144) ∨ (160 ≤ d ∧ d + 16 ≤ 216)) :
    blockAtMem m' (w64 p.W + BitVec.ofNat 64 d) = blockAtMem m (w64 p.W + BitVec.ofNat 64 d) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (by omega) (by omega) (by decide)
    · exact Lay.w_w (by omega) (by omega) (by decide)
    · exact Lay.w_w (by simp only [t2O]; omega) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.bw' (by omega)).symm
    · exact (L.d_w' (by omega)).symm

/-- What `tag d` writes, within `mutR`. -/
theorem tagR_mut {p : Prm} {d : Nat} (hd : d = tagO ∨ d = t2O) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] m m') : Frame (mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · rcases hd with rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_stk p

/-- The data across `tag`. -/
theorem data_tag {p : Prm} (L : Lay p) {d : Nat} (hd : d = tagO ∨ d = t2O) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] m m') :
    bytesAt m' (w64 p.D) p.n = bytesAt m (w64 p.D) p.n :=
  Proof.AesGcm.X86.bytesAt_frame h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by rcases hd with rfl | rfl <;> decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm) (by have := L.dw; omega)

/-- What `front` leaves: the environment, our caller's registers, the data
and the tag at `W + d`. -/
structure Front (p : Prm) (s s' : State) : Prop where
  env : Env p s'
  frame : Frame (entryR p :: mutR p) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem p.W s

/-- `front` for `seal`: the ciphertext over the data and the tag at `W`. -/
theorem sealFront_ok (v : BlocksImpl) {s : State} (h : onePre s) :
    WP isa (front (callees v) true tagO) s fun s' => Front (prmOf s) s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R) (ctxLstar s.mem (w64 (prmOf s).K))
          (prmOf s).tl (bytesAt s.mem (w64 (prmOf s).N) (prmOf s).nl) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)
          (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) =
        (bytesAt s'.mem (w64 (prmOf s).D) (prmOf s).n, bytesAt s'.mem (w64 (prmOf s).W) (prmOf s).tl) := by
  have L := lay_of h
  have Pp := pre_ok v h
  generalize prmOf s = p at L Pp ⊢
  unfold front
  refine seq_cont3 Pp fun s₃ P₃ => ?_
  refine WP.seq (WP.mono (bodySeal_ok v L P₃.env P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  have F₄ : Frame (mutR p) s₃.mem s₄.mem := bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := (ctxCiph_mut L F₄).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [body_keep L B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al) := by
    rw [body_keep L B.frame (d := sumO) (by decide), P₃.sum]
  refine WP.mono (tag_ok v L B.env (d := tagO) (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR p) s₄.mem s₅.mem := tagR_mut (.inl rfl) T₅.frame
  refine ⟨⟨T₅.env, P₃.frame.trans (mut_front (F₄.trans F₅)), by rw [T₅.rd, B.rd, P₃.rd],
    by rw [T₅.wr, B.wr, P₃.wr], saved_mut L (F₄.trans F₅) P₃.saved⟩, ?_⟩
  have hout := B.out
  rw [P₃.ciph, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  have tv := T₅.val
  rw [show w64 p.W + BitVec.ofNat 64 tagO = w64 p.W from BitVec.add_zero _] at tv
  rw [Proof.Ocb.encryptWith_eq, data_tag L (.inl rfl) T₅.frame, hout, Proof.Ocb.bytesAt_take_block _ _ L.tl16, tv,
    hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- `front` for `open`: the plaintext over the data and the tag at
`W + t2O`, which decide `OCB-DECRYPT` with the tag `tag`. -/
theorem openFront_ok (v : BlocksImpl) {s : State} (h : onePre s) (tag : List Byte) :
    WP isa (front (callees v) false t2O) s fun s' => Front (prmOf s) s s' ∧
      Spec.Ocb.decryptWith (ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R) (ctxInv s.mem (w64 (prmOf s).K) (prmOf s).R)
          (ctxLstar s.mem (w64 (prmOf s).K)) (prmOf s).tl (bytesAt s.mem (w64 (prmOf s).N) (prmOf s).nl)
          (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al) (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) tag =
        if bytesAt s'.mem (w64 (prmOf s).W + BitVec.ofNat 64 t2O) (prmOf s).tl = tag then
          some (bytesAt s'.mem (w64 (prmOf s).D) (prmOf s).n)
        else none := by
  have L := lay_of h
  have Pp := pre_ok v h
  generalize prmOf s = p at L Pp ⊢
  unfold front
  refine seq_cont3 Pp fun s₃ P₃ => ?_
  refine WP.seq (WP.mono (bodyOpen_ok v L P₃.env P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  have F₄ : Frame (mutR p) s₃.mem s₄.mem := bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := (ctxCiph_mut L F₄).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem (w64 p.K)) := by
    rw [body_keep L B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (w64 p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem (w64 p.K) p.R) (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.A) p.al) := by
    rw [body_keep L B.frame (d := sumO) (by decide), P₃.sum]
  refine WP.mono (tag_ok v L B.env (d := t2O) (.inr rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR p) s₄.mem s₅.mem := tagR_mut (.inr rfl) T₅.frame
  refine ⟨⟨T₅.env, P₃.frame.trans (mut_front (F₄.trans F₅)), by rw [T₅.rd, B.rd, P₃.rd],
    by rw [T₅.wr, B.wr, P₃.wr], saved_mut L (F₄.trans F₅) P₃.saved⟩, ?_⟩
  have hout := B.out
  rw [P₃.ciph, P₃.inv, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.ciph, P₃.inv, P₃.lstar, P₃.data] at hck
  rw [Proof.Ocb.decryptWith_eq, data_tag L (.inr rfl) T₅.frame, hout, Proof.Ocb.bytesAt_take_block _ _ L.tl16,
    T₅.val, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

end VG.Proof.AesOcb.X86
