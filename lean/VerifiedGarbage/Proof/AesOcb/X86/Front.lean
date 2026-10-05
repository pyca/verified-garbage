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

end VG.Proof.AesOcb.X86
