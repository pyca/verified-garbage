import VerifiedGarbage.Proof.AesGcm.AArch64.Seal

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. The entry also keeps
`tag_len` at `W + 248`; if §5.2.1.2 does not allow it, `open` returns 0.
Otherwise `tagIn` copies the received tag to `W`, `front_ok` starts the
state and absorbs the additional data,
`decAbs` absorbs the ciphertext, `finBody 112` writes the tag at `W + 112`,
`cmpSeg` compares it with the received one without a branch, and the data is
decrypted only if they are equal (`open_wp`), which is the one secret the
code branches on, as the contract allows.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr zeros)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `decAbs`: the additional data padded if this is the first text, and the
text absorbed. -/
theorem decAbs_ok (v : GcmImpl) {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
    {s : State} (h : BodyIn Ctx St W SP k R n P D a c H s) :
    WP isa (decAbs v.callees) s fun s₄ => Env Ctx St W SP s₄ ∧ Kept k s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₄.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c ++ bytesAt s.mem D n))) := by
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hlt := h.data.ok.lt
  refine WP.seq_assoc (WP.seq (WP.mono (pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_))
  refine WP.seq (WP.mono (textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (data_tFrame h.data) (by omega)
  have hd₃ : DataW Ctx St W s₃ D n := h.data.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
  have F₃ : Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₃.mem := by
    rw [m₃]; exact f₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  refine WP.ite (decide (n = 0)) (eval_zero ((hk₃ .x26 (by decide)).trans k26) hlt) (fun ht => ?_) (fun hf => ?_)
  · have hn0 : n = 0 := by simpa using ht
    refine WP.block_nil ⟨he₃, hk₃, x25₃, F₃, by rw [r₃.rd, rd₂], by rw [r₃.wr, wr₂], fun ha => ?_⟩
    rw [ghashInput_xf, length_bytesAt, hn0, show bytesAt s.mem D 0 = [] from rfl, List.append_nil, m₃]
    have := abs₂ ha
    rw [hn0] at this
    exact this
  · have hn0 : n ≠ 0 := by simpa using hf
    have hA : AbsIn Ctx St W SP k H (xf a c n) D n (P % 16) s₃ :=
      ⟨he₃, hk₃, x23₃, x24₃, x25₃, by rw [xf_len hn0, h.hc], hd₃.ok, by rw [m₃, hH₂]⟩
    refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) v hA)) fun s₄ ⟨h₄, rd₄, wr₄⟩ =>
      ⟨h₄.env, h₄.kept, h₄.x25,
        F₃.trans (h₄.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩),
        by rw [rd₄, r₃.rd, rd₂], by rw [wr₄, r₃.wr, wr₂], fun ha => ?_⟩
    rw [ghashInput_xf, length_bytesAt, ← hD₃]
    exact h₄.abs (by rw [m₃]; exact abs₂ ha)

end

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr zeros)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- The regions `openMain` writes, but the data. -/
abbrev omFrame (W : Addr) : List Region :=
  frontFrame (W + BitVec.ofNat 64 16) W ++ (tFrame (W + BitVec.ofNat 64 16) W 16 ++
    absFrame (W + BitVec.ofNat 64 16) W 16) ++ finFrame (W + BitVec.ofNat 64 16) W 112 ++
    [⟨W + BitVec.ofNat 64 256, 32⟩]

theorem omFrame_work (W : Addr) : ∀ r ∈ omFrame W, Region.Sub r (workR W) := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact finFrame_work W (.inr rfl) r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact frontFrame_work W r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (bodyFrame_work W 0 0 r (mem_bt hr)).resolve_right (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)
  · exact (bodyFrame_work W 0 0 r (mem_ba hr)).resolve_right (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)


theorem saved_omFrame {Ctx W : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W) :
    ∀ r ∈ omFrame W, (savedR W).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact saved_cmp L r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · exact saved_finFrame L (.inr rfl) r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_frontFrame L r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact saved_tFrame L (.inr rfl) r hr
  · exact saved_absFrame L (.inr rfl) r hr

/-- What `openMain` writes is above the received tag. -/
theorem omFrame_hi (W : Addr) : ∀ r ∈ omFrame W, Region.Sub r ⟨W + BitVec.ofNat 64 16, 2544⟩ := by
  have hi : ∀ d k, 16 ≤ d → d + k ≤ 2560 →
      Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 16, 2544⟩ :=
    fun d k h₁ h₂ => Offset.sub _ h₁ (by omega)
  have st : ∀ d k, d + k ≤ 80 →
      Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 16, 2544⟩ :=
    fun d k h => Offset.sub_base _ (by omega)
  intro r hr
  simp only [omFrame, frontFrame, j0Frame, absFrame, tFrame, finFrame, tagFrame, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  all_goals first
    | with_reducible exact Region.sub_prefix (by decide)
    | with_reducible exact st _ _ (by decide)
    | with_reducible exact hi _ _ (by decide) (by decide)

/-- The tag compared: 1 in `x27` if it is right, 0 if not. -/
theorem okBit_ok {s : State} {b : Bool} (h10 : s.gpr .x10 = BitVec.ofNat 64 (if b then 0 else 1)) :
    WP isa (.block [imm .x27 1, .sub .x .x27 .x27 .x10]) s fun s' =>
      s'.gpr .x27 = BitVec.ofNat 64 (if b then 1 else 0) ∧ Regs [.x27] s s' := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h10]
  cases b <;> decide

/-- `openMain` up to the branch on the tag. -/
def omA (c : Callees) : Prog isa :=
  .seq (j0 c) (.seq (oneAad c) (.seq (.block encPrep) (.seq (decAbs c) (.seq (.block finPrep)
    (.seq (finBody c uO) (.seq (.block [.ldr .x .x28 .x19 tlO]) (.seq cmpSeg
      (.block [imm .x27 1, .sub .x .x27 .x27 .x10]))))))))

/-- The rest: the branch on the tag, and the result. -/
def omB (c : Callees) : Prog isa :=
  .seq (.ite (.zero .x .x27) (.block []) (oneCrypt c)) (.block [mov .x0 .x27])

theorem Exec.seq_assoc {a b c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa (.seq a (.seq b c)) s t s') :
    Exec isa (.seq (.seq a b) c) s t s' := by
  cases h with
  | seq e₁ e₂ => cases e₂ with
    | seq eb ec => rw [← List.append_assoc]; exact .seq (.seq e₁ eb) ec

theorem Exec.seq_assoc' {a b c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa (.seq (.seq a b) c) s t s') : Exec isa (.seq a (.seq b c)) s t s' := by
  cases h with
  | seq e₁ e₂ => cases e₁ with
    | seq ea eb => rw [List.append_assoc]; exact .seq ea (.seq eb e₂)

/-- Programs with the same runs. -/
def PEq (c₁ c₂ : Prog isa) : Prop := ∀ s t s', Exec isa c₁ s t s' ↔ Exec isa c₂ s t s'

theorem PEq.assoc (a b c : Prog isa) : PEq (.seq (.seq a b) c) (.seq a (.seq b c)) :=
  fun _ _ _ => ⟨Exec.seq_assoc', Exec.seq_assoc⟩

theorem PEq.seq_right (a : Prog isa) {b b' : Prog isa} (h : PEq b b') : PEq (.seq a b) (.seq a b') := by
  intro s t s'
  constructor
  · intro e; cases e with | seq e₁ e₂ => exact .seq e₁ ((h _ _ _).mp e₂)
  · intro e; cases e with | seq e₁ e₂ => exact .seq e₁ ((h _ _ _).mpr e₂)

theorem PEq.symm {a b : Prog isa} (h : PEq a b) : PEq b a := fun s t s' => (h s t s').symm

theorem PEq.trans {a b c : Prog isa} (h₁ : PEq a b) (h₂ : PEq b c) : PEq a c :=
  fun s t s' => (h₁ s t s').trans (h₂ s t s')

theorem PEq.wp {a b : Prog isa} (h : PEq a b) {s : State} {Q : State → Prop} (w : WP isa b s Q) : WP isa a s Q := by
  obtain ⟨t, s', e, q⟩ := w; exact ⟨t, s', (h _ _ _).mpr e, q⟩

theorem PEq.rel {a b : Prog isa} (h : PEq a b) {P Q : State → State → Prop} (r : RelCT isa P b Q) :
    RelCT isa P a Q := fun _ _ _ _ _ _ hp e₁ e₂ => r _ _ _ _ _ _ hp ((h _ _ _).mp e₁) ((h _ _ _).mp e₂)

/-- `openMain` is `omA` then `omB`. -/
theorem openMain_split (c : Callees) : PEq (.seq (omA c) (omB c)) (openMain c) := by
  unfold omA omB openMain
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  exact PEq.assoc _ _ _

/-- What is known at the branch of `openMain`. -/
structure MidO (Ctx W SP D Np A : Addr) (R nl al n tl : Nat) (s s₇ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇
  frame : Frame (omFrame W) s.mem s₇.mem
  x22 : s₇.gpr .x22 = BitVec.ofNat 64 R
  x27 : s₇.gpr .x27 = BitVec.ofNat 64 (if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
    (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
    (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then 1 else 0)
  data : DataW Ctx (W + BitVec.ofNat 64 16) W s₇ D n
  sD : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  cb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))

/-- The slots are outside what `openMain` writes before the branch. -/
theorem slots_omFrame {Ctx W D : Addr} {n : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
    (ddW : (⟨D, n⟩ : Region).Disjoint (workR W)) :
    ∀ r ∈ omFrame W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  rotate_left
  · rcases List.mem_append.mp hr with hr | hr
    · exact slots_bodyFrame L ddW r (mem_bt hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using (L.st_w (a := 0) (n := 32) (d := 216) (k := 40) (by decide)
          (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · exact slots_frontFrame L r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact slots_bodyFrame L ddW r (mem_bt hr)
  · exact slots_bodyFrame L ddW r (mem_ba hr)

theorem openMainA_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h23 : s.gpr .x23 = Np) (h24 : s.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk (W + BitVec.ofNat 64 16) W s Np nl) (haad : DataOk (W + BitVec.ofNat 64 16) W s A al)
    (hdat : DataW Ctx (W + BitVec.ofNat 64 16) W s D n) (ddW : (⟨D, n⟩ : Region).Disjoint (workR W))
    (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (omA v.callees) s (MidO Ctx W SP D Np A R nl al n tl s) := by
  unfold omA
  have hle := tagLenOk_le hok
  have hnlt := hdat.ok.lt
  have dD : ∀ r ∈ omFrame W, (⟨D, n⟩ : Region).Disjoint r := keep_of_sub (omFrame_work W) ddW
  have dC : ∀ r ∈ omFrame W, (⟨Ctx, 256⟩ : Region).Disjoint r := keep_of_sub (omFrame_work W) dcW
  have sl := slots_omFrame L ddW
  have mF : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ omFrame W) → ∀ {m m' : Mem}, Frame rs m m' →
      Frame (omFrame W) m m' := fun hs _ _ hf => hf.mono hs
  refine front_ok L v he (fun _ _ => rfl : Kept s.gpr s) h23 h24 h26 h27 hnon haad rfl sA sL sD sN
    fun s₁ h₁ => ?_
  have F₁ : Frame (omFrame W) s.mem s₁.mem :=
    mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) h₁.frame
  have hdat₁ : DataW Ctx (W + BitVec.ofNat 64 16) W s₁ D n := hdat.of_eq h₁.rd h₁.wr
  have hB : BodyIn Ctx (W + BitVec.ofNat 64 16) W SP s₁.gpr R n 0 D (bytesAt s.mem A al) []
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) s₁ :=
    ⟨h₁.env, fun _ _ => rfl, by rw [h₁.x22, h22], hR, h₁.x25, h₁.x26, h₁.x27, h₁.x28, rfl, by decide, hdat₁,
      h₁.hH⟩
  refine WP.seq (WP.mono (decAbs_ok L v hB) fun s₂ ⟨he₂, hk₂, x25₂, f₂, rd₂, wr₂, abs₂⟩ => ?_)
  have F₂ : Frame (omFrame W) s.mem s₂.mem :=
    F₁.trans (mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))) f₂)
  have slot : ∀ {m : Mem}, Frame (omFrame W) s.mem m → ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      m.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d h₁ h₂ => slot_kept hf sl h₁ h₂
  refine WP.seq (WP.mono (finPrep_ok (al := al) (n := n) he₂.x19 (covers_left he₂.perm.w) (by rw [slot F₂ 224 (by decide) (by decide), sL])
    (by rw [slot F₂ 240 (by decide) (by decide), sN])) fun s₃ ⟨x26₃, x27₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have F₃ : Frame (omFrame W) s.mem s₃.mem := by rw [r₃.mem]; exact F₂
  have hC₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame F₁ dD (by omega)
  have hlen : ([] ++ bytesAt s₁.mem D n).length = n := by rw [List.nil_append, length_bytesAt]
  have x22₃ : s₃.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₃.others _ (by decide), hk₂ .x22 (by decide), h₁.x22, h22]
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
    blockAt_frame F₃ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))
  refine WP.seq (WP.mono (WP.with_rdwr (finBody_ok L v (.inr rfl) (a := bytesAt s.mem A al)
    (c := [] ++ bytesAt s₁.mem D n)
    (H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)) he₃ (fun _ _ => rfl) x22₃ hR
    (by rw [x26₃, length_bytesAt]) (by rw [x27₃, hlen]) (by rw [hlen]; exact hnlt) hH₃))
    fun s₄ ⟨⟨he₄, hk₄, f₄, out₄⟩, rd₄, wr₄⟩ => ?_)
  have F₄ : Frame (omFrame W) s.mem s₄.mem :=
    F₃.trans (mF (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)) f₄)
  obtain ⟨s₅, run₅, x28₅, r₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x28 .x19 tlO] s₄ = some s₅ ∧
      s₅.gpr .x28 = BitVec.ofNat 64 tl ∧ Regs [.x28] s₄ s₅ := by
    have q := he₄.perm.wR (show 248 + 8 ≤ 2560 by decide)
    have e := slot F₄ 248 (by decide) (by decide)
    rw [sT] at e
    refine ⟨_, by arun [he₄.x19, q], ?_⟩
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₄.mem.read (W + 248#64) 8 = s₄.mem.readW (W + BitVec.ofNat 64 248) 64 from rfl, e]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.of_regs r₅
  refine WP.seq (WP.mono (WP.with_rdwr (cmpSeg_ok L he₅ (fun _ _ => rfl : Kept s₅.gpr s₅) x28₅ hle))
    fun s₆ ⟨⟨x10₆, he₆, hk₆, _, f₆⟩, rd₆, wr₆⟩ => ?_)
  refine WP.mono (okBit_ok (b := decide (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl =
      bytesAt s₅.mem W tl)) (by rw [x10₆]; simp only [decide_eq_true_eq]))
    fun s₇ ⟨x27₇, r₇⟩ => ?_
  have he₇ := he₆.of_regs r₇
  have F₇ : Frame (omFrame W) s.mem s₇.mem := by
    rw [r₇.mem]
    exact F₄.trans (by rw [← r₅.mem]; exact mF (fun r hr => List.mem_append_right _ hr) f₆)
  -- The tag and the comparison.
  have hab : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (ghashInput (bytesAt s.mem A al) ([] ++ bytesAt s₁.mem D n)) := by
    rw [r₃.mem]; exact abs₂ h₁.abs
  have hj₃ : blockAt s₃.mem (W + BitVec.ofNat 64 16) =
      Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) := by
    rw [r₃.mem, blockAt_frame f₂ (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact st0_bodyFrame L ddW r (mem_bt hr)
      · exact st0_bodyFrame L ddW r (mem_ba hr)), h₁.j0]
  have hT₅ : bytesAt s₅.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
      (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n) := by
    rw [r₅.mem, out₄ hab, ciph_frame F₃ dC hR, hj₃, Proof.Gcm.fullTag_eq, List.nil_append, hC₁]
  have hW₅ : bytesAt s₅.mem W tl = bytesAt s.mem W tl := by
    rw [r₅.mem]
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega)
    have := (Offset.disjoint W (d := 0) (n := tl) (e := 16) (k := 2544) (.inl (by omega)) (by omega)
      (by decide)).sub_right (omFrame_hi W r hr)
    simpa using this
  have hb : (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₅.mem W tl) ↔
      (Spec.Gcm.fullTag (ciphOf s.mem Ctx R) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)
        (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl := by
    rw [← bytesAt_take _ _ hle, hT₅, hW₅]
  generalize hBd : decide (bytesAt s₅.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₅.mem W tl) = B at x27₇
  have hBeq : decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R) (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) = B := by
    rw [← hBd]; exact decide_eq_decide.mpr hb.symm
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega)
  have x22₇ : s₇.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₇.others _ (by decide), hk₆ .x22 (by decide), r₅.others _ (by decide), hk₄ .x22 (by decide), x22₃]
  have hcb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)) := by
    have d₁ : ∀ r ∈ tFrame (W + BitVec.ofNat 64 16) W 16 ++ absFrame (W + BitVec.ofNat 64 16) W 16,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact (acc_tFrame_free L r hr).sub_left (Region.sub_prefix (by decide))
      · exact (ctr_absFrame L r hr).sub_left (Region.sub_prefix (by decide))
    have d₂ : ∀ r ∈ finFrame (W + BitVec.ofNat 64 16) W 112,
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact (acc_tFrame_free L r hr).sub_left (Region.sub_prefix (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using L.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
    have d₃ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)],
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩
    rw [r₇.mem, blockAt_frame f₆ d₃, r₅.mem, blockAt_frame f₄ d₂, r₃.mem, blockAt_frame f₂ d₁, h₁.cb]
  exact ⟨he₇, F₇, x22₇, by rw [x27₇, hBeq],
    hdat.of_eq (by rw [r₇.rd, rd₆, r₅.rd, rd₄, r₃.rd, rd₂, h₁.rd]) (by rw [r₇.wr, wr₆, r₅.wr, wr₄, r₃.wr, wr₂, h₁.wr]),
    by rw [slot F₇ 232 (by decide) (by decide), sD], by rw [slot F₇ 240 (by decide) (by decide), sN], hcb⟩

/-- The loads before `crypt` in `oneCrypt`. -/
theorem ocLdr_ok {Ctx W SP D : Addr} {n : Nat} {s₇ : State} (he₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇)
    (sD₇ : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN₇ : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0]) s₇ fun s₈ =>
      s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧
        s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x23, .x24, .x25] s₇ s₈ := by
  have q₁ := he₇.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have q₂ := he₇.perm.wR (show 240 + 8 ≤ 2560 by decide)
  refine WP.run ⟨_, by arun [he₇.x19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₇.mem.read (W + 232#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, sD₇]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s₇.mem.read (W + 240#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN₇]; rfl

/-- What `crypt` needs in `oneCrypt`, after its loads. -/
theorem oc_in {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    {s s₇ s₈ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidO Ctx W SP D Np A R nl al n tl s s₇)
    (h : s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧
        s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x23, .x24, .x25] s₇ s₈) :
    CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D n s₈ :=
  ⟨mo.env.of_regs h.2.2.2, fun _ _ => rfl, by rw [h.2.2.2.others _ (by decide), mo.x22], hR, h.1, h.2.1, h.2.2.1,
    mo.data.of_eq h.2.2.2.rd h.2.2.2.wr⟩

theorem omIte_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (ddW : (⟨D, n⟩ : Region).Disjoint (workR W)) (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (mo : MidO Ctx W SP D Np A R nl al n tl s s₇) :
    WP isa (.ite (.zero .x .x27) (.block []) (oneCrypt v.callees)) s₇ fun s₈ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) W D n) s₇.mem s₈.mem ∧
      bytesAt s₈.mem D n = if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
          (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
          (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then
        gctr (ciphOf s.mem Ctx R) (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
          (bytesAt s.mem Np nl))) (bytesAt s.mem D n) else bytesAt s.mem D n := by
  have dD : ∀ r ∈ omFrame W, (⟨D, n⟩ : Region).Disjoint r := keep_of_sub (omFrame_work W) ddW
  have dC : ∀ r ∈ omFrame W, (⟨Ctx, 256⟩ : Region).Disjoint r := keep_of_sub (omFrame_work W) dcW
  have hnlt := mo.data.ok.lt
  have F₇ := mo.frame
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega)
  have x27₇ := mo.x27
  generalize decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R) (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
    (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) = B at x27₇ ⊢
  refine WP.ite (decide ((if B then 1 else 0) = 0)) (eval_zero x27₇ (by cases B <;> decide)) (fun ht => ?_)
    (fun hf => ?_)
  · have hB : B = false := by revert ht; cases B <;> simp
    subst hB
    exact WP.block_nil ⟨mo.env, rfl, Frame.refl _ _, by rw [hD₇]; rfl⟩
  · have hB : B = true := by revert hf; cases B <;> simp
    subst hB
    refine WP.seq (WP.mono (ocLdr_ok mo.env mo.sD mo.sN) fun s₈ h₈ => ?_)
    have r₈ := h₈.2.2.2
    have F₈ : Frame (omFrame W) s.mem s₈.mem := by rw [r₈.mem]; exact F₇
    have hcb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)) := by
      rw [r₈.mem, mo.cb]
    have hc₈ : ciphOf s₈.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame F₈ dC hR
    have hD₈ : bytesAt s₈.mem D n = bytesAt s.mem D n := bytesAt_frame F₈ dD (by omega)
    refine WP.mono (crypt_ok L v (icb := inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt s.mem Np nl))) (oc_in hR mo h₈)) fun s₉ h₉ => ⟨h₉.env, ?_, by rw [← r₈.mem]; exact h₉.frame, ?_⟩
    · rw [h₉.kept .x27 (by decide), r₈.others _ (by decide)]
    · rw [h₉.out (Proof.Gcm.ctr_zero _ _ _ _ hcb₈), hc₈, hD₈, Proof.Gcm.gctr_eq]
      rfl

theorem omB_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (ddW : (⟨D, n⟩ : Region).Disjoint (workR W)) (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (mo : MidO Ctx W SP D Np A R nl al n tl s s₇) :
    WP isa (omB v.callees) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: omFrame W ++ crFrame (W + BitVec.ofNat 64 16) W D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n := by
  unfold omB
  refine WP.seq (WP.mono (omIte_ok v L hR ddW dcW mo) fun s₈ ⟨he₈, x27₈, f₈, d₈⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨he₈.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, ?_, by simp [gpr_write, x27₈, mo.x27], d₈⟩
  exact (mo.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ (List.mem_append_left _ hr), fun _ h => h⟩).trans
    (f₈.sub fun r hr => ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), fun _ h => h⟩)

theorem openMain_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h23 : s.gpr .x23 = Np) (h24 : s.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk (W + BitVec.ofNat 64 16) W s Np nl) (haad : DataOk (W + BitVec.ofNat 64 16) W s A al)
    (hdat : DataW Ctx (W + BitVec.ofNat 64 16) W s D n) (ddW : (⟨D, n⟩ : Region).Disjoint (workR W))
    (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (openMain v.callees) s fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: omFrame W ++ crFrame (W + BitVec.ofNat 64 16) W D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n :=
  (openMain_split v.callees).symm.wp (WP.seq (c₁ := omA v.callees) (WP.mono (openMainA_ok v L he h22 hR h23 h24 h26 h27 hnon haad hdat ddW dcW
    sA sL sD sN sT hok) fun _ mo => omB_ok v L hR ddW dcW mo))

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr zeros)

/-- What is known after `open`'s entry, from the state `s₀` it was called in, with the
received tag the `tl` bytes at `Tg`. -/
structure OpenIn (Ctx W SP Np A D Tg : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
  lay : Lay Ctx (W + BitVec.ofNat 64 16) W
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 nl
  x26 : s.gpr .x26 = BitVec.ofNat 64 nl
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = BitVec.ofNat 64 tl
  tlt : tl < 2 ^ 64
  non : DataOk (W + BitVec.ofNat 64 16) W s Np nl
  aad : DataOk (W + BitVec.ofNat 64 16) W s A al
  dat : DataW Ctx (W + BitVec.ofNat 64 16) W s D n
  tagR : Covers [⟨Tg, tl⟩] (s.rd ++ s.wr)
  dnW : (⟨Np, nl⟩ : Region).Disjoint (workR W)
  daW : (⟨A, al⟩ : Region).Disjoint (workR W)
  ddW : (⟨D, n⟩ : Region).Disjoint (workR W)
  dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W)
  dtW : (⟨Tg, tl⟩ : Region).Disjoint (workR W)
  sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A
  sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl
  fr : Frame [entryR W, ⟨W, 16⟩] s₀.mem s.mem
  sv : SavedAt s.mem W s₀
  sp₀ : s₀.sp = SP

theorem OpenIn.of_regs {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s s' : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s) (r : Regs [.x9, .x10] s s') :
    OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s' :=
  ⟨o.lay, o.env.of_regs r, by rw [r.others _ (by decide), o.x22], o.rounds, by rw [r.others _ (by decide), o.x23],
    by rw [r.others _ (by decide), o.x24], by rw [r.others _ (by decide), o.x26],
    by rw [r.others _ (by decide), o.x27], by rw [r.others _ (by decide), o.x28], o.tlt,
    o.non.of_eq r.rd r.wr, o.aad.of_eq r.rd r.wr, o.dat.of_eq r.rd r.wr, by rw [r.rd, r.wr]; exact o.tagR,
    o.dnW, o.daW, o.ddW, o.dcW, o.dtW,
    by rw [r.mem, o.sA], by rw [r.mem, o.sL], by rw [r.mem, o.sD], by rw [r.mem, o.sN], by rw [r.mem, o.sT],
    by rw [r.mem]; exact o.fr, by rw [r.mem]; exact o.sv, o.sp₀⟩

/-- What the entry and `tagIn` write is in `work`. -/
theorem entry16_work (W : Addr) : ∀ r ∈ [entryR W, ⟨W, 16⟩], Region.Sub r (workR W) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Lay.wSub (by decide)
  · exact Region.sub_prefix (by decide)

/-- `OpenIn` after `tagIn`. -/
theorem OpenIn.tagIn {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s s' : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s) (f : Frame [⟨W, 16⟩] s.mem s'.mem)
    (og : Others loopRegs s s') (sp : s'.sp = s.sp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s' := by
  have L := o.lay
  have sl : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    slot_kept f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 216) (n := 40) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)) h₁ h₂
  exact ⟨L, o.env.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr,
    by rw [og _ (by decide), o.x22], o.rounds, by rw [og _ (by decide), o.x23],
    by rw [og _ (by decide), o.x24], by rw [og _ (by decide), o.x26],
    by rw [og _ (by decide), o.x27], by rw [og _ (by decide), o.x28], o.tlt,
    o.non.of_eq rd wr, o.aad.of_eq rd wr, o.dat.of_eq rd wr, by rw [rd, wr]; exact o.tagR,
    o.dnW, o.daW, o.ddW, o.dcW, o.dtW,
    by rw [sl 216 (by decide) (by decide), o.sA], by rw [sl 224 (by decide) (by decide), o.sL],
    by rw [sl 232 (by decide) (by decide), o.sD], by rw [sl 240 (by decide) (by decide), o.sN],
    by rw [sl 248 (by decide) (by decide), o.sT],
    o.fr.trans (f.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩),
    o.sv.frame f (saved_tag16 L), o.sp₀⟩

/-- `openPre`'s common arguments. -/
theorem openCore {s : State} (hs : openPre s) : oneCore 3 2 s := by
  simp only [openPre] at hs
  obtain ⟨hrd, hwr, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, -, dwa, wc, wn, wa, wd, ww, wsp, hR⟩ := hs
  exact ⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hwr]; simp,
    by rw [hwr]; simp, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, wc, wn, wa, wd, ww, wsp, hR⟩

/-- What `openPre` gives. -/
theorem openLay {s : State} (hs : openPre s) :
    OneLay s 3 2 ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint (workR (stackArg s 2)) := by
  have hs' := hs
  simp only [openPre] at hs'
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, dtw, -⟩ := hs'
  exact ⟨oneLay (openCore hs), covers_mem (by rw [hrd, hwr]; simp), dtw⟩

/-- `open`'s first block: the entry, the tag length and the tag. -/
theorem openEntry_ok {s : State} (hs : openAArch64.pre s) :
    WP isa (.block (oneEntry 16 ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr))) s fun s' =>
      OpenIn (s.gpr .x0) (stackArg s 2) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s s' ∧
      s'.gpr .x12 = stackArg s 0 := by
  obtain ⟨ol, tR, dtW⟩ := openLay hs
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  have hW16 : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg s 2 := rfl
  have hT8 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (stackArg s 1).toNat := by
    rw [ofNat_toNat']; rfl
  have hT0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := rfl
  have hsp16 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := hsp 2 (by decide)
  have hsp8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := hsp 1 (by decide)
  have hsp0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := hsp 0 (by decide)
  have darg (j : Nat) (hj : j + 8 ≤ 24) : (⟨s.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (workR (stackArg s 2)) := by
    refine daA.sub_left ?_
    show Region.Sub ⟨s.sp + BitVec.ofNat 64 j, 8⟩ ⟨s.sp + BitVec.ofNat 64 (8 * 0), 8 * 3⟩
    rw [show s.sp + BitVec.ofNat 64 (8 * 0) = s.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by omega)
  have h3 := ofNat_toNat' (s.gpr .x3)
  have h5 := ofNat_toNat' (s.gpr .x5)
  have h7 := ofNat_toNat' (s.gpr .x7)
  generalize hW : stackArg s 2 = W at *
  generalize hTg : stackArg s 0 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  generalize htlv : (stackArg s 1).toNat = tl at *
  have hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x7).isLt
  have htlt : tl < 2 ^ 64 := htlv ▸ (stackArg s 1).isLt
  refine WP.block_append (WP.mono (entryStash_ok (k := 16) (j := 8) (by decide) (by decide) hW16 hsp16 hsp8 hT8
      (darg 8 (by decide)) hCtx perm)
    fun s₂ ⟨he₂, x22₂, x23₂, x24₂, x26₂, x27₂, x28₂, sl₁, sl₂, sl₃, sl₄, sl₅, f₂, sv₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨s₃, run₃, x12₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := ldrSp_ok (t := .x12) (s := s₂) (k := 0) (by decide)
    (by rw [he₂.sp, f₂.readW (r := ⟨s.sp + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _)
      (keep_of_sub (entryR_work W) (darg 0 (by decide))) (by decide), hT0])
    (by rw [rd₂, wr₂, he₂.sp]; exact hsp0)
  refine WP.of_runBlock ⟨s₃, run₃, ?_, x12₃⟩
  rw [hA] at sl₁
  rw [← h5] at sl₂
  rw [hD] at sl₃
  rw [← h7] at sl₄
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  have g : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27, .x28], s₃.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have rd₄ : s₃.rd = s.rd := by rw [rd₃, rd₂]
  have wr₄ : s₃.wr = s.wr := by rw [wr₃, wr₂]
  exact ⟨L, he₂.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)) sp₃ rd₃ wr₃,
    by rw [g .x22 (by simp), x22₂, ← hRR, ofNat_toNat'], by rw [← hRR]; exact hR,
    by rw [g .x23 (by simp), x23₂, hNp], by rw [g .x24 (by simp), x24₂, ← h3], by rw [g .x26 (by simp), x26₂, ← h3],
    by rw [g .x27 (by simp), x27₂], by rw [g .x28 (by simp), x28₂], htlt,
    ⟨by rw [rd₄, wr₄]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩,
    ⟨by rw [rd₄, wr₄]; exact aR, hal ▸ (s.gpr .x5).isLt, wa, daW.sub_right sub16, daW⟩,
    ⟨⟨covers_left (by rw [wr₄]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩, by rw [wr₄]; exact dW, dcd⟩,
    by rw [rd₄, wr₄]; exact tR, dnW, daW, ddW, dcW, dtW, by rw [m₃, sl₁], by rw [m₃, sl₂],
    by rw [m₃, sl₃], by rw [m₃, sl₄], by rw [m₃, sl₅],
    by rw [m₃]; exact f₂.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩,
    by rw [m₃]; exact sv₂, rfl⟩

/-- What `openMain` reads, in a state after `tagIn`, as it was on entry. -/
theorem OpenIn.vals {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) :
    ciphOf t.mem Ctx R = ctxCiph s₀.mem Ctx R ∧ blockAt t.mem (Ctx + BitVec.ofNat 64 240) = ctxH s₀.mem Ctx ∧
      bytesAt t.mem Np nl = bytesAt s₀.mem Np nl ∧ bytesAt t.mem A al = bytesAt s₀.mem A al ∧
      bytesAt t.mem D n = bytesAt s₀.mem D n := by
  have hnlt := o.dat.ok.lt
  have hnl := o.non.lt
  have hal := o.aad.lt
  have kE : ∀ {X : Region}, X.Disjoint (workR W) → ∀ r ∈ [entryR W, ⟨W, 16⟩], X.Disjoint r :=
    fun hX => keep_of_sub (entry16_work W) hX
  exact ⟨ciph_frame o.fr (kE o.dcW) o.rounds, blockAt_frame o.fr (kE (o.dcW.sub_left (Lay.ctxSub (by decide)))),
    bytesAt_frame o.fr (kE o.dnW) (by omega), bytesAt_frame o.fr (kE o.daW) (by omega),
    bytesAt_frame o.fr (kE o.ddW) (by omega)⟩

/-- The received tag, after `tagIn`, as it was on entry. -/
theorem OpenIn.tag {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s) : bytesAt s.mem Tg tl = bytesAt s₀.mem Tg tl :=
  bytesAt_frame o.fr (keep_of_sub (entry16_work W) o.dtW) (by have := o.tlt; omega)

/-- `open`'s branch on the tag length. -/
theorem oite_ok (v : GcmImpl) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s₃ : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s₃) (x12₃ : s₃.gpr .x12 = Tg)
    (x9₃ : s₃.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk tl then 1 else 0)) :
    WP isa (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn (openMain v.callees))) s₃ fun s₄ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ SavedAt s₄.mem W s₀ ∧
      match Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
          (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl) with
      | some pt => (s₄.gpr .x0).setWidth 32 = 1 ∧ bytesAt s₄.mem D n = pt
      | none => (s₄.gpr .x0).setWidth 32 = 0 ∧ bytesAt s₄.mem D n = bytesAt s₀.mem D n := by
  have L := o.lay
  have ev : isa.eval (.zero .x .x9) s₃ = some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.ite _ ev (fun ht => ?_) (fun hf => ?_)
  · have hok : Spec.Gcm.tagLenOk tl = false := by
      revert ht; cases Spec.Gcm.tagLenOk tl <;> simp
    refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨o.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, o.sv, ?_⟩
    rw [Spec.Gcm.openResult, ite_eq_right (by simp [hok])]
    exact ⟨by simp [gpr_write], o.vals.2.2.2.2⟩
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := tagLenOk_le hok
    refine WP.seq (WP.mono (tagIn_ok o.env.x19 x12₃ o.x28 hle o.tagR o.env.perm.w
      (o.dtW.sub_right (Region.sub_prefix (by decide)))) fun s₃' ⟨rt, f, og, sp, rd, wr⟩ => ?_)
    have o' := o.tagIn f og sp rd wr
    have hT₃ : bytesAt s₃'.mem W tl = bytesAt s₀.mem Tg tl := by rw [rt, o.tag]
    refine WP.mono (openMain_ok v L o'.env o'.x22 o'.rounds o'.x23 o'.x24 o'.x26 o'.x27 o'.non o'.aad o'.dat
      o'.ddW o'.dcW o'.sA o'.sL o'.sD o'.sN o'.sT hok) fun s₄ hpost => ?_
    dsimp only at hpost
    obtain ⟨he₄, F₄, x0₄, d₄⟩ := hpost
    refine ⟨he₄, o'.sv.frame F₄ fun r hr => ?_, ?_⟩
    · rcases List.mem_cons.mp hr with h | hr
      · subst h; exact (o.ddW.sub_right (Lay.wSub (by decide))).symm
      rcases List.mem_append.mp hr with hr | hr
      · exact saved_omFrame L r hr
      · exact saved_crFrame L o'.dat r hr
    · obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o'.vals
      rw [hc₃, hH₃, hN₃, hA₃, hD₃, hT₃] at x0₄ d₄
      rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
      by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)
          (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
      · rw [ite_eq_left hc]
        simp only [hc, decide_true, ite_true] at x0₄ d₄
        exact ⟨by rw [x0₄]; rfl, d₄⟩
      · rw [ite_eq_right hc]
        simp only [hc, decide_false, Bool.false_eq_true, ite_false] at x0₄ d₄
        exact ⟨by rw [x0₄]; rfl, d₄⟩

theorem open_wp (v : GcmImpl) {s : State} (hs : openAArch64.pre s) :
    WP isa («open» v.callees) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  refine WP.seq (WP.mono (openEntry_ok hs) fun s₂ ⟨o₂, x12₂⟩ => ?_)
  refine WP.seq (WP.mono (tagLenOk_ok s₂ o₂.x28 o₂.tlt) fun s₃ ⟨x9₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (oite_ok v (o₂.of_regs r₃) (by rw [r₃.others _ (by decide), x12₂]) x9₃)
    fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  refine WP.mono (exit_ok he₄.x19 (he₄.sp.trans o₂.sp₀.symm) (covers_left he₄.perm.w) sv₄)
    fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  simp only [openAArch64, openRes]
  rw [hm, hx0]
  exact post₄

end VG.Proof.AesGcm.AArch64
