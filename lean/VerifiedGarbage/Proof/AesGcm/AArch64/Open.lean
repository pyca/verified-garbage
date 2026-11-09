module
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
public import VerifiedGarbage.Proof.AesGcm.AArch64.OneShot

import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. The entry also keeps
`tag_len` at `W + 248`; if `tagLenOk` does not allow it, `open` returns 0.
Otherwise `tagIn` copies the received tag to `W`, `front_ok` starts the
state and absorbs the additional data,
`decAbs` absorbs the ciphertext, `finBody 112` writes the tag at `W + 112`,
`cmpSeg` compares it with the received one without a branch, and the data is
decrypted only if they are equal (`open_wp`), which is the one secret the
code branches on, as the contract allows.

The same lemmas prove `vg_aes_gcm_open_to` (`openG c true`, `openTo_wp`): they
take `to` and the output `O` (`OpenInG`, `MidOG`, `openMainG_post`,
`openRestWithFl_wp`), and `OpenIn`, `MidO` are them in place (`O = D`). Out
of place the text at `src` is only read, the output is `dst` (`OutIn`, kept
at `W + dstO` by the entry, `openEntryTo_ok`), decrypted into by `cryptAlG`
if the tag is right and zeroed if not, or if the tag length is not allowed
(`wipeTo_ok`, `failTo_ok`).
-/

@[expose] public section

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
text absorbed, which it only reads (in place, or out of place: `to`). -/
theorem decAbs_ok (v : GcmImpl) {to : Bool} {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte}
    {H : Block} {s : State} (h : BodyInG to Ctx St W SP k R n P D a c H s) :
    WP isa (decAbs v.callees) s fun s₄ => Env Ctx St W SP s₄ ∧ Kept k s₄ ∧
      s₄.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ Frame (tFrame St W 16 ++ absFrame St W 16) s.mem s₄.mem ∧
      s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c ++ bytesAt s.mem D n))) := by
  have k26 : k .x26 = BitVec.ofNat 64 n := (h.kept .x26 (by decide)).symm.trans h.x26
  have k27 : k .x27 = BitVec.ofNat 64 P := (h.kept .x27 (by decide)).symm.trans h.x27
  have k28 : k .x28 = D := (h.kept .x28 (by decide)).symm.trans h.x28
  have hd := dataOk_of h.data
  have hlt := hd.lt
  refine WP.seq_assoc (WP.seq (WP.mono (pad_ok L v h) fun s₂ ⟨he₂, hk₂, hH₂, f₂, rd₂, wr₂, abs₂⟩ => ?_))
  refine WP.seq (WP.mono (textArgs_ok hk₂ k26 k27 k28 h.hP) fun s₃ ⟨x25₃, x23₃, x24₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have hD₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [m₃]; exact bytesAt_frame f₂ (dataOk_tFrame hd) (by omega_arith)
  have hd₃ : DataOk St W s₃ D n := hd.of_eq (by rw [r₃.rd, rd₂]) (by rw [r₃.wr, wr₂])
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
      ⟨he₃, hk₃, x23₃, x24₃, x25₃, by rw [xf_len hn0, h.hc], hd₃, by rw [m₃, hH₂]⟩
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
    fun d k h₁ h₂ => Offset.sub _ h₁ (by omega_arith)
  have st : ∀ d k, d + k ≤ 80 →
      Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 16, 2544⟩ :=
    fun d k h => Offset.sub_base _ (by omega_arith)
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
    (.seq (finBody c uO) (.seq (.block [.ldr .x .x28 .x19 tlO]) (.seq cmp
      (.block [imm .x27 1, .sub .x .x27 .x27 .x10]))))))))

/-- The rest: the branch on the tag, and the result. -/
def omB (c : Callees) : Prog isa :=
  .seq (.ite (.zero .x .x27) (.block []) (oneCrypt c)) (.block [mov .x0 .x27])

/-- `omB` with the counter mode `cr` (`cryptAl`, or `Tail.cryptAlT`) after
`oneCrypt`'s loads. -/
def omBWith (cr : Prog isa) : Prog isa :=
  .seq (.ite (.zero .x .x27) (.block [])
    (.seq (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0]) cr)) (.block [mov .x0 .x27])

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

/-- Out of place: the output, `n` bytes at `O`, writable, apart from the
text `D`, and kept at `W + dstO`. -/
structure OutIn (Ctx W D O : Addr) (n : Nat) (s : State) : Prop where
  dw : DataW Ctx (W + BitVec.ofNat 64 16) W s O n
  dd : (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩
  sO : s.mem.readW (W + BitVec.ofNat 64 320) 64 = O

theorem OutIn.of_eq {Ctx W D O : Addr} {n : Nat} {s s' : State} (h : OutIn Ctx W D O n s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hO : s'.mem.readW (W + BitVec.ofNat 64 320) 64 = s.mem.readW (W + BitVec.ofNat 64 320) 64) :
    OutIn Ctx W D O n s' :=
  ⟨h.dw.of_eq hrd hwr, h.dd, hO.trans h.sO⟩

/-- The output: out of place `OutIn`, in place the text itself. -/
theorem outG_of_eq {to : Bool} {Ctx W D O : Addr} {n : Nat} {s s' : State}
    (h : cond to (OutIn Ctx W D O n s) (O = D)) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hO : s'.mem.readW (W + BitVec.ofNat 64 320) 64 = s.mem.readW (W + BitVec.ofNat 64 320) 64) :
    cond to (OutIn Ctx W D O n s') (O = D) := by
  cases to
  · exact h
  · exact OutIn.of_eq h hrd hwr hO

/-- The output is writable, in place or not. -/
theorem outG_dataW {to : Bool} {Ctx W D O : Addr} {n : Nat} {s : State}
    (h : cond to (OutIn Ctx W D O n s) (O = D))
    (hd : cond to (DataOk (W + BitVec.ofNat 64 16) W s D n) (DataW Ctx (W + BitVec.ofNat 64 16) W s D n)) :
    DataW Ctx (W + BitVec.ofNat 64 16) W s O n := by
  cases to
  · have e : O = D := h
    subst e
    exact hd
  · exact OutIn.dw h

/-- What is known at the branch of `openMain` (`openMainG to`), memory having
changed since `s` only in `fr`, with the output at `O`. -/
structure MidOG (to : Bool) (fr : List Region) (Ctx W SP D O Np A : Addr) (R nl al n tl : Nat)
    (s s₇ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇
  frame : Frame fr s.mem s₇.mem
  x22 : s₇.gpr .x22 = BitVec.ofNat 64 R
  x27 : s₇.gpr .x27 = BitVec.ofNat 64 (if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
    (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
    (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then 1 else 0)
  data : cond to (DataOk (W + BitVec.ofNat 64 16) W s₇ D n) (DataW Ctx (W + BitVec.ofNat 64 16) W s₇ D n)
  sD : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  cb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))
  out : cond to (OutIn Ctx W D O n s₇) (O = D)

/-- `MidOG` in place. -/
abbrev MidO (fr : List Region) (Ctx W SP D Np A : Addr) (R nl al n tl : Nat) (s s₇ : State) : Prop :=
  MidOG false fr Ctx W SP D D Np A R nl al n tl s s₇

/-- What `openMain` writes before the branch is below `W + 320` or in the
keystream's space. -/
theorem omFrame_lo (W : Addr) : ∀ r ∈ omFrame W,
    Region.Sub r ⟨W, 320⟩ ∨ Region.Sub r ⟨W + BitVec.ofNat 64 512, 2048⟩ := by
  have lo : ∀ d k, d + k ≤ 320 → Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ ⟨W, 320⟩ :=
    fun d k h => Offset.sub_base _ h
  have st : ∀ d k, d + k ≤ 80 →
      Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ ⟨W, 320⟩ :=
    fun d k h => by rw [add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
  have hi : ∀ d k, 512 ≤ d → d + k ≤ 2560 →
      Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 512, 2048⟩ :=
    fun d k h₁ h₂ => Offset.sub _ h₁ (by omega_arith)
  intro r hr
  simp only [omFrame, frontFrame, j0Frame, absFrame, tFrame, finFrame, tagFrame, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  all_goals first
    | with_reducible exact .inl (lo _ _ (by decide))
    | with_reducible exact .inl (st _ _ (by decide))
    | with_reducible exact .inr (hi _ _ (by decide) (by decide))

/-- Where `open_to` keeps `dst` is outside what `openMain` writes before the
branch. -/
theorem dst_omFrame (W : Addr) : ∀ r ∈ omFrame W, (⟨W + BitVec.ofNat 64 320, 8⟩ : Region).Disjoint r := by
  intro r hr
  rcases omFrame_lo W r hr with h | h
  · exact (Offset.disjoint_base W (d := 320) (n := 8) (k := 320) (by decide) (by decide)).sub_right h
  · exact (Offset.disjoint W (d := 320) (n := 8) (e := 512) (k := 2048) (.inl (by decide)) (by decide)
      (by decide)).sub_right h

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

/-- `openMain` (`openMainG to`) up to the branch on the tag, which only reads
the text, with the output at `O`. -/
theorem openMainAG_ok (v : GcmImpl) (to : Bool) {Ctx W SP D O Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h23 : s.gpr .x23 = Np) (h24 : s.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk (W + BitVec.ofNat 64 16) W s Np nl) (haad : DataOk (W + BitVec.ofNat 64 16) W s A al)
    (hdat : cond to (DataOk (W + BitVec.ofNat 64 16) W s D n) (DataW Ctx (W + BitVec.ofNat 64 16) W s D n))
    (hout : cond to (OutIn Ctx W D O n s) (O = D)) (ddW : (⟨D, n⟩ : Region).Disjoint (workR W))
    (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (omA v.callees) s (MidOG to (omFrame W) Ctx W SP D O Np A R nl al n tl s) := by
  unfold omA
  have hle := tagLenOk_le hok
  have hnlt := (dataOk_of hdat).lt
  have dD : ∀ r ∈ omFrame W, (⟨D, n⟩ : Region).Disjoint r := keep_of_sub (omFrame_work W) ddW
  have dC : ∀ r ∈ omFrame W, (⟨Ctx, 256⟩ : Region).Disjoint r := keep_of_sub (omFrame_work W) dcW
  have sl := slots_omFrame L ddW
  have mF : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ omFrame W) → ∀ {m m' : Mem}, Frame rs m m' →
      Frame (omFrame W) m m' := fun hs _ _ hf => hf.mono hs
  refine front_ok L v he (fun _ _ => rfl : Kept s.gpr s) h23 h24 h26 h27 hnon haad rfl sA sL sD sN
    fun s₁ h₁ => ?_
  have F₁ : Frame (omFrame W) s.mem s₁.mem :=
    mF (fun r hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))) h₁.frame
  have hdat₁ := data_of_eq hdat h₁.rd h₁.wr
  have hB : BodyInG to Ctx (W + BitVec.ofNat 64 16) W SP s₁.gpr R n 0 D (bytesAt s.mem A al) []
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
  have hC₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame F₁ dD (by omega_arith)
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
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L he₅ (fun _ _ => rfl : Kept s₅.gpr s₅) x28₅ hle))
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
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega_arith)
    have := (Offset.disjoint W (d := 0) (n := tl) (e := 16) (k := 2544) (.inl (by omega_arith)) (by omega_arith)
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
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega_arith)
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
  have rd₇ : s₇.rd = s.rd := by rw [r₇.rd, rd₆, r₅.rd, rd₄, r₃.rd, rd₂, h₁.rd]
  have wr₇ : s₇.wr = s.wr := by rw [r₇.wr, wr₆, r₅.wr, wr₄, r₃.wr, wr₂, h₁.wr]
  exact ⟨he₇, F₇, x22₇, by rw [x27₇, hBeq], data_of_eq hdat rd₇ wr₇,
    by rw [slot F₇ 232 (by decide) (by decide), sD], by rw [slot F₇ 240 (by decide) (by decide), sN], hcb,
    outG_of_eq hout rd₇ wr₇ (F₇.readW (r := ⟨W + BitVec.ofNat 64 320, 8⟩) (Region.contains_self _ _)
      (dst_omFrame W) (by decide))⟩

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
    WP isa (omA v.callees) s (MidO (omFrame W) Ctx W SP D Np A R nl al n tl s) :=
  openMainAG_ok v false L he h22 hR h23 h24 h26 h27 hnon haad hdat rfl ddW dcW sA sL sD sN sT hok

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
    {fr : List Region} {s s₇ s₈ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidO fr Ctx W SP D Np A R nl al n tl s s₇)
    (h : s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧
        s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x23, .x24, .x25] s₇ s₈) :
    CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D n s₈ :=
  ⟨mo.env.of_regs h.2.2.2, fun _ _ => rfl, by rw [h.2.2.2.others _ (by decide), mo.x22], hR, h.1, h.2.1, h.2.2.1,
    mo.data.of_eq h.2.2.2.rd h.2.2.2.wr, rfl⟩

/-- `KeptTo` and `Kept` both keep `x27`. -/
theorem keptG_x27 {to : Bool} {k : Reg → BitVec 64} {s : State} (h : cond to (KeptTo k s) (Kept k s)) :
    s.gpr .x27 = k .x27 := by
  cases to
  · exact (h : Kept k s) .x27 (by decide)
  · exact (h : KeptTo k s) .x27 (by decide)

/-- `wipeG true`: the `n` bytes at `O` (kept at `W + dstO`, with `n` at
`W + lenO`) zeroed. -/
theorem wipeTo_ok {Ctx W SP O : Addr} {n : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (sO : s.mem.readW (W + BitVec.ofNat 64 320) 64 = O)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (hw : DataW Ctx (W + BitVec.ofNat 64 16) W s O n) :
    WP isa (wipeG true) s fun s' => bytesAt s'.mem O n = List.replicate n 0 ∧ Frame [⟨O, n⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have q₁ := he.perm.wR (show 320 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 240 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, x9₁, x10₁, x11₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.ldr .x .x9 .x19 dstO, .ldr .x .x10 .x19 lenO, imm .x11 0] s = some s₁ ∧ s₁.gpr .x9 = O ∧
      s₁.gpr .x10 = BitVec.ofNat 64 n ∧ s₁.gpr .x11 = 0 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by arun [he.x19, q₁, q₂, dstO], ?_⟩
    refine ⟨?_, ?_, by simp [gpr_write], fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
      rw [show s.mem.read (W + 320#64) 8 = s.mem.readW (W + BitVec.ofNat 64 320) 64 from rfl, sO]; rfl
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
      rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (wipeLoop_wp s₁ hw.ok.lt x9₁ x10₁ x11₁ (by rw [wr₁]; exact hw.wr) hw.ok.wrap)
    fun s' ⟨pz, f, g, sp, rd, wr, _⟩ => ⟨bytesAt_zeros pz, by rw [← m₁]; exact f,
      fun r h₁ h₂ h₃ => (g r h₁ h₂).trans (g₁ r h₁ h₂ h₃), sp.trans sp₁, rd.trans rd₁, wr.trans wr₁⟩

/-- The loads before `cryptAlG` in `oneCryptG`. -/
theorem ocLdrG_ok (to : Bool) {Ctx W SP D O : Addr} {n : Nat} {s₇ : State}
    (he₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇)
    (sD₇ : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN₇ : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sO₇ : cond to (s₇.mem.readW (W + BitVec.ofNat 64 320) 64 = O) True) :
    WP isa (.block (([.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0] : List Instr) ++
      cond to ([.ldr .x .x26 .x19 dstO] : List Instr) [])) s₇ fun s₈ =>
      s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧ s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧
        cond to (s₈.gpr .x26 = O) (s₈.gpr .x26 = s₇.gpr .x26) ∧ Regs [.x23, .x24, .x25, .x26] s₇ s₈ := by
  have q₁ := he₇.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have q₂ := he₇.perm.wR (show 240 + 8 ≤ 2560 by decide)
  have q₃ := he₇.perm.wR (show 320 + 8 ≤ 2560 by decide)
  have l₁ : s₇.mem.read (W + 232#64) 8 = D := by
    rw [show s₇.mem.read (W + 232#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, sD₇]
  have l₂ : s₇.mem.read (W + 240#64) 8 = BitVec.ofNat 64 n := by
    rw [show s₇.mem.read (W + 240#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN₇]
  cases to
  · refine WP.run ⟨_, by arun [he₇.x19, q₁, q₂, Bool.cond_false, List.append_nil], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, ?_, by simp [gpr_write], by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [l₁]; rfl
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [l₂]; rfl
  · have l₃ : s₇.mem.read (W + 320#64) 8 = O := by
      rw [show s₇.mem.read (W + 320#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 320) 64 from rfl]; exact sO₇
    refine WP.run ⟨_, by arun [he₇.x19, q₁, q₂, q₃, dstO, Bool.cond_true], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, ?_, by simp [gpr_write], ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [l₁]; rfl
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [l₂]; rfl
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [l₃]; rfl

/-- What `cryptAlG` needs in `oneCryptG`, after its loads. -/
theorem ocInG (to : Bool) {Ctx W SP D O Np A : Addr} {R nl al n tl : Nat}
    {fr : List Region} {s s₇ s₈ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidOG to fr Ctx W SP D O Np A R nl al n tl s s₇)
    (h : s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 n ∧ s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧
      cond to (s₈.gpr .x26 = O) (s₈.gpr .x26 = s₇.gpr .x26) ∧ Regs [.x23, .x24, .x25, .x26] s₇ s₈) :
    CrInG to Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D O n s₈ := by
  obtain ⟨h23, h24, h25, h26, r⟩ := h
  refine ⟨mo.env.of_regs r, ?_, by rw [r.others _ (by decide), mo.x22], hR, h23, h24, h25,
    data_of_eq mo.data r.rd r.wr, ?_⟩
  · cases to
    · exact fun _ _ => rfl
    · exact fun _ _ => rfl
  · cases to
    · exact mo.out
    · have o : OutIn Ctx W D O n s₇ := mo.out
      exact OutAt.mkTo (o.dw.of_eq r.rd r.wr) o.dd (by rw [h26]; exact (BitVec.add_zero O).symm)

/-- The branch on the tag (`openMainG to`'s), with the counter mode `cr`
(`cryptAlG`, or `Tail.cryptAlT` in place) after `oneCryptG`'s loads: out of
place, the output zeroed if the tag is wrong. -/
theorem omIteWithG_ok (to : Bool) (cr : Prog isa) {Ctx W SP D O Np A : Addr} {R nl al n tl : Nat}
    {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidOG to fr Ctx W SP D O Np A R nl al n tl s s₇) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hcr : ∀ {s₈ : State}, CrInG to Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D O n s₈ →
      (to = false → s₈.gpr .x26 = s₇.gpr .x26) → s₈.wr = s₇.wr → ∀ icb, WP isa cr s₈
        (CrOutG to Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R icb 0 D O n s₈.mem)) :
    WP isa (.ite (.zero .x .x27) (wipeG to)
      (.seq (.block (([.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0] : List Instr) ++
        cond to ([.ldr .x .x26 .x19 dstO] : List Instr) [])) cr)) s₇ fun s₈ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) W O n) s₇.mem s₈.mem ∧
      bytesAt s₈.mem O n = if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
          (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
          (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then
        gctr (ciphOf s.mem Ctx R) (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
          (bytesAt s.mem Np nl))) (bytesAt s.mem D n) else cond to (List.replicate n 0) (bytesAt s.mem D n) := by
  have hnlt := (dataOk_of mo.data).lt
  have F₇ := mo.frame
  have hD₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega_arith)
  have x27₇ := mo.x27
  generalize decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R) (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
    (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) = B at x27₇ ⊢
  refine WP.ite (decide ((if B then 1 else 0) = 0)) (eval_zero x27₇ (by cases B <;> decide)) (fun ht => ?_)
    (fun hf => ?_)
  · have hB : B = false := by revert ht; cases B <;> simp
    subst hB
    cases to
    · have e : O = D := mo.out
      subst e
      exact WP.block_nil ⟨mo.env, rfl, Frame.refl _ _, by rw [hD₇]; rfl⟩
    · have o : OutIn Ctx W D O n s₇ := mo.out
      refine WP.mono (wipeTo_ok mo.env o.sO mo.sN o.dw) fun s₈ ⟨z, f, g, sp, rd, wr⟩ =>
        ⟨mo.env.keep (fun r hr => g r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide) (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide) (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr,
          g _ (by decide) (by decide) (by decide),
          f.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩,
          by rw [z]; rfl⟩
  · have hB : B = true := by revert hf; cases B <;> simp
    subst hB
    refine WP.seq (WP.mono (ocLdrG_ok to (O := O) mo.env mo.sD mo.sN (by
      cases to
      · trivial
      · exact OutIn.sO mo.out)) fun s₈ h₈ => ?_)
    have r₈ := h₈.2.2.2.2
    have F₈ : Frame fr s.mem s₈.mem := by rw [r₈.mem]; exact F₇
    have hcb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)) := by
      rw [r₈.mem, mo.cb]
    have hc₈ : ciphOf s₈.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame F₈ dC hR
    have hD₈ : bytesAt s₈.mem D n = bytesAt s.mem D n := bytesAt_frame F₈ dD (by omega_arith)
    refine WP.mono (hcr (ocInG to hR mo h₈) (fun hto => by
        subst hto; exact h₈.2.2.2.1) r₈.wr
      (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))))
      fun s₉ h₉ => ⟨h₉.env, ?_, by rw [← r₈.mem]; exact h₉.frame, ?_⟩
    · rw [keptG_x27 h₉.kept, r₈.others _ (by decide)]
    · rw [h₉.out (Proof.Gcm.ctr_zero _ _ _ _ hcb₈), hc₈, hD₈, Proof.Gcm.gctr_eq]
      rfl

theorem omIteWith_ok (cr : Prog isa) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidO fr Ctx W SP D Np A R nl al n tl s s₇) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hcr : ∀ {s₈ : State}, CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D n s₈ →
      s₈.gpr .x26 = s₇.gpr .x26 → s₈.wr = s₇.wr → ∀ icb, WP isa cr s₈
        (CrOut Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R icb 0 D n s₈.mem)) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0]) cr)) s₇ fun s₈ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) W D n) s₇.mem s₈.mem ∧
      bytesAt s₈.mem D n = if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
          (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
          (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then
        gctr (ciphOf s.mem Ctx R) (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
          (bytesAt s.mem Np nl))) (bytesAt s.mem D n) else bytesAt s.mem D n := by
  have := omIteWithG_ok false cr hR mo dD dC fun h e26 hwr icb => hcr h (e26 rfl) hwr icb
  simpa only [wipeG, Bool.cond_false, List.append_nil] using this

theorem omIte_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidO fr Ctx W SP D Np A R nl al n tl s s₇) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r) :
    WP isa (.ite (.zero .x .x27) (.block []) (oneCrypt v.callees)) s₇ fun s₈ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) W D n) s₇.mem s₈.mem ∧
      bytesAt s₈.mem D n = if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
          (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
          (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then
        gctr (ciphOf s.mem Ctx R) (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
          (bytesAt s.mem Np nl))) (bytesAt s.mem D n) else bytesAt s.mem D n :=
  omIteWith_ok (cryptAl v.callees) hR mo dD dC fun h _ _ icb => cryptAl_ok L v (icb := icb) h rfl

/-- `omBWith`, in place or out of place (`openMainG to`'s branch on the tag,
with `cr` after `oneCryptG`'s loads). -/
def omBWithG (to : Bool) (cr : Prog isa) : Prog isa :=
  .seq (.ite (.zero .x .x27) (wipeG to)
    (.seq (.block ([.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0] ++
      cond to [.ldr .x .x26 .x19 dstO] [])) cr)) (.block [mov .x0 .x27])

/-- `omBWithG`, with what it writes from the branch on, for a frame `fr`
apart from the text and the key context: the output at `O`. -/
theorem omBXWithG_ok (to : Bool) (cr : Prog isa) {Ctx W SP D O Np A : Addr} {R nl al n tl : Nat}
    {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidOG to fr Ctx W SP D O Np A R nl al n tl s s₇) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hcr : ∀ {s₈ : State}, CrInG to Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D O n s₈ →
      (to = false → s₈.gpr .x26 = s₇.gpr .x26) → s₈.wr = s₇.wr → ∀ icb, WP isa cr s₈
        (CrOutG to Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R icb 0 D O n s₈.mem)) :
    WP isa (omBWithG to cr) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
        Frame (⟨O, n⟩ :: fr ++ crFrame (W + BitVec.ofNat 64 16) W O n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem O n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else cond to (List.replicate n 0) (bytesAt s.mem D n)) ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) W O n) s₇.mem s'.mem := by
  unfold omBWithG
  refine WP.seq (WP.mono (omIteWithG_ok to cr hR mo dD dC hcr) fun s₈ ⟨he₈, x27₈, f₈, d₈⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨⟨he₈.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, ?_, by simp [gpr_write, x27₈, mo.x27], d₈⟩, f₈⟩
  exact (mo.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ (List.mem_append_left _ hr), fun _ h => h⟩).trans
    (f₈.sub fun r hr => ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), fun _ h => h⟩)

/-- `omB`, with what it writes from the branch on: `omB_ok`, for a frame
`fr` apart from the text and the key context. -/
theorem omBXWith_ok (cr : Prog isa) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidO fr Ctx W SP D Np A R nl al n tl s s₇) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hcr : ∀ {s₈ : State}, CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D n s₈ →
      s₈.gpr .x26 = s₇.gpr .x26 → s₈.wr = s₇.wr → ∀ icb, WP isa cr s₈
        (CrOut Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R icb 0 D n s₈.mem)) :
    WP isa (omBWith cr) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: fr ++ crFrame (W + BitVec.ofNat 64 16) W D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n) ∧ Frame (crFrame (W + BitVec.ofNat 64 16) W D n) s₇.mem s'.mem := by
  have := omBXWithG_ok false cr hR mo dD dC fun h e26 hwr icb => hcr h (e26 rfl) hwr icb
  unfold omBWith
  simpa only [omBWithG, wipeG, Bool.cond_false, List.append_nil] using this

theorem omBX_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidO fr Ctx W SP D Np A R nl al n tl s s₇) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r) :
    WP isa (omB v.callees) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: fr ++ crFrame (W + BitVec.ofNat 64 16) W D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n) ∧ Frame (crFrame (W + BitVec.ofNat 64 16) W D n) s₇.mem s'.mem :=
  omBXWith_ok (cryptAl v.callees) hR mo dD dC fun h _ _ icb => cryptAl_ok L v (icb := icb) h rfl

theorem omB_ok (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (ddW : (⟨D, n⟩ : Region).Disjoint (workR W)) (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (mo : MidO fr Ctx W SP D Np A R nl al n tl s s₇) (hfr : ∀ r ∈ fr, Region.Sub r (workR W)) :
    WP isa (omB v.callees) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: fr ++ crFrame (W + BitVec.ofNat 64 16) W D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n :=
  WP.mono (omBX_ok v L hR mo (keep_of_sub hfr ddW) (keep_of_sub hfr dcW)) fun _ q => q.1

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
    sA sL sD sN sT hok) fun _ mo => omB_ok v L hR ddW dcW mo (omFrame_work W)))

/-- `openMainG to`'s branch on the tag and its result. -/
def omBG (c : Callees) (to : Bool) : Prog isa :=
  .seq (.ite (.zero .x .x27) (wipeG to) (oneCryptG c to)) (.block [mov .x0 .x27])

/-- `openMainG to` is `omA` then `omBG`. -/
theorem openMainG_split (c : Callees) (to : Bool) : PEq (.seq (omA c) (omBG c to)) (openMainG c to) := by
  unfold omA omBG openMainG
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  exact PEq.assoc _ _ _

theorem omBG_ok (v : GcmImpl) (to : Bool) {Ctx W SP D O Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (ddW : (⟨D, n⟩ : Region).Disjoint (workR W)) (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (mo : MidOG to fr Ctx W SP D O Np A R nl al n tl s s₇) (hfr : ∀ r ∈ fr, Region.Sub r (workR W)) :
    WP isa (omBG v.callees to) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
        Frame (⟨O, n⟩ :: fr ++ crFrame (W + BitVec.ofNat 64 16) W O n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem O n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else cond to (List.replicate n 0) (bytesAt s.mem D n) :=
  WP.mono (omBXWithG_ok to (cryptAlG v.callees to) hR mo (keep_of_sub hfr ddW) (keep_of_sub hfr dcW)
    fun h _ _ icb => cryptAlG_ok L v to (icb := icb) h rfl) fun _ q => q.1

/-- `openMainG to`: in place (`openMain`) or out of place, with the output at
`O`. -/
theorem openMainG_ok (v : GcmImpl) (to : Bool) {Ctx W SP D O Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h23 : s.gpr .x23 = Np) (h24 : s.gpr .x24 = BitVec.ofNat 64 nl)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 nl) (h27 : s.gpr .x27 = 0)
    (hnon : DataOk (W + BitVec.ofNat 64 16) W s Np nl) (haad : DataOk (W + BitVec.ofNat 64 16) W s A al)
    (hdat : cond to (DataOk (W + BitVec.ofNat 64 16) W s D n) (DataW Ctx (W + BitVec.ofNat 64 16) W s D n))
    (hout : cond to (OutIn Ctx W D O n s) (O = D)) (ddW : (⟨D, n⟩ : Region).Disjoint (workR W))
    (dcW : (⟨Ctx, 256⟩ : Region).Disjoint (workR W))
    (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (openMainG v.callees to) s fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
        Frame (⟨O, n⟩ :: omFrame W ++ crFrame (W + BitVec.ofNat 64 16) W O n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem O n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else cond to (List.replicate n 0) (bytesAt s.mem D n) :=
  (openMainG_split v.callees to).symm.wp (WP.seq (c₁ := omA v.callees) (WP.mono (openMainAG_ok v to L he h22 hR
    h23 h24 h26 h27 hnon haad hdat hout ddW dcW sA sL sD sN sT hok) fun _ mo =>
      omBG_ok v to L hR ddW dcW mo (omFrame_work W)))

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr zeros)

/-- What the entry and `tagIn` write: the slots and the received tag, and out
of place where `dst` is kept. -/
abbrev entryFr (to : Bool) (W : Addr) : List Region :=
  cond to [entryR W, ⟨W + BitVec.ofNat 64 320, 8⟩, ⟨W, 16⟩] [entryR W, ⟨W, 16⟩]

/-- What is known after the entry of `open` (or of `open_to`: `to`), from the
state `s₀` it was called in, with the received tag the `tl` bytes at `Tg`,
the text at `D`, which out of place is only read, and the output at `O`. -/
structure OpenInG (to : Bool) (Ctx W SP Np A D O Tg : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
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
  dat : cond to (DataOk (W + BitVec.ofNat 64 16) W s D n) (DataW Ctx (W + BitVec.ofNat 64 16) W s D n)
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
  fr : Frame (entryFr to W) s₀.mem s.mem
  sv : SavedAt s.mem W s₀
  sp₀ : s₀.sp = SP
  rd₀ : s.rd = s₀.rd
  wr₀ : s.wr = s₀.wr
  out : cond to (OutIn Ctx W D O n s) (O = D)

/-- What is known after `open`'s entry (`OpenInG` in place). -/
abbrev OpenIn (Ctx W SP Np A D Tg : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop :=
  OpenInG false Ctx W SP Np A D D Tg R nl al n tl s₀ s

theorem OpenInG.of_regs {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {s₀ s s' : State}
    {rs : List Reg} (o : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s) (r : Regs rs s s')
    (hd : ∀ q ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27, .x28], q ∉ rs := by decide) :
    OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s' :=
  ⟨o.lay, o.env.of_regs r fun q hq => hd q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp),
    by rw [r.others _ (hd _ (by simp)), o.x22], o.rounds, by rw [r.others _ (hd _ (by simp)), o.x23],
    by rw [r.others _ (hd _ (by simp)), o.x24], by rw [r.others _ (hd _ (by simp)), o.x26],
    by rw [r.others _ (hd _ (by simp)), o.x27], by rw [r.others _ (hd _ (by simp)), o.x28], o.tlt,
    o.non.of_eq r.rd r.wr, o.aad.of_eq r.rd r.wr, data_of_eq o.dat r.rd r.wr, by rw [r.rd, r.wr]; exact o.tagR,
    o.dnW, o.daW, o.ddW, o.dcW, o.dtW,
    by rw [r.mem, o.sA], by rw [r.mem, o.sL], by rw [r.mem, o.sD], by rw [r.mem, o.sN], by rw [r.mem, o.sT],
    by rw [r.mem]; exact o.fr, by rw [r.mem]; exact o.sv, o.sp₀, r.rd.trans o.rd₀, r.wr.trans o.wr₀,
    outG_of_eq o.out r.rd r.wr (by rw [r.mem])⟩

/-- What the entry and `tagIn` write is in `work`. -/
theorem entry16_work (W : Addr) : ∀ r ∈ [entryR W, ⟨W, 16⟩], Region.Sub r (workR W) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Lay.wSub (by decide)
  · exact Region.sub_prefix (by decide)

theorem entryFr_work (to : Bool) (W : Addr) : ∀ r ∈ entryFr to W, Region.Sub r (workR W) := by
  cases to
  · exact entry16_work W
  · intro r hr
    simp only [entryFr, Bool.cond_true, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Lay.wSub (by decide)
    · exact Lay.wSub (by decide)
    · exact Region.sub_prefix (by decide)

theorem mem_entryFr16 (to : Bool) (W : Addr) : (⟨W, 16⟩ : Region) ∈ entryFr to W := by
  cases to <;> simp [entryFr]

/-- The output is writable, in place or not. -/
theorem OpenInG.outW {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {s₀ s : State}
    (o : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s) : DataW Ctx (W + BitVec.ofNat 64 16) W s O n :=
  outG_dataW o.out o.dat

/-- `OpenInG` after `tagIn`. -/
theorem OpenInG.tagIn {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {s₀ s s' : State}
    (o : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s) (f : Frame [⟨W, 16⟩] s.mem s'.mem)
    (og : Others loopRegs s s') (sp : s'.sp = s.sp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s' := by
  have L := o.lay
  have sl : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    slot_kept f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 216) (n := 40) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)) h₁ h₂
  have sO : s'.mem.readW (W + BitVec.ofNat 64 320) 64 = s.mem.readW (W + BitVec.ofNat 64 320) 64 :=
    f.readW (r := ⟨W + BitVec.ofNat 64 320, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base W (d := 320) (n := 8) (k := 16) (by decide) (by decide)) (by decide)
  exact ⟨L, o.env.keep (fun r hr => og r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr,
    by rw [og _ (by decide), o.x22], o.rounds, by rw [og _ (by decide), o.x23],
    by rw [og _ (by decide), o.x24], by rw [og _ (by decide), o.x26],
    by rw [og _ (by decide), o.x27], by rw [og _ (by decide), o.x28], o.tlt,
    o.non.of_eq rd wr, o.aad.of_eq rd wr, data_of_eq o.dat rd wr, by rw [rd, wr]; exact o.tagR,
    o.dnW, o.daW, o.ddW, o.dcW, o.dtW,
    by rw [sl 216 (by decide) (by decide), o.sA], by rw [sl 224 (by decide) (by decide), o.sL],
    by rw [sl 232 (by decide) (by decide), o.sD], by rw [sl 240 (by decide) (by decide), o.sN],
    by rw [sl 248 (by decide) (by decide), o.sT],
    o.fr.trans (f.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact mem_entryFr16 to W,
      fun _ h => h⟩),
    o.sv.frame f (saved_tag16 L), o.sp₀, rd.trans o.rd₀, wr.trans o.wr₀, outG_of_eq o.out rd wr sO⟩

/-- `openPre`'s common arguments. -/
theorem openCore {w : Nat} {extra extraW : List Region} {s : State} (hs : openPreXW w extra s extraW) :
    oneCore (w + 1) w s := by
  simp only [openPreXW] at hs
  obtain ⟨hrd, hwr, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, -, dwa, wc, wn, wa, wd, ww, wsp, hR⟩ := hs
  exact ⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hwr]; simp,
    by rw [hwr]; simp, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, wc, wn, wa, wd, ww, wsp, hR⟩

/-- What `openPre` gives. -/
theorem openLay {w : Nat} {extra extraW : List Region} {s : State} (hs : openPreXW w extra s extraW) :
    OneLay s (w + 1) w ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint (workR (stackArg s w)) := by
  have hs' := hs
  simp only [openPreXW] at hs'
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, dtw, -⟩ := hs'
  exact ⟨oneLay (openCore hs), covers_mem (by rw [hrd, hwr]; simp), dtw⟩

/-- `open`'s first block: the entry, the tag length and the tag, with `work`
the stack argument `w`. -/
theorem openEntryW_ok {w : Nat} (hw : 2 ≤ w ∧ w ≤ 5) {extra extraW : List Region} {s : State}
    (hs : openPreXW w extra s extraW) :
    WP isa (.block (oneEntry (8 * w) ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr))) s fun s' =>
      OpenIn (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s s' ∧
      s'.gpr .x12 = stackArg s 0 := by
  obtain ⟨ol, tR, dtW⟩ := openLay hs
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  have hW16 : s.mem.readW (s.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg s w := rfl
  have hT8 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (stackArg s 1).toNat := by
    rw [ofNat_toNat']; rfl
  have hT0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := rfl
  have hsp16 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * w)) 8 := hsp w (by omega_arith)
  have hsp8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := hsp 1 (by omega_arith)
  have hsp0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := hsp 0 (by omega_arith)
  have darg (j : Nat) (hj : j + 8 ≤ 8 * (w + 1)) :
      (⟨s.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (workR (stackArg s w)) := by
    refine daA.sub_left ?_
    show Region.Sub ⟨s.sp + BitVec.ofNat 64 j, 8⟩ ⟨s.sp + BitVec.ofNat 64 (8 * 0), 8 * (w + 1)⟩
    rw [show s.sp + BitVec.ofNat 64 (8 * 0) = s.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by omega_arith)
  have h3 := ofNat_toNat' (s.gpr .x3)
  have h5 := ofNat_toNat' (s.gpr .x5)
  have h7 := ofNat_toNat' (s.gpr .x7)
  generalize hW : stackArg s w = W at *
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
  refine WP.block_append (WP.mono (entryStash_ok (k := 8 * w) (j := 8) (by omega_arith) (by decide) hW16 hsp16 hsp8 hT8
      (darg 8 (by omega_arith)) hCtx perm)
    fun s₂ ⟨he₂, x22₂, x23₂, x24₂, x26₂, x27₂, x28₂, sl₁, sl₂, sl₃, sl₄, sl₅, f₂, sv₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨s₃, run₃, x12₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := ldrSp_ok (t := .x12) (s := s₂) (k := 0) (by decide)
    (by rw [he₂.sp, f₂.readW (r := ⟨s.sp + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _)
      (keep_of_sub (entryR_work W) (darg 0 (by omega_arith))) (by decide), hT0])
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
    by rw [m₃]; exact f₂.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp [entryFr],
      fun _ h => h⟩,
    by rw [m₃]; exact sv₂, rfl, rd₄, wr₄, rfl⟩

/-- `openEntryW_ok` for `vg_aes_gcm_open` (`w = 2`) and its instance with the
powers (`w = 3`). -/
theorem openEntry_ok {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region} {s : State}
    (hs : openPreXW w extra s extraW) :
    WP isa (.block (oneEntry (8 * w) ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr))) s fun s' =>
      OpenIn (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s s' ∧
      s'.gpr .x12 = stackArg s 0 :=
  openEntryW_ok (by omega) hs

/-- What `openMain` reads, in a state after `tagIn`, as it was on entry. -/
theorem OpenInG.vals {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ t) :
    ciphOf t.mem Ctx R = ctxCiph s₀.mem Ctx R ∧ blockAt t.mem (Ctx + BitVec.ofNat 64 240) = ctxH s₀.mem Ctx ∧
      bytesAt t.mem Np nl = bytesAt s₀.mem Np nl ∧ bytesAt t.mem A al = bytesAt s₀.mem A al ∧
      bytesAt t.mem D n = bytesAt s₀.mem D n := by
  have hnlt := (dataOk_of o.dat).lt
  have hnl := o.non.lt
  have hal := o.aad.lt
  have kE : ∀ {X : Region}, X.Disjoint (workR W) → ∀ r ∈ entryFr to W, X.Disjoint r :=
    fun hX => keep_of_sub (entryFr_work to W) hX
  exact ⟨ciph_frame o.fr (kE o.dcW) o.rounds, blockAt_frame o.fr (kE (o.dcW.sub_left (Lay.ctxSub (by decide)))),
    bytesAt_frame o.fr (kE o.dnW) (by omega_arith), bytesAt_frame o.fr (kE o.daW) (by omega_arith),
    bytesAt_frame o.fr (kE o.ddW) (by omega_arith)⟩

/-- The received tag, after `tagIn`, as it was on entry. -/
theorem OpenInG.tag {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {s₀ s : State}
    (o : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s) : bytesAt s.mem Tg tl = bytesAt s₀.mem Tg tl :=
  bytesAt_frame o.fr (keep_of_sub (entryFr_work to W) o.dtW) (by have := o.tlt; omega_arith)

/-- What `open` leaves after its branch on the tag length, from the state
`s₀` it was called in, for the ciphertext `C`: the plaintext at the text if
the tag is right, and `F` of the memory if not. `OpenPost` is the case of the
text decrypted in place. -/
abbrev OpenPostG (Ctx W SP Np A D Tg : Addr) (R nl al n tl : Nat) (C : List Byte) (F : Mem → Prop)
    (s₀ s₄ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ SavedAt s₄.mem W s₀ ∧
    match Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
        C (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl) with
    | some pt => (s₄.gpr .x0).setWidth 32 = 1 ∧ bytesAt s₄.mem D n = pt
    | none => (s₄.gpr .x0).setWidth 32 = 0 ∧ F s₄.mem

/-- What `open` leaves after its branch on the tag length, from the state
`s₀` it was called in. -/
abbrev OpenPost (Ctx W SP Np A D Tg : Addr) (R nl al n tl : Nat) (s₀ s₄ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ SavedAt s₄.mem W s₀ ∧
    match Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl) with
    | some pt => (s₄.gpr .x0).setWidth 32 = 1 ∧ bytesAt s₄.mem D n = pt
    | none => (s₄.gpr .x0).setWidth 32 = 0 ∧ bytesAt s₄.mem D n = bytesAt s₀.mem D n

/-- `openMainG to`, once the received tag is at `W`: the plaintext at the
output if the tag is right; if not, out of place zeros there, in place the
text as it was. -/
theorem openMainG_post (v : GcmImpl) (to : Bool) {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} (o' : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ t)
    (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl) (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (openMainG v.callees to) t (OpenPostG Ctx W SP Np A O Tg R nl al n tl (bytesAt s₀.mem D n)
      (fun m => bytesAt m O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) s₀) := by
  have L := o'.lay
  refine WP.mono (openMainG_ok v to L o'.env o'.x22 o'.rounds o'.x23 o'.x24 o'.x26 o'.x27 o'.non o'.aad o'.dat
    o'.out o'.ddW o'.dcW o'.sA o'.sL o'.sD o'.sN o'.sT hok) fun s₄ hpost => ?_
  dsimp only at hpost
  obtain ⟨he₄, F₄, x0₄, d₄⟩ := hpost
  refine ⟨he₄, o'.sv.frame F₄ fun r hr => ?_, ?_⟩
  · rcases List.mem_cons.mp hr with h | hr
    · subst h; exact (o'.outW.ok.w.sub_right (Lay.wSub (by decide))).symm
    rcases List.mem_append.mp hr with hr | hr
    · exact saved_omFrame L r hr
    · exact saved_crFrame L o'.outW r hr
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

theorem openMainG_false (c : Callees) : openMainG c false = openMain c := by
  simp only [openMainG, openMain, wipeG, oneCryptG, oneCrypt, Bool.cond_false, List.append_nil, cryptAlG_false]

/-- `openMain`, once the received tag is at `W`. -/
theorem openMain_post (v : GcmImpl) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o' : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true) :
    WP isa (openMain v.callees) t (OpenPost Ctx W SP Np A D Tg R nl al n tl s₀) := by
  rw [← openMainG_false]
  exact openMainG_post v false o' hT₃ hok

/-- The branch on the tag length failing, in place: 0 returned, `F` of the
memory kept. -/
theorem failZero_ok {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {C : List Byte}
    {F : Mem → Prop} {s₀ s₃ : State} (o : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s₃) (hF : F s₃.mem)
    (hok : Spec.Gcm.tagLenOk tl = false) :
    WP isa (.block [imm .x0 0]) s₃ (OpenPostG Ctx W SP Np A O Tg R nl al n tl C F s₀) := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨o.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, o.sv, ?_⟩
  rw [Spec.Gcm.openResult, ite_eq_right (by simp [hok])]
  exact ⟨by simp [gpr_write], hF⟩

/-- The branch on the tag length failing, out of place: 0 returned, and the
output zeroed. -/
theorem failTo_ok {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {C : List Byte} {s₀ s₃ : State}
    (o : OpenInG true Ctx W SP Np A D O Tg R nl al n tl s₀ s₃) (hok : Spec.Gcm.tagLenOk tl = false) :
    WP isa (.seq (.block [imm .x0 0]) (wipeG true)) s₃
      (OpenPostG Ctx W SP Np A O Tg R nl al n tl C (fun m => bytesAt m O n = List.replicate n 0) s₀) := by
  obtain ⟨s₄, run₄, x0₄, r₄⟩ : ∃ s₄, runBlock isa [imm .x0 0] s₃ = some s₄ ∧ s₄.gpr .x0 = 0 ∧
      Regs [.x0] s₃ s₄ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have o₄ := o.of_regs r₄
  have ou : OutIn Ctx W D O n s₄ := o₄.out
  refine WP.mono (wipeTo_ok o₄.env ou.sO o₄.sN ou.dw) fun s₅ ⟨z, f, g, sp, rd, wr⟩ => ?_
  refine ⟨o₄.env.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr,
    o₄.sv.frame f fun r hr => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (ou.dw.ok.w.sub_right (Lay.wSub (by decide))).symm
  · rw [Spec.Gcm.openResult, ite_eq_right (by simp [hok])]
    exact ⟨by rw [g _ (by decide) (by decide) (by decide), x0₄]; rfl, z⟩

/-- The branch on the tag length, with `fl` if it fails and `m` once the
received tag is at `W`, for `OpenPostG` with the output at `O`. -/
theorem oiteWithFl_ok {fl m : Prog isa} {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat}
    {C : List Byte} {F : Mem → Prop} {s₀ s₃ : State}
    (o : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ s₃) (x12₃ : s₃.gpr .x12 = Tg)
    (x9₃ : s₃.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk tl then 1 else 0))
    (hfl : Spec.Gcm.tagLenOk tl = false → WP isa fl s₃ (OpenPostG Ctx W SP Np A O Tg R nl al n tl C F s₀))
    (hm : ∀ {t : State}, OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀ t →
      bytesAt t.mem W tl = bytesAt s₀.mem Tg tl → Spec.Gcm.tagLenOk tl = true →
      Others loopRegs s₃ t →
      WP isa m t (OpenPostG Ctx W SP Np A O Tg R nl al n tl C F s₀)) :
    WP isa (.ite (.zero .x .x9) fl (.seq tagIn m)) s₃
      (OpenPostG Ctx W SP Np A O Tg R nl al n tl C F s₀) := by
  have ev : isa.eval (.zero .x .x9) s₃ = some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.ite _ ev (fun ht => ?_) (fun hf => ?_)
  · exact hfl (by revert ht; cases Spec.Gcm.tagLenOk tl <;> simp)
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := tagLenOk_le hok
    refine WP.seq (WP.mono (tagIn_ok o.env.x19 x12₃ o.x28 hle o.tagR o.env.perm.w
      (o.dtW.sub_right (Region.sub_prefix (by decide)))) fun s₃' ⟨rt, f, og, sp, rd, wr⟩ => ?_)
    exact hm (o.tagIn f og sp rd wr) (by rw [rt, o.tag]) hok og

/-- `open`'s branch on the tag length, with `m` once the received tag is at
`W`, for `OpenPostG`. -/
theorem oiteWithG_ok {m : Prog isa} {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {C : List Byte}
    {F : Mem → Prop} {s₀ s₃ : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s₃) (x12₃ : s₃.gpr .x12 = Tg)
    (x9₃ : s₃.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk tl then 1 else 0)) (hF : F s₃.mem)
    (hm : ∀ {t : State}, OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t →
      bytesAt t.mem W tl = bytesAt s₀.mem Tg tl → Spec.Gcm.tagLenOk tl = true →
      Others loopRegs s₃ t →
      WP isa m t (OpenPostG Ctx W SP Np A D Tg R nl al n tl C F s₀)) :
    WP isa (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn m)) s₃
      (OpenPostG Ctx W SP Np A D Tg R nl al n tl C F s₀) :=
  oiteWithFl_ok o x12₃ x9₃ (failZero_ok o hF) hm

/-- `open`'s branch on the tag length, with `m` once the received tag is at `W`. -/
theorem oiteWith_ok {m : Prog isa} {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {s₀ s₃ : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ s₃) (x12₃ : s₃.gpr .x12 = Tg)
    (x9₃ : s₃.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk tl then 1 else 0))
    (hm : ∀ {t : State}, OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t →
      bytesAt t.mem W tl = bytesAt s₀.mem Tg tl → Spec.Gcm.tagLenOk tl = true →
      Others loopRegs s₃ t →
      WP isa m t (OpenPost Ctx W SP Np A D Tg R nl al n tl s₀)) :
    WP isa (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn m)) s₃
      (OpenPost Ctx W SP Np A D Tg R nl al n tl s₀) :=
  oiteWithG_ok (C := bytesAt s₀.mem D n) (F := fun m => bytesAt m D n = bytesAt s₀.mem D n) o x12₃ x9₃
    o.vals.2.2.2.2 hm

/-- `open` (or `open_to`: `to`) after its entry, with `fl` if the tag length
is not allowed and `m` once the received tag is at `W`, for `OpenPostG`: the
ciphertext `C`, and `F` of the memory if the tag is wrong, the output at `O`. -/
theorem openRestWithFl_wp {fl m : Prog isa} {to : Bool} {Ctx W Np A D O Tg : Addr} {R nl al n tl : Nat}
    {s s₂ : State} {C : List Byte} {F : Mem → Prop}
    (o₂ : OpenInG to Ctx W s.sp Np A D O Tg R nl al n tl s s₂) (x12₂ : s₂.gpr .x12 = Tg)
    (hfl : ∀ {t : State}, OpenInG to Ctx W s.sp Np A D O Tg R nl al n tl s t → Others [.x9, .x10] s₂ t →
      t.mem = s₂.mem → Spec.Gcm.tagLenOk tl = false →
      WP isa fl t (OpenPostG Ctx W s.sp Np A O Tg R nl al n tl C F s))
    (hm : ∀ {t : State}, OpenInG to Ctx W s.sp Np A D O Tg R nl al n tl s t →
      bytesAt t.mem W tl = bytesAt s.mem Tg tl → Spec.Gcm.tagLenOk tl = true →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = s₂.gpr r) →
      WP isa m t (OpenPostG Ctx W s.sp Np A O Tg R nl al n tl C F s)) :
    WP isa (.seq tagLenOk (.seq (.ite (.zero .x .x9) fl (.seq tagIn m)) (.block restore))) s₂
      fun s' => GprAbi s s' ∧
        match Spec.Gcm.openResult (ctxCiph s.mem Ctx R) (ctxH s.mem Ctx) tl (bytesAt s.mem Np nl) C
            (bytesAt s.mem A al) (bytesAt s.mem Tg tl) with
        | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem O n = pt
        | none => (s'.gpr .x0).setWidth 32 = 0 ∧ F s'.mem := by
  refine WP.seq (WP.mono (tagLenOk_ok s₂ o₂.x28 o₂.tlt) fun s₃ ⟨x9₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (oiteWithFl_ok (C := C) (F := F) (o₂.of_regs r₃) (by rw [r₃.others _ (by decide), x12₂])
    x9₃ (hfl (o₂.of_regs r₃) r₃.others r₃.mem)
    fun o' hT hok og => hm o' hT hok fun r hr => by
      rw [og r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
        r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)])
    fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  refine WP.mono (exit_ok he₄.x19 (he₄.sp.trans o₂.sp₀.symm) (covers_left he₄.perm.w) sv₄)
    fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  rw [hm, hx0]
  exact post₄

/-- `openRestWith_wp`, for `OpenPostG`: the ciphertext `C`, and `F` of the
memory if the tag is wrong (which the branch on the tag length keeps). -/
theorem openRestWithG_wp {m : Prog isa} {w : Nat} {s s₂ : State} {C : List Byte} {F : Mem → Prop}
    (o₂ : OpenIn (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
      (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s s₂)
    (x12₂ : s₂.gpr .x12 = stackArg s 0) (hF : ∀ {t : State}, Others [.x9, .x10] s₂ t → t.mem = s₂.mem → F t.mem)
    (hm : ∀ {t : State}, OpenIn (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s t →
      bytesAt t.mem (stackArg s w) (stackArg s 1).toNat = bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat →
      Spec.Gcm.tagLenOk (stackArg s 1).toNat = true →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = s₂.gpr r) →
      WP isa m t (OpenPostG (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat C F s)) :
    WP isa (.seq tagLenOk (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn m)) (.block restore))) s₂
      fun s' => GprAbi s s' ∧
        match Spec.Gcm.openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0))
            (stackArg s 1).toNat (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) C
            (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) with
        | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
        | none => (s'.gpr .x0).setWidth 32 = 0 ∧ F s'.mem :=
  openRestWithFl_wp o₂ x12₂ (fun o' og hmem hok => failZero_ok o' (hF og hmem) hok) hm

/-- `open` after its entry, with `m` once the received tag is at `W`, from
the registers `x4` to `x7` of the entry. -/
theorem openRestWith_wp {m : Prog isa} {w : Nat} {s s₂ : State}
    (o₂ : OpenIn (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
      (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s s₂)
    (x12₂ : s₂.gpr .x12 = stackArg s 0)
    (hm : ∀ {t : State}, OpenIn (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s t →
      bytesAt t.mem (stackArg s w) (stackArg s 1).toNat = bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat →
      Spec.Gcm.tagLenOk (stackArg s 1).toNat = true →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = s₂.gpr r) →
      WP isa m t (OpenPost (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s)) :
    WP isa (.seq tagLenOk (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn m)) (.block restore))) s₂
      fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  refine WP.seq (WP.mono (tagLenOk_ok s₂ o₂.x28 o₂.tlt) fun s₃ ⟨x9₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (oiteWith_ok (o₂.of_regs r₃) (by rw [r₃.others _ (by decide), x12₂]) x9₃
    fun o' hT hok og => hm o' hT hok fun r hr => by
      rw [og r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
        r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)])
    fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  refine WP.mono (exit_ok he₄.x19 (he₄.sp.trans o₂.sp₀.symm) (covers_left he₄.perm.w) sv₄)
    fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  simp only [openAArch64, openRes]
  rw [hm, hx0]
  exact post₄

theorem open_wp (v : GcmImpl) {s : State} (hs : openAArch64.pre s) :
    WP isa («open» v.callees) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  refine WP.seq (WP.mono (openEntry_ok (.inl rfl) (openPreX_W hs)) fun s₂ ⟨o₂, x12₂⟩ => ?_)
  exact openRestWith_wp o₂ x12₂ fun o' hT hok _ => openMain_post v o' hT hok

/-! ## `vg_aes_gcm_open_to`

`openG c true w`: the entry keeps `dst` at `W + dstO` (`openEntryTo_ok`); the
rest is `open`'s, generic over `to` (`openRestWithFl_wp`, `openMainG_post`),
with `src` only read and the output at `dst`, zeroed if the tag length is not
allowed (`failTo_ok`) or the tag is wrong. -/

/-- What `openToPreXW` gives, with `work` the stack argument `w`. -/
structure ToLay (s : State) (w : Nat) : Prop where
  lay : Lay (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w)
  perm : Perm (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s
  hsp : ∀ i < w + 1, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8
  args : (args s (w + 1)).Disjoint (workR (stackArg s w))
  non : DataOk (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s (s.gpr .x2) (s.gpr .x3).toNat
  aad : DataOk (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s (s.gpr .x4) (s.gpr .x5).toNat
  src : DataOk (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s (s.gpr .x6) (s.gpr .x7).toNat
  dst : DataW (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s (stackArg s 0) (s.gpr .x7).toNat
  sd : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (s.gpr .x7).toNat⟩
  dnW : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  daW : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  dsW : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  dcW : (⟨s.gpr .x0, 256⟩ : Region).Disjoint (workR (stackArg s w))
  tag : Covers [⟨stackArg s 2, (stackArg s 3).toNat⟩] (s.rd ++ s.wr)
  dtW : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  rounds : rounds (s.gpr .x1)

theorem openToLay {w : Nat} {extra extraW : List Region} {s : State} (hs : openToPreXW w extra s extraW) :
    ToLay s w := by
  simp only [openToPreXW] at hs
  obtain ⟨hrd, hwr, dcd, dcw, dnd, dnw, dad, daw, dsd, dsw, ddt, ddw, ddg, dtw, dwg, wc, wn, wa, wsr, wds, wt,
    ww, wsp, hR, hlen⟩ := hs
  have mc : (⟨s.gpr .x0, 256⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have mn : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ma : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ms : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have mt : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have mg : args s (w + 1) ∈ s.rd := by rw [hrd]; simp
  have md : (⟨stackArg s 0, (s.gpr .x7).toNat⟩ : Region) ∈ s.wr := by rw [hwr, ← hlen]; simp
  have mw : (⟨stackArg s w, 2560⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  rw [hlen] at dcd dnd dad dsd ddt ddw ddg wds
  have sub16 : Region.Sub ⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg s w)) := Lay.wSub (by decide)
  refine ⟨⟨wc, ?_, ww, dcw.sub_right sub16, dcw, ?_, ?_⟩, ⟨covers_mem mc,
    covers_off (k := 2560) (covers_of_mem mw) (show 16 + 80 ≤ 2560 by decide) (by decide), covers_of_mem mw⟩,
    fun i hi => ?_, dwg.symm, ⟨covers_mem mn, (s.gpr .x3).isLt, wn, dnw.sub_right sub16, dnw⟩,
    ⟨covers_mem ma, (s.gpr .x5).isLt, wa, daw.sub_right sub16, daw⟩,
    ⟨covers_mem ms, (s.gpr .x7).isLt, wsr, dsw.sub_right sub16, dsw⟩,
    ⟨⟨covers_left (covers_of_mem md), (s.gpr .x7).isLt, wds, ddw.sub_right sub16, ddw⟩, covers_of_mem md, dcd⟩,
    dsd, dnw, daw, dsw, dcw, covers_mem mt, dtw, hR⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega)]
    omega
  · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
      (by decide) (by decide)
  · exact Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 2464) (.inl (by decide))
      (by decide) (by decide)
  · refine ⟨args s (w + 1), List.mem_append_left _ mg, ?_⟩
    have e : stackArgAddr s 0 = s.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    simp only [args, e]
    exact Offset.contains_base _ (by omega) (by omega)

/-- The load of `dst`, the first stack argument, and its store at `W + dstO`. -/
theorem dstStash_ok {s : State} {W : Addr} {V : BitVec 64} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = V) :
    WP isa (.block [.ldrSp .x10 0, .str .x .x10 .x19 dstO]) s fun s' =>
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 320) V ∧ Others [.x10] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have w := in_off hw (show 320 + 8 ≤ 2560 by decide) (by decide)
  refine WP.run ⟨_, by arun [h19, hsp, w, dstO], rfl⟩ fun s' hs' => ?_
  subst hs'
  have e : s.mem.read (s.sp + BitVec.ofNat 64 0) 8 = V := by rw [← hV]; rfl
  refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, e]

/-- `open_to`'s first block: the entry, `dst` kept at `W + dstO`, the tag
length stashed and the tag in `x12`, with `work` the stack argument `w`. -/
theorem openEntryTo_ok {w : Nat} (hw : 4 ≤ w ∧ w ≤ 5) {extra extraW : List Region} {s : State}
    (hs : openToPreXW w extra s extraW) :
    WP isa (.block (openEntryG true w)) s fun s' =>
      OpenInG true (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (stackArg s 2) (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat
        (stackArg s 3).toNat s s' ∧ s'.gpr .x12 = stackArg s 2 := by
  obtain ⟨L, perm, hsp, dA, non, aad, src, dst, sd, dnW, daW, dsW, dcW, tR, dtW, hR⟩ := openToLay hs
  show WP isa (.block (((oneEntry (8 * w) ++ [.ldrSp .x10 0, .str .x .x10 .x19 dstO]) ++ stashArg 24) ++
    ([.ldrSp .x12 16] : List Instr))) s _
  have hW : s.mem.readW (s.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg s w := rfl
  have hD0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := rfl
  have hT16 : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg s 2 := rfl
  have hT24 : s.mem.readW (s.sp + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (stackArg s 3).toNat := by
    rw [ofNat_toNat']; rfl
  have spw : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * w)) 8 := hsp w (by omega_arith)
  have sp0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := hsp 0 (by omega_arith)
  have sp16 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := hsp 2 (by omega_arith)
  have sp24 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 24) 8 := hsp 3 (by omega_arith)
  have darg (j : Nat) (hj : j + 8 ≤ 8 * (w + 1)) :
      (⟨s.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (workR (stackArg s w)) := by
    refine dA.sub_left ?_
    show Region.Sub ⟨s.sp + BitVec.ofNat 64 j, 8⟩ ⟨s.sp + BitVec.ofNat 64 (8 * 0), 8 * (w + 1)⟩
    rw [show s.sp + BitVec.ofNat 64 (8 * 0) = s.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by omega_arith)
  have d0 := darg 0 (by omega_arith)
  have d16 := darg 16 (by omega_arith)
  have d24 := darg 24 (by omega_arith)
  have h3 := ofNat_toNat' (s.gpr .x3)
  have h5 := ofNat_toNat' (s.gpr .x5)
  have h7 := ofNat_toNat' (s.gpr .x7)
  generalize hW' : stackArg s w = W at *
  generalize hTg : stackArg s 2 = Tg at *
  generalize hO : stackArg s 0 = O at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  generalize htlv : (stackArg s 3).toNat = tl at *
  have htlt : tl < 2 ^ 64 := htlv ▸ (stackArg s 3).isLt
  -- Disjoint from a part of `work`.
  have kW : ∀ {X : Region}, X.Disjoint (workR W) → ∀ {d k : Nat}, d + k ≤ 2560 →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, k⟩ : Region)], X.Disjoint r := fun hX _ _ h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hX.sub_right (Lay.wSub h)
  have svd : ∀ {d : Nat}, 216 ≤ d → d + 8 ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 8⟩ : Region)],
      (savedR W).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (oneEntry_ok (k := 8 * w) (by omega_arith) hW spw hCtx perm)
    fun s₁ ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, sl₁, sl₂, sl₃, sl₄, f₁, sv₁, rd₁, wr₁⟩ => ?_)))
  refine WP.mono (dstStash_ok (V := O) he₁.x19 he₁.perm.w (by rw [rd₁, wr₁, he₁.sp]; exact sp0)
    (by rw [he₁.sp, f₁.readW (r := ⟨s.sp + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _)
      (keep_of_sub (entryR_work W) d0) (by decide), hD0]))
    fun s₂ ⟨m₂, og₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₂ : Frame [⟨W + BitVec.ofNat 64 320, 8⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.mono (stashArg_ok (W := W) (k := 24) (V := BitVec.ofNat 64 tl) (by decide)
    (by rw [og₂ _ (by decide), he₁.x19]) (by rw [wr₂]; exact he₁.perm.w)
    (by rw [rd₂, wr₂, sp₂, rd₁, wr₁, he₁.sp]; exact sp24)
    (by rw [sp₂, he₁.sp, F₂.readW (r := ⟨s.sp + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
        (kW d24 (by decide)) (by decide), f₁.readW (r := ⟨s.sp + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
        (keep_of_sub (entryR_work W) d24) (by decide), hT24]))
    fun s₃ ⟨x28₃, m₃, og₃, sp₃, rd₃, wr₃⟩ => ?_
  have F₃ : Frame [⟨W + BitVec.ofNat 64 248, 8⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨s₄, run₄, x12₄, g₄, sp₄, m₄, rd₄, wr₄⟩ := ldrSp_ok (t := .x12) (s := s₃) (k := 16) (by decide)
    (by rw [sp₃, sp₂, he₁.sp, F₃.readW (r := ⟨s.sp + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _)
        (kW d16 (by decide)) (by decide), F₂.readW (r := ⟨s.sp + BitVec.ofNat 64 16, 8⟩)
        (Region.contains_self _ _) (kW d16 (by decide)) (by decide),
        f₁.readW (r := ⟨s.sp + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _)
        (keep_of_sub (entryR_work W) d16) (by decide), hT16])
    (by rw [rd₃, wr₃, sp₃, rd₂, wr₂, sp₂, rd₁, wr₁, he₁.sp]; exact sp16)
  refine WP.of_runBlock ⟨s₄, run₄, ?_, x12₄⟩
  have g : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27], s₄.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g₄ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      og₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      og₂ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have so : ∀ d, d + 8 ≤ 248 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => by
      rw [m₄, m₃, readW_writeW_other _ _ _ (.inl hd) (by omega_arith) (by decide), m₂,
        readW_writeW_other _ _ _ (.inl (by omega_arith)) (by omega_arith) (by decide)]
  rw [hA] at sl₁
  rw [← h5] at sl₂
  rw [hD] at sl₃
  rw [← h7] at sl₄
  refine ⟨L, he₁.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)) (by rw [sp₄, sp₃, sp₂]) (by rw [rd₄, rd₃, rd₂])
      (by rw [wr₄, wr₃, wr₂]),
    by rw [g .x22 (by simp), x22₁, ← hRR, ofNat_toNat'], by rw [← hRR]; exact hR,
    by rw [g .x23 (by simp), x23₁, hNp], by rw [g .x24 (by simp), x24₁, ← h3], by rw [g .x26 (by simp), x26₁, ← h3],
    by rw [g .x27 (by simp), x27₁], by rw [g₄ _ (by decide), x28₃], htlt,
    non.of_eq rd₄' wr₄', aad.of_eq rd₄' wr₄', src.of_eq rd₄' wr₄', by rw [rd₄', wr₄']; exact tR,
    dnW, daW, dsW, dcW, dtW, by rw [so 216 (by decide), sl₁], by rw [so 224 (by decide), sl₂],
    by rw [so 232 (by decide), sl₃], by rw [so 240 (by decide), sl₄],
    by rw [m₄, m₃, Mem.readW_writeW_self64], ?_, ?_, rfl, rd₄', wr₄', ?_⟩
  · show Frame [entryR W, ⟨W + BitVec.ofNat 64 320, 8⟩, ⟨W, 16⟩] s.mem s₄.mem
    rw [m₄, m₃, m₂]
    exact ((f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..,
      fun _ h => h⟩).writeW (r := ⟨W + BitVec.ofNat 64 320, 8⟩) (by simp) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_self ..) _ (entry_contains W (by decide) (by decide))
  · rw [m₄]
    exact (sv₁.frame F₂ (svd (by decide) (by decide))).frame F₃ (svd (by decide) (by decide))
  · exact ⟨dst.of_eq rd₄' wr₄', sd, by
      rw [m₄, m₃, readW_writeW_other _ _ _ (.inr (by decide)) (by decide) (by decide), m₂,
        Mem.readW_writeW_self64]⟩

/-- `vg_aes_gcm_open_to` (`openG c true w`, with `work` the stack argument
`w`: 4, or 5 after the powers). -/
theorem openTo_wp (v : GcmImpl) {w : Nat} (hw : w = 4 ∨ w = 5) {extra extraW : List Region} {s : State}
    (hs : openToPreXW w extra s extraW) :
    WP isa (openG v.callees true w) s fun s' => GprAbi s s' ∧ openToPostOf s s' := by
  unfold openG openRestG
  refine WP.seq (WP.mono (openEntryTo_ok (by omega) hs) fun s₂ ⟨o₂, x12₂⟩ => ?_)
  refine WP.mono (openRestWithFl_wp (fl := .seq (.block [imm .x0 0]) (wipeG true))
    (m := openMainG v.callees true) (C := bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (F := fun m => bytesAt m (stackArg s 0) (s.gpr .x7).toNat = List.replicate (s.gpr .x7).toNat 0)
    o₂ x12₂ (fun o' _ _ hok => failTo_ok o' hok) fun o' hT hok _ => openMainG_post v true o' hT hok)
    fun s' ⟨ga, post⟩ => ⟨ga, ?_⟩
  simp only [openToPostOf, openToRes]
  exact post

end VG.Proof.AesGcm.AArch64
