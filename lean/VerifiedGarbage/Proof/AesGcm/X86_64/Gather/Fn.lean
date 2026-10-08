import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CallTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Run

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: correctness

Untrusted: everything here is checked by Lean. Each piece of the code, from
what holds before it to what holds after it (`w_entry2` … `w_fin`), which
the proof of constant time follows too; the slices, one call of
`vg_aes_gcm_stream_encrypt_to` each (`slices_ok`); the text, after the
additional data padded to a whole block (`text_ok`); and the whole function
(`sealGather_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block StreamRepr ctxCiph ctxH gctr inc32 j0 fullTag)
open VG.Proof.Gcm (padA)

/-- What the function returns with. -/
def Done (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.sealGatherPostG s s'

/-! ## What holds between the pieces -/

/-- After the first entry block. -/
def E1 (s : State) (s₁ : State) : Prop :=
  s₁.gpr .r11 = W s ∧ (∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 16) 64 = Ad s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 24) 64 = AL s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 64) 64 = stackArg s 1 ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 80) 64 = AL s ∧
    Frame [kpR s] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr

/-- Before the call of `vg_aes_gcm_stream_init`. -/
def E2 (s : State) (st : State) : Prop :=
  Base s (AL s) 0 st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = Nn s ∧ st.gpr .rdx = s.gpr .rcx ∧ st.gpr .rcx = St s

/-- Before the call of `vg_aes_gcm_stream_aad` on the additional data. -/
def P4 (s : State) (st : State) : Prop :=
  Mid s (AL s) 0 [] st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = St s ∧ st.gpr .rdx = BitVec.ofNat 64 0 ∧
    st.gpr .rcx = Ad s ∧ st.gpr .r8 = AL s

/-- After the length of the text. -/
def T1 (s : State) (st : State) : Prop :=
  Mid s (AL s) 0 (ad s) st ∧ st.gpr .r11 = W s ∧ st.zf = some (decide (L s = 0))

/-- After the remainder of the length of the additional data. -/
def T2 (s : State) (st : State) : Prop :=
  Mid s (AL s) 0 (ad s) st ∧ st.gpr .r11 = W s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = BitVec.ofNat 64 ((AL s).toNat % 16) ∧ st.zf = some (decide ((AL s).toNat % 16 = 0))

/-- The length of the padding. -/
abbrev pl (s : State) : Nat := 16 - (AL s).toNat % 16

/-- The length of the additional data, padded. -/
abbrev apP (s : State) : BitVec 64 := BitVec.ofNat 64 (padA (ad s)).length

/-- Before the call of `vg_aes_gcm_stream_aad` on the padding. -/
def T3 (s : State) (st : State) : Prop :=
  Mid s (AL s + BitVec.ofNat 64 (pl s)) 0 (ad s) st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = St s ∧
    st.gpr .rdx = AL s ∧ st.gpr .rcx = W s + BitVec.ofNat 64 88 ∧ st.gpr .r8 = BitVec.ofNat 64 (pl s)

/-- Before the call of `vg_aes_gcm_stream_encrypt_to` on slice `i`. -/
def S1 (s : State) (ap : BitVec 64) (i : Nat) (A : List Byte) (st : State) : Prop :=
  Mid s ap i A st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = ap ∧
    st.gpr .r8 = BitVec.ofNat 64 (gl s i) ∧ st.gpr .r9 = sb s i ∧
    st.gpr .r10 = Dst s + BitVec.ofNat 64 (gl s i) ∧ st.gpr .rax = BitVec.ofNat 64 (sl s i)

/-- After the call on slice `i`: its encryption done, the slots not yet past it. -/
def S2 (s : State) (ap : BitVec 64) (i : Nat) (A : List Byte) (st : State) : Prop :=
  Base s ap i st ∧ StreamRepr st.mem (St s) (ciph s) (hk s) (iv s) A (ct s (i + 1)) ∧
    bytesAt st.mem (Dst s) (gl s (i + 1)) = ct s (i + 1)

/-- Before the call of `vg_aes_gcm_stream_finish`: the streaming state
represents the message with the additional data and the whole ciphertext,
which the output holds. -/
def Fin (s : State) (st : State) : Prop :=
  ∃ ap i, Base s ap i st ∧ StreamRepr st.mem (St s) (ciph s) (hk s) (iv s) (ad s) (ct s (Cnt s)) ∧
    bytesAt st.mem (Dst s) (L s) = ct s (Cnt s)

/-- `Fin`, with the arguments of `vg_aes_gcm_stream_finish`. -/
def P7 (s : State) (st : State) : Prop :=
  Fin s st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = stackArg s 3 ∧ st.gpr .r9 = Tg s

theorem length_ad (s : State) : (ad s).length = (AL s).toNat := Cmac.bytesAt_length _ _ _

theorem al_eq (s : State) : AL s = BitVec.ofNat 64 (ad s).length := by rw [length_ad, ofNat_toNat]

/-- The encryption of a text in two pieces: that of the first, then the rest. -/
theorem gctr_split (ciph : Block → Block) (icb : Block) (x y : List Byte) :
    gctr ciph icb x ++ (gctr ciph icb (x ++ y)).drop x.length = gctr ciph icb (x ++ y) := by
  rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

theorem one_kpR {s : State} {r : Region} (hd : (kpR s).Disjoint r) : ∀ r' ∈ [kpR s], r.Disjoint r' := fun r' hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact hd.symm

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-! ## The pieces -/

theorem w_entry2 {st : State} (h : E1 s st) : WP isa (.block entry2) st (E2 s) := by
  obtain ⟨h11, hg, c₀, c₁, c₂, c₃, c₇, c₈, c₁₀, f₁, rd₁, wr₁⟩ := h
  exact WP.mono (entry2_ok hp h11 hg c₀ c₁ c₂ c₃ c₇ c₈ c₁₀ f₁ rd₁ wr₁)
    fun _ ⟨k, f₂, di, si, dx, cx, _, sp, cs, rd₂, wr₂⟩ => ⟨⟨sp, cs, rd₂, wr₂, k, frame_kpR f₂⟩, di, si, dx, cx⟩

theorem w_init (I : InitFn) {st : State} (h : E2 s st) :
    WP isa (.call I.fn.name I.fn.code) st (Mid s (AL s) 0 []) :=
  initCall_ok hp I h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem w_aadArgs {st : State} (h : Mid s (AL s) 0 [] st) : WP isa (.block aadArgs) st (P4 s) :=
  WP.mono (aadArgs_ok hp h.toBase) fun _ ⟨di, si, dx, cx, r8, cs, m, rd, wr⟩ =>
    ⟨h.regs m cs rd wr, di, si, dx, cx, r8⟩

theorem w_aad (A : AadFn) {st : State} (h : P4 s st) :
    WP isa (.call A.fn.name A.fn.code) st (Mid s (AL s) 0 (ad s)) := by
  obtain ⟨M₄, di, si, dx, cx, r8⟩ := h
  refine WP.mono (aadCall_ok hp A M₄ (hp.a_w.symm.sub_left stR_sub) hp.b_a
    (covers_of_mem (by rw [hp.rd]; simp)) hp.w_ad (AL s).isLt di si dx cx (by rw [r8, ofNat_toNat]))
    fun _ M₅ => ?_
  rwa [List.nil_append, ad_eq hp M₄.frame] at M₅

theorem w_textLen {st : State} (h : Mid s (AL s) 0 (ad s) st) : WP isa (.block textLen) st (T1 s) :=
  WP.mono (textLen_ok hp h.toBase) fun _ ⟨r11, z, cs, m, rd, wr⟩ => ⟨h.regs m cs rd wr, r11, z⟩

theorem w_padLen {st : State} (h : T1 s st) : WP isa (.block padLen) st (T2 s) :=
  WP.mono (padLen_ok hp h.1.toBase h.2.1) fun _ ⟨r11, cx, r8, z, cs, m, rd, wr⟩ =>
    ⟨h.1.regs m cs rd wr, r11, cx, r8, z⟩

omit hp in
/-- The additional data, already a whole number of blocks. -/
theorem pad_none {st : State} (h : T2 s st) (hr : (AL s).toNat % 16 = 0) : Mid s (apP s) 0 (padA (ad s)) st := by
  have hpad : padA (ad s) = ad s := by
    simp [padA, Proof.Gcm.padLen_of_mod (show (ad s).length % 16 = 0 by rw [length_ad]; exact hr),
      Spec.Gcm.zeros]
  rw [apP, hpad, ← al_eq]
  exact h.1

theorem w_padArgs {st : State} (h : T2 s st) : WP isa (.block padArgs) st (T3 s) := by
  obtain ⟨M₂, r11, cx, r8, -⟩ := h
  exact WP.mono (padArgs_ok hp M₂.toBase r11 cx r8) fun s₃ ⟨di, si, dx, cx, r8, k, f, cs₃, rd₃, wr₃⟩ =>
    ⟨⟨⟨by rw [cs₃ _ (by decide), M₂.rsp], fun r hr => by rw [cs₃ r hr, M₂.saved r hr], rd₃.trans M₂.rd,
      wr₃.trans M₂.wr, k, M₂.frame.trans (frame_kpR f)⟩, Nat.zero_le _,
      StreamTo.streamRepr_frame f (one_kpR kpR_stR) M₂.sr, by rw [gl_zero, ct_zero]; rfl⟩, di, si, dx, cx, r8⟩

theorem w_padCall (A : AadFn) {st : State} (h : T3 s st) (hr : (AL s).toNat % 16 ≠ 0) :
    WP isa (.call A.fn.name A.fn.code) st (Mid s (apP s) 0 (padA (ad s))) := by
  obtain ⟨M₃, di, si, dx, cx, r8⟩ := h
  have hw := hp.w_w
  have hpl : pl s = 16 - (AL s).toNat % 16 := rfl
  have hn : pl s ≤ 16 := by omega
  have wd : (W s + BitVec.ofNat 64 88).toNat = (W s).toNat + 88 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 88) (by decide)]; omega
  refine WP.mono (aadCall_ok hp A M₃ (Offset.disjoint _ (.inr (by omega)) (by decide) (by omega))
    (hp.b_w.sub_right (Offset.sub_base _ (by omega)))
    (covers_left (by rw [hp.wr]; exact StreamTo.covers_off (k := 184) (d := 88) (by simp) (by omega) (by decide)))
    (by rw [wd]; omega) (by omega) di si (by rw [dx, al_eq]) cx r8) fun s₄ M₄ => ?_
  have hpad : padA (ad s) = ad s ++ bytesAt st.mem (W s + BitVec.ofNat 64 88) (pl s) := by
    rw [M₃.kept.zeros hn]
    simp only [padA, Spec.Gcm.padLen, length_ad]
    congr 2; omega
  have hap : AL s + BitVec.ofNat 64 (pl s) = apP s := by
    rw [apP, hpad, List.length_append, length_ad, Cmac.bytesAt_length, ← ofNat_add_ofNat, ofNat_toNat]
  rw [← hap, hpad]
  exact M₄

theorem w_leftTest {ap : BitVec 64} {A : List Byte} {st : State} (h : Mid s ap 0 A st) :
    WP isa (.block leftTest) st fun st' => Mid s ap 0 A st' ∧ st'.zf = some (decide (Cnt s - 0 = 0)) :=
  WP.mono (leftTest_ok hp h.toBase) fun _ ⟨_, z, cs, m, rd, wr⟩ => ⟨h.regs m cs rd wr, z⟩

theorem w_sliceArgs {ap : BitVec 64} {A : List Byte} {i : Nat} (hi : i < Cnt s) {st : State}
    (h : Mid s ap i A st) : WP isa (.block sliceArgs) st (S1 s ap i A) :=
  WP.mono (sliceArgs_ok hp hi h.toBase) fun _ ⟨di, si, dx, cx, r8, r9, r10, ax, cs, m, rd, wr⟩ =>
    ⟨h.regs m cs rd wr, di, si, dx, cx, r8, r9, r10, ax⟩

theorem w_sliceCall (T : ToFn M) {ap : BitVec 64} {A : List Byte} (hap : ap = BitVec.ofNat 64 A.length)
    {i : Nat} (hi : i < Cnt s) {st : State} (h : S1 s ap i A st) :
    WP isa (.frame (.push [.rax, .r10, .rax]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st (S2 s ap i A) := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have gsl := gl_succ_le hp hi
  obtain ⟨M₁, di, si, dx, cx, r8, r9, r10, ax⟩ := h
  refine WP.mono (toCall_ok hp T hi M₁.toBase di si dx cx r8 r9 r10 ax) fun s₂ ⟨cs₂, rd₂, wr₂, f₂, post⟩ => ?_
  have B₂ := M₁.toBase.after hp cs₂ rd₂ wr₂ f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨wkR s, by simp, stR_sub⟩
      · exact ⟨dR s, by simp, dq_sub hp hi⟩)
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kpR_stR
      · exact (hp.d_w.symm.sub_left kpR_sub).sub_right (dq_sub hp hi)
  obtain ⟨sr₂, dd₂⟩ := post (iv s) A (pt s i) M₁.sr hap (length_pt s i).symm
  -- The output before slice `i`, which the call leaves as it was.
  have hD : bytesAt s₂.mem (Dst s) (gl s i) = ct s i := by
    rw [← M₁.out]
    refine bytesAt_frame f₂ (fun r hr => ?_) (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact hp.d_w.sub_left (Region.sub_prefix (gl_le hp (Nat.le_of_lt hi))) |>.sub_right stR_sub
    · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega)
    · exact hp.b_d.symm.sub_left (Region.sub_prefix (gl_le hp (Nat.le_of_lt hi)))
  refine ⟨B₂, by rw [← pt_succ] at sr₂; exact sr₂, ?_⟩
  rw [gl_succ, bytesAt_add, hD, dd₂]
  show _ = gctr (ciph s) (icb s) (pt s (i + 1))
  rw [pt_succ]
  exact gctr_split _ _ _ _

theorem w_sliceNext {ap : BitVec 64} {A : List Byte} {i : Nat} (hi : i < Cnt s) {st : State}
    (h : S2 s ap i A st) :
    WP isa (.block sliceNext) st fun st' => Mid s ap (i + 1) A st' ∧ st'.zf = some (decide (Cnt s - (i + 1) = 0)) := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have gsl := gl_succ_le hp hi
  obtain ⟨B₂, sr₂, out₂⟩ := h
  refine WP.mono (sliceNext_ok hp hi B₂) fun s₃ ⟨_, z, k, f₃, cs₃, rd₃, wr₃⟩ =>
    ⟨⟨⟨by rw [cs₃ _ (by decide), B₂.rsp], fun r hr => by rw [cs₃ r hr, B₂.saved r hr], rd₃.trans B₂.rd,
      wr₃.trans B₂.wr, k, B₂.frame.trans (frame_kpR f₃)⟩, by omega,
      StreamTo.streamRepr_frame f₃ (one_kpR kpR_stR) sr₂, ?_⟩, z⟩
  rw [← out₂]
  exact bytesAt_frame f₃ (one_kpR ((hp.d_w.symm.sub_left kpR_sub).sub_right
    (Region.sub_prefix (gl_succ s i ▸ gsl)))) (by rw [gl_succ]; omega)

/-- Slice `i`, from `Mid s ap i`: `Mid s ap (i + 1)`, and `ZF` if it was the last. -/
theorem slice_ok (T : ToFn M) {ap : BitVec 64} {A : List Byte} (hap : ap = BitVec.ofNat 64 A.length)
    {i : Nat} (hi : i < Cnt s) {st : State} (h : Mid s ap i A st) :
    WP isa (.seq (.block sliceArgs) (.seq (.frame (.push [.rax, .r10, .rax]) (.call T.fn.name T.fn.code)
      (.pop .rax 3)) (.block sliceNext))) st fun st' =>
      Mid s ap (i + 1) A st' ∧ st'.zf = some (decide (Cnt s - (i + 1) = 0)) :=
  WP.seq (WP.mono (w_sliceArgs hp hi h) fun _ h₁ => WP.seq (WP.mono (w_sliceCall hp T hap hi h₁)
    fun _ h₂ => w_sliceNext hp hi h₂))

/-- The slices, from `Mid s ap 0`: `Mid s ap (Cnt s)`. -/
theorem slices_ok (T : ToFn M) {ap : BitVec 64} {A : List Byte} (hap : ap = BitVec.ofNat 64 A.length) {st : State}
    (h : Mid s ap 0 A st) : WP isa (slices T.fn) st (Mid s ap (Cnt s) A) := by
  unfold slices
  refine WP.seq (WP.mono (w_leftTest hp h) fun s₁ ⟨M₁, z⟩ => ?_)
  refine WP.ite (decide (Cnt s - 0 = 0)) (by simp only [eval, z]) (fun e => ?_) (fun e => ?_)
  · have hC : Cnt s = 0 := by simpa using e
    exact WP.block_nil (hC ▸ M₁)
  have hC : 0 < Cnt s := by simp at e; omega
  refine WP.loop (fun n st => ∃ i, i < Cnt s ∧ n = Cnt s - i ∧ Mid s ap i A st)
    (fun n st ⟨i, hi, hn, hM⟩ => WP.mono (slice_ok hp T hap hi hM) fun st' ⟨hM', z'⟩ => ?_) (Cnt s) s₁
    ⟨0, hC, rfl, M₁⟩
  by_cases e' : Cnt s - (i + 1) = 0
  · exact .inl ⟨by simp [eval, z', e'], (show i + 1 = Cnt s by omega) ▸ hM'⟩
  · exact .inr ⟨by simp [eval, z', e'], Cnt s - (i + 1), by omega, i + 1, by omega, rfl, hM'⟩

/-- The encryption of all the slices, with no text. -/
theorem ct_cnt_nil (hL : L s = 0) : ct s (Cnt s) = [] :=
  List.eq_nil_of_length_eq_zero (by rw [length_ct, hp.glen, hL])

/-- No text: `Fin`. -/
theorem fin_none {st : State} (h : T1 s st) (hL : L s = 0) : Fin s st := by
  refine ⟨AL s, 0, h.1.toBase, ?_, ?_⟩
  · rw [ct_cnt_nil hp hL]; have := h.1.sr; rwa [ct_zero] at this
  · rw [ct_cnt_nil hp hL, hL]; rfl

/-- All the slices, after some text: `Fin`. -/
theorem fin_slices {st : State} (h : Mid s (apP s) (Cnt s) (padA (ad s)) st) (hL : L s ≠ 0) : Fin s st :=
  ⟨_, _, h.toBase, Proof.Gcm.streamRepr_padded (fun hc => hL (by
    rw [← hp.glen, ← length_ct, hc]; rfl)) h.sr, by rw [← hp.glen]; exact h.out⟩

/-- The text: none, or the additional data padded to a whole block, then the
slices. -/
theorem text_ok (A : AadFn) (T : ToFn M) {st : State} (h : Mid s (AL s) 0 (ad s) st) :
    WP isa (text A.fn T.fn) st (Fin s) := by
  unfold text
  refine WP.seq (WP.mono (w_textLen hp h) fun s₁ h₁ => ?_)
  refine WP.ite (decide (L s = 0)) (by simp only [eval, h₁.2.2]) (fun e => ?_) (fun e => ?_)
  · exact WP.block_nil (fin_none hp h₁ (by simpa using e))
  have hL : L s ≠ 0 := by simpa using e
  refine WP.seq (WP.mono (w_padLen hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Q := Mid s (apP s) 0 (padA (ad s))) ?_ fun s₃ M₃ =>
    WP.mono (slices_ok hp T rfl M₃) fun _ M₄ => fin_slices hp M₄ hL)
  refine WP.ite (decide ((AL s).toNat % 16 = 0)) (by simp only [eval, h₂.2.2.2.2]) (fun e₂ => ?_) (fun e₂ => ?_)
  · exact WP.block_nil (pad_none h₂ (by simpa using e₂))
  have hr : (AL s).toNat % 16 ≠ 0 := by simpa using e₂
  exact WP.seq (WP.mono (w_padArgs hp h₂) fun _ h₃ => w_padCall hp A h₃ hr)

theorem w_finArgs {st : State} (h : Fin s st) : WP isa (.block finArgs) st (P7 s) := by
  obtain ⟨ap, i, B, sr, out⟩ := h
  exact WP.mono (finArgs_ok hp B) fun _ ⟨di, si, dx, cx, r8, r9, cs, m, rd, wr⟩ =>
    ⟨⟨ap, i, B.regs m cs rd wr, m ▸ sr, m ▸ out⟩, di, si, dx, cx, r8, r9⟩

theorem w_fin (F : FinFn) {st : State} (h : P7 s st) : WP isa (.call F.fn.name F.fn.code) st (Done s) := by
  obtain ⟨⟨ap, i, B₇, sr₆, out₆⟩, di, si, dx, cx, r8, r9⟩ := h
  have hC : (ct s (Cnt s)).length = L s := by rw [length_ct, hp.glen]
  refine WP.mono (finCall_ok hp F B₇ sr₆ hC di si dx cx r8 r9) fun s₈ ⟨B₈, f₈, tag⟩ => ?_
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hdst : bytesAt s₈.mem (Dst s) (L s) = ct s (Cnt s) := by
    rw [← out₆]
    refine bytesAt_frame f₈ (fun r hr => ?_) (Nat.le_of_lt hL)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.d_w.sub_right stR_sub
    · exact hp.d_t
    · exact hp.b_d.symm
  refine ⟨⟨B₈.saved, B₈.frame.readW (Region.contains_self _ _) (ret_disj hp) (by decide)⟩, ?_⟩
  show Spec.Gcm.encryptWith (ciph s) (hk s) 16 (iv s) (pt s (Cnt s)) (ad s) =
    (bytesAt s₈.mem (Dst s) (L s), bytesAt s₈.mem (Tg s) 16)
  rw [Proof.Gcm.encryptWith_eq, hdst, tag]

/-- `vg_aes_gcm_seal_gather`, calling `I`, `A`, `T` and `F`. -/
theorem sealGather_wp (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn) :
    WP isa (sealGather I.fn A.fn T.fn F.fn) s (Done s) := by
  unfold sealGather
  exact WP.seq (WP.mono (entry1_ok hp) fun _ h₁ => WP.seq (WP.mono (w_entry2 hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (w_init hp I h₂) fun _ h₃ => WP.seq (WP.mono (w_aadArgs hp h₃) fun _ h₄ =>
      WP.seq (WP.mono (w_aad hp A h₄) fun _ h₅ => WP.seq (WP.mono (text_ok hp A T h₅) fun _ h₆ =>
        WP.seq (WP.mono (w_finArgs hp h₆) fun _ h₇ => w_fin hp F h₇)))))))

end

end VG.Proof.AesGcm.X86_64.Gather
