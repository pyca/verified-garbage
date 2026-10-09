import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.OpenVerified

/-!
# ChaCha20 and Poly1305 together (x86-64): `bulkO` is constant time

As `bulk_rel`: the taint analysis checks `enter`, each chunk and `leaveO`,
with only the pointers public; the loop's condition agrees in two runs by
correctness (`LO`).
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Spec.Poly1305 (bytesAt)

/-- Before chunk `t` of `open`, for some key and entry. -/
def CO (c dp : Addr) (L : Nat) (sp : Addr) (t : Nat) (s : State) : Prop :=
  ∃ R0 R1 A m₀, Key R0 R1 ∧ LO c dp L R0 R1 A m₀ sp t s

theorem FC.co {c dp : Addr} {L : Nat} {sp : Addr} {s : State} (h : FC c dp L sp s) : CO c dp L sp 0 s := by
  obtain ⟨R0, R1, A, hk, rd, wr, rdi, rcx, rsi, rsp, sl, C, acc⟩ := h
  refine ⟨R0, R1, A, s.mem, hk, rd, wr, rdi, rcx, by rw [rsi]; simp, rsp, Nat.zero_le _,
    by rw [sl, Nat.mul_zero, Nat.sub_zero], by simp [VG.Proof.ChaCha20.ctr_zero], fun k _ => by simp, C, ?_,
    Frame.refl _ _⟩
  rw [show 512 * 0 = 0 from rfl, show bytesAt s.mem dp 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
  exact acc

theorem chunkO_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) chunkO h).isSome = true := by
  taint_decide_sum []

theorem leaveO_taint : ∃ h, (taintS.check (τR [.rcx, .rsi, .rsp]) (.block leaveO) h).isSome = true := by
  taint_decide_sum []

section
variable {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) (sp : Addr)
include hl hge

/-- The chunks, while at least 512 bytes remain. -/
theorem loopO_rel :
    RelCT isa (fun s₁ s₂ => CO c dp L sp 0 s₁ ∧ CO c dp L sp 0 s₂) (.loop chunkO .ae)
      fun s₁ s₂ => ∃ T, CO c dp L sp T s₁ ∧ CO c dp L sp T s₂ ∧ L - 512 * T < 512 := by
  obtain ⟨_, hc⟩ := chunkO_taint
  let I : Nat → State → State → Prop := fun n s₁ s₂ =>
    ∃ t, n = L - 512 * t ∧ 512 ≤ L - 512 * t ∧ CO c dp L sp t s₁ ∧ CO c dp L sp t s₂
  have body : ∀ t, RelCT isa (fun s₁ s₂ => 512 ≤ L - 512 * t ∧ CO c dp L sp t s₁ ∧ CO c dp L sp t s₂) chunkO
      fun s₁ s₂ => (CO c dp L sp (t + 1) s₁ ∧ s₁.cf = some (decide (L - 512 * (t + 1) < 512))) ∧
        (CO c dp L sp (t + 1) s₂ ∧ s₂.cf = some (decide (L - 512 * (t + 1) < 512))) := by
    intro t
    have step : ∀ {s}, 512 ≤ L - 512 * t → CO c dp L sp t s → WP isa chunkO s fun s' =>
        CO c dp L sp (t + 1) s' ∧ s'.cf = some (decide (L - 512 * (t + 1) < 512)) :=
      fun hge' ⟨R0, R1, A, m₀, hk, hL⟩ => WP.mono (chunkO_ok hl hk hge' hL) fun s' ⟨hL', cf'⟩ =>
        ⟨⟨R0, R1, A, m₀, hk, hL'⟩, cf'⟩
    refine ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hc).wp
      fun _ _ h => ⟨step h.1 h.2.1, step h.1 h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    obtain ⟨-, ⟨_, _, _, _, _, h₁⟩, ⟨_, _, _, _, _, h₂⟩⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.rdi, h₂.rdi]
    · rw [h₁.rcx, h₂.rcx]
    · rw [h₁.rsi, h₂.rsi]
    · rw [h₁.rsp, h₂.rsp]
  refine (RelCT.loop (Q := fun s₁ s₂ => ∃ T, CO c dp L sp T s₁ ∧ CO c dp L sp T s₂ ∧ L - 512 * T < 512) I
    (fun n => ?_) (L - 512 * 0)).mono (fun _ _ h => ⟨0, rfl, by omega, h.1, h.2⟩) (fun _ _ h => h)
  refine (RelCT.exists_ (P := fun (x : {t // n = L - 512 * t ∧ 512 ≤ L - 512 * t}) s₁ s₂ =>
    CO c dp L sp x.1 s₁ ∧ CO c dp L sp x.1 s₂) fun ⟨t, hn, hge'⟩ => ?_).mono
    (fun _ _ ⟨t, hn, hge', h₁, h₂⟩ => ⟨⟨t, hn, hge'⟩, h₁, h₂⟩) (fun _ _ h => h)
  refine ((body t).mono (fun _ _ h => ⟨hge', h.1, h.2⟩) fun _ _ h => h).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨⟨h₁, c₁⟩, ⟨h₂, c₂⟩⟩
  refine ⟨by simp only [eval, c₁, c₂], fun hf => ?_, fun ht => ?_⟩
  · refine ⟨t + 1, h₁, h₂, ?_⟩
    by_contra hc
    simp [eval, c₁, hc] at hf
  · have : ¬ L - 512 * (t + 1) < 512 := fun hc => by simp [eval, c₁, hc] at ht
    exact ⟨L - 512 * (t + 1), by omega, t + 1, rfl, by omega, h₁, h₂⟩

/-- `bulkO`, with its permissions. -/
theorem bulkO_rel :
    RelCT isa (fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂) bulkO fun _ _ => True := by
  unfold bulkO
  obtain ⟨_, hE⟩ := enter_taint
  obtain ⟨_, hL⟩ := leaveO_taint
  have e := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂)
    (τR [.rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hE).wp
    (F₁ := CO c dp L sp 0) (F₂ := CO c dp L sp 0)
    fun _ _ h => ⟨WP.mono (enter_fc h.1) fun _ h => h.co, WP.mono (enter_fc h.2) fun _ h => h.co⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  · have lv := (RelCT.taint (A := taintS)
      (P := fun s₁ s₂ => ∃ T, CO c dp L sp T s₁ ∧ CO c dp L sp T s₂ ∧ L - 512 * T < 512)
      (τR [.rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hL)
    · exact e.seq ((loopO_rel hl hge sp).seq lv)
    · obtain ⟨T, ⟨_, _, _, _, _, h₁⟩, ⟨_, _, _, _, _, h₂⟩, -⟩ := h
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.rcx, h₂.rcx]
      · rw [h₁.rsi, h₂.rsi]
      · rw [h₁.rsp, h₂.rsp]
  · obtain ⟨⟨_, _, rsi₁, _, rcx₁, rsp₁, -⟩, ⟨_, _, rsi₂, _, rcx₂, rsp₂, -⟩⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [rcx₁, rcx₂]
    · rw [rsi₁, rsi₂]
    · rw [rsp₁, rsp₂]

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `openStitched` is constant time

As `open_rel`. `cryptO`'s branch for at most `fold` bytes is `open`'s code,
checked as before. With more, `cryptArgs` is checked; `bulkO` is constant
time by `bulkO_rel` (moved to `open`'s permissions by `relCT_narrow`), or
`whole` is checked; the rest's `macPadLengths` and `restArgs` are checked
with `rbx`, `rbp` public, functions of the public length (`PubM`); and the
call of `vg_chacha20_xor` on the rest by the implementation's own proof.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

/-! ## The parts of the code -/

/-- `cryptO`'s branch for at most `fold` bytes. -/
def smallO (b : Impl.Poly1305.X86_64.Blocks) : Prog isa := .seq (macPadLengths b .r14 .r13) cryptSmall

/-- `cryptO`'s branch for more. -/
def bigO (x : Impl.ChaCha20.X86_64.Callee) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
    (.seq (.ite .b (.block whole) bulkO)
    (.seq (macPadLengths b .rbx .rbp) (.seq (.block restArgs) (.call x.name x.code))))

def iteO (x : Impl.ChaCha20.X86_64.Callee) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .ite .b (smallO b) (bigO x b)

theorem openS_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa (openStitched x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA x.fold) (.seq (.call x.name x.code)
      (.seq (sealMid x.fold b) (.seq (iteO x b) (openPost x.fold)))))) s t s' := by
  cases h with | seq e₀ h => cases h with | seq hP h => cases hP with | seq ePA hP => cases hP with
  | seq eC ePB => cases h with | seq eMA h => cases h with | seq eLEN h => cases h with | seq hC h =>
  cases hC with | seq eCMP hC => cases hC with | seq eITE hC => cases hC with | seq eANC hC =>
  cases hC with | seq eFM hC => cases hC with | seq eADD eZK => cases h with | seq eFIN eCR =>
  have := Exec.seq e₀ (Exec.seq ePA (Exec.seq eC (Exec.seq (Exec.seq ePB (Exec.seq eMA (Exec.seq eLEN eCMP)))
    (Exec.seq eITE (Exec.seq (Exec.seq eANC (Exec.seq eFM (Exec.seq eADD eZK))) (Exec.seq eFIN eCR))))))
  simp only [List.append_assoc] at this ⊢
  exact this

/-! ## What holds where -/

/-- After `cryptArgs` and the comparison with 512, in one run. -/
def AtArgsO (fold : Nat) (s₀ s : State) : Prop :=
  ∃ σ, AtIteS fold s₀ σ ∧ Args s₀ σ s ∧ s.gpr .r15 = σ.gpr .r15 ∧ s.cf = some (decide (L s₀ < 512))

/-- After the branch on 512 bytes. -/
def MidSO (s₀ s : State) : Prop := ∃ σ key msg E, Inv s₀ σ ∧ MidO s₀ σ key msg E s

/-- After the rest's `macPadLengths`. -/
def MacDone (s₀ s : State) : Prop :=
  Inv s₀ s ∧ s.gpr .rbx = dp s₀ + BitVec.ofNat 64 (Eof (L s₀)) ∧ s.gpr .rbp = BitVec.ofNat 64 (L s₀ - Eof (L s₀))

/-- The public registers of those two: the context, the data and its rest. -/
structure PubM (s₀ s : State) : Prop where
  r15 : s.gpr .r15 = cx s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r9
  r14 : s.gpr .r14 = dp s₀
  r12 : s.gpr .r12 = tp s₀
  rbx : s.gpr .rbx = dp s₀ + BitVec.ofNat 64 (Eof (L s₀))
  rbp : s.gpr .rbp = BitVec.ofNat 64 (L s₀ - Eof (L s₀))
  wr : s.wr = s₀.wr

theorem MidSO.pub {s₀ s : State} (h : MidSO s₀ s) : PubM s₀ s := by
  obtain ⟨σ, key, msg, E, hi, hm⟩ := h
  have hE : E = Eof (L s₀) := hm.Ediv
  exact ⟨by rw [hm.keep _ (.inr (.inr (.inr (.inl rfl)))), hi.r15],
    by rw [hm.keep _ (.inr (.inr (.inr (.inr rfl)))), hi.rsp], by rw [hm.keep _ (.inr (.inl rfl)), hi.r13],
    by rw [hm.keep _ (.inr (.inr (.inl rfl))), hi.r14], by rw [hm.keep _ (.inl rfl), hi.r12],
    by rw [hm.rbx, hE], by rw [hm.rbp, hE], by rw [hm.wr, hi.wr]⟩

theorem MacDone.pub {s₀ s : State} (h : MacDone s₀ s) : PubM s₀ s :=
  ⟨h.1.r15, h.1.rsp, h.1.r13, h.1.r14, h.1.r12, h.2.1, h.2.2, h.1.wr⟩

/-- Before the call on the rest. -/
structure XO (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = off (cx s₀) 64
  rsi : s.gpr .rsi = dp s₀ + BitVec.ofNat 64 (Eof (L s₀))
  rdx : s.gpr .rdx = BitVec.ofNat 64 (L s₀ - Eof (L s₀))
  rcx : s.gpr .rcx = off (cx s₀) 128
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r9
  r14 : s.gpr .r14 = dp s₀
  r12 : s.gpr .r12 = tp s₀
  wr : s.wr = s₀.wr

/-- As `τS`, with `rbx` and `rbp` public. -/
def τM (enc : Bool) : X86_64.Taint.T :=
  { regs := .ofList [.r15, .rsp, .r13, .r14, .r12, .rbx, .rbp], flags := false, lens := lensOf enc,
    bases := [(.r15, ci enc, 0), (.r14, 0, 0)] }

section
variable {s₀ s₀' : State} (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀')

omit hp' hq in
include hp in
theorem PubM.wf {s : State} (h : PubM s₀ s) : X86_64.Taint.Wf (τM e) s := by
  have hw : s.wr = bif e then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀] := by rw [h.wr, hp.wr_eq]
  refine ⟨fun _ => regions_wf hp h.wr, fun p hm => ?_⟩
  simp only [τM, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;>
    simp only [X86_64.Taint.region, hw, h.r15, h.r14] <;> cases e <;> simp

include hp hp' hq in
theorem agreeM {s₁ s₂ : State} (h₁ : PubM s₀ s₁) (h₂ : PubM s₀' s₂) : X86_64.Taint.Agree (τM e) s₁ s₂ := by
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, p8, p9⟩ := hq'
  obtain ⟨c, d, t⟩ := pub_regs hq
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, h₁.wf hp, h₂.wf hp', ?_, ?_, X86_64.Taint.noLo,
    X86_64.Taint.noXr⟩
  · simp only [τM, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.r15, h₂.r15, cx, cx, p9]
    · rw [h₁.rsp, h₂.rsp, p7]
    · rw [h₁.r13, h₂.r13, p6]
    · rw [h₁.r14, h₂.r14, dp, dp, p5]
    · rw [h₁.r12, h₂.r12, tp, tp, p8]
    · rw [h₁.rbx, h₂.rbx, dp, dp, p5, L, L, p6]
    · rw [h₁.rbp, h₂.rbp, L, L, p6]
  · rw [h₁.wr, h₂.wr, hp.wr_eq, hp'.wr_eq, c, d, t]
  · intro sl h; simp [τM] at h
  · intro sl h; simp [τM] at h

omit hp' hq in
include hp in
theorem XO.hw {s : State} (h : XO s₀ s) : Covers (xR s₀) s.wr := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 64, by simp [off_eq], by show 64 + 64 ≤ 1696; omega⟩
  · exact ⟨dR s₀, by rw [h.wr]; exact hp.d_wr, Eof (L s₀), rfl, by show Eof (L s₀) + (L s₀ - Eof (L s₀)) ≤ L s₀; omega⟩
  · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 128, by simp [off_eq], by show 128 + 320 ≤ 1696; omega⟩

omit hp' hq in
include hp in
theorem XO.pre (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} (h : XO s₀ s) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] (xR s₀)) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (Eof (L s₀)), L s₀ - Eof (L s₀)⟩ (dR s₀) :=
    Offset.sub_base _ (by omega)
  exact xor_pre v h.rdi h.rsi h.rdx h.rcx (by omega)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ _ (by omega)) _) (by have := hp.wrap_d; omega))
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_d.sub_right dsub)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega))

omit hp' hq in
include hp in
theorem XO.call (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} (h : XO s₀ s) :
    WP isa (.call v.callee.name v.callee.code) s (After s₀) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (Eof (L s₀)), L s₀ - Eof (L s₀)⟩ (dR s₀) :=
    Offset.sub_base _ (by omega)
  refine xor_call v h.rdi h.rsi h.rdx h.rcx (by omega)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ _ (by omega)) _) (by have := hp.wrap_d; omega))
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_d.sub_right dsub)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (Covers.right (h.hw hp)) (h.hw hp)
    fun s' _ wr' cs' _ rsi' _ => ⟨rsi', by rw [cs' _ calleeSaved_rsp, h.rsp],
      by rw [cs' _ (by simp [calleeSaved]), h.r13], by rw [cs' _ (by simp [calleeSaved]), h.r14],
      by rw [cs' _ (by simp [calleeSaved]), h.r12], by rw [wr', h.wr]⟩

end

/-! ## Each run -/

theorem smallO_after (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : AtIteS v.callee.fold s₀ s) (hle : L s₀ ≤ v.callee.fold) : WP isa (smallO v.poly) s (After s₀) := by
  obtain ⟨hi, -, key, msg, hrep⟩ := h
  exact WP.mono (smallO_ok v hp hi.inv hle hi.ks hrep) fun s' c =>
    ⟨c.rsi, by rw [c.keep _ (.inr (.inr (.inr rfl))), hi.inv.rsp], by rw [c.keep _ (.inr (.inl rfl)), hi.inv.r13],
      by rw [c.keep _ (.inr (.inr (.inl rfl))), hi.inv.r14], by rw [c.keep _ (.inl rfl), hi.inv.r12],
      by rw [c.wr, hi.inv.wr]⟩

theorem argsO_at {fold : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtIteS fold s₀ s) :
    WP isa (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) s (AtArgsO fold s₀) :=
  WP.mono (argsCmpO_ok hp h.1.inv) fun _ ⟨ha, h15, cf⟩ => ⟨_, h, ha, h15, cf⟩

theorem wholeO_mid {fold : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtArgsO fold s₀ s)
    (hb : isa.eval .b s = some true) : WP isa (.block whole) s (MidSO s₀) := by
  obtain ⟨σ, ⟨hi, hst, key, msg, hrep⟩, ha, h15, cf⟩ := h
  simp only [eval, cf, Option.some.injEq, decide_eq_true_eq] at hb
  exact WP.mono (whole_midO hp ha h15 hb hst hrep) fun _ hm => ⟨σ, key, msg, 0, hi.inv, hm⟩

theorem bulkO_mid {fold : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtArgsO fold s₀ s)
    (hb : isa.eval .b s = some false) : WP isa bulkO s (MidSO s₀) := by
  obtain ⟨σ, ⟨hi, hst, key, msg, hrep⟩, ha, -, cf⟩ := h
  simp only [eval, cf, Option.some.injEq, decide_eq_false_iff_not] at hb
  exact WP.mono (bulk_midO hp hi.inv.wr ha hi.inv.r15 (by omega) hst hrep)
    fun _ ⟨E, hm⟩ => ⟨σ, key, msg, E, hi.inv, hm⟩

theorem macO_done (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : MidSO s₀ s) : WP isa (macPadLengths b .rbx .rbp) s (MacDone s₀) := by
  obtain ⟨σ, key, msg, E, hi, hm⟩ := h
  have hE : E = Eof (L s₀) := hm.Ediv
  have i : Inv s₀ s := Inv.step' hi hm.keep hm.rd hm.wr hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  exact WP.mono (macPadLengths_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcRest hp hm.EL) i
    hm.rbx hm.rbp) fun _ ⟨i', cs', _⟩ => ⟨i', by rw [cs' _ (by simp [calleeSaved]), hm.rbx, hE],
      by rw [cs' _ (by simp [calleeSaved]), hm.rbp, hE]⟩

theorem restO_x {s₀ : State} {s : State} (h : MacDone s₀ s) : WP isa (.block restArgs) s (XO s₀) :=
  WP.mono (restArgs_ok (s₀ := s₀) h.1.r15) fun _ ⟨rdi, rsi, rdx, rcx, g, _, wr, _⟩ =>
    ⟨rdi, by rw [rsi, h.2.1], by rw [rdx, h.2.2], rcx,
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.1.rsp],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.1.r13],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.1.r14],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.1.r12], by rw [wr, h.1.wr]⟩

/-! ## The taint analyses -/

theorem midO_taint {fold : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold b) :
    ∃ h, (taintS.check (τA false) (sealMid fold b) h).isSome = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksBigAvx2O, blocksBigAvx512O]

theorem smallO_taint {fold : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold b) :
    ∃ h, (taintS.check (τS false) (smallO b) h).isSome = true := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksSmallO, blocksBigAvx2O, blocksSmallAvx2O, blocksBigAvx512O,
      blocksSmallAvx512O]

theorem argsO_taint :
    ∃ h, (taintS.check (τS false) (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) h).isSome =
      true := by
  taint_decide_sum []

theorem macO_taint {fold : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold b) :
    ∃ h, (taintS.check (τM false) (macPadLengths b .rbx .rbp) h).isSome = true := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksSmallO, blocksBigAvx2O, blocksSmallAvx2O, blocksBigAvx512O,
      blocksSmallAvx512O]

theorem restO_taint : ∃ h, (taintS.check (τM false) (.block restArgs) h).isSome = true := by
  taint_decide_sum []

/-! ## The branch with more than `fold` bytes -/

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State} (hp : APre false s₀) (hp' : APre false s₀')
  (hq : pubX86_64 s₀ s₀')
include hp hp' hq

theorem bigO_rel :
    RelCT isa (fun s₁ s₂ => (AtIteS v.callee.fold s₀ s₁ ∧ AtIteS v.callee.fold s₀' s₂) ∧
      isa.eval .b s₁ = some false) (bigO v.callee v.poly) fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, -, p9⟩ := hq'
  have eL : L s₀' = L s₀ := by simp only [L, p6]
  have ec : cx s₀' = cx s₀ := by simp only [cx, p9]
  have ed : dp s₀' = dp s₀ := by simp only [dp, p5]
  obtain ⟨_, hA⟩ := argsO_taint
  obtain ⟨_, hW⟩ := whole_taint
  obtain ⟨_, hM⟩ := macO_taint v.fold_poly
  obtain ⟨_, hR⟩ := restO_taint
  have args := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtIteS v.callee.fold s₀ s₁ ∧
      AtIteS v.callee.fold s₀' s₂) ∧ isa.eval .b s₁ = some false) (τS false)
      (fun _ _ h => agreeS hp hp' hq h.1.1.1 h.1.2.1) hA).wp
    (F₁ := AtArgsO v.callee.fold s₀) (F₂ := AtArgsO v.callee.fold s₀') fun _ _ h =>
      ⟨argsO_at hp h.1.1, argsO_at hp' h.1.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hcf : ∀ s₁ s₂, (AtArgsO v.callee.fold s₀ s₁ ∧ AtArgsO v.callee.fold s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    obtain ⟨⟨_, -, -, -, c₁⟩, ⟨_, -, -, -, c₂⟩⟩ := h
    simp only [eval, c₁, c₂, eL]
  have wh := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtArgsO v.callee.fold s₀ s₁ ∧
      AtArgsO v.callee.fold s₀' s₂) ∧ isa.eval .b s₁ = some true) (τR [])
      (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hW).wp
    (F₁ := MidSO s₀) (F₂ := MidSO s₀') fun _ _ h => ⟨wholeO_mid hp h.1.1 h.2,
      wholeO_mid hp' h.1.2 (by rw [← hcf _ _ h.1]; exact h.2)⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hl : Lay (cx s₀) (dp s₀) (L s₀) :=
    ⟨(s₀.gpr .r9).isLt, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have bk : RelCT isa (fun s₁ s₂ => (AtArgsO v.callee.fold s₀ s₁ ∧ AtArgsO v.callee.fold s₀' s₂) ∧
      isa.eval .b s₁ = some false) bulkO fun s₁ s₂ => MidSO s₀ s₁ ∧ MidSO s₀' s₂ := by
    by_cases hge : 512 ≤ L s₀
    · refine ((relCT_narrow (c := bulkO) (fun _ => bulkWr (cx s₀) (dp s₀) (L s₀)) ?_
        (bulkO_rel hl hge (s₀.gpr .rsp))).wp (F₁ := MidSO s₀) (F₂ := MidSO s₀') ?_).mono (fun _ _ h => h)
        fun _ _ h => h.2
      · rintro s₁ s₂ ⟨⟨⟨σ₁, ⟨hi₁, -, key₁, msg₁, hrep₁⟩, ha₁, -⟩, ⟨σ₂, ⟨hi₂, -, key₂, msg₂, hrep₂⟩, ha₂, -⟩⟩, -⟩
        have b₁ := bulk_bp ha₁ hi₁.inv hrep₁
        have b₂ := bulk_bp ha₂ hi₂.inv hrep₂
        rw [ec, ed, eL, ← p7] at b₂
        obtain ⟨rd₁, wr₁, rsi₁, rdx₁, rcx₁, -, _, _, r₁⟩ := id b₁
        obtain ⟨rd₂, wr₂, rsi₂, rdx₂, rcx₂, -, _, _, r₂⟩ := id b₂
        exact ⟨bulk_covers hp (by rw [ha₁.wr, hi₁.inv.wr]), by
          rw [← ec, ← ed, ← eL]; exact bulk_covers hp' (by rw [ha₂.wr, hi₂.inv.wr]),
          ⟨_, bulkO_ok hl hge rd₁ wr₁ rsi₁ rdx₁ rcx₁ r₁⟩, ⟨_, bulkO_ok hl hge rd₂ wr₂ rsi₂ rdx₂ rcx₂ r₂⟩, b₁, b₂⟩
      · exact fun _ _ h => ⟨bulkO_mid hp h.1.1 h.2, bulkO_mid hp' h.1.2 (by rw [← hcf _ _ h.1]; exact h.2)⟩
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, _, c₁⟩, _⟩, hb⟩ => ?_
      simp only [eval, c₁, Option.some.injEq, decide_eq_false_iff_not] at hb
      omega
  have mac := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => MidSO s₀ s₁ ∧ MidSO s₀' s₂) (τM false)
      (fun _ _ h => agreeM hp hp' hq h.1.pub h.2.pub) hM).wp
    (F₁ := MacDone s₀) (F₂ := MacDone s₀') fun _ _ h =>
      ⟨macO_done v.poly hp h.1, macO_done v.poly hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have rest := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => MacDone s₀ s₁ ∧ MacDone s₀' s₂) (τM false)
      (fun _ _ h => agreeM hp hp' hq h.1.pub h.2.pub) hR).wp
    (F₁ := XO s₀) (F₂ := XO s₀') fun _ _ h => ⟨restO_x h.1, restO_x h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have call := (RelCT.callEx (n := v.callee.name) (P := fun s₁ s₂ => XO s₀ s₁ ∧ XO s₀' s₂) v.ok v.ct
    fun s₁ s₂ ⟨m₁, m₂⟩ => ⟨[], _, [], _, m₁.pre hp v, m₂.pre hp' v, ?_, Covers.right (m₁.hw hp),
      m₁.hw hp, Covers.right (m₂.hw hp'), m₂.hw hp', by rw [m₁.rsp, m₂.rsp, p7]⟩).wp
    (F₁ := After s₀) (F₂ := After s₀') fun _ _ h => ⟨h.1.call hp v, h.2.call hp' v⟩
  · exact args.seq ((RelCT.ite hcf wh bk).seq (mac.seq (rest.seq (call.mono (fun _ _ h => h) fun _ _ h => h.2))))
  · simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
      State.callEntry_rsp, callEntry_gpr' s₁ (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s₁ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₁ (by decide : Reg.rdx ≠ .rsp),
      callEntry_gpr' s₁ (by decide : Reg.rcx ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s₂ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdx ≠ .rsp),
      callEntry_gpr' s₂ (by decide : Reg.rcx ≠ .rsp), m₁.rdi, m₁.rsi, m₁.rdx, m₁.rcx, m₁.rsp, m₂.rdi, m₂.rsi,
      m₂.rdx, m₂.rcx, m₂.rsp, eL, ec, ed, p7]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end

/-! ## `openStitched` -/

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State}

theorem openS_rel (h₀ : preX86_64 false s₀) (h₀' : preX86_64 false s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (openStitched v.callee v.poly) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  have hfl := v.fold_le
  obtain ⟨_, hA⟩ := prologueA_taint false v.fold_poly
  obtain ⟨_, hmid⟩ := midO_taint v.fold_poly
  obtain ⟨_, hS⟩ := smallO_taint v.fold_poly
  obtain ⟨_, hpost⟩ := openPost_taint v.fold_poly
  have pA := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ false)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq) hA).wp
    (F₁ := FArgs v.callee.fold s₀) (F₂ := FArgs v.callee.fold s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok hfl hp, by rw [h.2]; exact prologueA_ok hfl hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have mid := ((RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => AfterF v.callee.fold s₀ s₁ ∧ AfterF v.callee.fold s₀' s₂) (τA false)
    (fun _ _ h => agreeA hp hp' hq h.1 h.2) hmid).wp (F₁ := AtIteS v.callee.fold s₀)
    (F₂ := AtIteS v.callee.fold s₀') fun _ _ h =>
      ⟨sealMidS_ok hfl v.poly hp h.1, sealMidS_ok hfl v.poly hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hc : ∀ s₁ s₂, (AtIteS v.callee.fold s₀ s₁ ∧ AtIteS v.callee.fold s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    have : L s₀ = L s₀' := by simp only [L, hq.2.2.2.2.2.1]
    simp [eval, h.1.1.cf, h.2.1.cf, this]
  have small := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteS v.callee.fold s₀ s₁ ∧ AtIteS v.callee.fold s₀' s₂) ∧ isa.eval .b s₁ = some true)
    (τS false) (fun _ _ h => agreeS hp hp' hq h.1.1.1 h.1.2.1) hS).wp (F₁ := After s₀) (F₂ := After s₀')
    fun s₁ s₂ h => by
      have e₁ := h.2
      have e₂ := (hc _ _ h.1).symm.trans h.2
      simp only [eval, h.1.1.1.cf, h.1.2.1.cf, Option.some.injEq, decide_eq_true_eq] at e₁ e₂
      exact ⟨smallO_after v hp h.1.1 (by omega), smallO_after v hp' h.1.2 (by omega)⟩
  have ite := RelCT.ite hc (small.mono (fun _ _ h => h) fun _ _ h => h.2) (bigO_rel v hp hp' hq)
  have post := RelCT.taint (A := taintS) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) (τ₁ false)
    (fun _ _ h => agree₁ hp hp' hq h.1 h.2) hpost
  have := (entry_rel hp hp' hq).seq (pA.seq ((call1_rel hp hp' hq v).seq (mid.seq (ite.seq post))))
  exact RelCT.of_exec openS_exec this

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `openStitched` and `openFor`, `Verified`

`openStitched` against `open`'s contracts, as `open_verified` and
`open_framed` (`../Verified.lean`), and `openFor`, which instances use.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch

theorem openS_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (openStitched v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases v.fold_poly with ⟨hf, hb⟩ | ⟨hf, hb⟩ | ⟨hf, hb⟩ <;>
    (simp only [openStitched, prologue, cryptO, Code.all, v.spSafe, hf, hb]; decide +kernel)

theorem openS_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa (openStitched v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' :=
  openStitched_correct v (APre.of s hs)

theorem openS_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa openX86_64.pre openX86_64.pub (openStitched v.callee v.poly) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (openS_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem openS_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target (openStitched v.callee v.poly) (openScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (openS_ok v) (openS_ct v)
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, X86_64.argRegs]
        simp only [Proof.ChaCha20Poly1305.openX86_64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openX86_64, Proof.ChaCha20Poly1305.preX86_64,
          Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
          List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
          [openSat] using openSat }

theorem bulkO_xdepth : bulkO.x86_64Depth = 0 := by decide +kernel

theorem openS_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) :
    (openStitched v.callee v.poly).x86_64Depth ≤ 24 := by
  have hx := v.xdepth
  have hb := blocks_xdepth v.poly
  simp only [openStitched, prologue, prologueA, prologueB, foldM, zeroKs, macPad, macPadLengths, wholeBlocks,
    padTail, cryptO, absorbLengths, finalizeTo, finalizeWith, Code.x86_64Depth, xorBuf_xdepth, init_xdepth,
    finalize_xdepth, bulkO_xdepth, Nat.max_le]
  omega

theorem openS_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 (openStitched v.callee v.poly))
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 1744) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1720) (k := 42) (openS_verified v) (by decide) (by decide) (by decide)
    (openS_spSafe v) (openS_xdepth v) (by decide) (pre_local _ _) (openPost_local _) (openPost_out _)
    openFrameSat_pre

/-! ## The `open` of an instance -/

theorem openFor_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (openFor v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h₁ := open_spSafe v
  have h₂ := openS_spSafe v
  generalize v.poly = b at h₁ h₂ ⊢
  cases b
  · exact h₁
  · exact h₂
  · exact h₁

theorem openFor_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 (openFor v.callee v.poly))
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 1744) := by
  have h₁ := open_framed v
  have h₂ := openS_framed v
  generalize v.poly = b at h₁ h₂ ⊢
  cases b
  · exact h₁
  · exact h₂
  · exact h₁

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
