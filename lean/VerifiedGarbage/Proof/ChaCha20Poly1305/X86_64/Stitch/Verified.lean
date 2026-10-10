import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Crypt
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified

/-!
# ChaCha20 and Poly1305 together (x86-64): `bulk` is constant time

The taint analysis checks `enter`, each chunk and `leave` on their own, with
only the pointers public; the loop's condition, which the analysis cannot
see is public (it compares the number of bytes left, kept in memory, with
512), agrees in two runs by correctness: it is a function of the length
(`LI`). `bulk_rel` is stated with `bulk`'s permissions (`bulkWr`), and
`relCT_narrow` moves it to `seal`'s.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts)
open VG.Proof.Poly1305.X86_64 (hval off)
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)

/-- Only the registers `rs` public. -/
abbrev τR (rs : List Reg) : X86_64.Taint.T := { regs := .ofList rs, flags := false }

theorem agree_regs (rs : List Reg) {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    X86_64.Taint.Agree (τR rs) s₁ s₂ :=
  ⟨⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩, fun h => absurd rfl h,
    ⟨fun h => absurd rfl h, fun _ hp => by simp at hp⟩, ⟨fun h => absurd rfl h, fun _ hp => by simp at hp⟩,
    fun _ h => by simp at h, fun _ h => by simp at h, X86_64.Taint.noLo, X86_64.Taint.noXr⟩

/-- Constant time on narrowed permissions: runs from states narrowed to the
regions `W` (which code that terminates from them writes in) leak the same
traces as from the states themselves. -/
theorem relCT_narrow {c : Prog isa} {Pr Pn : State → State → Prop} (W : State → List Region)
    (hw : ∀ s₁ s₂, Pr s₁ s₂ → Covers (W s₁) s₁.wr ∧ Covers (W s₂) s₂.wr ∧
      (∃ F, WP isa c (s₁.withRegions [] (W s₁)) F) ∧ (∃ F, WP isa c (s₂.withRegions [] (W s₂)) F) ∧
      Pn (s₁.withRegions [] (W s₁)) (s₂.withRegions [] (W s₂)))
    (h : RelCT isa Pn c fun _ _ => True) : RelCT isa Pr c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨w₁, w₂, ⟨_, u₁, n₁, en₁, -⟩, ⟨_, u₂, n₂, en₂, -⟩, hn⟩ := hw _ _ hp
  obtain ⟨x₁, -⟩ := regionModel.inline (s := s₁) (r := []) (w := W s₁) en₁ (Covers.right w₁) w₁
  obtain ⟨x₂, -⟩ := regionModel.inline (s := s₂) (r := []) (w := W s₂) en₂ (Covers.right w₂) w₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ x₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ x₂
  exact ⟨(h _ _ _ _ _ _ hn en₁ en₂).1, trivial⟩

/-- The state `bulk` starts from. -/
def BP (c dp : Addr) (L : Nat) (sp : Addr) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = bulkWr c dp L ∧ s.gpr .rsi = dp ∧ s.gpr .rdx = BitVec.ofNat 64 L ∧
    s.gpr .rcx = bfA c ∧ s.gpr .rsp = sp ∧ ∃ key msg, Repr s.mem (psA c) key msg

/-- After `enter`: what the first chunk needs. -/
def FC (c dp : Addr) (L : Nat) (sp : Addr) (s : State) : Prop :=
  ∃ R0 R1 A, Key R0 R1 ∧ s.rd = [] ∧ s.wr = bulkWr c dp L ∧ s.gpr .rdi = stA c ∧ s.gpr .rcx = bfA c ∧
    s.gpr .rsi = dp ∧ s.gpr .rsp = sp ∧ s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 L ∧
    Consts s.mem (bfA c) ∧ Acc R0 R1 A s

/-- Before chunk `t`. -/
def CI (c dp : Addr) (L : Nat) (sp : Addr) (t : Nat) (s : State) : Prop :=
  ∃ R0 R1 A m₀, Key R0 R1 ∧ LI c dp L R0 R1 A m₀ sp t s

theorem enter_fc {c dp : Addr} {L : Nat} {sp : Addr} {s : State} (h : BP c dp L sp s) :
    WP isa (.block enter) s (FC c dp L sp) := by
  obtain ⟨hrd, hwr, hrsi, hrdx, hrcx, hrsp, key, msg, hrep⟩ := h
  refine WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, _, C₁, sl₁, _, _, _, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨R0, hR0⟩ : ∃ R0, s.mem.readW (off (psA c) 24) 64 &&& Proof.Poly1305.X86_64.M0 = R0 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, s.mem.readW (off (psA c) 32) 64 &&& Proof.Poly1305.X86_64.M1 = R1 := ⟨_, rfl⟩
  have hk : Key R0 R1 := ⟨hR0 ▸ Proof.Poly1305.X86_64.r0_lt _, hR1 ▸ Proof.Poly1305.X86_64.r1_lt _,
    hR1 ▸ Proof.Poly1305.X86_64.r1_mod _⟩
  obtain ⟨A, hA⟩ : ∃ A, leNum (bytesAt s.mem (psA c) 24) = A := ⟨_, rfl⟩
  have hAP : A < P := by rw [← hA, hrep.2.2]; exact VG.Proof.Poly1305.accumulate_lt _ _
  rw [Proof.Poly1305.X86_64.leNum_acc] at hA
  refine ⟨R0, R1, A, hk, by rw [rd₁, hrd], by rw [wr₁, hwr], rdi₁, by rw [gk _ (.inl rfl), hrcx],
    by rw [gk _ (.inr (.inl rfl)), hrsi], by rw [gk _ (.inr (.inr rfl)), hrsp], by rw [sl₁, hrdx], C₁,
    r8₁.trans hR0, r9₁.trans hR1, by rw [r10₁, r9₁, hR1], ?_, ?_⟩
  · have hP : P = 2 ^ 130 - 5 := rfl
    rw [rbp₁]; omega_using [hA, hAP, hP]
  · simp only [hval, r11₁, rbx₁, rbp₁, hA]

theorem enter_taint : ∃ h, (taintS.check (τR [.rcx, .rsi, .rsp]) (.block enter) h).isSome = true := by
  taint_decide_sum []

theorem firstChunk_taint :
    ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) firstChunk h).isSome = true := by
  taint_decide_sum []

theorem chunk_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) chunk h).isSome = true := by
  taint_decide_sum []

theorem leave_taint : ∃ h, (taintS.check (τR [.rcx, .rsi, .rsp]) (.block leave) h).isSome = true := by
  taint_decide_sum []

theorem nil_taint : ∃ h, (taintS.check (τR []) (.block []) h).isSome = true := by
  taint_decide_sum []

section
variable {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) (sp : Addr)
include hl

/-- The later chunks, while at least 512 bytes remain. -/
theorem loop_rel :
    RelCT isa (fun s₁ s₂ => CI c dp L sp 1 s₁ ∧ CI c dp L sp 1 s₂ ∧
        s₁.cf = some (decide (L - 512 * 1 < 512)) ∧ s₂.cf = some (decide (L - 512 * 1 < 512)))
      (.ite .b (.block []) (.loop chunk .ae))
      fun s₁ s₂ => ∃ T, CI c dp L sp T s₁ ∧ CI c dp L sp T s₂ ∧ L - 512 * T < 512 := by
  refine RelCT.ite (fun s₁ s₂ h => by simp only [eval, h.2.2.1, h.2.2.2]) ?_ ?_
  · obtain ⟨_, hn⟩ := nil_taint
    refine ((RelCT.taint (A := taintS) (τR []) (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hn).wpDep
      (F := fun s s' => s' = s) fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨-, σ₁, σ₂, ⟨⟨h₁, h₂, c₁, -⟩, hb⟩, rfl, rfl⟩
    simp only [eval, c₁, Option.some.injEq, decide_eq_true_eq] at hb
    exact ⟨1, h₁, h₂, hb⟩
  · obtain ⟨_, hc⟩ := chunk_taint
    let I : Nat → State → State → Prop := fun n s₁ s₂ =>
      ∃ t, n = L - 512 * t ∧ 512 ≤ L - 512 * t ∧ CI c dp L sp t s₁ ∧ CI c dp L sp t s₂
    have body : ∀ t, RelCT isa (fun s₁ s₂ => 512 ≤ L - 512 * t ∧ CI c dp L sp t s₁ ∧ CI c dp L sp t s₂) chunk
        fun s₁ s₂ => (CI c dp L sp (t + 1) s₁ ∧ s₁.cf = some (decide (L - 512 * (t + 1) < 512))) ∧
          (CI c dp L sp (t + 1) s₂ ∧ s₂.cf = some (decide (L - 512 * (t + 1) < 512))) := by
      intro t
      have step : ∀ {s}, 512 ≤ L - 512 * t → CI c dp L sp t s → WP isa chunk s fun s' =>
          CI c dp L sp (t + 1) s' ∧ s'.cf = some (decide (L - 512 * (t + 1) < 512)) :=
        fun hge' ⟨R0, R1, A, m₀, hk, hL⟩ => WP.mono (chunk_ok hl hk hge' hL) fun s' ⟨hL', cf'⟩ =>
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
    refine (RelCT.loop (Q := fun s₁ s₂ => ∃ T, CI c dp L sp T s₁ ∧ CI c dp L sp T s₂ ∧ L - 512 * T < 512) I
      (fun n => ?_) (L - 512 * 1)).mono ?_ (fun _ _ h => h)
    · refine (RelCT.exists_ (P := fun (x : {t // n = L - 512 * t ∧ 512 ≤ L - 512 * t}) s₁ s₂ =>
        CI c dp L sp x.1 s₁ ∧ CI c dp L sp x.1 s₂) fun ⟨t, hn, hge'⟩ => ?_).mono
        (fun _ _ ⟨t, hn, hge', h₁, h₂⟩ => ⟨⟨t, hn, hge'⟩, h₁, h₂⟩) (fun _ _ h => h)
      refine ((body t).mono (fun _ _ h => ⟨hge', h.1, h.2⟩) fun _ _ h => h).mono (fun _ _ h => h) ?_
      rintro s₁ s₂ ⟨⟨h₁, c₁⟩, ⟨h₂, c₂⟩⟩
      refine ⟨by simp only [eval, c₁, c₂], fun hf => ?_, fun ht => ?_⟩
      · refine ⟨t + 1, h₁, h₂, ?_⟩
        by_contra hc
        simp [eval, c₁, hc] at hf
      · have : ¬ L - 512 * (t + 1) < 512 := fun hc => by simp [eval, c₁, hc] at ht
        exact ⟨L - 512 * (t + 1), by omega, t + 1, rfl, by omega, h₁, h₂⟩
    · rintro s₁ s₂ ⟨⟨h₁, h₂, c₁, -⟩, hb⟩
      have : ¬ L - 512 * 1 < 512 := fun hc => by simp [eval, c₁, hc] at hb
      exact ⟨1, rfl, by omega, h₁, h₂⟩
include hge in
/-- `bulk`, with its permissions. -/
theorem bulk_rel :
    RelCT isa (fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂) bulk fun _ _ => True := by
  unfold bulk
  obtain ⟨_, hE⟩ := enter_taint
  obtain ⟨_, hF⟩ := firstChunk_taint
  obtain ⟨_, hL⟩ := leave_taint
  have e := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂)
    (τR [.rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hE).wp
    fun _ _ h => ⟨enter_fc h.1, enter_fc h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  · have first : ∀ {s}, FC c dp L sp s → WP isa firstChunk s fun s' =>
        CI c dp L sp 1 s' ∧ s'.cf = some (decide (L - 512 * 1 < 512)) :=
      fun ⟨R0, R1, A, hk, rd, wr, rdi, rcx, rsi, rsp, sl, C, acc⟩ =>
        WP.mono (firstChunk_ok hl (m₀ := _) hge rd wr rdi rcx rsi rsp sl rfl C acc) fun s' ⟨hL', cf'⟩ =>
          ⟨⟨R0, R1, A, _, hk, hL'⟩, cf'⟩
    have f := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => FC c dp L sp s₁ ∧ FC c dp L sp s₂)
      (τR [.rdi, .rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hF).wp
      fun _ _ h => ⟨first h.1, first h.2⟩).mono (fun _ _ h => h)
      (Q' := fun (s₁ s₂ : State) => CI c dp L sp 1 s₁ ∧ CI c dp L sp 1 s₂ ∧
        s₁.cf = some (decide (L - 512 * 1 < 512)) ∧ s₂.cf = some (decide (L - 512 * 1 < 512)))
      fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩
    · have lv := (RelCT.taint (A := taintS)
        (P := fun s₁ s₂ => ∃ T, CI c dp L sp T s₁ ∧ CI c dp L sp T s₂ ∧ L - 512 * T < 512)
        (τR [.rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hL)
      · exact e.seq (f.seq ((loop_rel hl sp).seq lv))
      · obtain ⟨T, ⟨_, _, _, _, _, h₁⟩, ⟨_, _, _, _, _, h₂⟩, -⟩ := h
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.rcx, h₂.rcx]
        · rw [h₁.rsi, h₂.rsi]
        · rw [h₁.rsp, h₂.rsp]
    · obtain ⟨⟨_, _, _, _, _, _, rdi₁, rcx₁, rsi₁, rsp₁, -⟩, ⟨_, _, _, _, _, _, rdi₂, rcx₂, rsi₂, rsp₂, -⟩⟩ := h
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [rdi₁, rdi₂]
      · rw [rcx₁, rcx₂]
      · rw [rsi₁, rsi₂]
      · rw [rsp₁, rsp₂]
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
# ChaCha20 and Poly1305 together (x86-64): `sealStitched` is constant time

As `seal_rel`: the taint analysis checks the code between the calls, and
correctness says what holds at them. `cryptS`'s branches differ from
`crypt`'s: without whole chunks, the code is checked as before; with them,
`cryptArgs` is checked, `bulk` is constant time by `bulk_rel` (moved to
`seal`'s permissions by `relCT_narrow`), and the call of `vg_chacha20_xor`
after it, on the rest of the data, by the implementation's own proof, its
arguments being functions of the public length (`MidS`). After it, `rbx`
and `rbp` (the ciphertext not yet absorbed) are public too (`AfterS`).
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

/-! ## The parts of the code -/

/-- `cryptS`'s branch for at most `fold` bytes. -/
def smallS (w : Nat) : Prog isa :=
  .seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
    (.seq (xorBufX w .r14) (.block (ptr .rsi .r15 128 ++ whole)))

/-- `cryptS`'s branch for more. -/
def bigS (x : Impl.ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
    (.seq (.ite .b (.block whole) bulk) (.call x.name x.code))

def iteS (x : Impl.ChaCha20.X86_64.Callee) : Prog isa := .ite .b (smallS x.wide) (bigS x)

/-- `sealStitched` after the branch. -/
def postS (fold pass w : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (wipe fold pass w) (.seq (macPadLengths b .rbx .rbp) (.seq finalizeTag (.block restore)))

theorem sealS_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa (sealStitched x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA x.fold x.pass x.wide) (.seq (.call x.name x.code)
      (.seq (sealMid x.fold b) (.seq (iteS x) (postS x.fold x.pass x.wide b)))))) s t s' := by
  cases h with | seq e₀ h => cases h with | seq hP h => cases hP with | seq ePA hP => cases hP with
  | seq eC ePB => cases h with | seq eMA h => cases h with | seq eLEN h => cases h with | seq hC h =>
  cases hC with | seq eCMP hC => cases hC with | seq eITE hC => cases hC with | seq eANC hC =>
  cases hC with | seq eFM hC => cases hC with | seq eADD eZK => cases h with | seq eMC h =>
  cases h with | seq eFT eRE =>
  have := Exec.seq e₀ (Exec.seq ePA (Exec.seq eC (Exec.seq (Exec.seq ePB (Exec.seq eMA (Exec.seq eLEN eCMP)))
    (Exec.seq eITE (Exec.seq (Exec.seq eANC (Exec.seq eFM (Exec.seq eADD eZK)))
      (Exec.seq eMC (Exec.seq eFT eRE)))))))
  simp only [List.append_assoc] at this ⊢
  exact this

/-! ## What holds where -/

/-- At the branch on the length: as `AtIte`, and what `cryptS_ok` needs. -/
def AtIteS (fold pass : Nat) (s₀ s : State) : Prop :=
  AtIte fold pass s₀ s ∧ stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀) ∧
    ∃ key msg, Repr s.mem (off (cx s₀) 448) key msg

theorem sealMidS_ok {fold pass : Nat} (hf : fold ≤ 960) (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : AfterF fold pass s₀ s) : WP isa (sealMid fold b) s (AtIteS fold pass s₀) := by
  have hM := Nat.le_trans (mOf_le fold pass (L s₀)) hf
  refine WP.seq (WP.mono (prologueB_ok hf hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, _⟩ => ?_)
  refine WP.mono (cmpFold_ok (fold := fold) (by lit_omega) i₃.r13) fun s₄ ⟨g₄, rd₄, wr₄, m₄, c₄⟩ => ?_
  refine ⟨⟨i₃.step (fun r _ => by rw [g₄]) rd₄ wr₄ (rs := []) (by rw [m₄]; exact Frame.refl _ _)
      (fun _ h => by simp at h) (fun _ h => by simp at h), c₄,
    by rw [m₄]; exact ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)⟩, ?_, ?_⟩
  · rw [m₄, stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  · exact ⟨otk s₀, _, by rw [m₄]; exact Repr.frame f₃ (by rdisj_all) (r₂ _ _ h₁.poly)⟩

/-- `cryptArgs` and the comparison with 512. -/
theorem argsCmp_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) s fun s' =>
      Args s₀ s s' ∧ s'.cf = some (decide (L s₀ < 512)) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.block_append (WP.mono (cryptA_ok hp h) fun s₂ ⟨m₂, rdi₂, rsi₂, rdx₂, rcx₂, cs₂, rd₂, wr₂⟩ =>
    WP.mono (cmp512_ok hL9 (by rw [rdx₂, hL])) fun s₃ ⟨g₃, rd₃, wr₃, m₃, c₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun r hr => ?_, by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩, c₃⟩)
  · rw [m₃, m₂]
  · rw [g₃, rdi₂]
  · rw [g₃, rsi₂]
  · rw [g₃, rdx₂, hL]
  · rw [g₃, rcx₂]
  · rw [g₃, cs₂ _ (by simp [calleeSaved]), h.r13, hL]
  · rw [g₃, cs₂ _ (by simp [calleeSaved]), h.r14]
  · rw [g₃, cs₂ r (by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])]

/-- After `cryptS`'s branch: as `After`, and `rbx`, `rbp` the ciphertext not
yet absorbed. -/
structure AfterS (s₀ s : State) : Prop where
  rsi : s.gpr .rsi = off (cx s₀) 128
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r9
  r14 : s.gpr .r14 = dp s₀
  r12 : s.gpr .r12 = tp s₀
  rbx : s.gpr .rbx = dp s₀ + BitVec.ofNat 64 (aOf (L s₀))
  rbp : s.gpr .rbp = BitVec.ofNat 64 (L s₀ - aOf (L s₀))
  wr : s.wr = s₀.wr

theorem smallS_ok {fold pass w : Nat} (hf : fold ≤ 960) (hw : w = 4 ∨ w = 5 ∨ w = 6) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : AtIte fold pass s₀ s) (hle : L s₀ ≤ fold) :
    WP isa (smallS w) s (AfterS s₀) := by
  unfold smallS
  apply seq3
  refine WP.mono (cryptSmall_ok hf hw hp h.inv hle h.ks) fun s₃ c₃ => ?_
  refine WP.mono (whole_ok s₃) fun s₄ ⟨rbx₄, rbp₄, g₄, _, wr₄, _⟩ => ?_
  have a0 : aOf (L s₀) = 0 := by simp only [aOf]; omega
  refine ⟨by rw [g₄ _ (by decide) (by decide), c₃.rsi],
    by rw [g₄ _ (by decide) (by decide), c₃.cs _ calleeSaved_rsp (by decide), h.inv.rsp],
    by rw [g₄ _ (by decide) (by decide), c₃.cs _ (by simp [calleeSaved]) (by decide), h.inv.r13],
    by rw [g₄ _ (by decide) (by decide), c₃.cs _ (by simp [calleeSaved]) (by decide), h.inv.r14],
    by rw [g₄ _ (by decide) (by decide), c₃.cs _ (by simp [calleeSaved]) (by decide), h.inv.r12],
    by rw [rbx₄, c₃.cs _ (by simp [calleeSaved]) (by decide), h.inv.r14, a0]; simp,
    by rw [rbp₄, c₃.cs _ (by simp [calleeSaved]) (by decide), h.inv.r13, hL, a0, Nat.sub_zero],
    by rw [wr₄, c₃.wr, h.inv.wr]⟩

/-- Before the call of `vg_chacha20_xor` after `bulk`. -/
def MidS (s₀ s : State) : Prop :=
  ∃ σ key msg E a, Inv s₀ σ ∧ Mid s₀ σ key msg E a s

/-- The bytes encrypted before that call. -/
abbrev Eof (L : Nat) : Nat := 512 * (L / 512)

/-- The regions of that call. -/
abbrev xR (s₀ : State) : List Region :=
  [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀ + BitVec.ofNat 64 (Eof (L s₀)), L s₀ - Eof (L s₀)⟩, ⟨off (cx s₀) 128, 320⟩]

section
variable {s₀ : State} (hp : APre e s₀) {s : State} (h : MidS s₀ s)
include hp h

omit hp in
theorem MidS.vals : s.gpr .rdi = off (cx s₀) 64 ∧ s.gpr .rsi = dp s₀ + BitVec.ofNat 64 (Eof (L s₀)) ∧
    s.gpr .rdx = BitVec.ofNat 64 (L s₀ - Eof (L s₀)) ∧ s.gpr .rcx = off (cx s₀) 128 ∧
    s.gpr .rsp = s₀.gpr .rsp ∧ s.wr = s₀.wr := by
  obtain ⟨σ, key, msg, E, a, hi, hm⟩ := h
  have hE : Eof (L s₀) = E := hm.Ediv.symm
  rw [hE]
  exact ⟨hm.rdi, hm.rsi, hm.rdx, hm.rcx, by rw [hm.keep _ (.inr (.inr (.inr rfl))), hi.rsp], by rw [hm.wr, hi.wr]⟩

theorem MidS.hw : Covers (xR s₀) s.wr := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ctxR s₀, by rw [h.vals.2.2.2.2.2]; exact hp.ctx_wr, 64, by simp [off_eq],
      by show 64 + 64 ≤ 1696; omega⟩
  · exact ⟨dR s₀, by rw [h.vals.2.2.2.2.2]; exact hp.d_wr, Eof (L s₀), rfl,
      by show Eof (L s₀) + (L s₀ - Eof (L s₀)) ≤ L s₀; omega⟩
  · exact ⟨ctxR s₀, by rw [h.vals.2.2.2.2.2]; exact hp.ctx_wr, 128, by simp [off_eq],
      by show 128 + 320 ≤ 1696; omega⟩

theorem MidS.pre (v : Proof.ChaCha20.X86_64.XorImpl) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] (xR s₀)) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega
  obtain ⟨rdi, rsi, rdx, rcx, rsp, -⟩ := h.vals
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (Eof (L s₀)), L s₀ - Eof (L s₀)⟩ (dR s₀) :=
    Offset.sub_base _ (by omega)
  exact xor_pre v rdi rsi rdx rcx (by omega)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ _ (by omega)) _) (by have := hp.wrap_d; omega))
    (by rw [rsp]; exact hp.stk_sub (by lit_omega)) (by rw [rsp]; exact hp.stk_d.sub_right dsub)
    (by rw [rsp]; exact hp.stk_sub (by lit_omega))

theorem MidS.call (v : Proof.ChaCha20.X86_64.XorImpl) :
    WP isa (.call v.callee.name v.callee.code) s (AfterS s₀) := by
  obtain ⟨σ, key, msg, E, a, hi, hm⟩ := h
  refine WP.mono (call_mid v hp hi hm) fun s' c => ?_
  obtain ⟨a', aO, -, -, rbx, rbp, -⟩ := c.abs
  refine ⟨c.rsi, ?_, ?_, ?_, ?_, by rw [rbx, aO], by rw [rbp, aO], by rw [c.wr, hi.wr]⟩
  · rw [c.keep _ (.inr (.inr (.inr rfl))), hi.rsp]
  · rw [c.keep _ (.inr (.inl rfl)), hi.r13]
  · rw [c.keep _ (.inr (.inr (.inl rfl))), hi.r14]
  · rw [c.keep _ (.inl rfl), hi.r12]

end

/-! ## The taint after the branch -/

/-- As `τ₁`, with `rbx` and `rbp` public. -/
def τ₁S (enc : Bool) : X86_64.Taint.T :=
  { regs := .ofList [.rsi, .rsp, .r13, .r14, .r12, .rbx, .rbp], flags := false, lens := lensOf enc,
    bases := [(.rsi, ci enc, 128)] }

section
variable {s₀ s₀' : State} (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀')

omit hp' in
include hp in
theorem AfterS.wf {s : State} (h : AfterS s₀ s) : X86_64.Taint.Wf (τ₁S e) s := by
  have hw : s.wr = bif e then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀] := by rw [h.wr, hp.wr_eq]
  refine ⟨fun _ => regions_wf hp h.wr, fun p hm => ?_⟩
  simp only [τ₁S, List.mem_singleton] at hm
  subst hm
  simp only [X86_64.Taint.region, hw, h.rsi, off_eq]
  cases e <;> simp

include hp hp' hq in
theorem agree₁S {s₁ s₂ : State} (h₁ : AfterS s₀ s₁) (h₂ : AfterS s₀' s₂) :
    X86_64.Taint.Agree (τ₁S e) s₁ s₂ := by
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, p8, p9⟩ := hq'
  obtain ⟨c, d, t⟩ := pub_regs hq
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, h₁.wf hp, h₂.wf hp', ?_, ?_, X86_64.Taint.noLo,
    X86_64.Taint.noXr⟩
  · simp only [τ₁S, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.rsi, h₂.rsi, cx, cx, p9]
    · rw [h₁.rsp, h₂.rsp, p7]
    · rw [h₁.r13, h₂.r13, p6]
    · rw [h₁.r14, h₂.r14, dp, dp, p5]
    · rw [h₁.r12, h₂.r12, tp, tp, p8]
    · rw [h₁.rbx, h₂.rbx, dp, dp, p5, L, L, p6]
    · rw [h₁.rbp, h₂.rbp, L, L, p6]
  · rw [h₁.wr, h₂.wr, hp.wr_eq, hp'.wr_eq, c, d, t]
  · intro sl h; simp [τ₁S] at h
  · intro sl h; simp [τ₁S] at h

end

theorem smallS_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τS true) (smallS wide) h).isSome = true := by
  rcases h with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ <;> taint_decide_sum []

theorem argsS_taint :
    ∃ h, (taintS.check (τS true) (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) h).isSome =
      true := by
  taint_decide_sum []

theorem whole_taint : ∃ h, (taintS.check (τR []) (.block whole) h).isSome = true := by
  taint_decide_sum []

theorem postS_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τ₁S true) (postS fold pass wide b) h).isSome = true := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    taint_decide_sum [blocksBigS, blocksBigAvx2S, blocksBigAvx512S, blocksSmallS, blocksSmallAvx2S,
      blocksSmallAvx512S, finalizeSumS]

/-! ## The branch with whole chunks -/

/-- `bulk`'s permissions are `seal`'s. -/
theorem bulk_covers {s₀ : State} (hp : APre e s₀) {s : State} (hwr : s.wr = s₀.wr) :
    Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s.wr := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1696; omega⟩
  · exact ⟨dR s₀, by rw [hwr]; exact hp.d_wr, 0, by simp, by simp⟩
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1696; omega⟩
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 448, rfl, by show 448 + 128 ≤ 1696; omega⟩

theorem bulk_bp {s₀ : State} {σ s : State} (ha : Args s₀ σ s) (hi : Inv s₀ σ) {key msg : List Byte}
    (hrep : Repr σ.mem (off (cx s₀) 448) key msg) :
    BP (cx s₀) (dp s₀) (L s₀) (s₀.gpr .rsp) (s.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) :=
  ⟨rfl, rfl, ha.rsi, ha.rdx, by rw [State.withRegions_gpr, ha.rcx, off_eq],
    by rw [State.withRegions_gpr, ha.keep _ (.inr (.inr (.inr rfl))), hi.rsp], key, msg,
    by show Repr _ (cx s₀ + BitVec.ofNat 64 448) _ _
       rw [State.withRegions_mem, ha.mem, ← off_eq]; exact args_repr hrep⟩

/-- What the branch with whole chunks starts from, in one run. -/
def AtArgs (fold pass : Nat) (s₀ s : State) : Prop :=
  ∃ σ, AtIteS fold pass s₀ σ ∧ Args s₀ σ s ∧ s.cf = some (decide (L s₀ < 512))

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State} (hp : APre true s₀) (hp' : APre true s₀')
  (hq : pubX86_64 s₀ s₀')
include hp hp' hq

theorem bigS_rel :
    RelCT isa (fun s₁ s₂ => (AtIteS v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteS v.callee.fold v.callee.pass s₀' s₂) ∧
      isa.eval .b s₁ = some false) (bigS v.callee) fun s₁ s₂ => AfterS s₀ s₁ ∧ AfterS s₀' s₂ := by
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, -, p9⟩ := hq'
  have eL : L s₀' = L s₀ := by simp only [L, p6]
  have ec : cx s₀' = cx s₀ := by simp only [cx, p9]
  have ed : dp s₀' = dp s₀ := by simp only [dp, p5]
  obtain ⟨_, hA⟩ := argsS_taint
  obtain ⟨_, hW⟩ := whole_taint
  have argsOk : ∀ {σ₀ s}, APre true σ₀ → AtIteS v.callee.fold v.callee.pass σ₀ s →
      WP isa (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) s (AtArgs v.callee.fold v.callee.pass σ₀) :=
    fun hp h => WP.mono (argsCmp_ok hp h.1.inv) fun _ ⟨ha, cf⟩ => ⟨_, h, ha, cf⟩
  have args := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtIteS v.callee.fold v.callee.pass s₀ s₁ ∧
      AtIteS v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some false) (τS true)
      (fun _ _ h => agreeS hp hp' hq h.1.1.1 h.1.2.1) hA).wp
    (F₁ := AtArgs v.callee.fold v.callee.pass s₀) (F₂ := AtArgs v.callee.fold v.callee.pass s₀') fun _ _ h =>
      ⟨argsOk hp h.1.1, argsOk hp' h.1.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have wholeOk : ∀ {σ₀ s}, APre true σ₀ → AtArgs v.callee.fold v.callee.pass σ₀ s → isa.eval .b s = some true →
      WP isa (.block whole) s (MidS σ₀) := fun hp ⟨σ, ⟨hi, hst, key, msg, hrep⟩, ha, cf⟩ hb => by
    simp only [eval, cf, Option.some.injEq, decide_eq_true_eq] at hb
    exact WP.mono (whole_mid hp ha hb hst hrep) fun _ hm => ⟨σ, key, msg, 0, 0, hi.inv, hm⟩
  have wh := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtArgs v.callee.fold v.callee.pass s₀ s₁ ∧
      AtArgs v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some true) (τR [])
      (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hW).wp
    (F₁ := MidS s₀) (F₂ := MidS s₀') fun _ _ h => ⟨wholeOk hp h.1.1 h.2,
      wholeOk hp' h.1.2 (by
        rw [← h.2]; obtain ⟨⟨_, -, -, c₁⟩, ⟨_, -, -, c₂⟩⟩ := h.1; simp only [eval, c₁, c₂, eL])⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have bulkOk : ∀ {σ₀ s}, APre true σ₀ → AtArgs v.callee.fold v.callee.pass σ₀ s → isa.eval .b s = some false →
      WP isa bulk s (MidS σ₀) := fun hp ⟨σ, ⟨hi, hst, key, msg, hrep⟩, ha, cf⟩ hb => by
    simp only [eval, cf, Option.some.injEq, decide_eq_false_iff_not] at hb
    exact WP.mono (bulk_mid hp hi.inv.wr ha (by omega) hst hrep) fun _ ⟨E, a, hm⟩ => ⟨σ, key, msg, E, a, hi.inv, hm⟩
  have hl : Lay (cx s₀) (dp s₀) (L s₀) :=
    ⟨(s₀.gpr .r9).isLt, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have bk : RelCT isa (fun s₁ s₂ => (AtArgs v.callee.fold v.callee.pass s₀ s₁ ∧ AtArgs v.callee.fold v.callee.pass s₀' s₂) ∧
      isa.eval .b s₁ = some false) bulk fun s₁ s₂ => MidS s₀ s₁ ∧ MidS s₀' s₂ := by
    by_cases hge : 512 ≤ L s₀
    · refine ((relCT_narrow (c := bulk) (fun _ => bulkWr (cx s₀) (dp s₀) (L s₀)) ?_
        (bulk_rel hl hge (s₀.gpr .rsp))).wp (F₁ := MidS s₀) (F₂ := MidS s₀') ?_).mono (fun _ _ h => h)
        fun _ _ h => h.2
      · rintro s₁ s₂ ⟨⟨⟨σ₁, ⟨hi₁, -, key₁, msg₁, hrep₁⟩, ha₁, -⟩, ⟨σ₂, ⟨hi₂, -, key₂, msg₂, hrep₂⟩, ha₂, -⟩⟩, -⟩
        have b₁ := bulk_bp ha₁ hi₁.inv hrep₁
        have b₂ := bulk_bp ha₂ hi₂.inv hrep₂
        rw [ec, ed, eL, ← p7] at b₂
        obtain ⟨rd₁, wr₁, rsi₁, rdx₁, rcx₁, -, _, _, r₁⟩ := id b₁
        obtain ⟨rd₂, wr₂, rsi₂, rdx₂, rcx₂, -, _, _, r₂⟩ := id b₂
        exact ⟨bulk_covers hp (by rw [ha₁.wr, hi₁.inv.wr]), by
          rw [← ec, ← ed, ← eL]; exact bulk_covers hp' (by rw [ha₂.wr, hi₂.inv.wr]),
          ⟨_, bulk_ok hl hge rd₁ wr₁ rsi₁ rdx₁ rcx₁ r₁⟩, ⟨_, bulk_ok hl hge rd₂ wr₂ rsi₂ rdx₂ rcx₂ r₂⟩, b₁, b₂⟩
      · exact fun _ _ h => ⟨bulkOk hp h.1.1 h.2, bulkOk hp' h.1.2 (by
          rw [← h.2]; obtain ⟨⟨_, -, -, c₁⟩, ⟨_, -, -, c₂⟩⟩ := h.1; simp only [eval, c₁, c₂, eL])⟩
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, c₁⟩, _⟩, hb⟩ => ?_
      simp only [eval, c₁, Option.some.injEq, decide_eq_false_iff_not] at hb
      omega
  have call := (RelCT.callEx (n := v.callee.name) (P := fun s₁ s₂ => MidS s₀ s₁ ∧ MidS s₀' s₂) v.ok v.ct
    fun s₁ s₂ ⟨m₁, m₂⟩ => ⟨[], _, [], _, MidS.pre hp m₁ v, MidS.pre hp' m₂ v, ?_, Covers.right (MidS.hw hp m₁),
      MidS.hw hp m₁, Covers.right (MidS.hw hp' m₂), MidS.hw hp' m₂,
      by rw [(MidS.vals m₁).2.2.2.2.1, (MidS.vals m₂).2.2.2.2.1, p7]⟩).wp
    (F₁ := AfterS s₀) (F₂ := AfterS s₀') fun _ _ h => ⟨MidS.call hp h.1 v, MidS.call hp' h.2 v⟩
  · refine args.seq ((RelCT.ite (fun s₁ s₂ h => ?_) wh bk).seq (call.mono (fun _ _ h => h) fun _ _ h => h.2))
    obtain ⟨⟨_, -, -, c₁⟩, ⟨_, -, -, c₂⟩⟩ := h
    simp only [eval, c₁, c₂, eL]
  · obtain ⟨rdi₁, rsi₁, rdx₁, rcx₁, rsp₁, -⟩ := MidS.vals m₁
    obtain ⟨rdi₂, rsi₂, rdx₂, rcx₂, rsp₂, -⟩ := MidS.vals m₂
    simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
      State.callEntry_rsp, callEntry_gpr' s₁ (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s₁ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₁ (by decide : Reg.rdx ≠ .rsp),
      callEntry_gpr' s₁ (by decide : Reg.rcx ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s₂ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdx ≠ .rsp),
      callEntry_gpr' s₂ (by decide : Reg.rcx ≠ .rsp), rdi₁, rsi₁, rdx₁, rcx₁, rsp₁, rdi₂, rsi₂, rdx₂, rcx₂,
      rsp₂, eL, ec, ed, p7]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State}

theorem sealS_rel (h₀ : preX86_64 true s₀) (h₀' : preX86_64 true s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (sealStitched v.callee v.poly) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  have hfl := v.fold_le
  obtain ⟨_, hA⟩ := prologueA_taint true v.fold_poly
  obtain ⟨_, hmid⟩ := sealMid_taint v.fold_poly
  obtain ⟨_, hS⟩ := smallS_taint v.fold_poly
  obtain ⟨_, hpost⟩ := postS_taint v.fold_poly
  have pA := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ true)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq) hA).wp
    (F₁ := FArgs v.callee.fold v.callee.pass s₀) (F₂ := FArgs v.callee.fold v.callee.pass s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok hfl (pass_of v) (wide_of v) hp, by rw [h.2]; exact prologueA_ok hfl (pass_of v) (wide_of v) hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have mid := ((RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => AfterF v.callee.fold v.callee.pass s₀ s₁ ∧ AfterF v.callee.fold v.callee.pass s₀' s₂) (τA true)
    (fun _ _ h => agreeA hp hp' hq h.1 h.2) hmid).wp (F₁ := AtIteS v.callee.fold v.callee.pass s₀)
    (F₂ := AtIteS v.callee.fold v.callee.pass s₀') fun _ _ h =>
      ⟨sealMidS_ok hfl v.poly hp h.1, sealMidS_ok hfl v.poly hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hc : ∀ s₁ s₂, (AtIteS v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteS v.callee.fold v.callee.pass s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    have : L s₀ = L s₀' := by simp only [L, hq.2.2.2.2.2.1]
    simp [eval, h.1.1.cf, h.2.1.cf, this]
  have small := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteS v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteS v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some true)
    (τS true) (fun _ _ h => agreeS hp hp' hq h.1.1.1 h.1.2.1) hS).wp (F₁ := AfterS s₀) (F₂ := AfterS s₀')
    fun s₁ s₂ h => by
      have e₁ := h.2
      have e₂ := (hc _ _ h.1).symm.trans h.2
      simp only [eval, h.1.1.1.cf, h.1.2.1.cf, Option.some.injEq, decide_eq_true_eq] at e₁ e₂
      exact ⟨smallS_ok hfl (wide_of v) hp h.1.1.1 (by omega), smallS_ok hfl (wide_of v) hp' h.1.2.1 (by omega)⟩
  have ite := RelCT.ite hc (small.mono (fun _ _ h => h) fun _ _ h => h.2) (bigS_rel v hp hp' hq)
  have post := RelCT.taint (A := taintS) (P := fun s₁ s₂ => AfterS s₀ s₁ ∧ AfterS s₀' s₂) (τ₁S true)
    (fun _ _ h => agree₁S hp hp' hq h.1 h.2) hpost
  have := (entry_rel hp hp' hq).seq (pA.seq ((call1_rel hp hp' hq v).seq (mid.seq (ite.seq post))))
  exact RelCT.of_exec sealS_exec this

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `Verified`

`sealStitched` against `seal`'s contracts, as `seal_verified` and
`seal_framed` (`../Verified.lean`), and `sealFor`, which instances use: the
stitched code with the AVX2 implementation of `vg_poly1305_blocks`, `seal`
otherwise.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch

theorem sealS_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (sealStitched v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases v.fold_poly with ⟨hf, hpass, hw, hb⟩ | ⟨hf, hpass, hw, hb⟩ | ⟨hf, hpass, hw, hb⟩ <;>
    (simp only [sealStitched, prologue, cryptS, Code.all, v.spSafe, hf, hpass, hw, hb]; lit_decide)

theorem sealS_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa (sealStitched v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' :=
  sealStitched_correct v (APre.of s hs)

theorem sealS_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub (sealStitched v.callee v.poly) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (sealS_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem sealS_verified (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target (sealStitched v.callee v.poly) (sealScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (sealS_ok v) (sealS_ct v) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealX86_64,
      Proof.ChaCha20Poly1305.preX86_64, Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg,
      X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      [sealSat] using sealSat)

theorem bulk_xdepth : bulk.x86_64Depth = 0 := by decide +kernel

theorem sealS_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) :
    (sealStitched v.callee v.poly).x86_64Depth ≤ 24 := by
  have hx := v.xdepth
  have hb := blocks_xdepth v.poly
  simp only [sealStitched, prologue, prologueA, prologueB, foldM, zeroKs, macPad, macPadLengths, wholeBlocks,
    padTail, cryptS, absorbLengths, finalizeTag, finalizeWith, Code.x86_64Depth, xorBuf_xdepth, splitM_xdepth,
    init_xdepth,
    finalize_xdepth, bulk_xdepth, Nat.max_le]
  omega

theorem sealS_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 (sealStitched v.callee v.poly))
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1744) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1720) (k := 42) (sealS_verified v) (by decide) (by decide) (by decide)
    (sealS_spSafe v) (sealS_xdepth v) (by decide) (pre_local _ _) (sealPost_local _) (sealPost_out _)
    sealFrameSat_pre

/-! ## The `seal` of an instance -/

theorem sealFor_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (sealFor v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h₁ := seal_spSafe v
  have h₂ := sealS_spSafe v
  generalize v.poly = b at h₁ h₂ ⊢
  cases b
  · exact h₁
  · exact h₂
  · exact h₁

theorem sealFor_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) : (sealFor v.callee v.poly).x86_64Depth ≤ 24 := by
  have h₁ := seal_xdepth v
  have h₂ := sealS_xdepth v
  generalize v.poly = b at h₁ h₂ ⊢
  cases b
  · exact h₁
  · exact h₂
  · exact h₁

theorem sealFor_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1720 1 42 (sealFor v.callee v.poly))
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1744) := by
  have h₁ := seal_framed v
  have h₂ := sealS_framed v
  generalize v.poly = b at h₁ h₂ ⊢
  cases b
  · exact h₁
  · exact h₂
  · exact h₁

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `open`'s whole chunks

`Stitch.chunkO` absorbs the 512 bytes at `rsi` while ChaCha20's rounds run
(`srounds_ok`, as `seal`'s chunks do), then XORs the keystream into the same
bytes and advances `rsi` past them (`chunkMainO_ok`). Before chunk `t`
(`LO`), the first `512 t` bytes are decrypted, the counter is advanced by
`8 t`, the first `512 t` bytes of ciphertext (as they were on entry) are
absorbed, and the bytes left are `L - 512 t`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds Consts Incs stR bufR slotsR dR5 DWin W2 plus hiR
  setup_ok finish_ok W2_frame incs_frame hiR_slots hiR_sub slotsR_sub plus_block ks_shift ctr_add)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)
open VG.Spec.ChaCha20 (stateAt serialize innerBlock keystream)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- The 512 bytes at `q` absorbed, then XORed with eight blocks of keystream
from the state at `st`, and `rsi` advanced past them. -/
theorem chunkMainO_ok {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hwd : DWin s.wr q)
    (hin : ∀ off n, off + n ≤ 512 → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsd : (stR st).Disjoint (dR5 q)) (dsb : (stR st).Disjoint (bufR buf))
    (dbd : (bufR buf).Disjoint (dR5 q)) (dqs : (dR5 q).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa chunkMainO s fun s' =>
        (∀ k < 512, s'.mem (q + BitVec.ofNat 64 k) = s.mem (q + BitVec.ofNat 64 k) ^^^
          (serialize (plus (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j))
            (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
        Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q 512)) s' ∧
        Frame [slotsR buf, dR5 q] s.mem s'.mem ∧
        (∀ r, r ∉ absorbRegs → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.gpr .rsi = q + 512 ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold chunkMainO
  refine WP.seq (WP.mono (setup_ok hrdi hrcx hst hb hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem buf := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR buf] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  have q₁ : bytesAt s₁.mem q 512 = bytesAt s.mem q 512 := by
    have := bytes_frame F₁ dqs (j := 0) (n := 512) (by decide)
    simpa using this
  have h0 : SR buf q R0 R1 X (fun j => ctr (stateAt s.mem st) j) s₁ 0 s₁ :=
    ⟨hh, h15, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      rw [show 16 * firstBlock 0 = 0 from rfl, show bytesAt s₁.mem q 0 = [] from rfl,
        VG.Proof.Poly1305.absorbAll_nil]
      exact ⟨by rw [g₁]; exact hacc.r8, by rw [g₁]; exact hacc.r9, by rw [g₁]; exact hacc.r10,
        by rw [g₁]; exact hacc.h2, by simp only [hval, g₁]; exact hacc.val⟩⟩
  refine WP.seq (WP.mono (srounds_ok hk (by rw [g₁, hrcx]) (by rw [g₁, hrsi]) (by rw [wr₁]; exact hb) c₁.m8 dqs
    (by rw [rd₁, wr₁]; exact hin) 10 (by decide) h0) fun s₂ h₂ => ?_)
  have F₂ : Frame [slotsR buf] s.mem s₂.mem := F₁.trans h₂.frame
  have wr₂ : s₂.wr = s.wr := by rw [h₂.wr, wr₁]
  have gk₂ : ∀ r, r ∉ absorbRegs → s₂.gpr r = s.gpr r := fun r hr => by rw [h₂.gpr r hr, g₁]
  have inc₂ : Incs buf s₂.mem := incs_frame hc.inc F₂ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _)
  refine WP.block_append (WP.mono (finish_ok h₂.holds (st := st) (by rw [gk₂ _ (by decide), hrdi])
    (by rw [gk₂ _ (by decide), hrcx]) (by rw [gk₂ _ (by decide), hrsi]) (by rw [wr₂]; exact hst)
    (by rw [wr₂]; exact hb) (by rw [wr₂]; exact hwd) inc₂ dsd dsb dbd) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  refine WP.mono (addRsi_ok s₃) fun s₄ ⟨rsi₄, g₄, _, _, m₄, rd₄, wr₄⟩ => ?_
  have hS : stateAt s₂.mem st = stateAt s.mem st :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₂ (by simpa using dsb.sub_right (slotsR_sub buf))
  have hq₂ : ∀ k < 512, s₂.mem (q + BitVec.ofNat 64 k) = s.mem (q + BitVec.ofNat 64 k) := by
    intro k hk'
    refine F₂ _ ?_
    simp only [List.mem_singleton, forall_eq]
    intro hc'
    exact dqs.symm _ hc' (Offset.contains_base q (d := k) (n := 1) (k := 512) (by omega) (by lit_omega))
  have gk : ∀ r, r ∉ absorbRegs → r ≠ .rsi → s₄.gpr r = s.gpr r := fun r hr hs => by
    rw [g₄ r hs, g₃, gk₂ r hr]
  refine ⟨fun k hk' => by rw [m₄, d₃ k hk', hS, hq₂ k hk'], ?_, by rw [m₄]; exact (F₂.mono (by simp)).trans f₃,
    gk, by rw [rsi₄, g₃, gk₂ _ (by decide), hrsi], by rw [rd₄, rd₃, h₂.rd, rd₁], by rw [wr₄, wr₃, wr₂]⟩
  have a₂ := h₂.acc
  rw [firstBlock_ten, q₁] at a₂
  exact ⟨by rw [g₄ _ (by decide), g₃]; exact a₂.r8, by rw [g₄ _ (by decide), g₃]; exact a₂.r9,
    by rw [g₄ _ (by decide), g₃]; exact a₂.r10, by rw [g₄ _ (by decide), g₃]; exact a₂.h2,
    by simp only [hval, g₄ _ (show Reg.r11 ≠ .rsi by decide), g₄ _ (show Reg.rbx ≠ .rsi by decide),
      g₄ _ (show Reg.rbp ≠ .rsi by decide), g₃]; exact a₂.val⟩


/-- Before chunk `t` of `open`'s whole chunks, from the memory `m₀` on entry,
with the key `R0, R1` and the accumulator `A` on entry. -/
structure LO (c dp : Addr) (L : Nat) (R0 R1 : BitVec 64) (A : Nat) (m₀ : Mem) (sp : Addr)
    (t : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = bulkWr c dp L
  rdi : s.gpr .rdi = stA c
  rcx : s.gpr .rcx = bfA c
  rsi : s.gpr .rsi = dp + BitVec.ofNat 64 (512 * t)
  rsp : s.gpr .rsp = sp
  le : 512 * t ≤ L
  left : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 512 * t)
  cnt : stateAt s.mem (stA c) = ctr (stateAt m₀ (stA c)) (8 * t)
  data : ∀ k < L, s.mem (dp + BitVec.ofNat 64 k) =
    if k < 512 * t then m₀ (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt m₀ (stA c)) L).getD k 0
    else m₀ (dp + BitVec.ofNat 64 k)
  consts : Consts s.mem (bfA c)
  acc : Acc R0 R1 (absorbAll (rN R0 R1) A (bytesAt m₀ dp (512 * t))) s
  fr : Frame [stR (stA c), ⟨dp, L⟩, bufR (bfA c), ⟨slot (bfA c), 8⟩] m₀ s.mem

/-- The ciphertext of a chunk not yet decrypted is as it was on entry. -/
theorem LO.chunk_bytes {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr}
    {t : Nat} {s : State} (h : LO c dp L R0 R1 A m₀ sp t s) (hw : 512 * t + 512 ≤ L) :
    bytesAt s.mem (dp + BitVec.ofNat 64 (512 * t)) 512 = bytesAt m₀ (dp + BitVec.ofNat 64 (512 * t)) 512 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [Offset.add_add, h.data _ (by omega), ite_eq_right (by omega)]

/-- A chunk of `open`: the invariant from `t` to `t + 1`. -/
theorem chunkO_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {t : Nat} (hge : 512 ≤ L - 512 * t) {s : State}
    (h : LO c dp L R0 R1 A m₀ sp t s) :
    WP isa chunkO s fun s' => LO c dp L R0 R1 A m₀ sp (t + 1) s' ∧
      s'.cf = some (decide (L - 512 * (t + 1) < 512)) := by
  have hLe := hl.L_lt
  have hw : 512 * t + 512 ≤ L := by omega
  have hq : dp + BitVec.ofNat 64 (512 * t) + 512 = dp + BitVec.ofNat 64 (512 * (t + 1)) := by
    have := window_eq dp (t := t + 1) (by omega); rwa [Nat.add_sub_cancel] at this
  have mst : stR (stA c) ∈ s.wr := by rw [h.wr]; simp
  have mbf : bufR (bfA c) ∈ s.wr := by rw [h.wr]; simp
  have md : (⟨dp, L⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hwd : DWin s.wr (dp + BitVec.ofNat 64 (512 * t)) := by
    intro off n hn
    exact ⟨_, md, by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hin : ∀ off n, off + n ≤ 512 →
      InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 off) n := by
    intro off n hn
    exact ⟨_, List.mem_append_right _ md, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have dsd : (stR (stA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * t))) := hl.win_cd hw (by decide)
  have dbd : (bufR (bfA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * t))) := hl.win_cd hw (by decide)
  have dqs : (dR5 (dp + BitVec.ofNat 64 (512 * t))).Disjoint (slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right (win hw)).symm
  refine WP.seq (WP.mono (chunkMainO_ok hk h.rdi h.rcx h.rsi mst mbf hwd hin h.consts dsd st_bf dbd dqs h.acc)
    fun s₁ ⟨d₁, a₁, f₁, g₁, rsi₁, rd₁, wr₁⟩ => ?_)
  rw [hq] at rsi₁
  have dslot : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t))],
      (⟨slot (bfA c), 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_eq]
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · exact hl.win_cd hw (by decide)
  have sl₁ : s₁.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 512 * t) := by
    rw [f₁.readW (Region.contains_self _ _) dslot (by decide), h.left]
  refine WP.mono (next_ok (st := stA c) (buf := bfA c) (s := s₁) (by rw [g₁ _ (by decide) (by decide), h.rdi])
    (by rw [g₁ _ (by decide) (by decide), h.rcx]) (by rw [wr₁]; exact mst)
    ⟨psR c, by rw [wr₁, h.wr]; simp, slot_in⟩ st_slot
    (n := L - 512 * t) (by omega) hge sl₁)
    fun s₂ ⟨_, sl₂, cnt₂, f₂, g₂, rd₂, wr₂, _, _, cf₂⟩ => ?_
  have dst : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t))], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf.sub_right (slotsR_sub _)
    · exact dsd
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame f₁ dst
  have FA : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
      s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
  refine ⟨⟨by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr], by rw [g₂ _ (by decide) (by decide),
    g₁ _ (by decide) (by decide), h.rdi], by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rcx],
    by rw [g₂ _ (by decide) (by decide), rsi₁],
    by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rsp], by omega,
    by rw [sl₂, show L - 512 * t - 512 = L - 512 * (t + 1) by omega], ?_, ?_, ?_, ?_, ?_⟩,
    by rw [cf₂, show L - 512 * t - 512 = L - 512 * (t + 1) by omega]⟩
  · rw [cnt₂, S₁, h.cnt, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ctr_add,
      show 8 * t + 8 = 8 * (t + 1) by omega]
  · intro k hk'
    have n_st : ¬ (stR (stA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.st_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    have n_sl : ¬ (⟨slot (bfA c), 8⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.ps_d _ (slot_ps _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    have n_sls : ¬ (slotsR (bfA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.bf_d _ (slotsR_sub _ _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    rw [f₂ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact n_st
      · exact n_sl)]
    by_cases hin' : 512 * t ≤ k ∧ k < 512 * t + 512
    · have ea : dp + BitVec.ofNat 64 k =
          dp + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) := by
        rw [Offset.add_add, Nat.add_sub_cancel' hin'.1]
      have x₁ := d₁ (k - 512 * t) (by omega)
      rw [← ea] at x₁
      rw [x₁, h.data k hk', ite_eq_right (by omega : ¬ k < 512 * t), ite_eq_left (by omega : k < 512 * (t + 1)),
        plus_block, h.cnt, ks_shift _ hk' hin'.1]
    · have n_w : ¬ (dR5 (dp + BitVec.ofNat 64 (512 * t))).Contains (dp + BitVec.ofNat 64 k) 1 := by
        simp only [Region.Contains]
        rw [Offset.sub_toNat' _ (by omega) (by omega)]
        split <;> omega
      rw [f₁ _ (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact n_sls
          · exact n_w), h.data k hk']
      by_cases hlt : k < 512 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega : k < 512 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬ k < 512 * (t + 1))]
  · refine h.consts.frame FA ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hiR_slots _
    · exact (hl.bf_d.sub_left (hiR_sub _)).sub_right (win hw)
    · exact (st_bf.symm.sub_left (hiR_sub _))
    · exact ((Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide) :
        (bufR (bfA c)).Disjoint (psR c)).sub_left (hiR_sub _)).sub_right slot_ps
  · rw [h.chunk_bytes hw, ← VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega),
      ← VG.Proof.Poly1305.bytesAt_add, show 512 * t + 512 = 512 * (t + 1) by omega] at a₁
    exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact a₁.r8, by rw [g₂ _ (by decide) (by decide)]; exact a₁.r9,
      by rw [g₂ _ (by decide) (by decide)]; exact a₁.r10, by rw [g₂ _ (by decide) (by decide)]; exact a₁.h2,
      by simp only [hval, g₂ _ (show Reg.r11 ≠ .rax by decide) (by decide),
        g₂ _ (show Reg.rbx ≠ .rax by decide) (by decide), g₂ _ (show Reg.rbp ≠ .rax by decide) (by decide)]
         exact a₁.val⟩
  · refine h.fr.trans (FA.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨bufR (bfA c), by simp, slotsR_sub _⟩
    · exact ⟨⟨dp, L⟩, by simp, win hw⟩
    · exact ⟨stR (stA c), by simp, fun _ h => h⟩
    · exact ⟨⟨slot (bfA c), 8⟩, by simp, fun _ h => h⟩

/-- The chunks, while at least 512 bytes remain, from the first. -/
theorem chunksO_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {s : State} (hge : 512 ≤ L) (h : LO c dp L R0 R1 A m₀ sp 0 s) :
    WP isa (.loop chunkO .ae) s fun s' => ∃ T, LO c dp L R0 R1 A m₀ sp T s' ∧ L - 512 * T < 512 := by
  let Inv : Nat → State → Prop := fun n s => ∃ u, n = L - 512 * u ∧ 512 ≤ L - 512 * u ∧
    LO c dp L R0 R1 A m₀ sp u s
  refine WP.loop (M := isa) Inv (fun n s ⟨u, hn, hu, hL⟩ => ?_) _ s ⟨0, rfl, by omega, h⟩
  refine WP.mono (chunkO_ok hl hk hu hL) fun s' ⟨hL', cf'⟩ => ?_
  by_cases hlt : L - 512 * (u + 1) < 512
  · exact .inl ⟨by simp [eval, cf', hlt], u + 1, hL', hlt⟩
  · exact .inr ⟨by simp [eval, cf', hlt], L - 512 * (u + 1), by omega, u + 1, rfl, by omega, hL'⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `bulkO`

`enter`, the chunks while 512 bytes remain, and `leaveO`. Of `L ≥ 512`
bytes of data, the first `512 T` are decrypted and their ciphertext (as on
entry) absorbed into the Poly1305 state, and `rbx`, `rbp` and `rsi`, `rdx`
are the rest.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR)
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.Poly1305.X86_64 (hval Keeps off)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)
open VG.Proof.Poly1305 (absorbAll)

theorem leaveO_eq : leaveO = Impl.Poly1305.X86_64.reduce ++ ([.store (at_ .rcx accOff) .r11,
    .store (at_ .rcx (accOff + 8)) .rbx, .store (at_ .rcx (accOff + 16)) .rbp,
    .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .mov .rdx (.mem (at_ .rcx lenOff)),
    .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
    .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)] : List Instr) := rfl

theorem storeO_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) (hw : psR c ∈ s.wr) :
    WP isa (.block [.store (at_ .rcx accOff) .r11,
    .store (at_ .rcx (accOff + 8)) .rbx, .store (at_ .rcx (accOff + 16)) .rbp,
    .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .mov .rdx (.mem (at_ .rcx lenOff)),
    .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
    .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]) s fun s' =>
      s'.mem = accMem s.mem c (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp) ∧
      s'.gpr .rbx = s.gpr .rsi ∧ s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧
      s'.gpr .rdx = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .rdx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 →
        s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions s.wr (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, hw, Offset.contains c (by omega) (by omega) (by decide)⟩
  have i : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions (s.rd ++ s.wr) (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, List.mem_append_right _ hw, Offset.contains c (by omega) (by omega) (by decide)⟩
  have o0 := o 448 (by decide) (by decide); have o1 := o 456 (by decide) (by decide)
  have o2 := o 464 (by decide) (by decide)
  have i0 := i 544 (by decide) (by decide); have i1 := i 520 (by decide) (by decide)
  have i2 := i 528 (by decide) (by decide); have i3 := i 536 (by decide) (by decide)
  apply WP.of_runBlock
  have se128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, State.store64,
    State.load64, readSrc, execAlu, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, hrcx, accOff,
    r12Off, r13Off, r14Off, lenOff, ofInt_bf, Nat.reduceAdd, reduceCtorEq, o0, o1, o2, i0, i1, i2, i3,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 => by
    simp only [h1, h2, h3, h4, h5, h6, h7, ite_false], trivial, trivial⟩
  all_goals simp (disch := decide) only [readW_writeW_ofNat, se128, bfA, BitVec.add_sub_cancel]

theorem bulkO_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) {s : State}
    (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 L) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa bulkO s fun s' => ∃ T, 1 ≤ T ∧ 512 * T ≤ L ∧ L - 512 * T < 512 ∧
      (∀ k < L, s'.mem (dp + BitVec.ofNat 64 k) = if k < 512 * T then
        s.mem (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt s.mem (stA c)) L).getD k 0
        else s.mem (dp + BitVec.ofNat 64 k)) ∧
      stateAt s'.mem (stA c) = ctr (stateAt s.mem (stA c)) (8 * T) ∧
      Repr s'.mem (psA c) key (msg ++ bytesAt s.mem dp (512 * T)) ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rsi = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rdi = stA c ∧ s'.gpr .rcx = bfA c ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.gpr .r13 = s.gpr .r13 ∧ s'.gpr .r14 = s.gpr .r14 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hLe := hl.L_lt
  unfold bulkO
  refine WP.seq (WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_)
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨R0, hR0⟩ : ∃ R0, s.mem.readW (off (psA c) 24) 64 &&& Proof.Poly1305.X86_64.M0 = R0 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, s.mem.readW (off (psA c) 32) 64 &&& Proof.Poly1305.X86_64.M1 = R1 := ⟨_, rfl⟩
  have hk : Key R0 R1 := ⟨hR0 ▸ Proof.Poly1305.X86_64.r0_lt _, hR1 ▸ Proof.Poly1305.X86_64.r1_lt _,
    hR1 ▸ Proof.Poly1305.X86_64.r1_mod _⟩
  have hr : clamp (leNum (key.take 16)) = rN R0 R1 := by
    rw [← hrep.2.1, ← Proof.Poly1305.X86_64.off_24, Proof.Poly1305.X86_64.clamp_key, hR0, hR1]
  obtain ⟨A, hA⟩ : ∃ A, leNum (bytesAt s.mem (psA c) 24) = A := ⟨_, rfl⟩
  have hAm : A = accumulate (rN R0 R1) msg := by rw [← hA, hrep.2.2, hr]
  have hAP : A < P := hAm ▸ VG.Proof.Poly1305.accumulate_lt _ _
  have hA' := hA
  rw [Proof.Poly1305.X86_64.leNum_acc] at hA'
  have dst : ∀ r ∈ [bufR (bfA c), stashR c], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf
    · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ dst
  have ds : ∀ k < L, ∀ d n, d + n ≤ 576 → ¬ (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 :=
    fun k hk d n h hc => hl.cd h _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
  have e₁ : ∀ k < L, s₁.mem (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k) := fun k hk => F₁ _ (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ds k hk 128 320 (by decide)
    · exact ds k hk 520 32 (by decide))
  have hd₁ : ∀ n, n ≤ L → bytesAt s₁.mem dp n = bytesAt s.mem dp n := fun n hn => by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => e₁ i (by have := List.mem_range.mp hi; omega)
  have h0 : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) 0 s₁ := by
    refine ⟨by rw [rd₁, hrd], by rw [wr₁, hwr], rdi₁, by rw [gk _ (.inl rfl), hrcx],
      by rw [gk _ (.inr (.inl rfl)), hrsi]; simp, gk _ (.inr (.inr rfl)), by omega,
      by rw [sl₁, hrdx, Nat.mul_zero, Nat.sub_zero], by simp [VG.Proof.ChaCha20.ctr_zero], fun k _ => by simp, C₁, ?_, Frame.refl _ _⟩
    rw [show 512 * 0 = 0 from rfl, show bytesAt s₁.mem dp 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
    refine ⟨r8₁.trans hR0, r9₁.trans hR1, by rw [r10₁, r9₁, hR1], ?_, ?_⟩
    · have hP : P = 2 ^ 130 - 5 := rfl
      rw [rbp₁]; omega_using [hA', hAP, hP]
    · simp only [hval, r11₁, rbx₁, rbp₁, hA']
  refine WP.seq (WP.mono (chunksO_ok hl hk hge h0) fun s₃ ⟨T, L₃, hT⟩ => ?_)
  rw [leaveO_eq]
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₃) fun s₄ ⟨red, k₄⟩ => ?_)
  refine WP.mono (storeO_ok (c := c) (s := s₄) (by rw [k₄.gpr', L₃.rcx]) (by rw [k₄.2.2.2, L₃.wr]; simp))
    fun s₅ ⟨m₅, rbx₅, rbp₅, rdx₅, r12₅, r13₅, r14₅, r15₅, g₅, rd₅, wr₅⟩ => ?_
  have hTL := L₃.le
  have hT1 : 1 ≤ T := by
    by_contra h'
    have : T = 0 := by omega
    subst this; omega
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have FA : Frame [accR c] s₃.mem s₅.mem := by rw [m₅, ← m₄]; exact accMem_frame _ _ _ _ _
  have S₅ : stateAt s₅.mem (stA c) = stateAt s₃.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame FA (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  have st3 : ∀ d, 520 ≤ d → d + 8 ≤ 544 →
      s₃.mem.readW (c + BitVec.ofNat 64 d) 64 = s₁.mem.readW (c + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    refine L₃.fr.readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint c (Or.inr (by omega)) (by omega) (by decide)
    · exact hl.cd (by omega)
    · exact Offset.disjoint c (Or.inr (by omega)) (by omega) (by decide)
    · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by omega)) (by omega) (by decide)
  have hkey : bytesAt s₅.mem (c + BitVec.ofNat 64 472) 32 = bytesAt s.mem (c + BitVec.ofNat 64 472) 32 := by
    have e₁ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) FA (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)) (by decide)
    have e₂ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) L₃.fr (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · exact hl.cd (by decide)
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
    have e₃ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) F₁ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
    rw [e₁, e₂, e₃]
  have hslot : s₄.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 (L - 512 * T) := by
    rw [m₄, ← slot_eq, L₃.left]
  have g5 : ∀ r : Reg, r = .rdi ∨ r = .rcx ∨ r = .rsp ∨ r = .rsi → s₅.gpr r = s₃.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k₄.gpr']
  refine ⟨T, hT1, hTL, hT, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [g5 _ (.inl rfl), L₃.rdi],
    by rw [g5 _ (.inr (.inl rfl)), L₃.rcx], ?_, ?_, ?_, r15₅, by rw [g5 _ (.inr (.inr (.inl rfl))), L₃.rsp],
    by rw [rd₅, k₄.2.2.1, L₃.rd, hrd], by rw [wr₅, k₄.2.2.2, L₃.wr, hwr]⟩
  · intro k hk
    rw [FA _ (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ds k hk 448 24 (by decide)),
      L₃.data k hk, e₁ k hk, S₁]
  · rw [S₅, L₃.cnt, S₁]
  · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := hrep.1; omega
  · rw [psA_24, hkey, ← psA_24]; exact hrep.2.1
  · rw [m₅, accMem_acc]
    show hval s₄ = _
    rw [red L₃.acc.h2, L₃.acc.val, hd₁ _ hTL, hr, VG.Proof.Poly1305.accumulate_append hrep.1, ← hAm,
      Nat.mod_eq_of_lt (VG.Proof.Poly1305.absorbAll_lt hAP _)]
  · rw [rbx₅, k₄.gpr', L₃.rsi]
  · rw [rbp₅, hslot]
  · rw [g5 _ (.inr (.inr (.inr rfl))), L₃.rsi]
  · rw [rdx₅, hslot]
  · rw [r12₅, m₄, st3 520 (by decide) (by decide), v12]
  · rw [r13₅, m₄, st3 528 (by decide) (by decide), v13]
  · rw [r14₅, m₄, st3 536 (by decide) (by decide), v14]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `cryptO`

`Stitch.cryptO`, in `open`'s context, does what `open`'s `macPadLengths`
followed by `crypt` does (`cryptO_ok`): the padded ciphertext and the
lengths block absorbed, and the data decrypted. With at most `fold` bytes it
is that code. Otherwise `bulkO` decrypts and absorbs the whole chunks
(`bulkO_ok`, moved to `open`'s permissions with `RegionModel.wp_narrow`),
or nothing below 512 bytes (`MidO`); `macPadLengths` absorbs the rest, as it
was on entry, and the lengths block; and `vg_chacha20_xor` decrypts the
rest from the counter `bulkO` leaves.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

/-- After `cryptO`'s branch on 512 bytes: the first `E` bytes (a multiple of
64, all the whole chunks) decrypted, and their ciphertext, as it was in the
state `s` before the branch's arguments, absorbed. -/
structure MidO (s₀ s : State) (key msg : List Byte) (E : Nat) (s' : State) : Prop where
  rbx : s'.gpr .rbx = dp s₀ + BitVec.ofNat 64 E
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L s₀ - E)
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  E64 : E % 64 = 0
  EL : E ≤ L s₀
  Ediv : E = 512 * (L s₀ / 512)
  st : stateAt s'.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64)
  data : ∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then
    s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  frame : Frame [sub s₀ 64 512, dR s₀] s.mem s'.mem
  repr : Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (dp s₀) E)

/-- Below 512 bytes: nothing decrypted yet, nothing absorbed. -/
theorem whole_midO {s₀ : State} (hp : APre e s₀) {s s₂ : State} (ha : Args s₀ s s₂)
    (h15 : s₂.gpr .r15 = s.gpr .r15) (hlt : L s₀ < 512)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (.block whole) s₂ (MidO s₀ s key msg 0) := by
  refine WP.mono (whole_ok s₂) fun s₃ ⟨rbx₃, rbp₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  refine ⟨by rw [rbx₃, ha.r14]; simp, by rw [rbp₃, ha.r13, Nat.sub_zero], fun r hr => ?_, by rw [rd₃, ha.rd],
    by rw [wr₃, ha.wr], rfl, Nat.zero_le _, by omega, ?_, fun k hk => ?_, ?_, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [g₃ _ (by decide) (by decide), ha.keep _ (.inl rfl)]
    · rw [g₃ _ (by decide) (by decide), ha.keep _ (.inr (.inl rfl))]
    · rw [g₃ _ (by decide) (by decide), ha.keep _ (.inr (.inr (.inl rfl)))]
    · rw [g₃ _ (by decide) (by decide), h15]
    · rw [g₃ _ (by decide) (by decide), ha.keep _ (.inr (.inr (.inr rfl)))]
  · rw [m₃, ha.mem, stateAt_ctr, hst, set12_initState, Nat.zero_div, VG.Proof.ChaCha20.ctr_zero]
  · rw [m₃, ha.mem, args_data hp _ hk, ite_eq_right (Nat.not_lt_zero _)]
  · rw [m₃, ha.mem]
    exact (args_frame s₀ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · rw [show bytesAt s.mem (dp s₀) 0 = [] from rfl, List.append_nil, m₃, ha.mem]
    exact args_repr hrep

/-- The whole chunks: `bulkO`, with its permissions. -/
theorem bulk_midO {s₀ : State} (hp : APre e s₀) {s s₂ : State} (hwr : s.wr = s₀.wr) (ha : Args s₀ s s₂)
    (h15 : s.gpr .r15 = cx s₀) (hge : 512 ≤ L s₀)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa bulkO s₂ fun s₃ => ∃ E, MidO s₀ s key msg E s₃ := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hl : Lay (cx s₀) (dp s₀) (L s₀) := ⟨hL9, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have st₂ : stateAt s₂.mem (stA (cx s₀)) = initState (K s₀) 1 (N s₀) := by
    show stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64) = _
    rw [ha.mem, ← off_eq, stateAt_ctr, hst, set12_initState]
  have hw : Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.wr := bulk_covers hp (by rw [ha.wr, hwr])
  have hn : bulkO.noCalls = true := by decide +kernel
  refine regionModel.wp_narrow (r := []) (w := bulkWr (cx s₀) (dp s₀) (L s₀))
    (bulkO_ok hl hge (s := s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) rfl rfl ha.rsi ha.rdx
      (by rw [State.withRegions_gpr, ha.rcx, off_eq])
      (by show Repr _ (cx s₀ + BitVec.ofNat 64 448) _ _
          rw [State.withRegions_mem, ha.mem, ← off_eq]; exact args_repr hrep))
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s₃ _ rd₃ wr₃ f₃ hP => ?_
  obtain ⟨T, t1, le, lt, data, cnt, repr, rbx, rbp, rsi, rdx, rdi, rcx, r12, r13, r14, r15, rsp, -, -⟩ := hP
  have f₃' : Frame (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.mem s₃.mem := f₃
  have cnt' : stateAt s₃.mem (cx s₀ + BitVec.ofNat 64 64) =
      ctr (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (8 * T) := cnt
  have data' : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = if k < 512 * T then
      s₂.mem (dp s₀ + BitVec.ofNat 64 k) ^^^
        (keystream (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)).getD k 0
      else s₂.mem (dp s₀ + BitVec.ofNat 64 k) := data
  have hb : bytesAt s₂.mem (dp s₀) (512 * T) = bytesAt s.mem (dp s₀) (512 * T) := by
    simp only [bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [ha.mem, args_data hp _ (by have := List.mem_range.mp hk; omega)]
  refine ⟨512 * T, rbx, rbp, fun r hr => ?_, (rd₃ : s₃.rd = s₂.rd).trans ha.rd, (wr₃ : s₃.wr = s₂.wr).trans ha.wr,
    by omega, le, by omega, ?_, fun k hk => ?_, ?_, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (r12 : s₃.gpr .r12 = s₂.gpr .r12).trans (ha.keep _ (.inl rfl))
    · exact (r13 : s₃.gpr .r13 = s₂.gpr .r13).trans (ha.keep _ (.inr (.inl rfl)))
    · exact (r14 : s₃.gpr .r14 = s₂.gpr .r14).trans (ha.keep _ (.inr (.inr (.inl rfl))))
    · exact (r15 : s₃.gpr .r15 = cx s₀).trans h15.symm
    · exact (rsp : s₃.gpr .rsp = s₂.gpr .rsp).trans (ha.keep _ (.inr (.inr (.inr rfl))))
  · rw [off_eq, cnt', st₂, show 512 * T / 64 = 8 * T by omega]
  · rw [data' k hk, st₂, ha.mem, args_data hp _ hk]
  · rw [ha.mem] at f₃'
    refine ((args_frame s₀ s.mem).sub fun r hr => ?_).trans (f₃'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have e : sub s₀ 64 512 = ⟨cx s₀ + BitVec.ofNat 64 64, 512⟩ := by rw [sub, off_eq]
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
  · rw [off_eq, ← hb]; exact repr

theorem movRest_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .rbx), .mov .rdx (.reg .rbp)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rbx ∧ s'.gpr .rdx = s.gpr .rbp ∧ (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left',
    reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial⟩

/-- `restArgs`: the arguments of the call on the rest. -/
theorem restArgs_ok {s₀ : State} {s : State} (h15 : s.gpr .r15 = cx s₀) :
    WP isa (.block restArgs) s fun s' =>
      s'.gpr .rdi = off (cx s₀) 64 ∧ s'.gpr .rsi = s.gpr .rbx ∧ s'.gpr .rdx = s.gpr .rbp ∧
      s'.gpr .rcx = off (cx s₀) 128 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  unfold restArgs
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 64) (by lit_omega) s)
    fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (movRest_ok s₁) fun s₂ ⟨rsi₂, rdx₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
  refine WP.mono (ptr_ok .rcx .r15 (k := 128) (by lit_omega) s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  refine ⟨by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), e₁, h15],
    by rw [g₃ _ (by decide), rsi₂, g₁ _ (by decide)], by rw [g₃ _ (by decide), rdx₂, g₁ _ (by decide)],
    by rw [e₃, g₂ _ (by decide) (by decide), g₁ _ (by decide), h15], fun r a b c d => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [m₃, m₂, m₁]⟩
  rw [g₃ r d, g₂ r b c, g₁ r a]

/-- The rest, `[E, L)`, decrypted by the implementation `v` of `vg_chacha20_xor`
from the counter the chunks left. -/
theorem restCall_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : Inv s₀ s) {E : Nat} (hE : E % 64 = 0) (hEL : E ≤ L s₀)
    (hrbx : s.gpr .rbx = dp s₀ + BitVec.ofNat 64 E) (hrbp : s.gpr .rbp = BitVec.ofNat 64 (L s₀ - E))
    (hst : stateAt s.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64)) :
    WP isa (.seq (.block restArgs) (.call v.callee.name v.callee.code)) s fun s' =>
      s'.gpr .rsi = off (cx s₀) 128 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      (∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then s.mem (dp s₀ + BitVec.ofNat 64 k)
        else s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0) ∧
      s'.mxcsr = s.mxcsr := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩ (dR s₀) := Offset.sub_base _ (by omega)
  refine WP.seq (WP.mono_mx (by decide +kernel) (restArgs_ok (s₀ := s₀) h.r15)
    fun s₁ ⟨rdi₁, rsi₁, rdx₁, rcx₁, g₁, rd₁, wr₁, m₁⟩ mx₁ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h.rsp]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩, ⟨off (cx s₀) 128, 320⟩]
      s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₁, h.wr]; exact hp.ctx_wr, 64, by simp [off_eq], by show 64 + 64 ≤ 1696; omega⟩
    · exact ⟨dR s₀, by rw [wr₁, h.wr]; exact hp.d_wr, E, rfl, by show E + (L s₀ - E) ≤ L s₀; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₁, h.wr]; exact hp.ctx_wr, 128, by simp [off_eq], by show 128 + 320 ≤ 1696; omega⟩
  refine WP.mono_mx (by simp only [Code.allInstrs, v.mxcsr]) (Q := fun s' => s'.gpr .rsi = off (cx s₀) 128 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      (∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then s.mem (dp s₀ + BitVec.ofNat 64 k)
        else s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0))
    ?_ fun s' h' mx' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2, by rw [mx', mx₁]⟩
  refine xor_call v (S := off (cx s₀) 64) (D := dp s₀ + BitVec.ofNat 64 E) (B := off (cx s₀) 128)
    rdi₁ (by rw [rsi₁, hrbx]) (by rw [rdx₁, hrbp]) rcx₁ (by omega)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ E (by omega)) _) (by have := hp.wrap_d; omega))
    (by rw [rsp₁]; exact hp.stk_sub (by lit_omega)) (by rw [rsp₁]; exact hp.stk_d.sub_right dsub)
    (by rw [rsp₁]; exact hp.stk_sub (by lit_omega)) (Covers.right hw) hw
    fun s' rd' wr' cs' f' rsi' data' => ?_
  rw [rsp₁] at f'
  have ks' : (keystream (stateAt s₁.mem (off (cx s₀) 64)) (L s₀ - E)).length = L s₀ - E :=
    VG.Proof.ChaCha20.length_keystream _ _
  refine ⟨rsi', fun r hr => ?_, by rw [rd', rd₁], by rw [wr', wr₁], ?_, fun k hk => ?_⟩
  · have := calleeSaved_ne hr
    rw [cs' r hr, g₁ r this.2.2.2.2 this.2.2.2.1 this.2.2.1 this.2.1]
  · rw [m₁] at f'
    refine f'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, dsub⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · by_cases hkE : k < E
    · rw [ite_eq_left hkE, ← m₁]
      refine f' _ fun r hr hc => ?_
      have hin : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.c_d _ (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega) _ hc) hin
      · simp only [Region.Contains] at hc
        rw [Offset.sub_toNat' _ (by omega) (by omega)] at hc
        split at hc <;> omega
      · exact hp.c_d _ (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega) _ hc) hin
      · exact hp.stk_d _ hc hin
    · have x := xor_at ks' data' (j := k - E) (by omega)
      rw [Offset.add_add, Nat.add_sub_cancel' (by omega), m₁, hst, ks_from _ hE hk (by omega)] at x
      rw [ite_eq_right hkE, x]

/-- After `cryptO`'s branch, before the keystream is wiped: what `open`'s
`macPadLengths` and `crypt`'s branch leave. -/
structure CryptedO (s₀ s : State) (key msg : List Byte) (s' : State) : Prop where
  rsi : s'.gpr .rsi = off (cx s₀) 128
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .rsp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sub s₀ 64 528, dR s₀, stkR s₀] s.mem s'.mem
  data : bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))
  repr : Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem (dp s₀) (L s₀) ++
    pad16 (bytesAt s.mem (dp s₀) (L s₀))) ++ bytesAt s.mem (off (cx s₀) 592) 16)
  mx : s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

/-- `cryptArgs` and the comparison with 512, and `r15` kept. -/
theorem argsCmpO_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) s fun s₂ =>
      Args s₀ s s₂ ∧ s₂.gpr .r15 = s.gpr .r15 ∧ s₂.cf = some (decide (L s₀ < 512)) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.block_append (WP.mono (cryptA_ok hp h) fun s₂ ⟨m₂, rdi₂, rsi₂, rdx₂, rcx₂, cs₂, rd₂, wr₂⟩ =>
    WP.mono (cmp512_ok hL9 (by rw [rdx₂, hL])) fun s₃ ⟨g₃, rd₃, wr₃, m₃, c₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun r hr => ?_, by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩, ?_, c₃⟩)
  · rw [m₃, m₂]
  · rw [g₃, rdi₂]
  · rw [g₃, rsi₂]
  · rw [g₃, rdx₂, hL]
  · rw [g₃, rcx₂]
  · rw [g₃, cs₂ _ (by simp [calleeSaved]), h.r13, hL]
  · rw [g₃, cs₂ _ (by simp [calleeSaved]), h.r14]
  · rw [g₃, cs₂ r (by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
  · rw [g₃, cs₂ _ (by simp [calleeSaved])]

/-- More than `fold` bytes: the whole chunks decrypted and absorbed by
`bulkO` (none below 512 bytes), the rest and the lengths block absorbed, and
the rest decrypted by the implementation `v` of `vg_chacha20_xor`. -/
theorem bigO_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (.seq (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
      (.seq (.ite .b (.block whole) bulkO)
      (.seq (macPadLengths v.poly .rbx .rbp)
      (.seq (.block restArgs) (.call v.callee.name v.callee.code))))) s (CryptedO s₀ s key msg) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono_mx (by decide +kernel) (argsCmpO_ok hp h) fun s₂ ⟨ha, h15, cf₂⟩ mx₂ => ?_)
  -- The whole chunks, if any.
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (Q := fun (s₃ : State) => ∃ E, MidO s₀ s key msg E s₃) ?_ fun s₃ ⟨E, hm⟩ mx₃ => ?_)
  · refine WP.ite (decide (L s₀ < 512)) (by simp [eval, cf₂]) (fun hc => ?_) (fun hc' => ?_)
    · exact WP.mono (whole_midO hp ha h15 (by simpa using hc) hst hrep) fun s₄ hm₄ => ⟨0, hm₄⟩
    · simp only [decide_eq_false_iff_not] at hc'
      exact bulk_midO hp h.wr ha h.r15 (by omega) hst hrep
  have hEL := hm.EL
  have i₃ : Inv s₀ s₃ := Inv.step' h hm.keep hm.rd hm.wr hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  -- The rest absorbed, as it was on entry, with the lengths block.
  refine WP.seq (WP.mono (macPadLengths_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩
    (srcRest hp hEL) i₃ hm.rbx hm.rbp) fun s₄ ⟨i₄, cs₄, f₄, mx₄, r₄⟩ => ?_)
  have st₄ : stateAt s₄.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64) := by
    rw [stateAt_frame f₄ (by rdisj_all), hm.st]
  -- The rest decrypted.
  refine WP.mono (restCall_ok v hp i₄ hm.E64 hEL (by rw [cs₄ _ (by simp [calleeSaved]), hm.rbx])
    (by rw [cs₄ _ (by simp [calleeSaved]), hm.rbp]) st₄) fun s₅ ⟨rsi₅, cs₅, rd₅, wr₅, f₅, d₅, mx₅⟩ => ?_
  have dd : ∀ k < L s₀, ∀ r ∈ macR s₀, ¬ r.Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk r hr hc
    have hin : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.c_d _ (sub_ctx s₀ (k := 448) (n := 144) (by lit_omega) _ hc) hin
    · exact hp.stk_d _ hc hin
  have e₄ : ∀ k < L s₀, s₄.mem (dp s₀ + BitVec.ofNat 64 k) = s₃.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => f₄ _ (dd k hk)
  have rest : bytesAt s₃.mem (dp s₀ + BitVec.ofNat 64 E) (L s₀ - E) =
      bytesAt s.mem (dp s₀ + BitVec.ofNat 64 E) (L s₀ - E) := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [Offset.add_add, hm.data _ (by omega), ite_eq_right (by omega)]
  have lens : bytesAt s₃.mem (off (cx s₀) 592) 16 = bytesAt s.mem (off (cx s₀) 592) 16 :=
    bytesAt_frame hm.frame (by rdisj_all) (by lit_omega)
  refine ⟨rsi₅, fun r hr => ?_, by rw [rd₅, i₄.rd, h.rd], by rw [wr₅, i₄.wr, h.wr], ?_, ?_, ?_, ?_⟩
  · have hc : r ∈ calleeSaved := by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved]
    rw [cs₅ r hc, cs₄ r hc, hm.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)]
  · refine ((hm.frame.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)).trans (f₅.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
    · simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
    apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
    intro k hk
    rw [d₅ k hk, e₄ k hk]
    by_cases hkE : k < E
    · rw [ite_eq_left hkE, hm.data k hk, ite_eq_left hkE]
    · rw [ite_eq_right hkE, hm.data k hk, ite_eq_right hkE]
  · have R₄ := r₄ key _ hm.repr
    rw [rest, lens] at R₄
    have R₅ := Repr.frame f₅ (by rdisj_all) R₄
    rwa [List.append_assoc msg, split_pad _ _ (by have := hm.E64; omega) hEL] at R₅
  · rw [mx₅, mx₄, mx₃, mx₂]

/-- At most `fold` bytes: `open`'s `macPadLengths`, then the keystream from
the prologue XORed into them. -/
theorem smallO_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hle : L s₀ ≤ v.callee.fold)
    (hks : ∀ k < mOf v.callee.fold v.callee.pass (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (.seq (macPadLengths v.poly .r14 .r13)
      (.seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
        (.seq (xorBufX v.callee.wide .r14) (.block (ptr .rsi .r15 128))))) s (CryptedO s₀ s key msg) := by
  have hL' := Nat.le_of_lt (s₀.gpr .r9).isLt
  have hM := Nat.le_trans (mOf_le v.callee.fold v.callee.pass (L s₀)) v.fold_le
  refine WP.seq (WP.mono (macPadLengths_ok v.poly hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) h
    h.r14 (by rw [h.r13]; exact hL s₀)) fun s₄ ⟨i₄, cs₄, f₄, mx₄, r₄⟩ => ?_)
  refine WP.mono_mx (by rcases wide_of v with h | h | h <;> (rw [h]; decide +kernel)) (cryptSmall_ok v.fold_le (wide_of v) hp i₄ hle (ks_frame f₄ (by rdisj_all) hM hks))
    fun s₅ c₅ mx₅ => ?_
  have D₄ : bytesAt s₄.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) := bytesAt_frame f₄ (by rdisj_all) hL'
  refine ⟨c₅.rsi, fun r hr => ?_, by rw [c₅.rd, i₄.rd, h.rd], by rw [c₅.wr, i₄.wr, h.wr], ?_, by rw [c₅.data, D₄],
    Repr.frame c₅.frame (by rdisj_all) (r₄ key msg hrep), by rw [mx₅, mx₄]⟩
  · have hc : r ∈ calleeSaved := by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved]
    rw [c₅.cs r hc (by rcases hr with rfl | rfl | rfl | rfl <;> decide), cs₄ r hc]
  · refine (f₄.sub fun r hr => ?_).trans (c₅.frame.sub fun r hr => ?_)
    · simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem foldM_mx (v : Proof.ChaCha20.X86_64.XorImpl) :
    (foldM v.callee.fold v.callee.pass).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases v.fold_poly with ⟨hf, hpass, -⟩ | ⟨hf, hpass, -⟩ | ⟨hf, hpass, -⟩ <;>
    (rw [hf, hpass]; decide +kernel)

/-- `cryptO`: as `open`'s `macPadLengths` and then `crypt`, by any
implementation `v` of `vg_chacha20_xor` and its `vg_poly1305_blocks`. -/
theorem cryptO_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mOf v.callee.fold v.callee.pass (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (cryptO v.callee v.poly) s fun s' => Inv s₀ s' ∧
      Frame [sub s₀ 64 528, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) ∧
      Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem (dp s₀) (L s₀) ++
        pad16 (bytesAt s.mem (dp s₀) (L s₀))) ++ bytesAt s.mem (off (cx s₀) 592) 16) ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hfl := v.fold_le
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hm := mOf_le v.callee.fold v.callee.pass (L s₀)
  unfold cryptO
  refine WP.seq (WP.mono_mx rfl (cmpFold_ok (fold := v.callee.fold) (by lit_omega) h.r13)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁, c₁⟩ mx₁ => ?_)
  have h₁ : Inv s₀ s₁ := h.step (fun r _ => by rw [g₁]) rd₁ wr₁ (rs := []) (by rw [m₁]; exact Frame.refl _ _)
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  refine WP.seq (WP.mono (Q := CryptedO s₀ s₁ key msg) ?_ fun s₂ c₂ => ?_)
  · refine WP.ite (decide (L s₀ < v.callee.fold + 1)) (by simp [eval, c₁]) (fun hc => ?_) (fun hc => ?_)
    · simp only [decide_eq_true_eq] at hc
      exact smallO_ok v hp h₁ (by omega) (by rw [m₁]; exact hks) (by rw [m₁]; exact hrep)
    · exact bigO_ok v hp h₁ (by rw [m₁]; exact hst) (by rw [m₁]; exact hrep)
  -- The keystream wiped, as in `crypt_ok`.
  refine WP.seq (WP.mono_mx (by decide +kernel) (anchor_ok .rsi (k := 128) (by lit_omega) s₂)
    fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_)
  have cs₃ : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp → s₃.gpr r = s.gpr r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [g₃ _ (by decide), c₂.keep _ (.inl rfl), g₁]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inl rfl)), g₁]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inr (.inl rfl))), g₁]
    · rw [e3, c₂.rsi, off_sub, h.r15]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inr (.inr rfl))), g₁]
  have fc : Frame [sub s₀ 64 528, dR s₀, stkR s₀] s.mem s₃.mem := by rw [m₃, ← m₁]; exact c₂.frame
  have i₃ : Inv s₀ s₃ := Inv.step' h cs₃ (by rw [rd₃, c₂.rd, rd₁]) (by rw [wr₃, c₂.wr, wr₁]) fc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact stk_work s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
      · exact (hp.stk_sub (by lit_omega)).symm)
  refine WP.seq (WP.mono_mx (foldM_mx v) (foldM_ok (fold := v.callee.fold) (pass := v.callee.pass) (len := L s₀) (by lit_omega) (pass_of v)
    hL9 (by rw [i₃.r13]; exact hL s₀)) fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ mx₄ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (add64_ok (n := mOf v.callee.fold v.callee.pass (L s₀)) d₄)
    fun s₅ ⟨d₅, g₅, rd₅, wr₅, m₅⟩ mx₅ => ?_)
  refine WP.mono_mx (by rcases wide_of v with h | h | h <;> (rw [h]; decide +kernel)) (zeroKs_ok (wide_of v) hp (n := 64 + mOf v.callee.fold v.callee.pass (L s₀)) (by omega)
    (by lit_omega) d₅ (by rw [g₅ _ (by decide), g₄ _ (by decide), i₃.r15]) (by rw [wr₅, wr₄, i₃.wr]))
    fun s₆ ⟨g₆, rd₆, wr₆, f₆, _⟩ mx₆ => ?_
  have g36 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 => by
    rw [g₆ r h1 h2, g₅ r h3, g₄ r h3]
  have f₅₆ : Frame [sub s₀ 672 1024] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
  have hbd : bytesAt s₆.mem (dp s₀) (L s₀) = bytesAt s₃.mem (dp s₀) (L s₀) :=
    bytesAt_frame f₅₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (by omega)
  refine ⟨Inv.step' i₃ (fun r hr => g36 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
      (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) f₅₆
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    ?_, ?_, ?_, ?_⟩
  · refine (fc.sub fun r hr => ?_).trans (f₅₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · rw [hbd, m₃, c₂.data, m₁]
  · rw [← m₁]
    refine Repr.frame f₅₆ (fun r hr => ?_) (by rw [m₃]; exact c₂.repr)
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [mx₆, mx₅, mx₄, mx₃, c₂.mx, mx₁]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `openStitched` is correct

As `open_correct`, with `cryptO` (`cryptO_ok`) in place of `open`'s
`macPadLengths` and `crypt`, which it does at once.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

theorem openStitched_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openStitched v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  refine WP.seq (WP.mono_mx (by decide +kernel) (entry_ok hp) fun s₀' e₀ mx₀ => ?_)
  subst e₀
  refine WP.seq (WP.mono_mx (prologue_mx v) (prologue_ok v hp) fun s₁ h₁ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono_mx (by decide +kernel) (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]),
    h₁.rbp])) fun s₃ ⟨i₃, _, f₃, len₃⟩ mx₃ => ?_)
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by rw [bytesAt_frame f₃ (by rdisj_all) hL', D₂]
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  have hM := Nat.le_trans (mOf_le v.callee.fold v.callee.pass (L s₀)) v.fold_le
  have ks₃ := ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)
  have R₃ := Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  refine WP.seq (WP.mono (cryptO_ok v hp i₃ st₃ ks₃ R₃) fun s₆ ⟨i₆, f₆, pt₆, R₆, mx₆⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (finalizeTo_ok hp i₆ (out := 48) (.inl (by omega_using [])))
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, rcx₇, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.block_append (WP.mono_mx (by decide +kernel) (compare_ok hp rcx₇
    (by rw [cs₇ _ (by simp [calleeSaved]), i₆.r12]) (by rw [rd₇, i₆.rd])
    (by rw [wr₇, i₆.wr])) fun s₈ ⟨rax₈, g₈, m₈, rd₈, wr₈⟩ mx₈ => ?_)
  refine WP.mono_mx (by decide +kernel) (restore_ok hp (by rw [g₈ _ (by decide) (by decide), rdi₇])
    (by rw [m₈]; exact i₆.saved.frame f₇ (by rdisj_all))
    (by rw [g₈ _ (by decide) (by decide), cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₈, rd₇, i₆.rd]) (by rw [wr₈, wr₇, i₆.wr])) fun s₉ ⟨cs₉, rax₉, m₉⟩ mx₉ => ?_
  -- The tag computed, and the one received.
  have T₇ := tag₇ _ _ R₆
  have L₃ : bytesAt s₃.mem (off (cx s₀) 592) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := len₃
  have T0₇ : bytesAt s₇.mem (tp s₀) 16 = T0 s₀ := by
    rw [bytesAt_frame f₇ (by rdisj_all) (by lit_omega), bytesAt_frame i₆.frame (by rdisj_all) (by lit_omega)]
  have P₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₉, m₈, bytesAt_frame f₇ (by rdisj_all) hL', pt₆, D₃]
  rw [L₃, D₃, hA] at T₇
  refine ⟨⟨cs₉, by rw [m₉, m₈]; exact ret_kept hp i₆.frame (hp.ret_c.sub_right (sub_ctx _ (by lit_omega))) f₇,
    by rw [mx₉, mx₈, mx₇, mx₆, mx₃, mx₂, mx₁, mx₀]⟩, ?_⟩
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₇.mem (off (cx s₀) 48) 16 := by
    rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  rw [openX86_64, Contract.post_mk]
  rw [rax₉, rax₈]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left (hm.symm.trans (hmac.trans T0₇.symm)), P₉⟩
  next hn => exact ite_eq_right fun he => decrypt_eq_none hn ((hm.trans he).trans T0₇)

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

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
def smallO (w : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (macPadLengths b .r14 .r13) (cryptSmall w)

/-- `cryptO`'s branch for more. -/
def bigO (x : Impl.ChaCha20.X86_64.Callee) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
    (.seq (.ite .b (.block whole) bulkO)
    (.seq (macPadLengths b .rbx .rbp) (.seq (.block restArgs) (.call x.name x.code))))

def iteO (x : Impl.ChaCha20.X86_64.Callee) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .ite .b (smallO x.wide b) (bigO x b)

theorem openS_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa (openStitched x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA x.fold x.pass x.wide) (.seq (.call x.name x.code)
      (.seq (sealMid x.fold b) (.seq (iteO x b) (openPost x.fold x.pass x.wide)))))) s t s' := by
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
def AtArgsO (fold pass : Nat) (s₀ s : State) : Prop :=
  ∃ σ, AtIteS fold pass s₀ σ ∧ Args s₀ σ s ∧ s.gpr .r15 = σ.gpr .r15 ∧ s.cf = some (decide (L s₀ < 512))

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
    (h : AtIteS v.callee.fold v.callee.pass s₀ s) (hle : L s₀ ≤ v.callee.fold) : WP isa (smallO v.callee.wide v.poly) s (After s₀) := by
  obtain ⟨hi, -, key, msg, hrep⟩ := h
  exact WP.mono (smallO_ok v hp hi.inv hle hi.ks hrep) fun s' c =>
    ⟨c.rsi, by rw [c.keep _ (.inr (.inr (.inr rfl))), hi.inv.rsp], by rw [c.keep _ (.inr (.inl rfl)), hi.inv.r13],
      by rw [c.keep _ (.inr (.inr (.inl rfl))), hi.inv.r14], by rw [c.keep _ (.inl rfl), hi.inv.r12],
      by rw [c.wr, hi.inv.wr]⟩

theorem argsO_at {fold pass : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtIteS fold pass s₀ s) :
    WP isa (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) s (AtArgsO fold pass s₀) :=
  WP.mono (argsCmpO_ok hp h.1.inv) fun _ ⟨ha, h15, cf⟩ => ⟨_, h, ha, h15, cf⟩

theorem wholeO_mid {fold pass : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtArgsO fold pass s₀ s)
    (hb : isa.eval .b s = some true) : WP isa (.block whole) s (MidSO s₀) := by
  obtain ⟨σ, ⟨hi, hst, key, msg, hrep⟩, ha, h15, cf⟩ := h
  simp only [eval, cf, Option.some.injEq, decide_eq_true_eq] at hb
  exact WP.mono (whole_midO hp ha h15 hb hst hrep) fun _ hm => ⟨σ, key, msg, 0, hi.inv, hm⟩

theorem bulkO_mid {fold pass : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtArgsO fold pass s₀ s)
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

theorem midO_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τA false) (sealMid fold b) h).isSome = true := by
  rcases h with ⟨rfl, rfl, -, rfl⟩ | ⟨rfl, rfl, -, rfl⟩ | ⟨rfl, rfl, -, rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksBigAvx2O, blocksBigAvx512O]

theorem smallO_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τS false) (smallO wide b) h).isSome = true := by
  rcases h with ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksSmallO, blocksBigAvx2O, blocksSmallAvx2O, blocksBigAvx512O,
      blocksSmallAvx512O]

theorem argsO_taint :
    ∃ h, (taintS.check (τS false) (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) h).isSome =
      true := by
  taint_decide_sum []

theorem macO_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τM false) (macPadLengths b .rbx .rbp) h).isSome = true := by
  rcases h with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
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
    RelCT isa (fun s₁ s₂ => (AtIteS v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteS v.callee.fold v.callee.pass s₀' s₂) ∧
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
  have args := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtIteS v.callee.fold v.callee.pass s₀ s₁ ∧
      AtIteS v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some false) (τS false)
      (fun _ _ h => agreeS hp hp' hq h.1.1.1 h.1.2.1) hA).wp
    (F₁ := AtArgsO v.callee.fold v.callee.pass s₀) (F₂ := AtArgsO v.callee.fold v.callee.pass s₀') fun _ _ h =>
      ⟨argsO_at hp h.1.1, argsO_at hp' h.1.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hcf : ∀ s₁ s₂, (AtArgsO v.callee.fold v.callee.pass s₀ s₁ ∧ AtArgsO v.callee.fold v.callee.pass s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    obtain ⟨⟨_, -, -, -, c₁⟩, ⟨_, -, -, -, c₂⟩⟩ := h
    simp only [eval, c₁, c₂, eL]
  have wh := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtArgsO v.callee.fold v.callee.pass s₀ s₁ ∧
      AtArgsO v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some true) (τR [])
      (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hW).wp
    (F₁ := MidSO s₀) (F₂ := MidSO s₀') fun _ _ h => ⟨wholeO_mid hp h.1.1 h.2,
      wholeO_mid hp' h.1.2 (by rw [← hcf _ _ h.1]; exact h.2)⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hl : Lay (cx s₀) (dp s₀) (L s₀) :=
    ⟨(s₀.gpr .r9).isLt, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have bk : RelCT isa (fun s₁ s₂ => (AtArgsO v.callee.fold v.callee.pass s₀ s₁ ∧ AtArgsO v.callee.fold v.callee.pass s₀' s₂) ∧
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
    (F₁ := FArgs v.callee.fold v.callee.pass s₀) (F₂ := FArgs v.callee.fold v.callee.pass s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok hfl (pass_of v) (wide_of v) hp, by rw [h.2]; exact prologueA_ok hfl (pass_of v) (wide_of v) hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have mid := ((RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => AfterF v.callee.fold v.callee.pass s₀ s₁ ∧ AfterF v.callee.fold v.callee.pass s₀' s₂) (τA false)
    (fun _ _ h => agreeA hp hp' hq h.1 h.2) hmid).wp (F₁ := AtIteS v.callee.fold v.callee.pass s₀)
    (F₂ := AtIteS v.callee.fold v.callee.pass s₀') fun _ _ h =>
      ⟨sealMidS_ok hfl v.poly hp h.1, sealMidS_ok hfl v.poly hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hc : ∀ s₁ s₂, (AtIteS v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteS v.callee.fold v.callee.pass s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    have : L s₀ = L s₀' := by simp only [L, hq.2.2.2.2.2.1]
    simp [eval, h.1.1.cf, h.2.1.cf, this]
  have small := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteS v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteS v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some true)
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
  rcases v.fold_poly with ⟨hf, hpass, hw, hb⟩ | ⟨hf, hpass, hw, hb⟩ | ⟨hf, hpass, hw, hb⟩ <;>
    (simp only [openStitched, prologue, cryptO, Code.all, v.spSafe, hf, hpass, hw, hb]; lit_decide)

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
    padTail, cryptO, absorbLengths, finalizeTo, finalizeWith, Code.x86_64Depth, xorBuf_xdepth, splitM_xdepth,
    init_xdepth,
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
