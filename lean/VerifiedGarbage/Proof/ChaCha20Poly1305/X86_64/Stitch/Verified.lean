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
def smallS : Prog isa :=
  .seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
    (.seq (xorBufX .r14) (.block (ptr .rsi .r15 128 ++ whole)))

/-- `cryptS`'s branch for more. -/
def bigS (x : Impl.ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
    (.seq (.ite .b (.block whole) bulk) (.call x.name x.code))

def iteS (x : Impl.ChaCha20.X86_64.Callee) : Prog isa := .ite .b smallS (bigS x)

/-- `sealStitched` after the branch. -/
def postS (fold pass : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (wipe fold pass) (.seq (macPadLengths b .rbx .rbp) (.seq finalizeTag (.block restore)))

theorem sealS_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa (sealStitched x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA x.fold x.pass) (.seq (.call x.name x.code)
      (.seq (sealMid x.fold b) (.seq (iteS x) (postS x.fold x.pass b)))))) s t s' := by
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

theorem smallS_ok {fold pass : Nat} (hf : fold ≤ 960) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : AtIte fold pass s₀ s) (hle : L s₀ ≤ fold) : WP isa smallS s (AfterS s₀) := by
  unfold smallS
  apply seq3
  refine WP.mono (cryptSmall_ok hf hp h.inv hle h.ks) fun s₃ c₃ => ?_
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

theorem smallS_taint : ∃ h, (taintS.check (τS true) smallS h).isSome = true := by
  taint_decide_sum []

theorem argsS_taint :
    ∃ h, (taintS.check (τS true) (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) h).isSome =
      true := by
  taint_decide_sum []

theorem whole_taint : ∃ h, (taintS.check (τR []) (.block whole) h).isSome = true := by
  taint_decide_sum []

theorem postS_taint {fold pass : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass b) :
    ∃ h, (taintS.check (τ₁S true) (postS fold pass b) h).isSome = true := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
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
  obtain ⟨_, hS⟩ := smallS_taint
  obtain ⟨_, hpost⟩ := postS_taint v.fold_poly
  have pA := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ true)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq) hA).wp
    (F₁ := FArgs v.callee.fold v.callee.pass s₀) (F₂ := FArgs v.callee.fold v.callee.pass s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok hfl (pass_of v) hp, by rw [h.2]; exact prologueA_ok hfl (pass_of v) hp'⟩).mono
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
      exact ⟨smallS_ok hfl hp h.1.1.1 (by omega), smallS_ok hfl hp' h.1.2.1 (by omega)⟩
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
  rcases v.fold_poly with ⟨hf, hpass, hb⟩ | ⟨hf, hpass, hb⟩ | ⟨hf, hpass, hb⟩ <;>
    (simp only [sealStitched, prologue, cryptS, Code.all, v.spSafe, hf, hpass, hb]; lit_decide)

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
