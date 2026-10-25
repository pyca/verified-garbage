module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Prologue
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.SmallTest
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailK
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Lit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Tail3O
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Pad
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Prefix
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBufX
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Prologue
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.SmallTest
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailK
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Lit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Tail3O
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Pad
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Prefix
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBufX
meta import VerifiedGarbage.Proof.Framework.ContractPost
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Crypt
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Crypt
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# ChaCha20 and Poly1305 together (x86-64): `bulk` is constant time

The taint analysis checks `enter`, each chunk and `leave` on their own, with
only the pointers public; the loop's condition, which the analysis cannot
see is public (it compares the number of bytes left, kept in memory, with
512), agrees in two runs by correctness: it is a function of the length
(`LI`), as are the conditions on the bytes left after the loop
(`rest_rel`). The tail is checked in two parts: `tailAB` with only the
pointers public, and the XOR into the bytes left with their address and
number, loaded from memory, public by correctness (`TailMid`). `bulk_rel` is stated with `bulk`'s permissions (`bulkWr`), and
`relCT_narrow` moves it to `seal`'s.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts)
open VG.Proof.Poly1305.X86_64 (hval off)
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)

/-- Solve permission-list facts without simplifying the region addresses. -/
tactic_template "frame_regions" : tactic => `(tactic|
  simp only [bulkWr, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    eq_self, or_true, true_or, and_true, forall_eq_or_imp, forall_eq])

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

theorem firstChunk_taint (vl : Bool) :
    ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (firstChunk vl) h).isSome = true := by
  cases vl <;> taint_decide_sum []

/-! The stitched rounds, which the chunks of `seal` and `open` and the tails
of eight blocks run after `setup`, analysed once for each configuration, as
summaries. -/

taint_summary sroundsFF : taintS (τR [.rdi, .rcx, .rsi, .rsp]) (sroundsFor false false)
taint_summary sroundsFT : taintS (τR [.rdi, .rcx, .rsi, .rsp]) (sroundsFor false true)
taint_summary sroundsTF : taintS (τR [.rdi, .rcx, .rsi, .rsp]) (sroundsFor true false)
taint_summary sroundsTT : taintS (τR [.rdi, .rcx, .rsi, .rsp]) (sroundsFor true true)

theorem chunk_taint (vl : Bool) :
    ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (chunk vl false) h).isSome = true := by
  cases vl
  · taint_decide_sum [sroundsFF]
  · taint_decide_sum [sroundsTF]

theorem chunkP_taint (vl : Bool) :
    ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (chunk vl true) h).isSome = true := by
  cases vl
  · taint_decide_sum [sroundsFT]
  · taint_decide_sum [sroundsTT]

theorem leave_taint : ∃ h, (taintS.check (τR [.rcx, .rsi, .rsp]) (.block leave) h).isSome = true := by
  taint_decide_sum []

theorem nil_taint : ∃ h, (taintS.check (τR []) (.block []) h).isSome = true := by
  taint_decide_sum []

theorem restPre_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp])
    (.block [.mov .rdx (.mem (Impl.ChaCha20.X86_64.at_ .rcx lenOff)), .alu .sub .rdx (.imm 1),
      .alu .cmp .rdx (.imm 256)]) h).isSome = true := by
  taint_decide_sum []

theorem cmp128_taint :
    ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (.block [.alu .cmp .rdx (.imm 128)]) h).isSome = true := by
  taint_decide_sum []

theorem cmp448_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp])
    (.block (padIns .rax 19 ++ ([.alu .cmp .rdx (.imm 448)] : List Instr))) h).isSome = true := by
  taint_decide_sum []

theorem padK_taint : ∃ h, (taintS.check (τR []) (.block (padIns .rax 29)) h).isSome = true := by
  taint_decide_sum []

theorem tailKAB_taint (vl pre : Bool) :
    ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (tailKAB vl pre) h).isSome = true := by
  cases vl <;> cases pre <;> taint_decide_sum [sroundsFF, sroundsFT, sroundsTF, sroundsTT]

theorem tailAB_taint (two pre : Bool) :
    ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (tailAB two pre) h).isSome = true := by
  cases two <;> cases pre <;> taint_decide_sum []

theorem tailXE_taint : ∃ h, (taintS.check (τR [.rbx, .rsi, .rdx, .r9, .rsp])
    (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.seq (Impl.ChaCha20.X86_64.XorBuf.xorBufX 5 .rbx)
      (.block [.vop .vzeroupper, .mov .rcx (.reg .r9), .mov32 .rdx (.imm 0)]))) h).isSome = true := by
  taint_decide_sum []

section
variable {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) (sp : Addr) (vl : Bool)
include hl

/-- The later chunks, while at least 512 bytes remain. -/
theorem loop_rel :
    RelCT isa (fun s₁ s₂ => CI c dp L sp 1 s₁ ∧ CI c dp L sp 1 s₂ ∧
        s₁.cf = some (decide (L - 512 * 1 < 512)) ∧ s₂.cf = some (decide (L - 512 * 1 < 512)))
      (.ite .b (.block []) (.loop (chunk vl false) .ae))
      fun s₁ s₂ => ∃ T, CI c dp L sp T s₁ ∧ CI c dp L sp T s₂ ∧ L - 512 * T < 512 := by
  refine RelCT.ite (fun s₁ s₂ h => by simp only [eval, h.2.2.1, h.2.2.2]) ?_ ?_
  · obtain ⟨_, hn⟩ := nil_taint
    refine ((RelCT.taint (A := taintS) (τR []) (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hn).wpDep
      (F := fun s s' => s' = s) fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩).mono (fun _ _ h => h) ?_
    rintro _ _ ⟨-, σ₁, σ₂, ⟨⟨h₁, h₂, c₁, -⟩, hb⟩, rfl, rfl⟩
    simp only [eval, c₁, Option.some.injEq, decide_eq_true_eq] at hb
    exact ⟨1, h₁, h₂, hb⟩
  · obtain ⟨_, hc⟩ := chunk_taint vl
    let I : Nat → State → State → Prop := fun n s₁ s₂ =>
      ∃ t, n = L - 512 * t ∧ 512 ≤ L - 512 * t ∧ CI c dp L sp t s₁ ∧ CI c dp L sp t s₂
    have body : ∀ t, RelCT isa (fun s₁ s₂ => 512 ≤ L - 512 * t ∧ CI c dp L sp t s₁ ∧ CI c dp L sp t s₂) (chunk vl false)
        fun s₁ s₂ => (CI c dp L sp (t + 1) s₁ ∧ s₁.cf = some (decide (L - 512 * (t + 1) < 512))) ∧
          (CI c dp L sp (t + 1) s₂ ∧ s₂.cf = some (decide (L - 512 * (t + 1) < 512))) := by
      intro t
      have step : ∀ {s}, 512 ≤ L - 512 * t → CI c dp L sp t s → WP isa (chunk vl false) s fun s' =>
          CI c dp L sp (t + 1) s' ∧ s'.cf = some (decide (L - 512 * (t + 1) < 512)) :=
        fun hge' ⟨R0, R1, A, m₀, hk, hL⟩ => WP.mono (chunk_ok vl hl hk hge' hL) fun s' ⟨hL', cf'⟩ =>
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
        exact ⟨L - 512 * (t + 1), by omega_arith, t + 1, rfl, by omega_arith, h₁, h₂⟩
    · rintro s₁ s₂ ⟨⟨h₁, h₂, c₁, -⟩, hb⟩
      have : ¬ L - 512 * 1 < 512 := fun hc => by simp [eval, c₁, hc] at hb
      exact ⟨1, rfl, by omega_arith, h₁, h₂⟩
/-- `CI` with the comparison of the bytes left, `1 ≤ L - 512 T ≤ 256`. -/
def CP (c dp : Addr) (L : Nat) (sp : Addr) (T : Nat) (s : State) : Prop :=
  ∃ R0 R1 A m₀, Key R0 R1 ∧ LI c dp L R0 R1 A m₀ sp T s ∧
    s.cf = some (decide (1 ≤ L - 512 * T ∧ L - 512 * T ≤ 256)) ∧
    s.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - 1

/-- `CI` with the comparison of the bytes left with 128. -/
def C128 (c dp : Addr) (L : Nat) (sp : Addr) (T : Nat) (s : State) : Prop :=
  ∃ R0 R1 A m₀, Key R0 R1 ∧ LI c dp L R0 R1 A m₀ sp T s ∧ s.cf = some (decide (L - 512 * T ≤ 128))

/-- Before `tailS`: the `N` bytes at offset `o` of the data to absorb, and
the `n` after them to encrypt (`TP`). -/
def TT (c dp : Addr) (L o N n : Nat) (sp : Addr) (s : State) : Prop :=
  ∃ R0 R1 X, Key R0 R1 ∧ TP c dp L o N n R0 R1 X sp s

/-- The tail: the analysis checks `tailAB` with only the pointers public, and
the XOR into the bytes left with their address and number public, which they
are by correctness (`TailMidG`). -/
theorem tailSg_rel {o N n : Nat} (two pre : Bool) (hN : N = 16 * total pre)
    (hhi : n ≤ 128 * (if two then 2 else 1)) :
    RelCT isa (fun s₁ s₂ => TT c dp L o N n sp s₁ ∧ TT c dp L o N n sp s₂) (tailS two pre) fun _ _ => True := by
  obtain ⟨_, hA⟩ := tailAB_taint two pre
  obtain ⟨_, hX⟩ := tailXE_taint
  have mid : ∀ {s}, TT c dp L o N n sp s → WP isa (tailAB two pre) s fun s' =>
      ∃ R0 R1 X σ, TailMidG c dp o N n R0 R1 X sp σ s' :=
    fun ⟨R0, R1, X, hk, h⟩ => WP.mono (tailABg_ok hl hk two pre hN hhi h) fun s' t => ⟨R0, R1, X, _, t⟩
  have ag₁ : ∀ s₁ s₂, TT c dp L o N n sp s₁ ∧ TT c dp L o N n sp s₂ →
      X86_64.Taint.Agree (τR [.rdi, .rcx, .rsi, .rsp]) s₁ s₂ := by
    rintro s₁ s₂ ⟨⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩
    refine agree_regs _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.rdi, h₂.rdi]
    · rw [h₁.rcx, h₂.rcx]
    · rw [h₁.rsi, h₂.rsi]
    · rw [h₁.rsp, h₂.rsp]
  have ab := ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp]) ag₁ hA).wp
    fun _ _ h => ⟨mid h.1, mid h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have ag₃ : ∀ s₁ s₂, ((∃ R0 R1 X σ, TailMidG c dp o N n R0 R1 X sp σ s₁) ∧
      (∃ R0 R1 X σ, TailMidG c dp o N n R0 R1 X sp σ s₂)) →
      X86_64.Taint.Agree (τR [.rbx, .rsi, .rdx, .r9, .rsp]) s₁ s₂ := by
    rintro s₁ s₂ ⟨⟨_, _, _, _, t₁⟩, ⟨_, _, _, _, t₂⟩⟩
    refine agree_regs _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [t₁.rbx, t₂.rbx]
    · rw [t₁.rsi, t₂.rsi]
    · rw [t₁.rdx, t₂.rdx]
    · rw [t₁.r9, t₂.r9]
    · rw [t₁.rsp, t₂.rsp]
  exact ab.seq (RelCT.taint (A := taintS) (τR [.rbx, .rsi, .rdx, .r9, .rsp]) ag₃ hX)

/-- The tail after the whole chunks. -/
theorem tailS_rel (T : Nat) (two : Bool) (hhi : L - 512 * T ≤ 128 * (if two then 2 else 1)) :
    RelCT isa (fun s₁ s₂ => CI c dp L sp T s₁ ∧ CI c dp L sp T s₂) (tailS two false) fun _ _ => True :=
  (tailSg_rel hl sp two false (N := 512) rfl hhi).mono
    (fun _ _ ⟨⟨R0, R1, _, _, hk, h₁⟩, ⟨R0', R1', _, _, hk', h₂⟩⟩ =>
      ⟨⟨R0, R1, _, hk, TP.of_LI h₁⟩, ⟨R0', R1', _, hk', TP.of_LI h₂⟩⟩) fun _ _ h => h

/-- `CI` with the comparison of the bytes left, `1 ≤ L - 512 T ≤ 448`. -/
def C448 (c dp : Addr) (L : Nat) (sp : Addr) (T : Nat) (s : State) : Prop :=
  ∃ R0 R1 A m₀, Key R0 R1 ∧ LI c dp L R0 R1 A m₀ sp T s ∧
    s.cf = some (decide (1 ≤ L - 512 * T ∧ L - 512 * T ≤ 448))

/-- Before `tailKX`: `TT`, with the kernel's constants stored and the
keystream's slots writable. -/
def TK (c dp : Addr) (L o N n : Nat) (sp : Addr) (s : State) : Prop :=
  ∃ R0 R1 X, Key R0 R1 ∧ TP c dp L o N n R0 R1 X sp s ∧ Consts s.mem (bfA c) ∧ kR (bfA c) ∈ s.wr

/-- `tailKX`: the analysis checks `tailKAB` with only the pointers public, and
the XOR into the bytes left with their address and number public, which they
are by correctness (`TailMidKg`). -/
theorem tailKXg_rel {o N n : Nat} (pre : Bool) (hN : N = 16 * total pre) (ho : o + 512 ≤ L) (hn : n ≤ 512) :
    RelCT isa (fun s₁ s₂ => TK c dp L o N n sp s₁ ∧ TK c dp L o N n sp s₂) (tailKX vl pre) fun _ _ => True := by
  obtain ⟨_, hA⟩ := tailKAB_taint vl pre
  obtain ⟨_, hX⟩ := tailXE_taint
  have mid : ∀ {s}, TK c dp L o N n sp s → WP isa (tailKAB vl pre) s fun s' =>
      ∃ R0 R1 X σ, TailMidKg c dp o N n R0 R1 X sp σ s' :=
    fun ⟨R0, R1, X, hk, h, hc, mk⟩ => WP.mono (tailKABg_ok vl pre hl hk hN ho hn h hc mk)
      fun s' t => ⟨R0, R1, X, _, t⟩
  have ag₁ : ∀ s₁ s₂, TK c dp L o N n sp s₁ ∧ TK c dp L o N n sp s₂ →
      X86_64.Taint.Agree (τR [.rdi, .rcx, .rsi, .rsp]) s₁ s₂ := by
    rintro s₁ s₂ ⟨⟨_, _, _, _, h₁, _⟩, ⟨_, _, _, _, h₂, _⟩⟩
    refine agree_regs _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.rdi, h₂.rdi]
    · rw [h₁.rcx, h₂.rcx]
    · rw [h₁.rsi, h₂.rsi]
    · rw [h₁.rsp, h₂.rsp]
  have ab := ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp]) ag₁ hA).wp
    fun _ _ h => ⟨mid h.1, mid h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have ag₃ : ∀ s₁ s₂, ((∃ R0 R1 X σ, TailMidKg c dp o N n R0 R1 X sp σ s₁) ∧
      (∃ R0 R1 X σ, TailMidKg c dp o N n R0 R1 X sp σ s₂)) →
      X86_64.Taint.Agree (τR [.rbx, .rsi, .rdx, .r9, .rsp]) s₁ s₂ := by
    rintro s₁ s₂ ⟨⟨_, _, _, _, t₁⟩, ⟨_, _, _, _, t₂⟩⟩
    refine agree_regs _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [t₁.rbx, t₂.rbx]
    · rw [t₁.rsi, t₂.rsi]
    · rw [t₁.rdx, t₂.rdx]
    · rw [t₁.r9, t₂.r9]
    · rw [t₁.rsp, t₂.rsp]
  exact ab.seq (RelCT.taint (A := taintS) (τR [.rbx, .rsi, .rdx, .r9, .rsp]) ag₃ hX)

/-- `tailKX` after the whole chunks, with 257 to 448 bytes left. -/
theorem tailKX_rel (T : Nat) (hlo : 257 ≤ L - 512 * T) (hhi : L - 512 * T ≤ 448) :
    RelCT isa (fun s₁ s₂ => CI c dp L sp T s₁ ∧ CI c dp L sp T s₂) (tailKX vl false) fun _ _ => True := by
  by_cases hT : 1 ≤ T ∧ 512 * T ≤ L
  · exact (tailKXg_rel hl sp vl (o := 512 * (T - 1)) (N := 512) (n := L - 512 * T) false rfl (by omega_arith)
      (by omega_arith)).mono (fun _ _ ⟨⟨R0, R1, _, _, hk, h₁⟩, ⟨R0', R1', _, _, hk', h₂⟩⟩ =>
        ⟨⟨R0, R1, _, hk, TP.of_LI h₁, h₁.consts, by rw [h₁.wr]; simp⟩,
          ⟨R0', R1', _, hk', TP.of_LI h₂, h₂.consts, by rw [h₂.wr]; simp⟩⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ ⟨⟨_, _, _, _, _, h₁⟩, _⟩ => hT ⟨h₁.t1, h₁.le⟩

/-- `tailK`: `tailKX`, then its padding. -/
theorem tailK_rel (T : Nat) (hlo : 257 ≤ L - 512 * T) (hhi : L - 512 * T ≤ 448) :
    RelCT isa (fun s₁ s₂ => CI c dp L sp T s₁ ∧ CI c dp L sp T s₂) (tailK vl) fun _ _ => True := by
  obtain ⟨_, hp⟩ := padK_taint
  exact (tailKX_rel hl sp vl T hlo hhi).seq
    (RelCT.taint (A := taintS) (τR []) (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hp)

/-- After the whole chunks: the tail or `leave`, by the bytes left, which are
public by correctness (`LI`). -/
theorem rest_rel (T : Nat) :
    RelCT isa (fun s₁ s₂ => CI c dp L sp T s₁ ∧ CI c dp L sp T s₂ ∧ L - 512 * T < 512) (restT vl)
      fun _ _ => True := by
  unfold restT
  obtain ⟨_, hP⟩ := restPre_taint
  obtain ⟨_, hC⟩ := cmp128_taint
  obtain ⟨_, hC4⟩ := cmp448_taint
  obtain ⟨_, hL⟩ := leave_taint
  have pre : ∀ {s}, CI c dp L sp T s → WP isa (.block [.mov .rdx (.mem (Impl.ChaCha20.X86_64.at_ .rcx lenOff)),
      .alu .sub .rdx (.imm 1), .alu .cmp .rdx (.imm 256)]) s (CP c dp L sp T) :=
    fun ⟨R0, R1, A, m₀, hk, h⟩ => WP.mono (restPre_ok hl.L_lt h) fun s' ⟨h', cf, rdx⟩ =>
      ⟨R0, R1, A, m₀, hk, h', cf, rdx⟩
  have p := ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp]) (P := fun s₁ s₂ =>
      CI c dp L sp T s₁ ∧ CI c dp L sp T s₂ ∧ L - 512 * T < 512) (fun s₁ s₂ h => agree_regs _ ?_) hP).wp
    (F₁ := CP c dp L sp T) (F₂ := CP c dp L sp T) fun _ _ h => ⟨pre h.1, pre h.2.1⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  · refine p.seq (RelCT.ite (fun s₁ s₂ h => ?_) ?_ ?_)
    · obtain ⟨⟨_, _, _, _, _, _, c₁, _⟩, ⟨_, _, _, _, _, _, c₂, _⟩⟩ := h
      simp only [eval, c₁, c₂]
    · -- 1 to 256 bytes left.
      by_cases hc : 1 ≤ L - 512 * T ∧ L - 512 * T ≤ 256
      · have c128 : ∀ {s}, CP c dp L sp T s → WP isa (.block [.alu .cmp .rdx (.imm 128)]) s (C128 c dp L sp T) :=
          fun ⟨R0, R1, A, m₀, hk, h, _, rdx⟩ => WP.mono (cmp128_ok hc.1 hc.2 h rdx) fun s' ⟨h', cf⟩ =>
            ⟨R0, R1, A, m₀, hk, h', cf⟩
        have q := ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp])
          (P := fun s₁ s₂ => (CP c dp L sp T s₁ ∧ CP c dp L sp T s₂) ∧ isa.eval .b s₁ = some true)
          (fun s₁ s₂ h => agree_regs _ ?_) hC).wp
          (F₁ := C128 c dp L sp T) (F₂ := C128 c dp L sp T) fun _ _ h => ⟨c128 h.1.1, c128 h.1.2⟩).mono
          (fun _ _ h => h) fun _ _ h => h.2
        · refine q.seq (RelCT.ite (fun s₁ s₂ h => ?_) ?_ ?_)
          · obtain ⟨⟨_, _, _, _, _, _, c₁⟩, ⟨_, _, _, _, _, _, c₂⟩⟩ := h
            simp only [eval, c₁, c₂]
          · by_cases h128 : L - 512 * T ≤ 128
            · exact (tailS_rel hl sp T false (by simp only [Bool.false_eq_true, ite_false]; omega_arith)).mono
                (fun _ _ ⟨⟨⟨R0, R1, A, m₀, hk, h₁, _⟩, ⟨R0', R1', A', m₀', hk', h₂, _⟩⟩, _⟩ =>
                  ⟨⟨R0, R1, A, m₀, hk, h₁⟩, ⟨R0', R1', A', m₀', hk', h₂⟩⟩) fun _ _ h => h
            · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, _, _, _, c₁⟩, _⟩, hb⟩ => ?_
              simp only [eval, c₁, Option.some.injEq, decide_eq_true_eq] at hb
              exact h128 hb
          · exact (tailS_rel hl sp T true (by simp only [ite_true]; omega_arith)).mono
              (fun _ _ ⟨⟨⟨R0, R1, A, m₀, hk, h₁, _⟩, ⟨R0', R1', A', m₀', hk', h₂, _⟩⟩, _⟩ =>
                ⟨⟨R0, R1, A, m₀, hk, h₁⟩, ⟨R0', R1', A', m₀', hk', h₂⟩⟩) fun _ _ h => h
        · obtain ⟨⟨⟨_, _, _, _, _, h₁, _⟩, ⟨_, _, _, _, _, h₂, _⟩⟩, -⟩ := h
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [h₁.rdi, h₂.rdi]
          · rw [h₁.rcx, h₂.rcx]
          · rw [h₁.rsi, h₂.rsi]
          · rw [h₁.rsp, h₂.rsp]
      · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, _, _, _, c₁, _⟩, _⟩, hb⟩ => ?_
        simp only [eval, c₁, Option.some.injEq, decide_eq_true_eq] at hb
        exact hc hb
    · -- None or more than 256: `tailK` for up to 448, else `leave`.
      by_cases hc : 1 ≤ L - 512 * T ∧ L - 512 * T ≤ 256
      · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, _, _, _, c₁, _⟩, _⟩, hb⟩ => ?_
        simp only [eval, c₁, Option.some.injEq, decide_eq_false_iff_not] at hb
        exact hb hc
      · have c448 : ∀ {s}, CP c dp L sp T s → WP isa (.block (padIns .rax 19 ++ ([.alu .cmp .rdx (.imm 448)] : List Instr))) s
            (C448 c dp L sp T) :=
          fun ⟨R0, R1, A, m₀, hk, h, _, rdx⟩ => WP.mono (cmp448_ok hl.L_lt h rdx) fun s' ⟨h', cf⟩ =>
            ⟨R0, R1, A, m₀, hk, h', cf⟩
        have q := ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp])
          (P := fun s₁ s₂ => (CP c dp L sp T s₁ ∧ CP c dp L sp T s₂) ∧ isa.eval .b s₁ = some false)
          (fun s₁ s₂ h => agree_regs _ ?_) hC4).wp
          (F₁ := C448 c dp L sp T) (F₂ := C448 c dp L sp T) fun _ _ h => ⟨c448 h.1.1, c448 h.1.2⟩).mono
          (fun _ _ h => h) fun _ _ h => h.2
        · refine q.seq (RelCT.ite (fun s₁ s₂ h => ?_) ?_ ?_)
          · obtain ⟨⟨_, _, _, _, _, _, c₁⟩, ⟨_, _, _, _, _, _, c₂⟩⟩ := h
            simp only [eval, c₁, c₂]
          · by_cases h448 : 1 ≤ L - 512 * T ∧ L - 512 * T ≤ 448
            · refine RelCT.mono (tailK_rel hl sp vl T ?_ h448.2) (fun _ _ ⟨⟨⟨R0, R1, A, m₀, hk, h₁, _⟩,
                ⟨R0', R1', A', m₀', hk', h₂, _⟩⟩, _⟩ => ⟨⟨R0, R1, A, m₀, hk, h₁⟩, ⟨R0', R1', A', m₀', hk', h₂⟩⟩)
                fun _ _ h => h
              omega_arith
            · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, _, _, _, c₁⟩, _⟩, hb⟩ => ?_
              simp only [eval, c₁, Option.some.injEq, decide_eq_true_eq] at hb
              exact h448 hb
          · refine RelCT.taint (A := taintS) (τR [.rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hL
            obtain ⟨⟨⟨_, _, _, _, _, h₁, _⟩, ⟨_, _, _, _, _, h₂, _⟩⟩, -⟩ := h
            intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · rw [h₁.rcx, h₂.rcx]
            · rw [h₁.rsi, h₂.rsi]
            · rw [h₁.rsp, h₂.rsp]
        · obtain ⟨⟨⟨_, _, _, _, _, h₁, _⟩, ⟨_, _, _, _, _, h₂, _⟩⟩, -⟩ := h
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [h₁.rdi, h₂.rdi]
          · rw [h₁.rcx, h₂.rcx]
          · rw [h₁.rsi, h₂.rsi]
          · rw [h₁.rsp, h₂.rsp]
  · obtain ⟨⟨_, _, _, _, _, h₁⟩, ⟨_, _, _, _, _, h₂⟩, -⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.rdi, h₂.rdi]
    · rw [h₁.rcx, h₂.rcx]
    · rw [h₁.rsi, h₂.rsi]
    · rw [h₁.rsp, h₂.rsp]

include hge in
/-- `bulk`, with its permissions. -/
theorem bulk_rel :
    RelCT isa (fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂) (bulk vl) fun _ _ => True := by
  unfold bulk
  obtain ⟨_, hE⟩ := enter_taint
  obtain ⟨_, hF⟩ := firstChunk_taint vl
  have e := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂)
    (τR [.rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hE).wp
    fun _ _ h => ⟨enter_fc h.1, enter_fc h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  · have first : ∀ {s}, FC c dp L sp s → WP isa (firstChunk vl) s fun s' =>
        CI c dp L sp 1 s' ∧ s'.cf = some (decide (L - 512 * 1 < 512)) :=
      fun ⟨R0, R1, A, hk, rd, wr, rdi, rcx, rsi, rsp, sl, C, acc⟩ =>
        WP.mono (firstChunk_ok vl hl (m₀ := _) hge rd wr rdi rcx rsi rsp sl rfl C acc) fun s' ⟨hL', cf'⟩ =>
          ⟨⟨R0, R1, A, _, hk, hL'⟩, cf'⟩
    have f := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => FC c dp L sp s₁ ∧ FC c dp L sp s₂)
      (τR [.rdi, .rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hF).wp
      fun _ _ h => ⟨first h.1, first h.2⟩).mono (fun _ _ h => h)
      (Q' := fun (s₁ s₂ : State) => CI c dp L sp 1 s₁ ∧ CI c dp L sp 1 s₂ ∧
        s₁.cf = some (decide (L - 512 * 1 < 512)) ∧ s₂.cf = some (decide (L - 512 * 1 < 512)))
      fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩
    · exact e.seq (f.seq ((loop_rel hl sp vl).seq (RelCT.exists_ fun T => rest_rel hl sp vl T)))
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

/-! ## After the 448 bytes whose keystream the prologue computed -/

/-- Where `bulkP`, or `enter` and `tailS` after the 448 bytes, start. -/
def BPP (c dp : Addr) (L : Nat) (sp : Addr) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = bulkWr c dp L ∧ s.gpr .rsi = dp ∧ s.gpr .rdx = BitVec.ofNat 64 (L - 448) ∧
    s.gpr .rcx = bfA c ∧ s.gpr .rsp = sp ∧ ∃ key msg, Repr s.mem (psA c) key msg

/-- The permissions of the data after the 448 bytes are in those of all of it. -/
theorem covers_shift {c dp : Addr} {L : Nat} (h : 448 ≤ L) :
    Covers (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448)) (bulkWr c dp L) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨Proof.ChaCha20.X86_64.Avx2.stR (stA c), by simp, 0, by simp, by simp⟩
  · exact ⟨⟨dp, L⟩, by simp, 448, rfl, by show 448 + (L - 448) ≤ L; omega_arith⟩
  · exact ⟨Proof.ChaCha20.X86_64.Avx2.bufR (bfA c), by simp, 0, by simp, by simp⟩
  · exact ⟨psR c, by simp, 0, by simp, by simp⟩
  · exact ⟨kR (bfA c), by simp, 0, by simp, by simp⟩

section
variable {c dp : Addr} {L : Nat} (hl : Lay c dp L) (sp : Addr) (vl : Bool)
include hl

omit hl in
theorem bpp_agree {s₁ s₂ : State} (h₁ : BPP c dp L sp s₁) (h₂ : BPP c dp L sp s₂) :
    X86_64.Taint.Agree (τR [.rcx, .rsi, .rsp]) s₁ s₂ := by
  obtain ⟨_, _, rsi₁, _, rcx₁, rsp₁, -⟩ := h₁
  obtain ⟨_, _, rsi₂, _, rcx₂, rsp₂, -⟩ := h₂
  refine agree_regs _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [rcx₁, rcx₂]
  · rw [rsi₁, rsi₂]
  · rw [rsp₁, rsp₂]

/-- `TK` with the comparison of the bytes left, `1 ≤ n ≤ 256`. -/
def TKP (c dp : Addr) (L o N n : Nat) (sp : Addr) (s : State) : Prop :=
  TK c dp L o N n sp s ∧ s.cf = some (decide (1 ≤ n ∧ n ≤ 256)) ∧ s.gpr .rdx = BitVec.ofNat 64 n - 1

/-- `TK` with the comparison of the bytes left with 128. -/
def TK128 (c dp : Addr) (L o N n : Nat) (sp : Addr) (s : State) : Prop :=
  TK c dp L o N n sp s ∧ s.cf = some (decide (n ≤ 128))

/-- The rest without whole chunks after the 448 bytes: `enter` and the
comparisons checked by the analysis, the bytes left public by correctness
(`TP`), and the tails by `tailSg_rel` and `tailKXg_rel`. -/
theorem tailPS_rel (hlo : 449 ≤ L) (hhi : L ≤ 960) :
    RelCT isa (fun s₁ s₂ => BPP c dp L sp s₁ ∧ BPP c dp L sp s₂) (.seq (.block enter) (tailP vl))
      fun _ _ => True := by
  unfold tailP
  obtain ⟨_, hE⟩ := enter_taint
  obtain ⟨_, hP⟩ := restPre_taint
  obtain ⟨_, hC⟩ := cmp128_taint
  have tk : ∀ {s}, BPP c dp L sp s → WP isa (.block enter) s (TK c dp L 0 448 (L - 448) sp) :=
    fun ⟨_, wr, rsi, rdx, rcx, rsp, _, _, rep⟩ => WP.mono (enterTP_ok hlo wr rsi rdx rcx rep)
      fun _ ⟨R0, R1, X, hk, h, hc, mk⟩ => ⟨R0, R1, X, hk, by rw [rsp] at h; exact h, hc, mk⟩
  have e := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => BPP c dp L sp s₁ ∧ BPP c dp L sp s₂)
    (τR [.rcx, .rsi, .rsp]) (fun _ _ h => bpp_agree sp h.1 h.2) hE).wp
    (F₁ := TK c dp L 0 448 (L - 448) sp) (F₂ := TK c dp L 0 448 (L - 448) sp)
    fun _ _ h => ⟨tk h.1, tk h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have agTP : ∀ {o N n : Nat} {s₁ s₂ : State} {R0 R1 X R0' R1' X'},
      TP c dp L o N n R0 R1 X sp s₁ → TP c dp L o N n R0' R1' X' sp s₂ →
      X86_64.Taint.Agree (τR [.rdi, .rcx, .rsi, .rsp]) s₁ s₂ := by
    intro o N n s₁ s₂ R0 R1 X R0' R1' X' h₁ h₂
    refine agree_regs _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.rdi, h₂.rdi]
    · rw [h₁.rcx, h₂.rcx]
    · rw [h₁.rsi, h₂.rsi]
    · rw [h₁.rsp, h₂.rsp]
  have pre : ∀ {s}, TK c dp L 0 448 (L - 448) sp s → WP isa (.block [.mov .rdx (.mem (Impl.ChaCha20.X86_64.at_ .rcx lenOff)),
      .alu .sub .rdx (.imm 1), .alu .cmp .rdx (.imm 256)]) s (TKP c dp L 0 448 (L - 448) sp) :=
    fun ⟨R0, R1, X, hk, h, hc, mk⟩ => WP.mono (lenP_ok hl.L_lt h) fun s' ⟨h', m', w', _, _, cf, rdx⟩ =>
      ⟨⟨R0, R1, X, hk, h', by rw [m']; exact hc, by rw [w']; exact mk⟩, cf, rdx⟩
  have p := ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp]) (P := fun s₁ s₂ =>
      TK c dp L 0 448 (L - 448) sp s₁ ∧ TK c dp L 0 448 (L - 448) sp s₂)
      (fun _ _ ⟨⟨_, _, _, _, h₁, _⟩, ⟨_, _, _, _, h₂, _⟩⟩ => agTP h₁ h₂) hP).wp
    (F₁ := TKP c dp L 0 448 (L - 448) sp) (F₂ := TKP c dp L 0 448 (L - 448) sp)
    fun _ _ h => ⟨pre h.1, pre h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  refine e.seq (p.seq (RelCT.ite (fun s₁ s₂ ⟨⟨_, c₁, _⟩, ⟨_, c₂, _⟩⟩ => by simp only [eval, c₁, c₂]) ?_ ?_))
  · -- 1 to 256 bytes left.
    by_cases hc : 1 ≤ L - 448 ∧ L - 448 ≤ 256
    swap
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, c₁, _⟩, _⟩, hb⟩ => ?_
      simp only [eval, c₁, Option.some.injEq, decide_eq_true_eq] at hb
      exact hc hb
    have c128 : ∀ {s}, TKP c dp L 0 448 (L - 448) sp s → WP isa (.block [.alu .cmp .rdx (.imm 128)]) s
        (TK128 c dp L 0 448 (L - 448) sp) :=
      fun ⟨⟨R0, R1, X, hk, h, hc', mk⟩, _, rdx⟩ => WP.mono (cmpP128_ok hc.1 hc.2 rdx) fun s' ⟨g', m', w', _, cf⟩ =>
        ⟨⟨R0, R1, X, hk, TP.of_rdx h (fun r _ => by rw [g']) m' w', by rw [m']; exact hc', by rw [w']; exact mk⟩, cf⟩
    have q := ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp])
      (P := fun s₁ s₂ => (TKP c dp L 0 448 (L - 448) sp s₁ ∧ TKP c dp L 0 448 (L - 448) sp s₂) ∧
        isa.eval .b s₁ = some true)
      (fun _ _ ⟨⟨⟨⟨_, _, _, _, h₁, _⟩, _⟩, ⟨⟨_, _, _, _, h₂, _⟩, _⟩⟩, _⟩ => agTP h₁ h₂) hC).wp
      (F₁ := TK128 c dp L 0 448 (L - 448) sp) (F₂ := TK128 c dp L 0 448 (L - 448) sp)
      fun _ _ h => ⟨c128 h.1.1, c128 h.1.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    refine q.seq (RelCT.ite (fun s₁ s₂ ⟨⟨_, c₁⟩, ⟨_, c₂⟩⟩ => by simp only [eval, c₁, c₂]) ?_ ?_)
    · by_cases h128 : L - 448 ≤ 128
      · exact (tailSg_rel hl sp false true (o := 0) (N := 448) (n := L - 448) rfl
          (by simp only [Bool.false_eq_true, ite_false]; omega_arith)).mono
          (fun _ _ ⟨⟨⟨⟨R0, R1, X, hk, h₁, _⟩, _⟩, ⟨⟨R0', R1', X', hk', h₂, _⟩, _⟩⟩, _⟩ =>
            ⟨⟨R0, R1, X, hk, h₁⟩, ⟨R0', R1', X', hk', h₂⟩⟩) fun _ _ h => h
      · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, c₁⟩, _⟩, hb⟩ => ?_
        simp only [eval, c₁, Option.some.injEq, decide_eq_true_eq] at hb
        exact h128 hb
    · exact (tailSg_rel hl sp true true (o := 0) (N := 448) (n := L - 448) rfl
        (by simp only [ite_true]; omega_arith)).mono
        (fun _ _ ⟨⟨⟨⟨R0, R1, X, hk, h₁, _⟩, _⟩, ⟨⟨R0', R1', X', hk', h₂, _⟩, _⟩⟩, _⟩ =>
          ⟨⟨R0, R1, X, hk, h₁⟩, ⟨R0', R1', X', hk', h₂⟩⟩) fun _ _ h => h
  · -- 257 to 512 bytes left.
    by_cases hc : 1 ≤ L - 448 ∧ L - 448 ≤ 256
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, c₁, _⟩, _⟩, hb⟩ => ?_
      simp only [eval, c₁, Option.some.injEq, decide_eq_false_iff_not] at hb
      exact hb hc
    exact (tailKXg_rel hl sp vl (o := 0) (N := 448) (n := L - 448) true rfl (by omega_arith) (by omega_arith)).mono
      (fun _ _ ⟨⟨⟨h₁, _⟩, ⟨h₂, _⟩⟩, _⟩ => ⟨h₁, h₂⟩) fun _ _ h => h

omit hl in
/-- After `bulkP`'s first chunk: `bulk`'s loop invariant on the data after
the 448 bytes (on its permissions), from which the rest runs. -/
def AfterP (vl : Bool) (c dp : Addr) (L : Nat) (sp : Addr) (s : State) : Prop :=
  CI c (dp + BitVec.ofNat 64 448) (L - 448) sp 1 (s.withRegions [] (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448))) ∧
    s.cf = some (decide (L - 448 - 512 * 1 < 512)) ∧ s.wr = bulkWr c dp L ∧
    ∃ F, WP isa (.seq (.ite .b (.block []) (.loop (chunk vl false) .ae)) (restT vl))
      (s.withRegions [] (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448))) F

omit hl in
/-- After `bulkP`'s `enter`. -/
def EnterP (vl : Bool) (c dp : Addr) (L : Nat) (sp : Addr) (s : State) : Prop :=
  s.gpr .rdi = stA c ∧ s.gpr .rcx = bfA c ∧ s.gpr .rsi = dp ∧ s.gpr .rsp = sp ∧
    WP isa (chunk vl true) s (AfterP vl c dp L sp)

/-- `bulkP`: `enter` and the first chunk checked by the analysis, and the rest
by `bulk`'s proof (`loop_rel`, `rest_rel`) on the data after the 448 bytes,
moved to the permissions of all of it by `relCT_narrow`. -/
theorem bulkP_rel (hge : 960 ≤ L) :
    RelCT isa (fun s₁ s₂ => BPP c dp L sp s₁ ∧ BPP c dp L sp s₂) (bulkP vl) fun _ _ => True := by
  have hLe := hl.L_lt
  have hl' := hl.shift (o := 448) (by omega_arith)
  unfold bulkP
  obtain ⟨_, hE⟩ := enter_taint
  obtain ⟨_, hC⟩ := chunkP_taint vl
  have head : ∀ {s}, BPP c dp L sp s → WP isa (.block enter) s (EnterP vl c dp L sp) :=
    fun ⟨_, wr, rsi, rdx, rcx, rsp, _, _, rep⟩ =>
      WP.mono (bulkPHead_ok vl hl hge wr rsi rdx rcx rep) fun _ ⟨a, b, c', d, w⟩ =>
        ⟨a, b, c', by rw [d, rsp], WP.mono w fun _ ⟨ci, cf, _, wr', ex⟩ =>
          ⟨by rw [rsp] at ci; exact ci, cf, by rw [wr', wr], ex⟩⟩
  have e := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => BPP c dp L sp s₁ ∧ BPP c dp L sp s₂)
    (τR [.rcx, .rsi, .rsp]) (fun _ _ h => bpp_agree sp h.1 h.2) hE).wp
    (F₁ := EnterP vl c dp L sp) (F₂ := EnterP vl c dp L sp)
    fun _ _ h => ⟨head h.1, head h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have ch := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => EnterP vl c dp L sp s₁ ∧ EnterP vl c dp L sp s₂)
    (τR [.rdi, .rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hC).wp
    (F₁ := AfterP vl c dp L sp) (F₂ := AfterP vl c dp L sp)
    fun _ _ h => ⟨h.1.2.2.2.2, h.2.2.2.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  · have rest := relCT_narrow (c := .seq (.ite .b (.block []) (.loop (chunk vl false) .ae)) (restT vl))
      (Pr := fun s₁ s₂ => AfterP vl c dp L sp s₁ ∧ AfterP vl c dp L sp s₂)
      (Pn := fun s₁ s₂ => CI c (dp + BitVec.ofNat 64 448) (L - 448) sp 1 s₁ ∧
        CI c (dp + BitVec.ofNat 64 448) (L - 448) sp 1 s₂ ∧
        s₁.cf = some (decide (L - 448 - 512 * 1 < 512)) ∧ s₂.cf = some (decide (L - 448 - 512 * 1 < 512)))
      (fun _ => bulkWr c (dp + BitVec.ofNat 64 448) (L - 448))
      (fun s₁ s₂ ⟨⟨ci₁, cf₁, wr₁, ex₁⟩, ⟨ci₂, cf₂, wr₂, ex₂⟩⟩ =>
        ⟨by rw [wr₁]; exact covers_shift (by omega_arith), by rw [wr₂]; exact covers_shift (by omega_arith), ex₁, ex₂,
          ci₁, ci₂, cf₁, cf₂⟩)
      ((loop_rel hl' sp vl).seq (RelCT.exists_ fun T => rest_rel hl' sp vl T))
    exact e.seq (ch.seq rest)
  · obtain ⟨⟨rdi₁, rcx₁, rsi₁, rsp₁, -⟩, ⟨rdi₂, rcx₂, rsi₂, rsp₂, -⟩⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [rdi₁, rdi₂]
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
arguments being functions of the public length (`MidS`). Whether the call
is made depends on the length alone too (`rdx_of`: `bulk` ends with `tailS`,
`DoneS`, or not). After it, `rbx` and `rbp` (the ciphertext not yet
absorbed) are public too (`AfterS`).
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

/-! ## The parts of the code -/

/-- `cryptS`'s branch for at most `fold` bytes. -/
def smallS (w : Nat) : Prog isa :=
  .seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
    (.seq (xorBufX w .r14) (.block (ptr .rsi .r15 128 ++ whole)))

/-- The call of `vg_chacha20_xor` if data is left. -/
def callIf (x : Impl.ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block [.mov .rsi (.reg .rcx)]) (.call x.name x.code))

/-- `cryptS`'s branch for more: `m` (`mLoad`), by which `bigS` or `preS`, then
the call if data is left. -/
def bigR (x : Impl.ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block mLoad) (.seq (.block [.alu .test .rdx (.reg .rdx)])
    (.seq (.ite .e (bigS x.vl) (preS x)) (callIf x)))

def iteS (x : Impl.ChaCha20.X86_64.Callee) : Prog isa := .ite .b (smallS x.wide) (bigR x)

/-- The keystream wiped (`wipeL`). -/
def wipeS (fold extra w : Nat) : Prog isa :=
  .seq (.block (anchor .rsi 128)) (.seq (wipeL fold extra) (.seq (.block [.alu .add .rdx (.imm 64)]) (zeroKs w)))

/-- `sealStitched` after the branch. -/
def postS (fold w : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (wipeS fold 512 w) (.seq (macPadLengths b .rbx .rbp) (.seq finalizeTag (.block restore)))

theorem sealS_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa (sealStitched x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA x.fold x.pass x.wide) (.seq (.call x.name x.code)
      (.seq (sealMid x.fold b) (.seq (iteS x) (postS x.fold x.wide b)))))) s t s' := by
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

/-- `m` where the prologue stored it (`mStore`). -/
abbrev MSlot (fold : Nat) (s₀ s : State) : Prop :=
  s.mem.readW (off (cx s₀) 48) 64 = BitVec.ofNat 64 (mOf fold 512 (L s₀))

/-- As `AtIteS`, with `m` stored. -/
def AtIteM (fold : Nat) (s₀ s : State) : Prop := AtIteS fold 512 s₀ s ∧ MSlot fold s₀ s

theorem sealMidM_ok {fold pass : Nat} (hf : fold ≤ 960) (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : AfterF fold pass s₀ s) : WP isa (sealMid fold b) s fun s' =>
      AtIteS fold pass s₀ s' ∧ (pass = 512 → s'.mem.readW (off (cx s₀) 48) 64 = BitVec.ofNat 64 (mOf fold pass (L s₀))) := by
  have hM := Nat.le_trans (mOf_le fold pass (L s₀)) hf
  refine WP.seq (WP.mono (prologueB_ok hf hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by decide), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, _⟩ => ?_)
  refine WP.mono (cmpFold_ok (fold := fold) (by lit_omega) i₃.r13) fun s₄ ⟨g₄, rd₄, wr₄, m₄, c₄⟩ => ?_
  refine ⟨⟨⟨i₃.step (fun r _ => by rw [g₄]) rd₄ wr₄ (rs := []) (by rw [m₄]; exact Frame.refl _ _)
      (fun _ h => by simp at h) (fun _ h => by simp at h), c₄,
    by rw [m₄]; exact ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)⟩, ?_, ?_⟩, fun hps => ?_⟩
  · rw [m₄, stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  · exact ⟨otk s₀, _, by rw [m₄]; exact Repr.frame f₃ (by rdisj_all) (r₂ _ _ h₁.poly)⟩
  · rw [m₄, f₃.readW (r := sub s₀ 48 8) (Region.contains_self _ _) (by rdisj_all) (by decide),
      f₂.readW (r := sub s₀ 48 8) (Region.contains_self _ _) (by rdisj_all) (by decide)]
    exact h₁.mslot hps

theorem sealMidS_ok {fold pass : Nat} (hf : fold ≤ 960) (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : AfterF fold pass s₀ s) : WP isa (sealMid fold b) s (AtIteS fold pass s₀) :=
  WP.mono (sealMidM_ok hf b hp h) fun _ h => h.1

/-- At `open`'s branch on the length: as `AtIteS`, and the keystream `twoKs` left
at `ctx + 736`. -/
def AtIteX (fold pass : Nat) (s₀ s : State) : Prop :=
  AtIte fold pass s₀ s ∧ stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀) ∧
    (∃ key msg, Repr s.mem (off (cx s₀) 448) key msg) ∧ TailKs s₀ s.mem

theorem sealMidX_ok {fold pass : Nat} (hf : fold ≤ 960) (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : AfterF fold pass s₀ s) (ht : TailKs s₀ s.mem) :
    WP isa (sealMid fold b) s (AtIteX fold pass s₀) := by
  have hM := Nat.le_trans (mOf_le fold pass (L s₀)) hf
  refine WP.seq (WP.mono (prologueBF_ok hf hp h) fun s₁ ⟨h₁, f₁⟩ => ?_)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by decide), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, _⟩ => ?_)
  refine WP.mono (cmpFold_ok (fold := fold) (by lit_omega) i₃.r13) fun s₄ ⟨g₄, rd₄, wr₄, m₄, c₄⟩ => ?_
  refine ⟨⟨i₃.step (fun r _ => by rw [g₄]) rd₄ wr₄ (rs := []) (by rw [m₄]; exact Frame.refl _ _)
      (fun _ h => by simp at h) (fun _ h => by simp at h), c₄,
    by rw [m₄]; exact ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)⟩, ?_, ?_,
    by rw [m₄]; exact ((ht.frame f₁ (by rdisj_all)).frame f₂ (by rdisj_all)).frame f₃ (by rdisj_all)⟩
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
  · rw [g₃, cs₂ _ (by decide), h.r13, hL]
  · rw [g₃, cs₂ _ (by decide), h.r14]
  · rw [g₃, cs₂ r (by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])]

/-- After `cryptS`'s branch: as `After`, and `rbx`, `rbp` the ciphertext not
yet absorbed. -/
structure AfterS (fold : Nat) (s₀ s : State) : Prop where
  rsi : s.gpr .rsi = off (cx s₀) 128
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r9
  r14 : s.gpr .r14 = dp s₀
  r12 : s.gpr .r12 = tp s₀
  rbx : s.gpr .rbx = dp s₀ + BitVec.ofNat 64 (aOf fold (L s₀))
  rbp : s.gpr .rbp = BitVec.ofNat 64 (L s₀ - aOf fold (L s₀))
  wr : s.wr = s₀.wr

theorem smallS_ok {fold pass w : Nat} (hf : fold ≤ 960) (hw : w = 4 ∨ w = 5 ∨ w = 6) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : AtIte fold pass s₀ s) (hle : L s₀ ≤ fold) :
    WP isa (smallS w) s (AfterS fold s₀) := by
  unfold smallS
  apply seq3
  refine WP.mono (cryptSmall_ok hf hw hp h.inv hle h.ks) fun s₃ c₃ => ?_
  refine WP.mono (whole_ok s₃) fun s₄ ⟨rbx₄, rbp₄, g₄, _, wr₄, _⟩ => ?_
  have a0 : aOf fold (L s₀) = 0 := by simp only [aOf]; rw [ite_eq_left hle]
  refine ⟨by rw [g₄ _ (by decide) (by decide), c₃.rsi],
    by rw [g₄ _ (by decide) (by decide), c₃.cs _ calleeSaved_rsp (by decide), h.inv.rsp],
    by rw [g₄ _ (by decide) (by decide), c₃.cs _ (by decide) (by decide), h.inv.r13],
    by rw [g₄ _ (by decide) (by decide), c₃.cs _ (by decide) (by decide), h.inv.r14],
    by rw [g₄ _ (by decide) (by decide), c₃.cs _ (by decide) (by decide), h.inv.r12],
    by rw [rbx₄, c₃.cs _ (by decide) (by decide), h.inv.r14, a0]; simp,
    by rw [rbp₄, c₃.cs _ (by decide) (by decide), h.inv.r13, hL, a0, Nat.sub_zero],
    by rw [wr₄, c₃.wr, h.inv.wr]⟩

/-- Before the call of `vg_chacha20_xor` after `bulk`. -/
def MidS (fold : Nat) (s₀ s : State) : Prop :=
  ∃ σ key msg E a, Inv s₀ σ ∧ Mid fold s₀ σ key msg E a s

/-- After `bulk` ended by `tailS`. -/
def DoneS (fold : Nat) (s₀ s : State) : Prop :=
  ∃ σ key msg, Inv s₀ σ ∧ DoneT fold s₀ σ key msg s

/-- The bytes encrypted before that call. -/
abbrev Eof (L : Nat) : Nat := 512 * (L / 512)

/-- The regions of that call. -/
abbrev xR (s₀ : State) : List Region :=
  [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀ + BitVec.ofNat 64 (Eof (L s₀)), L s₀ - Eof (L s₀)⟩, ⟨off (cx s₀) 128, 320⟩]

section
variable {fold : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : MidS fold s₀ s)
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
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega_arith
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ctxR s₀, by rw [h.vals.2.2.2.2.2]; exact hp.ctx_wr, 64, by simp [off_eq],
      by show 64 + 64 ≤ 1696; omega_arith⟩
  · exact ⟨dR s₀, by rw [h.vals.2.2.2.2.2]; exact hp.d_wr, Eof (L s₀), rfl,
      by show Eof (L s₀) + (L s₀ - Eof (L s₀)) ≤ L s₀; omega_arith⟩
  · exact ⟨ctxR s₀, by rw [h.vals.2.2.2.2.2]; exact hp.ctx_wr, 128, by simp [off_eq],
      by show 128 + 320 ≤ 1696; omega_arith⟩

theorem MidS.pre (v : Proof.ChaCha20.X86_64.XorImpl) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] (xR s₀)) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega_arith
  obtain ⟨rdi, rsi, rdx, rcx, rsp, -⟩ := h.vals
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (Eof (L s₀)), L s₀ - Eof (L s₀)⟩ (dR s₀) :=
    Offset.sub_base _ (by omega_arith)
  exact xor_pre v rdi rsi rdx rcx (by omega_arith)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ _ (by omega_arith)) _) (by have := hp.wrap_d; omega_arith))
    (by rw [rsp]; exact hp.stk_sub (by lit_omega)) (by rw [rsp]; exact hp.stk_d.sub_right dsub)
    (by rw [rsp]; exact hp.stk_sub (by lit_omega))

omit h in
theorem MidS.call (v : Proof.ChaCha20.X86_64.XorImpl) (h : MidS v.callee.fold s₀ s) :
    WP isa (.call v.callee.name v.callee.code) s (AfterS v.callee.fold s₀) := by
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

/-- As `τ₁`, with `rbx` and `rbp` public, and `m` (`MSlot`). -/
def τ₁S (enc : Bool) : X86_64.Taint.T :=
  { regs := .ofList [.rsi, .rsp, .r13, .r14, .r12, .rbx, .rbp], flags := false, lens := lensOf enc,
    bases := [(.rsi, ci enc, 128)], slots := [(ci enc, 48, 8)] }

section
variable {s₀ s₀' : State} (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀')

omit hp' in
include hp in
theorem AfterS.wf {fold : Nat} {s : State} (h : AfterS fold s₀ s) : X86_64.Taint.Wf (τ₁S e) s := by
  have hw : s.wr = bif e then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀] := by rw [h.wr, hp.wr_eq]
  refine ⟨fun _ => regions_wf hp h.wr, fun p hm => ?_⟩
  simp only [τ₁S, List.mem_singleton] at hm
  subst hm
  simp only [X86_64.Taint.region, hw, h.rsi, off_eq]
  cases e <;> simp

include hp hp' hq in
theorem agree₁S {fold : Nat} {s₁ s₂ : State} (h₁ : AfterS fold s₀ s₁) (h₂ : AfterS fold s₀' s₂)
    (ms₁ : MSlot fold s₀ s₁) (ms₂ : MSlot fold s₀' s₂) :
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
  · intro sl h; simp only [τ₁S, List.mem_singleton] at h; subst h; cases e <;> decide
  · intro sl h k hk₁ hk₂
    simp only [τ₁S, List.mem_singleton] at h; subst h
    dsimp only at hk₁ hk₂
    have ba : ∀ {σ₀ s : State}, APre e σ₀ → s.wr = σ₀.wr →
        X86_64.Taint.byteAddr s (ci e) k = off (cx σ₀) 48 + BitVec.ofNat 64 (k - 48) := fun hp hw => by
      rw [off_eq, BitVec.add_assoc, ← BitVec.ofNat_add, show 48 + (k - 48) = k by omega_arith]
      simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, hp.wr_eq]; cases e <;> rfl
    have hL : L s₀' = L s₀ := by simp only [L, p6]
    have ec : cx s₀' = cx s₀ := by simp only [cx, p9]
    rw [ba hp h₁.wr, ba hp' h₂.wr, ec,
      ← Mem.extractLsb'_read s₁.mem (off (cx s₀) 48) (n := 8) (j := k - 48) (by omega_arith),
      ← Mem.extractLsb'_read s₂.mem (off (cx s₀) 48) (n := 8) (j := k - 48) (by omega_arith)]
    have e₁ : s₁.mem.read (off (cx s₀) 48) 8 = BitVec.ofNat 64 (mOf fold 512 (L s₀)) := ms₁
    have e₂ : s₂.mem.read (off (cx s₀') 48) 8 = BitVec.ofNat 64 (mOf fold 512 (L s₀')) := ms₂
    rw [ec, hL] at e₂
    rw [e₁, e₂]

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

/-! ## The call if data is left -/

theorem xTest_taint : ∃ h, (taintS.check (τR []) (.block xTest) h).isSome = true := by
  taint_decide_sum []

theorem twoKs_taint (vl : Bool) : ∃ h, (taintS.check (τR [.r15, .rdi, .rsp]) (twoKs vl) h).isSome = true := by
  cases vl <;> taint_decide_sum []

theorem fourKs_taint (vl : Bool) : ∃ h, (taintS.check (τR [.r15, .rdi, .rsp]) (fourKs vl) h).isSome = true := by
  cases vl <;> taint_decide_sum []

theorem xTestV_taint : ∃ h, (taintS.check (τR []) (.block xTestV) h).isSome = true := by
  taint_decide_sum []

theorem twoKsB_taint (vl : Bool) : ∃ h, (taintS.check (τR [.r15, .rdi, .rsp]) (twoKsB vl) h).isSome = true := by
  cases vl <;> taint_decide_sum []

theorem cmpRax64_taint : ∃ h, (taintS.check (τR []) (.block [.alu .cmp .rax (.imm 64)]) h).isSome = true := by
  taint_decide_sum []

theorem fTest_taint : ∃ h, (taintS.check (τR []) (.block fTest) h).isSome = true := by
  taint_decide_sum []

theorem testRdx_taint : ∃ h, (taintS.check (τR []) (.block [.alu .test .rdx (.reg .rdx)]) h).isSome = true := by
  taint_decide_sum []

theorem movRsi_taint : ∃ h, (taintS.check (τR []) (.block [.mov .rsi (.reg .rcx)]) h).isSome = true := by
  taint_decide_sum []

section
variable {fold : Nat} {s₀ s s' : State}

/-- `MidS` and `DoneS` read only the registers, the memory and the
permissions. -/
theorem MidS.of_eq (h : MidS fold s₀ s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : MidS fold s₀ s' := by
  obtain ⟨σ, key, msg, E, a, hi, m⟩ := h
  exact ⟨σ, key, msg, E, a, hi, by rw [hg]; exact m.rdi, by rw [hg]; exact m.rcx, by rw [hg]; exact m.rsi,
    by rw [hg]; exact m.rdx, by rw [hg]; exact m.rbx, by rw [hg]; exact m.rbp, fun r hr => by rw [hg]; exact m.keep r hr,
    by rw [hrd]; exact m.rd, by rw [hwr]; exact m.wr, m.E64, m.Ediv, m.aEq, m.EL, m.aE, m.a16, m.aO,
    by rw [hm]; exact m.st, fun k hk => by rw [hm]; exact m.data k hk, by rw [hm]; exact m.frame,
    by rw [hm]; exact m.repr⟩

theorem DoneS.of_eq (h : DoneS fold s₀ s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : DoneS fold s₀ s' := by
  obtain ⟨σ, key, msg, hi, d⟩ := h
  obtain ⟨a, aO, a16, aL, rbx, rbp, repr⟩ := d.abs
  exact ⟨σ, key, msg, hi, by rw [hg]; exact d.rdx, by rw [hg]; exact d.rcx, fun r hr => by rw [hg]; exact d.keep r hr,
    by rw [hrd]; exact d.rd, by rw [hwr]; exact d.wr, by rw [hm]; exact d.frame, by rw [hm]; exact d.data,
    ⟨a, aO, a16, aL, by rw [hg]; exact rbx, by rw [hg]; exact rbp, by rw [hm]; exact repr⟩, d.tail⟩

/-- With more than `fold` (448) bytes, `bulk` ends with `leave` (or there are
no chunks) exactly when neither it nor `bulkP` ends with `tailS`. -/
theorem MidS.not_tail (h : MidS fold s₀ s) (hf448 : fold = 448) (hf : fold < L s₀) : ¬ TailLen fold (L s₀) := by
  obtain ⟨σ, key, msg, E, a, hi, m⟩ := h
  have aO := m.aO
  have aEq := m.aEq
  have Ediv := m.Ediv
  subst hf448
  intro ht
  simp only [aOf] at aO
  rw [ite_eq_right (by omega_arith)] at aO
  by_cases hpre : PreLen 448 (L s₀)
  · rw [ite_eq_left hpre] at aO; omega_arith
  · rw [ite_eq_right hpre, ite_eq_left (by omega)] at aO; omega

/-- The number of bytes left, as a function of the length. -/
theorem rdx_of (h : MidS fold s₀ s ∨ DoneS fold s₀ s) (hf448 : fold = 448) (hf : fold < L s₀) :
    s.gpr .rdx = if TailLen fold (L s₀) then 0 else BitVec.ofNat 64 (L s₀ - Eof (L s₀)) := by
  rcases h with m | ⟨σ, key, msg, hi, d⟩
  · rw [ite_eq_right (m.not_tail hf448 hf), (MidS.vals m).2.2.1]
  · rw [ite_eq_left d.tail, d.rdx]

theorem test_after (h : MidS fold s₀ s ∨ DoneS fold s₀ s) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      (MidS fold s₀ s' ∨ DoneS fold s₀ s') ∧ s'.zf = some (s'.gpr .rdx == 0) :=
  WP.mono (testRdx_ok s) fun s' ⟨g, m, rd, wr, z⟩ => ⟨by
    rcases h with h | h
    · exact .inl (h.of_eq g m rd wr)
    · exact .inr (h.of_eq g m rd wr), by rw [z, g]⟩

/-- Nothing left: `rsi` at `buf`, as the call would leave it. -/
theorem skip_after (h : MidS fold s₀ s ∨ DoneS fold s₀ s) (hz : s.gpr .rdx = 0) :
    WP isa (.block [.mov .rsi (.reg .rcx)]) s (AfterS fold s₀) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.mono (Stitch.movR_ok .rsi .rcx) fun s' ⟨rsi', g', _, _, wr', _, _⟩ => ?_
  rcases h with ⟨σ, key, msg, E, a, hi, m⟩ | ⟨σ, key, msg, hi, d⟩
  · have hEL := m.EL
    have hE : L s₀ - E = 0 := by
      have := m.rdx
      rw [hz] at this
      have := congrArg BitVec.toNat this
      rw [Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega_arith)] at this
      simp at this; omega_arith
    refine ⟨by rw [rsi', m.rcx], by rw [g' _ (by decide), m.keep _ (.inr (.inr (.inr rfl))), hi.rsp],
      by rw [g' _ (by decide), m.keep _ (.inr (.inl rfl)), hi.r13],
      by rw [g' _ (by decide), m.keep _ (.inr (.inr (.inl rfl))), hi.r14],
      by rw [g' _ (by decide), m.keep _ (.inl rfl), hi.r12], by rw [g' _ (by decide), m.rbx, m.aO],
      by rw [g' _ (by decide), m.rbp, m.aO], by rw [wr', m.wr, hi.wr]⟩
  · obtain ⟨a, aO, -, -, rbx, rbp, -⟩ := d.abs
    refine ⟨by rw [rsi', d.rcx], by rw [g' _ (by decide), d.keep _ (.inr (.inr (.inr rfl))), hi.rsp],
      by rw [g' _ (by decide), d.keep _ (.inr (.inl rfl)), hi.r13],
      by rw [g' _ (by decide), d.keep _ (.inr (.inr (.inl rfl))), hi.r14],
      by rw [g' _ (by decide), d.keep _ (.inl rfl), hi.r12], by rw [g' _ (by decide), rbx, aO],
      by rw [g' _ (by decide), rbp, aO], by rw [wr', d.wr, hi.wr]⟩

end

/-! ## The branch with whole chunks -/

/-- `bulk`'s permissions are `seal`'s. -/
theorem bulk_covers {s₀ : State} (hp : APre e s₀) {s : State} (hwr : s.wr = s₀.wr) :
    Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s.wr := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1696; omega_arith⟩
  · exact ⟨dR s₀, by rw [hwr]; exact hp.d_wr, 0, by simp, by simp⟩
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1696; omega_arith⟩
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 448, rfl, by show 448 + 128 ≤ 1696; omega_arith⟩
  · exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, 736, by simp only [kA, bfA, Offset.add_add]; try rfl,
      by show 736 + 512 ≤ 1696; omega_arith⟩

theorem bulk_bp {s₀ : State} {σ s : State} (ha : Args s₀ σ s) (hi : Inv s₀ σ) {key msg : List Byte}
    (hrep : Repr σ.mem (off (cx s₀) 448) key msg) :
    BP (cx s₀) (dp s₀) (L s₀) (s₀.gpr .rsp) (s.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) :=
  ⟨rfl, rfl, ha.rsi, ha.rdx, by rw [State.withRegions_gpr, ha.rcx, off_eq],
    by rw [State.withRegions_gpr, ha.keep _ (.inr (.inr (.inr rfl))), hi.rsp], key, msg,
    by show Repr _ (cx s₀ + BitVec.ofNat 64 448) _ _
       rw [State.withRegions_mem, ha.mem, ← off_eq]; exact args_repr hrep⟩

/-- What the branch with whole chunks starts from, in one run. -/
def AtArgs (fold pass : Nat) (s₀ s : State) : Prop :=
  ∃ σ, AtIteS fold pass s₀ σ ∧ Args s₀ σ s ∧ s.cf = some (decide (L s₀ < 512)) ∧ ¬ PreLen fold (L s₀)

/-- After `foldM` in `cryptS`'s branch for more than `fold` bytes, from `σ`
at the branch: `rdx` is `m`. -/
def AtF (fold pass : Nat) (s₀ s : State) : Prop :=
  ∃ σ, AtIteS fold pass s₀ σ ∧ fold < L s₀ ∧ (∀ r, r ≠ .rdx → s.gpr r = σ.gpr r) ∧ s.mem = σ.mem ∧
    s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.gpr .rdx = BitVec.ofNat 64 (mOf fold pass (L s₀))

/-- After `foldM` and the `test`: `ZF` whether `m` is 0. -/
def AtM (fold pass : Nat) (s₀ s : State) : Prop :=
  AtF fold pass s₀ s ∧ s.zf = some (BitVec.ofNat 64 (mOf fold pass (L s₀)) == 0)

theorem AtF.inv {fold pass : Nat} {s₀ s : State} (h : AtF fold pass s₀ s) : Inv s₀ s := by
  obtain ⟨σ, hσ, -, g, m, rd, wr, -⟩ := h
  exact hσ.1.inv.step (fun r hr => g r (by rintro rfl; simp [calleeSaved] at hr)) rd wr (rs := [])
    (by rw [m]; exact Frame.refl _ _) (fun _ h => by simp at h) (fun _ h => by simp at h)

/-- `Args` reads only what `foldM` and the `test` keep. -/
theorem Args.of_eq {s₀ σ s s' : State} (h : Args s₀ s s') (hg : ∀ r, r ≠ .rdx → s.gpr r = σ.gpr r)
    (hm : s.mem = σ.mem) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) : Args s₀ σ s' :=
  ⟨by rw [h.mem, hm], h.rdi, h.rsi, h.rdx, h.rcx, h.r13, h.r14,
    fun r hr => by rw [h.keep r hr, hg r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)],
    by rw [h.rd, hrd], by rw [h.wr, hwr]⟩

/-- After `cryptPre` for the 448 bytes. -/
def PA (s₀ s : State) : Prop :=
  XArgsM s₀ 448 s ∧ (∃ key msg, Repr s.mem (off (cx s₀) 448) key msg) ∧ PreLen 448 (L s₀) ∧ 448 < L s₀

/-- After `rsi` is set to the data and `rdx` compared with 512. -/
def PB (s₀ s : State) : Prop :=
  s.gpr .rsi = dp s₀ ∧ s.gpr .rdx = BitVec.ofNat 64 (L s₀ - 448) ∧ s.gpr .rcx = off (cx s₀) 128 ∧
    s.gpr .rsp = s₀.gpr .rsp ∧ s.wr = s₀.wr ∧ (∃ key msg, Repr s.mem (off (cx s₀) 448) key msg) ∧
    s.cf = some (decide (L s₀ - 448 < 513)) ∧ PreLen 448 (L s₀) ∧ 448 < L s₀

theorem mLoad_taint : ∃ h, (taintS.check (τS true) (.block mLoad) h).isSome = true := by
  taint_decide_sum []

theorem cryptPreP_taint : ∃ h, (taintS.check (τS true) (cryptPre 448 512 5) h).isSome = true := by
  taint_decide_sum []

theorem movCmp_taint :
    ∃ h, (taintS.check (τR []) (.block [.mov .rsi (.reg .r14), .alu .cmp .rdx (.imm 513)]) h).isSome = true := by
  taint_decide_sum []

theorem PB.bpp {s₀ s : State} (h : PB s₀ s) :
    BPP (cx s₀) (dp s₀) (L s₀) (s₀.gpr .rsp) (s.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) := by
  obtain ⟨rsi, rdx, rcx, rsp, -, ⟨key, msg, rep⟩, -⟩ := h
  exact ⟨rfl, rfl, rsi, rdx, by rw [State.withRegions_gpr, rcx, off_eq], rsp, key, msg,
    by rw [State.withRegions_mem, show psA (cx s₀) = off (cx s₀) 448 by rw [off_eq]]; exact rep⟩

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {s₀ s₀' : State} (hp : APre true s₀)
  (hp' : APre true s₀') (hq : pubX86_64 s₀ s₀')
include hv hp hp' hq

/-- The 448 bytes whose keystream the prologue computed, then the rest: the
analysis checks `cryptPre` and the comparison, and the branches on the length
are `tailPS_rel` and `bulkP_rel`, on their permissions. -/
theorem preS_rel :
    RelCT isa (fun s₁ s₂ => (AtM v.callee.fold 512 s₀ s₁ ∧ AtM v.callee.fold 512 s₀' s₂) ∧
      isa.eval .e s₁ = some false) (preS { v.callee with pass := 512 }) fun _ _ => True := by
  obtain ⟨hf, -, hw⟩ := avx2_of v hv
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, -, p9⟩ := hq'
  have eL : L s₀' = L s₀ := by simp only [L, p6]
  have ec : cx s₀' = cx s₀ := by simp only [cx, p9]
  have ed : dp s₀' = dp s₀ := by simp only [dp, p5]
  -- `m` is 448.
  have pre : ∀ {σ₀ s}, AtM v.callee.fold 512 σ₀ s → isa.eval .e s = some false →
      PreLen 448 (L σ₀) ∧ 448 < L σ₀ := by
    rintro σ₀ s ⟨⟨σ, -, hfL, -⟩, z⟩ hb
    simp only [eval, z, Option.some.injEq] at hb
    have hn : mOf v.callee.fold 512 (L σ₀) ≠ 0 := fun h0 => by simp [h0] at hb
    rw [mOf_big (by omega_arith), hf] at hn
    simp only [splitOf, show (512 : Nat) ≠ 0 by decide, ite_false, ite_true] at hn
    refine ⟨?_, by rw [hf] at hfL; exact hfL⟩
    split at hn
    · assumption
    · exact absurd rfl hn
  by_cases hP : PreLen 448 (L s₀) ∧ 448 < L s₀
  swap
  · exact RelCT.of_false fun s₁ s₂ ⟨⟨h₁, _⟩, hb⟩ => hP (pre h₁ hb)
  obtain ⟨_, hC⟩ := cryptPreP_taint
  obtain ⟨_, hM⟩ := movCmp_taint
  have hC' : ∃ h, (taintS.check (τS true) (cryptPre v.callee.fold 512 v.callee.wide) h).isSome = true := by
    rw [hf, hw]; exact ⟨_, hC⟩
  obtain ⟨_, hC''⟩ := hC'
  have paOk : ∀ {σ₀ s}, APre true σ₀ → AtM v.callee.fold 512 σ₀ s → isa.eval .e s = some false →
      WP isa (cryptPre v.callee.fold 512 v.callee.wide) s (PA σ₀) := by
    intro σ₀ s hp h hb
    obtain ⟨hpre, hbig⟩ := pre h hb
    have hi := h.1.inv
    obtain ⟨⟨σ, ⟨-, -, key, msg, hrep⟩, -, -, m, -⟩, -⟩ := h
    exact WP.mono (cryptPreR_ok v hf hp hi hpre hbig (by rw [m]; exact hrep)) fun _ ⟨a, r⟩ =>
      ⟨a, ⟨key, msg, r⟩, hpre, hbig⟩
  have pa := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtM v.callee.fold 512 s₀ s₁ ∧
      AtM v.callee.fold 512 s₀' s₂) ∧ isa.eval .e s₁ = some false) (τS true)
      (fun _ _ h => agreeI hp hp' hq h.1.1.1.inv h.1.2.1.inv) hC'').wp (F₁ := PA s₀) (F₂ := PA s₀')
    fun _ _ h => ⟨paOk hp h.1.1 h.2, paOk hp' h.1.2 (by
      rw [← h.2]; obtain ⟨⟨_, z₁⟩, ⟨_, z₂⟩⟩ := h.1; simp only [eval, z₁, z₂, eL])⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have pbOk : ∀ {σ₀ s}, PA σ₀ s → WP isa (.block [.mov .rsi (.reg .r14), .alu .cmp .rdx (.imm 513)]) s (PB σ₀) := by
    intro σ₀ s ⟨a, r, hpre, hbig⟩
    have hL9 : L σ₀ < 2 ^ 64 := (σ₀.gpr .r9).isLt
    exact WP.mono (movCmp_ok (by omega_arith) a.rdx) fun _ ⟨rsi, g, _, wr, m, c⟩ =>
      ⟨by rw [rsi, a.r14], by rw [g _ (by decide), a.rdx], by rw [g _ (by decide), a.rcx],
        by rw [g _ (by decide), a.rsp], by rw [wr, a.wr], by rw [m]; exact r, c, hpre, hbig⟩
  have pb := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => PA s₀ s₁ ∧ PA s₀' s₂) (τR [])
      (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hM).wp (F₁ := PB s₀) (F₂ := PB s₀')
    fun _ _ h => ⟨pbOk h.1, pbOk h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hl : Lay (cx s₀) (dp s₀) (L s₀) :=
    ⟨(s₀.gpr .r9).isLt, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  -- The second run's regions are the first's.
  have b₂ : ∀ {s}, PB s₀' s → BPP (cx s₀) (dp s₀) (L s₀) (s₀.gpr .rsp)
      (s.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) := fun h => by
    have := h.bpp; rw [ec, ed, eL, ← p7] at this; exact this
  have cov : ∀ {s}, PB s₀ s → Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s.wr := fun h => bulk_covers hp h.2.2.2.2.1
  have cov' : ∀ {s}, PB s₀' s → Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s.wr := fun h => by
    rw [← ec, ← ed, ← eL]; exact bulk_covers hp' h.2.2.2.2.1
  refine pa.seq (pb.seq (RelCT.ite (fun s₁ s₂ h => by
    simp only [eval, h.1.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, eL]) ?_ ?_))
  · -- No whole chunks after the 448 bytes.
    by_cases hc : L s₀ - 448 < 513
    swap
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨h₁, _⟩, hb⟩ => ?_
      simp only [eval, h₁.2.2.2.2.2.2.1, Option.some.injEq, decide_eq_true_eq] at hb
      exact hc hb
    refine (relCT_narrow (c := .seq (.block enter) (tailP v.callee.vl))
      (fun _ => bulkWr (cx s₀) (dp s₀) (L s₀)) (fun s₁ s₂ ⟨⟨h₁, h₂⟩, _⟩ => ?_)
      (tailPS_rel hl (s₀.gpr .rsp) v.callee.vl (by omega) (by omega))).mono (fun _ _ h => h) fun _ _ h => h
    have B₁ := h₁.bpp
    have B₂ := b₂ h₂
    obtain ⟨-, wr₁, rsi₁, rdx₁, rcx₁, -, k₁, m₁, r₁⟩ := id B₁
    obtain ⟨-, wr₂, rsi₂, rdx₂, rcx₂, -, k₂, m₂, r₂⟩ := id B₂
    exact ⟨cov h₁, cov' h₂, ⟨_, tailPS_ok _ hl (by omega) (by omega) wr₁ rsi₁ rdx₁ rcx₁ r₁⟩,
      ⟨_, tailPS_ok _ hl (by omega) (by omega) wr₂ rsi₂ rdx₂ rcx₂ r₂⟩, B₁, B₂⟩
  · -- The whole chunks after the 448 bytes.
    by_cases hc : L s₀ - 448 < 513
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨h₁, _⟩, hb⟩ => ?_
      simp only [eval, h₁.2.2.2.2.2.2.1, Option.some.injEq, decide_eq_false_iff_not] at hb
      exact hb hc
    have hr : 1 ≤ (L s₀ - 448) % 512 ∧ (L s₀ - 448) % 512 ≤ 448 := by omega
    refine (relCT_narrow (c := bulkP v.callee.vl) (fun _ => bulkWr (cx s₀) (dp s₀) (L s₀)) (fun s₁ s₂ ⟨⟨h₁, h₂⟩, _⟩ => ?_)
      (bulkP_rel hl (s₀.gpr .rsp) v.callee.vl (by omega_arith))).mono (fun _ _ h => h) fun _ _ h => h
    have B₁ := h₁.bpp
    have B₂ := b₂ h₂
    obtain ⟨-, wr₁, rsi₁, rdx₁, rcx₁, -, k₁, m₁, r₁⟩ := id B₁
    obtain ⟨-, wr₂, rsi₂, rdx₂, rcx₂, -, k₂, m₂, r₂⟩ := id B₂
    exact ⟨cov h₁, cov' h₂, ⟨_, bulkP_ok _ hl (by omega_arith) hr wr₁ rsi₁ rdx₁ rcx₁ r₁⟩,
      ⟨_, bulkP_ok _ hl (by omega_arith) hr wr₂ rsi₂ rdx₂ rcx₂ r₂⟩, B₁, B₂⟩

end

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {s₀ s₀' : State} (hp : APre true s₀)
  (hp' : APre true s₀') (hq : pubX86_64 s₀ s₀')
include hv hp hp' hq

theorem bigR_rel :
    RelCT isa (fun s₁ s₂ => (AtIteM v.callee.fold s₀ s₁ ∧ AtIteM v.callee.fold s₀' s₂) ∧
      isa.eval .b s₁ = some false) (bigR { v.callee with pass := 512 }) fun s₁ s₂ =>
        AfterS v.callee.fold s₀ s₁ ∧ AfterS v.callee.fold s₀' s₂ := by
  obtain ⟨hf, -, hw⟩ := avx2_of v hv
  have hfl := v.fold_le
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, -, p9⟩ := hq'
  have eL : L s₀' = L s₀ := by simp only [L, p6]
  have ec : cx s₀' = cx s₀ := by simp only [cx, p9]
  have ed : dp s₀' = dp s₀ := by simp only [dp, p5]
  by_cases hfL : v.callee.fold < L s₀
  swap
  · refine RelCT.of_false fun s₁ s₂ ⟨⟨h₁, _⟩, hb⟩ => ?_
    simp only [eval, h₁.1.1.cf, Option.some.injEq, decide_eq_false_iff_not] at hb
    omega_arith
  have hfL' : v.callee.fold < L s₀' := by rw [eL]; exact hfL
  -- `m`, and whether it is 0.
  obtain ⟨_, hF⟩ := mLoad_taint
  have fOk : ∀ {σ₀ s}, APre true σ₀ → v.callee.fold < L σ₀ → AtIteM v.callee.fold σ₀ s →
      WP isa (.block mLoad) s (AtF v.callee.fold 512 σ₀) :=
    fun {σ₀ _} hp hf' h => WP.mono (mLoad_ok (n := mOf v.callee.fold 512 (L σ₀)) h.1.1.inv.r15
      (by rw [h.1.1.inv.wr]; exact hp.in_ctx (a := 48) (w := 8) (by lit_omega)) h.2)
      fun _ ⟨d, g, rd, wr, m⟩ => ⟨_, h.1, hf', g, m, rd, wr, d⟩
  have fm := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtIteM v.callee.fold s₀ s₁ ∧
      AtIteM v.callee.fold s₀' s₂) ∧ isa.eval .b s₁ = some false) (τS true)
      (fun _ _ h => agreeS hp hp' hq h.1.1.1.1 h.1.2.1.1) hF).wp
    (F₁ := AtF v.callee.fold 512 s₀) (F₂ := AtF v.callee.fold 512 s₀') fun _ _ h =>
      ⟨fOk hp hfL h.1.1, fOk hp' hfL' h.1.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨_, hT⟩ := testRdx_taint
  have tOk : ∀ {σ₀ s}, AtF v.callee.fold 512 σ₀ s →
      WP isa (.block [.alu .test .rdx (.reg .rdx)]) s (AtM v.callee.fold 512 σ₀) := by
    intro σ₀ s ⟨σ, hσ, hf', gσ, mσ, rdσ, wrσ, d⟩
    exact WP.mono (testRdx_ok _) fun _ ⟨g, m, rd, wr, z⟩ =>
      ⟨⟨σ, hσ, hf', fun r hr => by rw [g, gσ r hr], by rw [m, mσ], by rw [rd, rdσ], by rw [wr, wrσ],
        by rw [g, d]⟩, by rw [z, d]⟩
  have tt := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => AtF v.callee.fold 512 s₀ s₁ ∧
      AtF v.callee.fold 512 s₀' s₂) (τR []) (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hT).wp
    (F₁ := AtM v.callee.fold 512 s₀) (F₂ := AtM v.callee.fold 512 s₀') fun _ _ h =>
      ⟨tOk h.1, tOk h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hM : ∀ {σ₀ : State}, v.callee.fold < L σ₀ →
      mOf v.callee.fold 512 (L σ₀) = if PreLen 448 (L σ₀) then 448 else 0 := by
    intro σ₀ h
    rw [mOf_big (by omega_arith), hf]; simp only [splitOf, show (512 : Nat) ≠ 0 by decide, ite_false, ite_true]
  have hm0 : ∀ {σ₀ s}, AtM v.callee.fold 512 σ₀ s →
      (isa.eval .e s = some true ↔ mOf v.callee.fold 512 (L σ₀) = 0) := by
    rintro σ₀ s ⟨-, z⟩
    have hL9 : L σ₀ < 2 ^ 64 := (σ₀.gpr .r9).isLt
    have := mOf_le v.callee.fold 512 (L σ₀)
    simp only [eval, z, Option.some.injEq, beq_ofNat_zero (show mOf v.callee.fold 512 (L σ₀) < 2 ^ 64 by omega_arith),
      decide_eq_true_eq]
  -- No keystream computed past the one-time key: `bigS`.
  obtain ⟨_, hA⟩ := argsS_taint
  obtain ⟨_, hW⟩ := whole_taint
  have argsOk : ∀ {σ₀ s}, APre true σ₀ → AtM v.callee.fold 512 σ₀ s → isa.eval .e s = some true →
      WP isa (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) s
        (AtArgs v.callee.fold 512 σ₀) := by
    intro σ₀ s hp h hb
    have hi := h.1.inv
    obtain ⟨⟨σ, hσ, hf', g, m, rd, wr, d⟩, z⟩ := h
    have h0 := (hm0 ⟨⟨σ, hσ, hf', g, m, rd, wr, d⟩, z⟩).mp hb
    rw [hM hf'] at h0
    have hnp : ¬ PreLen v.callee.fold (L σ₀) := by
      rw [hf]; split at h0
      · exact absurd h0 (by decide)
      · assumption
    exact WP.mono (argsCmp_ok hp hi) fun _ ⟨ha, cf⟩ => ⟨σ, hσ, ha.of_eq g m rd wr, cf, hnp⟩
  have args := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtM v.callee.fold 512 s₀ s₁ ∧
      AtM v.callee.fold 512 s₀' s₂) ∧ isa.eval .e s₁ = some true) (τS true)
      (fun _ _ h => agreeI hp hp' hq h.1.1.1.inv h.1.2.1.inv) hA).wp
    (F₁ := AtArgs v.callee.fold 512 s₀) (F₂ := AtArgs v.callee.fold 512 s₀') fun _ _ h =>
      ⟨argsOk hp h.1.1 h.2, argsOk hp' h.1.2 (by
        rw [← h.2]; obtain ⟨⟨_, z₁⟩, ⟨_, z₂⟩⟩ := h.1; simp only [eval, z₁, z₂, eL])⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have wholeOk : ∀ {σ₀ s}, APre true σ₀ → v.callee.fold < L σ₀ → AtArgs v.callee.fold 512 σ₀ s →
      isa.eval .b s = some true →
      WP isa (.block whole) s fun s' => MidS v.callee.fold σ₀ s' ∨ DoneS v.callee.fold σ₀ s' :=
    fun hp hf ⟨σ, ⟨hi, hst, key, msg, hrep⟩, ha, cf, hnp⟩ hb => by
      simp only [eval, cf, Option.some.injEq, decide_eq_true_eq] at hb
      exact WP.mono (whole_mid hp ha hnp hb hst hrep) fun _ hm => .inl ⟨σ, key, msg, 0, 0, hi.inv, hm⟩
  have wh := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtArgs v.callee.fold 512 s₀ s₁ ∧
      AtArgs v.callee.fold 512 s₀' s₂) ∧ isa.eval .b s₁ = some true) (τR [])
      (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hW).wp
    (F₁ := fun s => MidS v.callee.fold s₀ s ∨ DoneS v.callee.fold s₀ s)
    (F₂ := fun s => MidS v.callee.fold s₀' s ∨ DoneS v.callee.fold s₀' s) fun _ _ h => ⟨wholeOk hp hfL h.1.1 h.2,
      wholeOk hp' hfL' h.1.2 (by
        rw [← h.2]; obtain ⟨⟨_, -, -, c₁, -⟩, ⟨_, -, -, c₂, -⟩⟩ := h.1; simp only [eval, c₁, c₂, eL])⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have bulkOk : ∀ {σ₀ s}, APre true σ₀ → v.callee.fold < L σ₀ → AtArgs v.callee.fold 512 σ₀ s →
      isa.eval .b s = some false →
      WP isa (bulk v.callee.vl) s fun s' => MidS v.callee.fold σ₀ s' ∨ DoneS v.callee.fold σ₀ s' :=
    fun hp hf ⟨σ, ⟨hi, hst, key, msg, hrep⟩, ha, cf, hnp⟩ hb => by
      simp only [eval, cf, Option.some.injEq, decide_eq_false_iff_not] at hb
      refine WP.mono (bulk_mid _ hp hi.inv.wr ha hf hnp (by omega_arith) hst hrep) fun _ h => ?_
      rcases h with ⟨E, a, hm⟩ | hd
      · exact .inl ⟨σ, key, msg, E, a, hi.inv, hm⟩
      · exact .inr ⟨σ, key, msg, hi.inv, hd⟩
  have hl : Lay (cx s₀) (dp s₀) (L s₀) :=
    ⟨(s₀.gpr .r9).isLt, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have bk : RelCT isa (fun s₁ s₂ => (AtArgs v.callee.fold 512 s₀ s₁ ∧ AtArgs v.callee.fold 512 s₀' s₂) ∧
      isa.eval .b s₁ = some false) (bulk v.callee.vl) fun s₁ s₂ =>
        (MidS v.callee.fold s₀ s₁ ∨ DoneS v.callee.fold s₀ s₁) ∧
        (MidS v.callee.fold s₀' s₂ ∨ DoneS v.callee.fold s₀' s₂) := by
    by_cases hge : 512 ≤ L s₀
    · refine ((relCT_narrow (c := bulk v.callee.vl) (fun _ => bulkWr (cx s₀) (dp s₀) (L s₀)) ?_
        (bulk_rel hl hge (s₀.gpr .rsp) v.callee.vl)).wp (F₁ := fun s => MidS v.callee.fold s₀ s ∨ DoneS v.callee.fold s₀ s)
          (F₂ := fun s => MidS v.callee.fold s₀' s ∨ DoneS v.callee.fold s₀' s) ?_).mono (fun _ _ h => h)
        fun _ _ h => h.2
      · rintro s₁ s₂ ⟨⟨⟨σ₁, ⟨hi₁, -, key₁, msg₁, hrep₁⟩, ha₁, -⟩, ⟨σ₂, ⟨hi₂, -, key₂, msg₂, hrep₂⟩, ha₂, -⟩⟩, -⟩
        have b₁ := bulk_bp ha₁ hi₁.inv hrep₁
        have b₂ := bulk_bp ha₂ hi₂.inv hrep₂
        rw [ec, ed, eL, ← p7] at b₂
        obtain ⟨rd₁, wr₁, rsi₁, rdx₁, rcx₁, -, _, _, r₁⟩ := id b₁
        obtain ⟨rd₂, wr₂, rsi₂, rdx₂, rcx₂, -, _, _, r₂⟩ := id b₂
        exact ⟨bulk_covers hp (by rw [ha₁.wr, hi₁.inv.wr]), by
          rw [← ec, ← ed, ← eL]; exact bulk_covers hp' (by rw [ha₂.wr, hi₂.inv.wr]),
          ⟨_, bulk_ok _ hl hge rd₁ wr₁ rsi₁ rdx₁ rcx₁ r₁⟩, ⟨_, bulk_ok _ hl hge rd₂ wr₂ rsi₂ rdx₂ rcx₂ r₂⟩, b₁, b₂⟩
      · exact fun _ _ h => ⟨bulkOk hp hfL h.1.1 h.2, bulkOk hp' hfL' h.1.2 (by
          rw [← h.2]; obtain ⟨⟨_, -, -, c₁, -⟩, ⟨_, -, -, c₂, -⟩⟩ := h.1; simp only [eval, c₁, c₂, eL])⟩
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, c₁, _⟩, _⟩, hb⟩ => ?_
      simp only [eval, c₁, Option.some.injEq, decide_eq_false_iff_not] at hb
      omega_arith
  have big : RelCT isa (fun s₁ s₂ => (AtM v.callee.fold 512 s₀ s₁ ∧ AtM v.callee.fold 512 s₀' s₂) ∧
      isa.eval .e s₁ = some true) (bigS v.callee.vl) fun s₁ s₂ =>
        (MidS v.callee.fold s₀ s₁ ∨ DoneS v.callee.fold s₀ s₁) ∧
        (MidS v.callee.fold s₀' s₂ ∨ DoneS v.callee.fold s₀' s₂) :=
    args.seq (RelCT.ite (fun s₁ s₂ h => by
      obtain ⟨⟨_, -, -, c₁, -⟩, ⟨_, -, -, c₂, -⟩⟩ := h
      simp only [eval, c₁, c₂, eL]) wh bk)
  -- The keystream of the first 448 bytes computed: `preS`.
  have prOk : ∀ {σ₀ s}, APre true σ₀ → AtM v.callee.fold 512 σ₀ s → isa.eval .e s = some false →
      WP isa (preS { v.callee with pass := 512 }) s fun s' =>
        MidS v.callee.fold σ₀ s' ∨ DoneS v.callee.fold σ₀ s' := by
    intro σ₀ s hp h hb
    have hi := h.1.inv
    obtain ⟨⟨σ, ⟨hσ, hst, key, msg, hrep⟩, hf', g, m, rd, wr, d⟩, z⟩ := h
    have h0 : ¬ mOf v.callee.fold 512 (L σ₀) = 0 := fun e => by
      have := (hm0 ⟨⟨σ, ⟨hσ, hst, key, msg, hrep⟩, hf', g, m, rd, wr, d⟩, z⟩).mpr e
      rw [this] at hb; cases hb
    rw [hM hf'] at h0
    have hpre : PreLen 448 (L σ₀) := by
      split at h0
      · assumption
      · exact absurd rfl h0
    have h448 : mOf v.callee.fold 512 (L σ₀) = 448 := by rw [hM hf', ite_eq_left hpre]
    refine WP.mono (preS_mid v hf hp hi hpre (by rw [hf] at hf'; exact hf') (by rw [m]; exact hst)
      (fun k hk => by rw [m]; exact hσ.ks k (by rw [h448]; exact hk)) (by rw [m]; exact hrep)) fun s' d => ?_
    exact .inr ⟨s, key, msg, hi, by rw [hf]; exact d⟩
  have pr := ((preS_rel v hv hp hp' hq).wp
    (F₁ := fun s => MidS v.callee.fold s₀ s ∨ DoneS v.callee.fold s₀ s)
    (F₂ := fun s => MidS v.callee.fold s₀' s ∨ DoneS v.callee.fold s₀' s) fun _ _ h =>
      ⟨prOk hp h.1.1 h.2, prOk hp' h.1.2 (by
        rw [← h.2]; obtain ⟨⟨_, z₁⟩, ⟨_, z₂⟩⟩ := h.1; simp only [eval, z₁, z₂, eL])⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have call := (RelCT.callEx (n := v.callee.name)
    (P := fun s₁ s₂ => MidS v.callee.fold s₀ s₁ ∧ MidS v.callee.fold s₀' s₂) v.ok v.ct
    fun s₁ s₂ ⟨m₁, m₂⟩ => ⟨[], _, [], _, MidS.pre hp m₁ v, MidS.pre hp' m₂ v, ?_, Covers.right (MidS.hw hp m₁),
      MidS.hw hp m₁, Covers.right (MidS.hw hp' m₂), MidS.hw hp' m₂,
      by rw [(MidS.vals m₁).2.2.2.2.1, (MidS.vals m₂).2.2.2.2.1, p7]⟩).wp
    (F₁ := AfterS v.callee.fold s₀) (F₂ := AfterS v.callee.fold s₀') fun _ _ h =>
      ⟨MidS.call hp v h.1, MidS.call hp' v h.2⟩
  · -- The call if data is left.
    obtain ⟨_, hM'⟩ := movRsi_taint
    have t := ((RelCT.taint (A := taintS) (τR [])
      (P := fun s₁ s₂ => (MidS v.callee.fold s₀ s₁ ∨ DoneS v.callee.fold s₀ s₁) ∧
        (MidS v.callee.fold s₀' s₂ ∨ DoneS v.callee.fold s₀' s₂))
      (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hT).wp
      (F₁ := fun (s : State) => (MidS v.callee.fold s₀ s ∨ DoneS v.callee.fold s₀ s) ∧
        s.zf = some (s.gpr .rdx == 0))
      (F₂ := fun (s : State) => (MidS v.callee.fold s₀' s ∨ DoneS v.callee.fold s₀' s) ∧
        s.zf = some (s.gpr .rdx == 0))
      fun _ _ h => ⟨test_after h.1, test_after h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    have hz : ∀ s₁ s₂, ((MidS v.callee.fold s₀ s₁ ∨ DoneS v.callee.fold s₀ s₁) ∧ s₁.zf = some (s₁.gpr .rdx == 0)) ∧
        ((MidS v.callee.fold s₀' s₂ ∨ DoneS v.callee.fold s₀' s₂) ∧ s₂.zf = some (s₂.gpr .rdx == 0)) →
        isa.eval .e s₁ = isa.eval .e s₂ := by
      rintro s₁ s₂ ⟨⟨h₁, z₁⟩, ⟨h₂, z₂⟩⟩
      simp only [eval, z₁, z₂, rdx_of h₁ hf hfL, rdx_of h₂ hf hfL', eL]
    have ci : RelCT isa (fun s₁ s₂ => (MidS v.callee.fold s₀ s₁ ∨ DoneS v.callee.fold s₀ s₁) ∧
        (MidS v.callee.fold s₀' s₂ ∨ DoneS v.callee.fold s₀' s₂)) (callIf { v.callee with pass := 512 })
        (fun s₁ s₂ => AfterS v.callee.fold s₀ s₁ ∧ AfterS v.callee.fold s₀' s₂) := t.seq (RelCT.ite hz ?_ ?_)
    · refine fm.seq (tt.seq ((RelCT.ite (fun s₁ s₂ h => ?_) big pr).seq ci))
      obtain ⟨⟨_, z₁⟩, ⟨_, z₂⟩⟩ := h
      simp only [eval, z₁, z₂, eL]
    · -- Nothing left.
      refine ((RelCT.taint (A := taintS) (τR []) (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hM').wp
        (F₁ := AfterS v.callee.fold s₀) (F₂ := AfterS v.callee.fold s₀') fun s₁ s₂ h => ⟨?_, ?_⟩).mono
        (fun _ _ h => h) fun _ _ h => h.2
      · obtain ⟨⟨⟨h₁, z₁⟩, -⟩, hb⟩ := h
        simp only [eval, z₁, Option.some.injEq, beq_iff_eq] at hb
        exact skip_after h₁ hb
      · have hb := (hz _ _ h.1).symm.trans h.2
        obtain ⟨⟨-, ⟨h₂, z₂⟩⟩, -⟩ := h
        simp only [eval, z₂, Option.some.injEq, beq_iff_eq] at hb
        exact skip_after h₂ hb
    · -- The call.
      refine call.mono (fun s₁ s₂ h => ?_) fun _ _ h => h.2
      have hb₂ := (hz _ _ h.1).symm.trans h.2
      obtain ⟨⟨⟨h₁, z₁⟩, ⟨h₂, z₂⟩⟩, hb₁⟩ := h
      simp only [eval, z₁, Option.some.injEq, beq_eq_false_iff_ne] at hb₁
      simp only [eval, z₂, Option.some.injEq, beq_eq_false_iff_ne] at hb₂
      refine ⟨?_, ?_⟩
      · rcases h₁ with m | ⟨_, _, _, _, d⟩
        · exact m
        · exact absurd d.rdx hb₁
      · rcases h₂ with m | ⟨_, _, _, _, d⟩
        · exact m
        · exact absurd d.rdx hb₂
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

theorem prologueAP_taint : ∃ h, (taintS.check (τ₀ true) (prologueA 448 512 5) h).isSome = true := by
  taint_decide_sum []

theorem postSP_taint : ∃ h, (taintS.check (τ₁S true) (postS 448 5 .avx2) h).isSome = true := by
  taint_decide_sum [blocksBigAvx2S, blocksSmallAvx2S, finalizeSumS]

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {s₀ s₀' : State}
include hv

/-- The prologue's choice of the call, `twoKs` or `fourKs`: by the length,
which is public. -/
theorem xselA_rel {pass : Nat} (hpass : XPass pass) (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => FArgs v.callee.fold pass s₀ s₁ ∧ FArgs v.callee.fold pass s₀' s₂)
      (xselA { v.callee with pass := pass }) fun s₁ s₂ =>
        (AfterF v.callee.fold pass s₀ s₁ ∧ TailKs s₀ s₁.mem) ∧ (AfterF v.callee.fold pass s₀' s₂ ∧ TailKs s₀' s₂.mem) := by
  have hq' := hq
  obtain ⟨-, -, -, -, -, p6, p7, -, p9⟩ := hq'
  have eL : L s₀' = L s₀ := by simp only [L, p6]
  have tOk : ∀ {σ₀ s}, FArgs v.callee.fold pass σ₀ s → WP isa (.block xTest) s fun t =>
      FArgs v.callee.fold pass σ₀ t ∧ isa.eval .b t = some (decide (L σ₀ < 449)) ∧
        (1 ≤ L σ₀ → (t.gpr .rax).toNat = (L σ₀ - 1) % 512) := by
    intro σ₀ s h
    refine WP.mono (xTest_ok s) fun s₁ ⟨cf₁, rax₁, g₁, m₁, rd₁, wr₁, _⟩ =>
      ⟨?_, by rw [cf₁, h.r13], fun hl => by rw [rax₁ (by rw [h.r13]; exact hl), h.r13]⟩
    exact ⟨by rw [g₁ _ (by decide), h.rdi], by rw [g₁ _ (by decide), h.rsi],
      by rw [g₁ _ (by decide), h.rdx], by rw [g₁ _ (by decide), h.rcx],
      by rw [g₁ _ (by decide), h.r15], by rw [g₁ _ (by decide), h.r14],
      by rw [g₁ _ (by decide), h.r13], by rw [g₁ _ (by decide), h.r12],
      by rw [g₁ _ (by decide), h.rbx], by rw [g₁ _ (by decide), h.rbp],
      by rw [g₁ _ (by decide), h.rsp], by rw [rd₁, h.rd], by rw [wr₁, h.wr],
      by rw [m₁]; exact h.saved, by rw [m₁]; exact h.fine, by rw [m₁]; exact h.st, by rw [m₁]; exact h.st',
      fun k hk => by rw [m₁]; exact h.zero k hk, fun hps => by rw [m₁]; exact h.mslot hps⟩
  have fOk : ∀ {σ₀ s}, 449 ≤ L σ₀ → FArgs v.callee.fold pass σ₀ s →
      (1 ≤ L σ₀ → (s.gpr .rax).toNat = (L σ₀ - 1) % 512) →
      WP isa (.block fTest) s fun t =>
        FArgs v.callee.fold pass σ₀ t ∧ isa.eval .b t = some (decide (FLen (L σ₀))) := by
    intro σ₀ s hl h hr
    refine WP.mono (fTest_ok s) fun s₁ ⟨cf₁, g₁, m₁, rd₁, wr₁, _⟩ =>
      ⟨?_, by rw [cf₁, hr (by omega_using [hl])]⟩
    exact ⟨by rw [g₁ _ (by decide)]; exact h.rdi, by rw [g₁ _ (by decide)]; exact h.rsi,
      by rw [g₁ _ (by decide)]; exact h.rdx, by rw [g₁ _ (by decide)]; exact h.rcx,
      by rw [g₁ _ (by decide)]; exact h.r15, by rw [g₁ _ (by decide)]; exact h.r14,
      by rw [g₁ _ (by decide)]; exact h.r13, by rw [g₁ _ (by decide)]; exact h.r12,
      by rw [g₁ _ (by decide)]; exact h.rbx, by rw [g₁ _ (by decide)]; exact h.rbp,
      by rw [g₁ _ (by decide)]; exact h.rsp, by rw [rd₁]; exact h.rd,
      by rw [wr₁]; exact h.wr, by rw [m₁]; exact h.saved, by rw [m₁]; exact h.fine, by rw [m₁]; exact h.st,
      by rw [m₁]; exact h.st', fun k hk => by rw [m₁]; exact h.zero k hk, fun hps => by rw [m₁]; exact h.mslot hps⟩
  have agK : ∀ {s₁ s₂ : State}, FArgs v.callee.fold pass s₀ s₁ → FArgs v.callee.fold pass s₀' s₂ →
      X86_64.Taint.Agree (τR [.r15, .rdi, .rsp]) s₁ s₂ := fun h₁ h₂ => agree_regs _ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r15, h₂.r15, cx, cx, p9]
    · rw [h₁.rdi, h₂.rdi, cx, cx, p9]
    · rw [h₁.rsp, h₂.rsp, p7]
  obtain ⟨_, hT⟩ := xTest_taint
  have t := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => FArgs v.callee.fold pass s₀ s₁ ∧
      FArgs v.callee.fold pass s₀' s₂) (τR []) (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hT).wp
    (F₁ := fun t => FArgs v.callee.fold pass s₀ t ∧ isa.eval .b t = some (decide (L s₀ < 449)) ∧
      (1 ≤ L s₀ → (t.gpr .rax).toNat = (L s₀ - 1) % 512))
    (F₂ := fun t => FArgs v.callee.fold pass s₀' t ∧ isa.eval .b t = some (decide (L s₀' < 449)) ∧
      (1 ≤ L s₀' → (t.gpr .rax).toNat = (L s₀' - 1) % 512))
    fun _ _ h => ⟨tOk h.1, tOk h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  unfold xselA
  refine t.seq (RelCT.ite (fun s₁ s₂ h => by rw [h.1.2.1, h.2.2.1, eL]) ?_ ?_)
  · by_cases hx : L s₀ < 449
    · have hx' : L s₀' < 449 := by rw [eL]; exact hx
      exact (call1_rel hp hp' hq v).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩)
        fun _ _ h => ⟨⟨h.1, TailKs.of_xlen fun h' => by omega_using [hx, h'.1]⟩,
          ⟨h.2, TailKs.of_xlen fun h' => by omega_using [hx', h'.1]⟩⟩
    · refine RelCT.of_false fun s₁ _ h => ?_
      have e := h.1.1.2.1.symm.trans h.2
      simp [hx] at e
  · by_cases hx : L s₀ < 449
    · refine RelCT.of_false fun s₁ _ h => ?_
      have e := h.1.1.2.1.symm.trans h.2
      simp [hx] at e
    · have hl : 449 ≤ L s₀ := by omega_using [hx]
      have hl' : 449 ≤ L s₀' := by rw [eL]; exact hl
      obtain ⟨_, hC⟩ := fTest_taint
      have c := ((RelCT.taint (A := taintS) (τR []) (P := fun s₁ s₂ =>
          ((FArgs v.callee.fold pass s₀ s₁ ∧ isa.eval .b s₁ = some (decide (L s₀ < 449)) ∧
            (1 ≤ L s₀ → (s₁.gpr .rax).toNat = (L s₀ - 1) % 512)) ∧
          (FArgs v.callee.fold pass s₀' s₂ ∧ isa.eval .b s₂ = some (decide (L s₀' < 449)) ∧
            (1 ≤ L s₀' → (s₂.gpr .rax).toNat = (L s₀' - 1) % 512))) ∧ isa.eval .b s₁ = some false)
          (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hC).wp
        (F₁ := fun t => FArgs v.callee.fold pass s₀ t ∧ isa.eval .b t = some (decide (FLen (L s₀))))
        (F₂ := fun t => FArgs v.callee.fold pass s₀' t ∧ isa.eval .b t = some (decide (FLen (L s₀'))))
        fun _ _ h => ⟨fOk hl h.1.1.1 h.1.1.2.2, fOk hl' h.1.2.1 h.1.2.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
      refine c.seq (RelCT.ite (fun s₁ s₂ h => by rw [h.1.2, h.2.2, eL]) ?_ ?_)
      · by_cases hF : FLen (L s₀)
        · obtain ⟨_, hK⟩ := fourKs_taint v.callee.vl
          have hF' : FLen (L s₀') := by rw [eL]; exact hF
          exact ((RelCT.taint (A := taintS) (τR [.r15, .rdi, .rsp]) (fun s₁ s₂ h => agK h.1.1.1 h.1.2.1) hK).wp
            fun _ _ h => ⟨fourKs_ok v hv hpass hp h.1.1.1 (xlen_of_flen hl hF),
              fourKs_ok v hv hpass hp' h.1.2.1 (xlen_of_flen hl' hF')⟩).mono
            (fun _ _ h => h) fun _ _ h => h.2
        · refine RelCT.of_false fun s₁ _ h => ?_
          have e := h.1.1.2.symm.trans h.2
          simp [hF] at e
      · by_cases hF : FLen (L s₀)
        · refine RelCT.of_false fun s₁ _ h => ?_
          have e := h.1.1.2.symm.trans h.2
          simp [hF] at e
        · obtain ⟨_, hK⟩ := twoKs_taint v.callee.vl
          have hF' : ¬ FLen (L s₀') := by rw [eL]; exact hF
          exact ((RelCT.taint (A := taintS) (τR [.r15, .rdi, .rsp]) (fun s₁ s₂ h => agK h.1.1.1 h.1.2.1) hK).wp
            fun _ _ h => ⟨twoKs_ok v hv hpass hp h.1.1.1 hl hF, twoKs_ok v hv hpass hp' h.1.2.1 hl' hF'⟩).mono
            (fun _ _ h => h) fun _ _ h => h.2

/-- The prologue's choice of `twoKs` or the call: by the length, which is
public. -/
theorem xselV_rel {pass : Nat} (hpass : XPass pass) (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => FArgs v.callee.fold pass s₀ s₁ ∧ FArgs v.callee.fold pass s₀' s₂)
      (xselV { v.callee with pass := pass }) fun s₁ s₂ =>
        (AfterF v.callee.fold pass s₀ s₁ ∧ TailKs s₀ s₁.mem) ∧ (AfterF v.callee.fold pass s₀' s₂ ∧ TailKs s₀' s₂.mem) := by
  have hq' := hq
  obtain ⟨-, -, -, -, -, p6, p7, -, p9⟩ := hq'
  have eL : L s₀' = L s₀ := by simp only [L, p6]
  have tOk : ∀ {σ₀ s}, FArgs v.callee.fold pass σ₀ s → WP isa (.block xTestV) s fun t =>
      FArgs v.callee.fold pass σ₀ t ∧ isa.eval .b t = some (decide (XLen (L σ₀))) ∧
        (513 ≤ L σ₀ → (t.gpr .rax).toNat = (L σ₀ - 1) % 512) := by
    intro σ₀ s h
    refine WP.mono (xTestV_ok s) fun s₁ ⟨cf₁, rax₁, g₁, m₁, rd₁, wr₁, _⟩ =>
      ⟨?_, by rw [cf₁, h.r13], fun hl => by rw [rax₁ (by rw [h.r13]; exact hl), h.r13]⟩
    exact ⟨by rw [g₁ _ (by decide) (by decide), h.rdi], by rw [g₁ _ (by decide) (by decide), h.rsi],
      by rw [g₁ _ (by decide) (by decide), h.rdx], by rw [g₁ _ (by decide) (by decide), h.rcx],
      by rw [g₁ _ (by decide) (by decide), h.r15], by rw [g₁ _ (by decide) (by decide), h.r14],
      by rw [g₁ _ (by decide) (by decide), h.r13], by rw [g₁ _ (by decide) (by decide), h.r12],
      by rw [g₁ _ (by decide) (by decide), h.rbx], by rw [g₁ _ (by decide) (by decide), h.rbp],
      by rw [g₁ _ (by decide) (by decide), h.rsp], by rw [rd₁, h.rd], by rw [wr₁, h.wr],
      by rw [m₁]; exact h.saved, by rw [m₁]; exact h.fine, by rw [m₁]; exact h.st, by rw [m₁]; exact h.st',
      fun k hk => by rw [m₁]; exact h.zero k hk, fun hps => by rw [m₁]; exact h.mslot hps⟩
  have cOk : ∀ {σ₀ s}, XLen (L σ₀) → FArgs v.callee.fold pass σ₀ s →
      (513 ≤ L σ₀ → (s.gpr .rax).toNat = (L σ₀ - 1) % 512) →
      WP isa (.block [.alu .cmp .rax (.imm 64)]) s fun t =>
        FArgs v.callee.fold pass σ₀ t ∧ isa.eval .b t = some (decide (XLen1 (L σ₀))) := by
    intro σ₀ s hx h hr
    refine WP.mono (cmpRax64_ok s) fun s₁ ⟨cf₁, g₁, m₁, rd₁, wr₁, _⟩ => ⟨?_, by rw [cf₁, hr hx.1]⟩
    exact ⟨by rw [g₁]; exact h.rdi, by rw [g₁]; exact h.rsi, by rw [g₁]; exact h.rdx, by rw [g₁]; exact h.rcx,
      by rw [g₁]; exact h.r15, by rw [g₁]; exact h.r14, by rw [g₁]; exact h.r13, by rw [g₁]; exact h.r12,
      by rw [g₁]; exact h.rbx, by rw [g₁]; exact h.rbp, by rw [g₁]; exact h.rsp, by rw [rd₁]; exact h.rd,
      by rw [wr₁]; exact h.wr, by rw [m₁]; exact h.saved, by rw [m₁]; exact h.fine, by rw [m₁]; exact h.st,
      by rw [m₁]; exact h.st', fun k hk => by rw [m₁]; exact h.zero k hk, fun hps => by rw [m₁]; exact h.mslot hps⟩
  have agK : ∀ {s₁ s₂ : State}, FArgs v.callee.fold pass s₀ s₁ → FArgs v.callee.fold pass s₀' s₂ →
      X86_64.Taint.Agree (τR [.r15, .rdi, .rsp]) s₁ s₂ := fun h₁ h₂ => agree_regs _ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r15, h₂.r15, cx, cx, p9]
    · rw [h₁.rdi, h₂.rdi, cx, cx, p9]
    · rw [h₁.rsp, h₂.rsp, p7]
  obtain ⟨_, hT⟩ := xTestV_taint
  have t := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => FArgs v.callee.fold pass s₀ s₁ ∧
      FArgs v.callee.fold pass s₀' s₂) (τR []) (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hT).wp
    (F₁ := fun t => FArgs v.callee.fold pass s₀ t ∧ isa.eval .b t = some (decide (XLen (L s₀))) ∧
      (513 ≤ L s₀ → (t.gpr .rax).toNat = (L s₀ - 1) % 512))
    (F₂ := fun t => FArgs v.callee.fold pass s₀' t ∧ isa.eval .b t = some (decide (XLen (L s₀'))) ∧
      (513 ≤ L s₀' → (t.gpr .rax).toNat = (L s₀' - 1) % 512))
    fun _ _ h => ⟨tOk h.1, tOk h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  unfold xselV
  refine t.seq (RelCT.ite (fun s₁ s₂ h => by rw [h.1.2.1, h.2.2.1, eL]) ?_ ?_)
  · by_cases hx : XLen (L s₀)
    · have hx' : XLen (L s₀') := by rw [eL]; exact hx
      obtain ⟨_, hC⟩ := cmpRax64_taint
      have c := ((RelCT.taint (A := taintS) (τR []) (P := fun s₁ s₂ =>
          ((FArgs v.callee.fold pass s₀ s₁ ∧ isa.eval .b s₁ = some (decide (XLen (L s₀))) ∧
            (513 ≤ L s₀ → (s₁.gpr .rax).toNat = (L s₀ - 1) % 512)) ∧
          (FArgs v.callee.fold pass s₀' s₂ ∧ isa.eval .b s₂ = some (decide (XLen (L s₀'))) ∧
            (513 ≤ L s₀' → (s₂.gpr .rax).toNat = (L s₀' - 1) % 512))) ∧ isa.eval .b s₁ = some true)
          (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hC).wp
        (F₁ := fun t => FArgs v.callee.fold pass s₀ t ∧ isa.eval .b t = some (decide (XLen1 (L s₀))))
        (F₂ := fun t => FArgs v.callee.fold pass s₀' t ∧ isa.eval .b t = some (decide (XLen1 (L s₀'))))
        fun _ _ h => ⟨cOk hx h.1.1.1 h.1.1.2.2, cOk hx' h.1.2.1 h.1.2.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
      refine c.seq (RelCT.ite (fun s₁ s₂ h => by rw [h.1.2, h.2.2, eL]) ?_ ?_)
      · by_cases h1 : XLen1 (L s₀)
        · obtain ⟨_, hK⟩ := twoKsB_taint v.callee.vl
          have h1' : XLen1 (L s₀') := by rw [eL]; exact h1
          exact ((RelCT.taint (A := taintS) (τR [.r15, .rdi, .rsp]) (fun s₁ s₂ h => agK h.1.1.1 h.1.2.1) hK).wp
            fun _ _ h => ⟨twoKsB_ok v hv hpass hp h.1.1.1 (by omega_using [hx.1])
                fun hf => absurd hf.1 (Nat.not_le.mpr h1),
              twoKsB_ok v hv hpass hp' h.1.2.1 (by omega_using [hx'.1])
                fun hf => absurd hf.1 (Nat.not_le.mpr h1')⟩).mono
            (fun _ _ h => h) fun _ _ h => h.2
        · refine RelCT.of_false fun s₁ _ h => ?_
          have e := h.1.1.2.symm.trans h.2
          simp [h1] at e
      · obtain ⟨_, hK⟩ := fourKs_taint v.callee.vl
        exact ((RelCT.taint (A := taintS) (τR [.r15, .rdi, .rsp]) (fun s₁ s₂ h => agK h.1.1.1 h.1.2.1) hK).wp
          fun _ _ h => ⟨fourKs_ok v hv hpass hp h.1.1.1 hx, fourKs_ok v hv hpass hp' h.1.2.1 hx'⟩).mono
          (fun _ _ h => h) fun _ _ h => h.2
    · refine RelCT.of_false fun s₁ _ h => ?_
      have e := h.1.1.2.1.symm.trans h.2
      simp [hx] at e
  · by_cases hx : XLen (L s₀)
    · refine RelCT.of_false fun s₁ _ h => ?_
      have e := h.1.1.2.1.symm.trans h.2
      simp [hx] at e
    · have hx' : ¬ XLen (L s₀') := by rw [eL]; exact hx
      exact (call1_rel hp hp' hq v).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩)
        fun _ _ h => ⟨⟨h.1, TailKs.of_xlen hx⟩, ⟨h.2, TailKs.of_xlen hx'⟩⟩

/-- The prologue's choice, either way. -/
theorem xsel_rel {pass : Nat} (hpass : XPass pass) (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => FArgs v.callee.fold pass s₀ s₁ ∧ FArgs v.callee.fold pass s₀' s₂)
      (xsel { v.callee with pass := pass }) fun s₁ s₂ =>
        (AfterF v.callee.fold pass s₀ s₁ ∧ TailKs s₀ s₁.mem) ∧ (AfterF v.callee.fold pass s₀' s₂ ∧ TailKs s₀' s₂.mem) := by
  unfold xsel; split
  · exact xselV_rel v hv hpass hp hp' hq
  · exact xselA_rel v hv hpass hp hp' hq

theorem sealS_rel (h₀ : preX86_64 true s₀) (h₀' : preX86_64 true s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (sealStitched { v.callee with pass := 512 } v.poly)
      fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  have hfl := v.fold_le
  obtain ⟨hf, -, hw⟩ := avx2_of v hv
  have hP : PassOk v.callee.fold 512 := .inr (.inr ⟨rfl, hf⟩)
  have hA' : ∃ h, (taintS.check (τ₀ true) (prologueA v.callee.fold 512 v.callee.wide) h).isSome = true := by
    rw [hf, hw]; exact prologueAP_taint
  obtain ⟨_, hA⟩ := hA'
  obtain ⟨_, hmid⟩ := sealMid_taint v.fold_poly
  obtain ⟨_, hS⟩ := smallS_taint v.fold_poly
  have hpost' : ∃ h, (taintS.check (τ₁S true) (postS v.callee.fold v.callee.wide v.poly) h).isSome = true := by
    rw [hf, hw, hv]; exact postSP_taint
  obtain ⟨_, hpost⟩ := hpost'
  have pA := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ true)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq) hA).wp
    (F₁ := FArgs v.callee.fold 512 s₀) (F₂ := FArgs v.callee.fold 512 s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok hfl hP (wide_of v) hp, by rw [h.2]; exact prologueA_ok hfl hP (wide_of v) hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have mid := ((RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => AfterF v.callee.fold 512 s₀ s₁ ∧ AfterF v.callee.fold 512 s₀' s₂) (τA true)
    (fun _ _ h => agreeA hp hp' hq h.1 h.2) hmid).wp (F₁ := AtIteM v.callee.fold s₀)
    (F₂ := AtIteM v.callee.fold s₀') fun _ _ h =>
      ⟨WP.mono (sealMidM_ok hfl v.poly hp h.1) fun _ h => ⟨h.1, h.2 rfl⟩,
        WP.mono (sealMidM_ok hfl v.poly hp' h.2) fun _ h => ⟨h.1, h.2 rfl⟩⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hc : ∀ s₁ s₂, (AtIteM v.callee.fold s₀ s₁ ∧ AtIteM v.callee.fold s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    have : L s₀ = L s₀' := by simp only [L, hq.2.2.2.2.2.1]
    simp [eval, h.1.1.1.cf, h.2.1.1.cf, this]
  have small := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteM v.callee.fold s₀ s₁ ∧ AtIteM v.callee.fold s₀' s₂) ∧
      isa.eval .b s₁ = some true)
    (τS true) (fun _ _ h => agreeS hp hp' hq h.1.1.1.1 h.1.2.1.1) hS).wp (F₁ := AfterS v.callee.fold s₀)
    (F₂ := AfterS v.callee.fold s₀')
    fun s₁ s₂ h => by
      have e₁ := h.2
      have e₂ := (hc _ _ h.1).symm.trans h.2
      simp only [eval, h.1.1.1.1.cf, h.1.2.1.1.cf, Option.some.injEq, decide_eq_true_eq] at e₁ e₂
      exact ⟨smallS_ok hfl (wide_of v) hp h.1.1.1.1 (by omega_arith), smallS_ok hfl (wide_of v) hp' h.1.2.1.1 (by omega_arith)⟩
  -- `m` stays where the prologue stored it.
  have keep : ∀ {σ₀ s}, APre true σ₀ → AtIteM v.callee.fold σ₀ s →
      WP isa (.ite .b (smallS v.callee.wide) (bigR { v.callee with pass := 512 })) s (MSlot v.callee.fold σ₀) := by
    intro σ₀ s hp ⟨⟨hi, hst, key, msg, hrep⟩, ms⟩
    refine WP.mono (cryptIte_ok v hv hp hi.inv hi.cf hst hi.ks ms hrep) fun s' c => ?_
    show s'.mem.readW _ _ = _
    rw [c.frame.readW (r := sub σ₀ 48 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_disj σ₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj σ₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx σ₀ (by lit_omega))
      · exact (hp.stk_sub (by lit_omega)).symm) (by decide)]
    exact ms
  have ite := (RelCT.ite hc (small.mono (fun _ _ h => h) fun _ _ h => h.2) (bigR_rel v hv hp hp' hq)).wp
    (F₁ := MSlot v.callee.fold s₀) (F₂ := MSlot v.callee.fold s₀') fun _ _ h => ⟨keep hp h.1, keep hp' h.2⟩
  have post := RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AfterS v.callee.fold s₀ s₁ ∧
    AfterS v.callee.fold s₀' s₂) ∧ MSlot v.callee.fold s₀ s₁ ∧ MSlot v.callee.fold s₀' s₂) (τ₁S true)
    (fun _ _ h => agree₁S hp hp' hq h.1.1 h.1.2 h.2.1 h.2.2) hpost
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
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)

/-- The stitched loops never write the stack pointer, for either rounds. -/
theorem bulkO_spSafe (vl : Bool) : (bulkO vl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases vl <;> exact Code.all_of_allInstrs (by lit_decide)

theorem bulkP_spSafe (vl : Bool) : (bulkP vl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases vl <;> exact Code.all_of_allInstrs (by lit_decide)

theorem bigS_spSafe (vl : Bool) : (bigS vl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases vl <;> exact Code.all_of_allInstrs (by lit_decide)

theorem tailP_spSafe (vl : Bool) : (tailP vl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases vl <;> exact Code.all_of_allInstrs (by lit_decide)

/-- As `seal_spSafe`, with the stitched loops' checks above. -/
theorem sealS_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    (sealStitched { v.callee with pass := 512 } v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  obtain ⟨hf, -, hw⟩ := avx2_of v hv
  have hc := v.spSafe
  have hb := blocks_spSafe v.poly
  have h₁ := bigS_spSafe v.callee.vl
  have h₂ := bulkP_spSafe v.callee.vl
  have h₃ := tailP_spSafe v.callee.vl
  generalize hP : (fun i => !X86_64.isa.writesSp i) = P at hc hb h₁ h₂ h₃ ⊢
  rw [hv] at hb ⊢
  simp only [dataCopy, sealStitched, prologue, cryptS, preS, Code.all, hc, hb, h₁, h₂, h₃, hf, hw,
    macPad, macPadLengths, Code.iteCold, wholeBlocks, padRest, Bool.cond_false, padCopy, padTail, absorbLengths, Bool.and_true, Bool.true_and]
  subst hP; lit_decide

theorem sealS_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa (sealStitched { v.callee with pass := 512 } v.poly) s t s' ∧ abiPreserved s s' ∧
      sealX86_64.post s s' :=
  sealStitched_correct v hv (APre.of s hs)

theorem sealS_ct (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub (sealStitched { v.callee with pass := 512 } v.poly) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (sealS_rel v hv h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem sealS_verified (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    Verified X86_64.target (sealStitched { v.callee with pass := 512 } v.poly)
      (sealScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (sealS_ok v hv) (sealS_ct v hv) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealX86_64,
      Proof.ChaCha20Poly1305.preX86_64, Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg,
      X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      [sealSat] using sealSat)

theorem bulk_xdepth (vl : Bool) : (bulk vl).x86_64Depth = 0 := by cases vl <;> lit_decide
theorem bigS_xdepth (vl : Bool) : (bigS vl).x86_64Depth = 0 := by cases vl <;> lit_decide
theorem bulkP_xdepth (vl : Bool) : (bulkP vl).x86_64Depth = 0 := by cases vl <;> lit_decide
theorem twoKs_xdepth (vl : Bool) : (twoKs vl).x86_64Depth = 0 := by cases vl <;> lit_decide

theorem twoKsB_xdepth (vl : Bool) : (twoKsB vl).x86_64Depth = 0 := by cases vl <;> lit_decide

theorem fourKs_xdepth (vl : Bool) : (fourKs vl).x86_64Depth = 0 := by cases vl <;> lit_decide
theorem tailP_xdepth (vl : Bool) : (tailP vl).x86_64Depth = 0 := by cases vl <;> lit_decide

theorem sealS_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) :
    (sealStitched { v.callee with pass := 512 } v.poly).x86_64Depth ≤ 24 := by
  have hx := v.xdepth
  have hb := blocks_xdepth v.poly
  have hc := padRest_xdepth (dataCopy v.poly) v.poly 2
  have ha := padSite_xdepth (dataCopy v.poly) v.poly .rbx .rbp
  simp only [sealStitched, prologue, prologueA, prologueB, zeroKs, macPad, macPadLengths, Code.iteCold, wholeBlocks,
    padRest, padCopy, padTail, cryptS, wipeL_xdepth, preS, cryptPre, absorbLengths, finalizeTag, finalizeWith, Code.x86_64Depth, xorBuf_xdepth,
    foldM_xdepth, init_xdepth, finalize_xdepth, bigS_xdepth, bulkP_xdepth, tailP_xdepth, Nat.max_le] at hc ha ⊢
  omega_arith

theorem sealS_framed (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1728 1 42 (sealStitched { v.callee with pass := 512 } v.poly))
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1752) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1728) (k := 42) (sealS_verified v hv) (by decide) (by decide) (by decide)
    (sealS_spSafe v hv) (sealS_xdepth v) (by decide) (pre_local _ _) (sealPost_local _) (sealPost_out _)
    sealFrameSat_pre

/-! ## Short data with the AVX2 code

`sealSmall big` compares `len` (`r9`) with `smallLim` and runs the
stitched AVX2 `seal` below it, `big` otherwise. The comparison changes only
the flags, which `seal`'s contract does not read (`FlagsOnly`), and both runs
of the constant-time proof take the same branch, `len` being public. -/

/-- A state that differs from `s` at most in the flags. -/
structure FlagsOnly (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mx : t.mxcsr = s.mxcsr

/-- The comparison of `len` with `smallLim` and the window. -/
abbrev cmpSmall (vl : Bool) : List Instr := smallTest (smallLim vl)

/-- What the comparison leaves, from `s`. -/
def Cmped (vl : Bool) (s t : State) : Prop :=
  isa.eval .b t = some (decide ((s.gpr .r9).toNat < smallLim vl ∨
    (winLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < winHi))) ∧ FlagsOnly s t

theorem cmpSmall_ok (vl : Bool) (s : State) : WP isa (.block (cmpSmall vl)) s (Cmped vl s) :=
  WP.mono (smallTest_ok (by cases vl <;> decide) (by cases vl <;> decide) (by cases vl <;> decide) s)
    fun _ ⟨e, g, m, rd, wr, mx⟩ => ⟨e, g, m, rd, wr, mx⟩

namespace FlagsOnly

variable {s t : State} (h : FlagsOnly s t)
include h

theorem rdi : t.gpr .rdi = s.gpr .rdi := h.gpr _ (by decide) (by decide)
theorem rsi : t.gpr .rsi = s.gpr .rsi := h.gpr _ (by decide) (by decide)
theorem rdx : t.gpr .rdx = s.gpr .rdx := h.gpr _ (by decide) (by decide)
theorem rcx : t.gpr .rcx = s.gpr .rcx := h.gpr _ (by decide) (by decide)
theorem r8 : t.gpr .r8 = s.gpr .r8 := h.gpr _ (by decide) (by decide)
theorem r9 : t.gpr .r9 = s.gpr .r9 := h.gpr _ (by decide) (by decide)
theorem rsp : t.gpr .rsp = s.gpr .rsp := h.gpr _ (by decide) (by decide)

theorem arg (i : Nat) : stackArg t i = stackArg s i := by
  show t.mem.readW (t.gpr .rsp + _) 64 = s.mem.readW (s.gpr .rsp + _) 64
  rw [h.mem, h.rsp]

theorem argAddr (i : Nat) : stackArgAddr t i = stackArgAddr s i := by
  show t.gpr .rsp + _ = s.gpr .rsp + _
  rw [h.rsp]

theorem pre (hs : sealX86_64.pre s) : sealX86_64.pre t := by
  show preX86_64 true t
  have ha := h.arg
  have hb := h.argAddr
  simp only [preX86_64, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp, h.rd, h.wr, ha, hb] at hs ⊢
  exact hs

theorem post {z : State} (hz : sealX86_64.post t z) : sealX86_64.post s z := by
  have ha := h.arg
  simp only [sealX86_64, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.mem, ha] at hz ⊢
  exact hz

theorem abi {z : State} (hz : abiPreserved t z) : abiPreserved s z := by
  obtain ⟨h₁, h₂, h₃⟩ := hz
  refine ⟨fun r hr => ?_, by rw [← h.mem, ← h.rsp]; exact h₂, by rw [← h.mx]; exact h₃⟩
  have : r ≠ .rax ∧ r ≠ .r10 := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [h₁ r hr, h.gpr r this.1 this.2]

end FlagsOnly

theorem FlagsOnly.pub {s₁ s₂ t₁ t₂ : State} (h₁ : FlagsOnly s₁ t₁) (h₂ : FlagsOnly s₂ t₂)
    (hp : sealX86_64.pub s₁ s₂) : sealX86_64.pub t₁ t₂ := by
  show pubX86_64 t₁ t₂
  simp only [pubX86_64, h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.rsp, h₂.rdi, h₂.rsi, h₂.rdx,
    h₂.rcx, h₂.r8, h₂.r9, h₂.rsp, h₁.arg, h₂.arg]
  exact hp

theorem sealSmall_ok (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : ∀ s, sealX86_64.pre s → ∃ t s', Exec isa big s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s')
    (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa (sealSmall u.callee big) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  have hw : WP isa (sealSmall u.callee big) s fun z => abiPreserved s z ∧ sealX86_64.post s z := by
    refine WP.seq (WP.mono (cmpSmall_ok u.callee.vl s) fun e ⟨he, hf⟩ => ?_)
    refine WP.ite _ he (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨t, s', ex, ha, hp⟩ := sealS_ok u hu e (hf.pre hs)
      rw [hu] at ex
      exact ⟨t, s', ex, hf.abi ha, hf.post hp⟩
    · obtain ⟨t, s', ex, ha, hp⟩ := hb e (hf.pre hs)
      exact ⟨t, s', ex, hf.abi ha, hf.post hp⟩
  obtain ⟨t, s', he, hq⟩ := hw
  exact ⟨t, s', he, hq⟩

/-- Pairs of states that `seal`'s contract allows, with the same public data. -/
abbrev PP (s₁ s₂ : State) : Prop := sealX86_64.pre s₁ ∧ sealX86_64.pre s₂ ∧ sealX86_64.pub s₁ s₂

/-- Constant-time code, from states after the comparison in two runs. -/
theorem rel_cmped {vl : Bool} {c : Prog isa} (hc : ConstantTime isa sealX86_64.pre sealX86_64.pub c)
    {R : State → State → Prop}
    (hR : ∀ a b, R a b → ∃ σ₁ σ₂, PP σ₁ σ₂ ∧ Cmped vl σ₁ a ∧ Cmped vl σ₂ b) :
    RelCT isa R c fun _ _ => True := by
  intro a b t₁ t₂ a' b' hr e₁ e₂
  obtain ⟨σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, f₁⟩, ⟨-, f₂⟩⟩ := hR a b hr
  exact ⟨hc _ _ _ _ _ _ (f₁.pre p₁) (f₂.pre p₂) (FlagsOnly.pub f₁ f₂ hp) e₁ e₂, trivial⟩

theorem sealSmall_ct (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa} (hb : ConstantTime isa sealX86_64.pre sealX86_64.pub big) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub (sealSmall u.callee big) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have hblk : RelCT isa PP (.block (cmpSmall u.callee.vl)) fun _ _ => True := by
    obtain ⟨_, hc⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r9]) (.block (cmpSmall u.callee.vl)) hc).isSome = true := by
      generalize u.callee.vl = vl; cases vl <;> exact ⟨_, by taint_decide⟩
    exact RelCT.taint (A := taint) (Taint.ofRegs [.r9]) (fun s₁ s₂ h => Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2.2.2.2.2.1)) hc
  refine RelCT.seq (RelCT.wpDep (F := Cmped u.callee.vl) hblk fun s₁ s₂ _ => ⟨cmpSmall_ok _ s₁, cmpSmall_ok _ s₂⟩) ?_
  refine RelCT.ite (fun a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, ⟨e₁, _⟩, ⟨e₂, _⟩⟩ => ?_) ?_ ?_
  · rw [e₁, e₂, show σ₁.gpr .r9 = σ₂.gpr .r9 from hp.2.2.2.2.2.1]
  · have hs := sealS_ct u hu
    rw [hu] at hs
    exact rel_cmped hs
      fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩
  · exact rel_cmped hb fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩

theorem sealSmall_verified (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : ∀ s, sealX86_64.pre s → ∃ t s', Exec isa big s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s')
    (hc : ConstantTime isa sealX86_64.pre sealX86_64.pub big) :
    Verified X86_64.target (sealSmall u.callee big) (sealScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (sealSmall_ok u hu hb) (sealSmall_ct u hu hc) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealX86_64,
      Proof.ChaCha20Poly1305.preX86_64, Proof.ChaCha20Poly1305.pubX86_64, X86_64.abi, X86_64.stackArg,
      X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      [sealSat] using sealSat)

theorem sealSmall_spSafe (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa} (hb : big.all (fun i => !X86_64.isa.writesSp i) = true) :
    (sealSmall u.callee big).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := sealS_spSafe u hu
  rw [hu] at h
  simp only [sealSmall, Code.all, hb, Bool.and_true]
  exact Bool.and_eq_true_iff.mpr ⟨by generalize u.callee.vl = vl; cases vl <;> decide, h⟩

theorem sealSmall_xdepth (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa} (hb : big.x86_64Depth ≤ 24) : (sealSmall u.callee big).x86_64Depth ≤ 24 := by
  have h := sealS_xdepth u
  rw [hu] at h
  simp only [sealSmall, Code.x86_64Depth, Nat.max_le]
  exact ⟨by decide, h, hb⟩

/-! ## The `seal` of an instance -/

theorem sealFor_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (sealFor v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h₁ := seal_spSafe v
  cases hb : v.poly with
  | avx2 => have h₂ := sealS_spSafe v hb; rw [hb] at h₂; exact h₂
  | avx512 =>
    rw [hb] at h₁
    have := sealSmall_spSafe v.small v.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | _ => rw [hb] at h₁; exact h₁

theorem sealFor_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) : (sealFor v.callee v.poly).x86_64Depth ≤ 24 := by
  have h₁ := seal_xdepth v
  have h₂ := sealS_xdepth v
  cases hb : v.poly with
  | avx2 => rw [hb] at h₂; exact h₂
  | avx512 =>
    rw [hb] at h₁
    have := sealSmall_xdepth v.small v.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | _ => rw [hb] at h₁; exact h₁

theorem sealFor_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1728 1 42 (sealFor v.callee v.poly))
      (Spec.ChaCha20Poly1305.sealContract X86_64.abi 1752) := by
  have h₁ := seal_framed v
  cases hb : v.poly with
  | avx2 => have h₂ := sealS_framed v hb; rw [hb] at h₂; exact h₂
  | avx512 =>
    have ho := seal_ok v
    have hc := seal_ct v
    have hs := seal_spSafe v
    have hd := seal_xdepth v
    rw [hb] at ho hc hs hd
    have hv := sealSmall_verified v.small v.small_poly ho hc
    have hs' := sealSmall_spSafe v.small v.small_poly hs
    have hd' := sealSmall_xdepth v.small v.small_poly hd
    rw [Proof.ChaCha20.X86_64.XorImpl.small_callee] at hv hs' hd'
    exact X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
      (n := 212) (post := Spec.ChaCha20Poly1305.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
      (bytes := 1728) (k := 42) hv (by decide) (by decide) (by decide) hs' hd' (by decide) (pre_local _ _) (sealPost_local _) (sealPost_out _)
      sealFrameSat_pre
  | _ => rw [hb] at h₁; exact h₁

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
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds Consts Incs stR bufR slotsR dR5 DWin W2 plus hiR
  setup_ok finish_ok W2_frame incs_frame hiR_slots hiR_sub slotsR_sub plus_block ks_shift ctr_add)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)
open VG.Spec.ChaCha20 (stateAt serialize innerBlock keystream)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- The 512 bytes at `q` absorbed, then XORed with eight blocks of keystream
from the state at `st`, and `rsi` advanced past them. -/
theorem chunkMainO_ok (vl : Bool) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hwd : DWin s.wr q)
    (hin : ∀ off n, off + n ≤ 512 → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsd : (stR st).Disjoint (dR5 q)) (dsb : (stR st).Disjoint (bufR buf))
    (dbd : (bufR buf).Disjoint (dR5 q)) (dqs : (dR5 q).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa (chunkMainO vl) s fun s' =>
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
    have := bytes_frame F₁ dqs (by decide) (j := 0) (n := 512) (by decide)
    simpa using this
  have h0 : SR false buf q R0 R1 X (fun j => ctr (stateAt s.mem st) j) s₁ 0 s₁ :=
    ⟨hh, h15, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      rw [show 16 * firstBlock false 0 = 0 from rfl, show bytesAt s₁.mem q 0 = [] from rfl,
        VG.Proof.Poly1305.absorbAll_nil]
      exact ⟨by rw [g₁]; exact hacc.r8, by rw [g₁]; exact hacc.r9, by rw [g₁]; exact hacc.r10,
        by rw [g₁]; exact hacc.h2, by simp only [hval, g₁]; exact hacc.val⟩⟩
  refine WP.seq (WP.mono (sroundsFor_ok (T := 32) hk (by rw [g₁, hrsi]) (by rw [rd₁, wr₁]; exact hin) vl false
    (by decide) (Nat.le_refl 32)
    (by rw [g₁, hrcx]) (by rw [wr₁]; exact hb) c₁.m8 ⟨c₁.lo16, c₁.hi16⟩ dqs h0) fun s₂ h₂ => ?_)
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
    exact dqs.symm _ hc' (Offset.contains_base q (d := k) (n := 1) (k := 512) (by omega_arith) (by lit_omega))
  have gk : ∀ r, r ∉ absorbRegs → r ≠ .rsi → s₄.gpr r = s.gpr r := fun r hr hs => by
    rw [g₄ r hs, g₃, gk₂ r hr]
  refine ⟨fun k hk' => by rw [m₄, d₃ k hk', hS, hq₂ k hk'], ?_, by rw [m₄]; exact (F₂.mono (by frame_regions)).trans f₃,
    gk, by rw [rsi₄, g₃, gk₂ _ (by decide), hrsi], by rw [rd₄, rd₃, h₂.rd, rd₁], by rw [wr₄, wr₃, wr₂]⟩
  have a₂ := h₂.acc
  rw [firstBlock_ten, total_false, q₁] at a₂
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
  rw [Offset.add_add, h.data _ (by omega_arith), ite_eq_right (by omega_arith)]

/-- A chunk of `open`: the invariant from `t` to `t + 1`. -/
theorem chunkO_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {t : Nat} (hge : 512 ≤ L - 512 * t) {s : State}
    (h : LO c dp L R0 R1 A m₀ sp t s) :
    WP isa (chunkO vl) s fun s' => LO c dp L R0 R1 A m₀ sp (t + 1) s' ∧
      s'.cf = some (decide (L - 512 * (t + 1) < 512)) := by
  have hLe := hl.L_lt
  have hw : 512 * t + 512 ≤ L := by omega_arith
  have hq : dp + BitVec.ofNat 64 (512 * t) + 512 = dp + BitVec.ofNat 64 (512 * (t + 1)) := by
    have := window_eq dp (t := t + 1) (by omega_arith); rwa [Nat.add_sub_cancel] at this
  have mst : stR (stA c) ∈ s.wr := by rw [h.wr]; frame_regions
  have mbf : bufR (bfA c) ∈ s.wr := by rw [h.wr]; frame_regions
  have md : (⟨dp, L⟩ : Region) ∈ s.wr := by rw [h.wr]; frame_regions
  have hwd : DWin s.wr (dp + BitVec.ofNat 64 (512 * t)) := by
    intro off n hn
    exact ⟨_, md, by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hin : ∀ off n, off + n ≤ 512 →
      InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 off) n := by
    intro off n hn
    exact ⟨_, List.mem_append_right _ md, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have dsd : (stR (stA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * t))) := hl.win_cd hw (by decide)
  have dbd : (bufR (bfA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * t))) := hl.win_cd hw (by decide)
  have dqs : (dR5 (dp + BitVec.ofNat 64 (512 * t))).Disjoint (slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right (win hw)).symm
  refine WP.seq (WP.mono (chunkMainO_ok vl hk h.rdi h.rcx h.rsi mst mbf hwd hin h.consts dsd st_bf dbd dqs h.acc)
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
    ⟨psR c, by rw [wr₁, h.wr]; frame_regions, slot_in⟩ st_slot
    (n := L - 512 * t) (by omega_arith) hge sl₁)
    fun s₂ ⟨_, sl₂, cnt₂, f₂, g₂, rd₂, wr₂, _, _, cf₂⟩ => ?_
  have dst : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t))], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf.sub_right (slotsR_sub _)
    · exact dsd
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame f₁ dst
  have FA : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
      s.mem s₂.mem := (f₁.mono (by frame_regions)).trans (f₂.mono (by frame_regions))
  refine ⟨⟨by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr], by rw [g₂ _ (by decide) (by decide),
    g₁ _ (by decide) (by decide), h.rdi], by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rcx],
    by rw [g₂ _ (by decide) (by decide), rsi₁],
    by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rsp], by omega_arith,
    by rw [sl₂, show L - 512 * t - 512 = L - 512 * (t + 1) by omega_arith], ?_, ?_, ?_, ?_, ?_⟩,
    by rw [cf₂, show L - 512 * t - 512 = L - 512 * (t + 1) by omega_arith]⟩
  · rw [cnt₂, S₁, h.cnt, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ctr_add,
      show 8 * t + 8 = 8 * (t + 1) by omega_arith]
  · intro k hk'
    have n_st : ¬ (stR (stA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.st_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    have n_sl : ¬ (⟨slot (bfA c), 8⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.ps_d _ (slot_ps _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    have n_sls : ¬ (slotsR (bfA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.bf_d _ (slotsR_sub _ _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    rw [f₂ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact n_st
      · exact n_sl)]
    by_cases hin' : 512 * t ≤ k ∧ k < 512 * t + 512
    · have ea : dp + BitVec.ofNat 64 k =
          dp + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) := by
        rw [Offset.add_add, Nat.add_sub_cancel' hin'.1]
      have x₁ := d₁ (k - 512 * t) (by omega_arith)
      rw [← ea] at x₁
      rw [x₁, h.data k hk', ite_eq_right (by omega_arith : ¬ k < 512 * t), ite_eq_left (by omega_arith : k < 512 * (t + 1)),
        plus_block, h.cnt, ks_shift _ hk' hin'.1]
    · have n_w : ¬ (dR5 (dp + BitVec.ofNat 64 (512 * t))).Contains (dp + BitVec.ofNat 64 k) 1 := by
        simp only [Region.Contains]
        rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)]
        split <;> omega_arith
      rw [f₁ _ (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact n_sls
          · exact n_w), h.data k hk']
      by_cases hlt : k < 512 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega_arith : k < 512 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_arith : ¬ k < 512 * (t + 1))]
  · refine h.consts.frame FA ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hiR_slots _
    · exact (hl.bf_d.sub_left (hiR_sub _)).sub_right (win hw)
    · exact (st_bf.symm.sub_left (hiR_sub _))
    · exact ((Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide) :
        (bufR (bfA c)).Disjoint (psR c)).sub_left (hiR_sub _)).sub_right slot_ps
  · rw [h.chunk_bytes hw, ← VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega_arith),
      ← VG.Proof.Poly1305.bytesAt_add, show 512 * t + 512 = 512 * (t + 1) by omega_arith] at a₁
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
theorem chunksO_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {s : State} (hge : 512 ≤ L) (h : LO c dp L R0 R1 A m₀ sp 0 s) :
    WP isa (.loop (chunkO vl) .ae) s fun s' => ∃ T, LO c dp L R0 R1 A m₀ sp T s' ∧ L - 512 * T < 512 := by
  let Inv : Nat → State → Prop := fun n s => ∃ u, n = L - 512 * u ∧ 512 ≤ L - 512 * u ∧
    LO c dp L R0 R1 A m₀ sp u s
  refine WP.loop (M := isa) Inv (fun n s ⟨u, hn, hu, hL⟩ => ?_) _ s ⟨0, rfl, by omega_arith, h⟩
  refine WP.mono (chunkO_ok vl hl hk hu hL) fun s' ⟨hL', cf'⟩ => ?_
  by_cases hlt : L - 512 * (u + 1) < 512
  · exact .inl ⟨by simp [eval, cf', hlt], u + 1, hL', hlt⟩
  · exact .inr ⟨by simp [eval, cf', hlt], L - 512 * (u + 1), by omega_arith, u + 1, rfl, by omega_arith, hL'⟩

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
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
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
    ⟨_, hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
  have i : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions (s.rd ++ s.wr) (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, List.mem_append_right _ hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
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

/-- `LO` reads no flag, and of the registers only the kernel's and Poly1305's
key and accumulator. -/
theorem LO.of_rdx {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    {s s' : State} (h : LO c dp L R0 R1 A m₀ sp T s) (hg : ∀ r, r ≠ .rdx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : LO c dp L R0 R1 A m₀ sp T s' :=
  ⟨by rw [hrd, h.rd], by rw [hwr, h.wr], by rw [hg _ (by decide), h.rdi], by rw [hg _ (by decide), h.rcx],
    by rw [hg _ (by decide), h.rsi], by rw [hg _ (by decide), h.rsp], h.le, by rw [hm, h.left],
    by rw [hm, h.cnt], fun k hk => by rw [hm, h.data k hk], by rw [hm]; exact h.consts,
    ⟨by rw [hg _ (by decide)]; exact h.acc.r8, by rw [hg _ (by decide)]; exact h.acc.r9,
      by rw [hg _ (by decide)]; exact h.acc.r10, by rw [hg _ (by decide)]; exact h.acc.h2,
      by simp only [hval, hg Reg.r11 (by decide), hg Reg.rbx (by decide), hg Reg.rbp (by decide)]
         exact h.acc.val⟩,
    by rw [hm]; exact h.fr⟩

/-- `restO`'s test: `rdx` the bytes left less 193, `CF` set if 193 to 511 are left. -/
theorem restPreO_ok₀ {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    (hL : L < 2 ^ 64) {s : State} (h : LO c dp L R0 R1 A m₀ sp T s) :
    WP isa (.block [.mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 193), .alu .cmp .rdx (.imm 319)]) s
      fun s' => LO c dp L R0 R1 A m₀ sp T s' ∧
        s'.cf = some (decide (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + 319)) ∧
        s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - BitVec.ofNat 64 193 := by
  have hsl : InRegions (s.rd ++ s.wr) (slot (bfA c)) 8 :=
    ⟨psR c, List.mem_append_right _ (by rw [h.wr]; frame_regions), slot_in⟩
  have hv := h.left
  simp only [slot, lenOff] at hsl hv
  have e193 : BitVec.signExtend 64 (193 : BitVec 32) = BitVec.ofNat 64 193 := by decide
  have e319 : BitVec.signExtend 64 (319 : BitVec 32) = BitVec.ofNat 64 319 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, readSrc, execAlu,
    arithFlags, State.load64, State.setReg, State.setFlags, lenOff, h.rcx, hsl, hv, e193, e319, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨LO.of_rdx h (fun r hr => by simp [hr]) rfl rfl rfl, ?_, by simp⟩
  rw [Proof.Poly1305.X86_64.toNat_ofNat_lt (by decide)]
  congr 1
  apply propext
  have hr : L - 512 * T < 2 ^ 64 := by omega_arith
  rw [BitVec.toNat_sub, Proof.Poly1305.X86_64.toNat_ofNat_lt hr,
    Proof.Poly1305.X86_64.toNat_ofNat_lt (n := 193) (by decide)]
  by_cases h65 : 193 ≤ L - 512 * T
  · rw [show 2 ^ 64 - 193 + (L - 512 * T) = 2 ^ 64 + (L - 512 * T - 193) by omega_arith, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

/-- `restO`'s test after its padding. -/
theorem restPreO_ok {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    (hL : L < 2 ^ 64) {s : State} (h : LO c dp L R0 R1 A m₀ sp T s) :
    WP isa (.block (padIns .rdx 5 ++ ([.mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 193),
      .alu .cmp .rdx (.imm 319)] : List Instr))) s
      fun s' => LO c dp L R0 R1 A m₀ sp T s' ∧
        s'.cf = some (decide (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + 319)) ∧
        s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - BitVec.ofNat 64 193 :=
  WP.block_append (WP.mono (padIns_ok .rdx (by decide) s) fun _ p =>
    restPreO_ok₀ hL (LO.of_rdx h p.gpr p.mem p.rd p.wr))

/-- `restO`'s later tests, on `rdx` the bytes left less 193: `CF` set if 193
to `192 + n` are left. -/
theorem restCmpO_ok {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    (hL : L < 2 ^ 64) {i : BitVec 32} {n : Nat} (hn : n ≤ 512) (xi : BitVec.signExtend 64 i = BitVec.ofNat 64 n)
    {s : State} (h : LO c dp L R0 R1 A m₀ sp T s)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - BitVec.ofNat 64 193) :
    WP isa (.block [.alu .cmp .rdx (.imm i)]) s
      fun s' => LO c dp L R0 R1 A m₀ sp T s' ∧
        s'.cf = some (decide (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + n)) ∧ s'.gpr .rdx = s.gpr .rdx := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    xi, hrdx, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨LO.of_rdx h (fun _ _ => rfl) rfl rfl rfl, ?_, trivial⟩
  rw [Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega_arith)]
  congr 1
  apply propext
  have hr : L - 512 * T < 2 ^ 64 := by omega_arith
  rw [BitVec.toNat_sub, Proof.Poly1305.X86_64.toNat_ofNat_lt hr,
    Proof.Poly1305.X86_64.toNat_ofNat_lt (n := 193) (by decide)]
  by_cases h65 : 193 ≤ L - 512 * T
  · rw [show 2 ^ 64 - 193 + (L - 512 * T) = 2 ^ 64 + (L - 512 * T - 193) by omega_arith, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

/-- The blocks `tailO` absorbs of `n` bytes left. -/
def kOf (n : Nat) : Nat := if n ≤ 128 then 4 else if n < 192 then 8 else 12

theorem kOf_ok (n : Nat) : OK (kOf n) := by
  unfold kOf; split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

theorem kOf_le {n : Nat} (h : 64 ≤ n) : 16 * kOf n ≤ n := by
  unfold kOf; split <;> (try split) <;> omega_arith

/-- The blocks `tail3O` or `tailKO` absorbs of `n` bytes left. -/
def kOfK (n : Nat) : Nat := if n < 385 then 16 else 24

theorem kOfK_le {n : Nat} (h : 257 ≤ n) : 16 * kOfK n ≤ n := by
  unfold kOfK; split <;> omega_arith

/-- After `bulkO`, from `s`: the first `512 T` bytes of the `L` decrypted, and
`512 T + a` absorbed (`a` the first blocks of 64 to 256 bytes left, whose
keystream `tailO` computed into `buf`, or none), `rbx`, `rbp` the bytes
after those. -/
structure BulkOR (c dp : Addr) (L : Nat) (s : State) (key msg : List Byte) (T a : Nat) (s' : State) :
    Prop where
  t1 : 1 ≤ T
  le : 512 * T ≤ L
  lt : L - 512 * T < 512
  data : ∀ k < L, s'.mem (dp + BitVec.ofNat 64 k) = if k < 512 * T then
    s.mem (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt s.mem (stA c)) L).getD k 0
    else s.mem (dp + BitVec.ofNat 64 k)
  cnt : stateAt s'.mem (stA c) = ctr (stateAt s.mem (stA c)) (8 * T)
  repr : Repr s'.mem (psA c) key (msg ++ bytesAt s.mem dp (512 * T + a))
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T + a)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L - (512 * T + a))
  r12 : s'.gpr .r12 = s.gpr .r12
  r13 : s'.gpr .r13 = s.gpr .r13
  r14 : s'.gpr .r14 = s.gpr .r14
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  tail : (a = 0 ∧ ¬ (193 ≤ L - 512 * T ∧ L - 512 * T ≤ 256) ∧ L - 512 * T < 257) ∨
    (193 ≤ L - 512 * T ∧ L - 512 * T ≤ 256 ∧ a = 16 * kOf (L - 512 * T) ∧
      ∀ i < L - 512 * T, s'.mem (bfA c + BitVec.ofNat 64 i) =
        (keystream (stateAt s.mem (stA c)) L).getD (512 * T + i) 0) ∨
    (257 ≤ L - 512 * T ∧ a = 16 * kOfK (L - 512 * T) ∧
      ∀ i < L - 512 * T, s'.mem (kA (bfA c) + BitVec.ofNat 64 i) =
        (keystream (stateAt s.mem (stA c)) L).getD (512 * T + i) 0)
  /-- The keystream `twoKs` left at `ctx + 736` kept, unless the rest's is there. -/
  x736 : L - 512 * T < 257 →
    ∀ k < 192, s'.mem (c + BitVec.ofNat 64 (736 + k)) = s.mem (c + BitVec.ofNat 64 (736 + k))

/-- What `bulkO`'s `enter` leaves, from `s` to `s₁`, for its end. -/
structure OEnt (c dp : Addr) (L : Nat) (s : State) (key msg : List Byte) (R0 R1 : BitVec 64) (A : Nat)
    (s₁ : State) : Prop where
  hk : Key R0 R1
  hr : clamp (leNum (key.take 16)) = rN R0 R1
  hAm : A = accumulate (rN R0 R1) msg
  hAP : A < P
  e₁ : ∀ k < L, s₁.mem (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k)
  S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c)
  v12 : s₁.mem.readW (c + BitVec.ofNat 64 520) 64 = s.gpr .r12
  v13 : s₁.mem.readW (c + BitVec.ofNat 64 528) 64 = s.gpr .r13
  v14 : s₁.mem.readW (c + BitVec.ofNat 64 536) 64 = s.gpr .r14
  kb : bytesAt s₁.mem (c + BitVec.ofNat 64 472) 32 = bytesAt s.mem (c + BitVec.ofNat 64 472) 32
  len : msg.length % 16 = 0
  krep : bytesAt s.mem (psA c + 24) 32 = key
  rd : s.rd = []
  wr : s.wr = bulkWr c dp L
  x736 : ∀ k < 192, s₁.mem (c + BitVec.ofNat 64 (736 + k)) = s.mem (c + BitVec.ofNat 64 (736 + k))

/-- A byte at `ctx + 736` (the keystream `twoKs` left) is outside the regions of
`ctx` below it. -/
theorem x736_nc (c : Addr) {d n k : Nat} (h : d + n ≤ 736) (hk : k < 192) :
    ¬ (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Contains (c + BitVec.ofNat 64 (736 + k)) 1 := fun hc =>
  Offset.disjoint c (d := d) (n := n) (e := 736 + k) (k := 1) (.inl (by omega_arith)) (by lit_omega) (by lit_omega) _ hc
    (Region.contains_self _ _)

/-- The chunks keep `ctx + 736`. -/
theorem lo_x736 {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr}
    {T : Nat} {s₃ : State} (L₃ : LO c dp L R0 R1 A m₀ sp T s₃) {k : Nat} (hk : k < 192) :
    s₃.mem (c + BitVec.ofNat 64 (736 + k)) = m₀ (c + BitVec.ofNat 64 (736 + k)) :=
  L₃.fr _ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact x736_nc c (d := 64) (n := 64) (by decide) hk
    · exact fun hc => hl.cd (d := 736 + k) (n := 1) (by omega_arith) _ (Region.contains_self _ _) hc
    · exact x736_nc c (d := 128) (n := 320) (by decide) hk
    · rw [slot_eq]; exact x736_nc c (d := 544) (n := 8) (by decide) hk

section
variable {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) {s s₁ : State} {key msg : List Byte}
  {R0 R1 : BitVec 64} {A : Nat} (he : OEnt c dp L s key msg R0 R1 A s₁)
include hl hge he

omit hge he in
theorem lo_ctx {T : Nat} {s₃ : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃) {d : Nat}
    (h₁ : 520 ≤ d) (h₂ : d + 8 ≤ 544) :
    s₃.mem.readW (c + BitVec.ofNat 64 d) 64 = s₁.mem.readW (c + BitVec.ofNat 64 d) 64 := by
  refine L₃.fr.readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact hl.cd (by omega_arith)
  · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
  · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by omega_arith)) (by omega_arith) (by decide)

omit hge in
theorem OEnt.key₃ {T : Nat} {s₃ : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃) :
    bytesAt s₃.mem (c + BitVec.ofNat 64 472) 32 = bytesAt s.mem (c + BitVec.ofNat 64 472) 32 := by
  rw [← he.kb]
  exact bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) L₃.fr (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · exact hl.cd (by decide)
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)

omit hl he in
theorem lo_t1 {T : Nat} {s₃ : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃)
    (hT : L - 512 * T < 512) : 1 ≤ T := by
  have := L₃.le
  by_contra h'
  have : T = 0 := by omega
  subst this; omega_arith

omit hl hge in
theorem OEnt.data {T : Nat} {s₃ s' : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃)
    {rs : List Region} (hrs : ∀ r ∈ rs, ∀ k < L, ¬ r.Contains (dp + BitVec.ofNat 64 k) 1)
    (F : Frame rs s₃.mem s'.mem) :
    ∀ k < L, s'.mem (dp + BitVec.ofNat 64 k) = if k < 512 * T then
      s.mem (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt s.mem (stA c)) L).getD k 0
      else s.mem (dp + BitVec.ofNat 64 k) := by
  intro k hk
  rw [F _ fun r hr => hrs r hr k hk, L₃.data k hk, he.e₁ k hk, he.S₁]

omit hl hge in
theorem OEnt.acc {T : Nat} {s₃ : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃) {a : Nat}
    (ha : 512 * T + a ≤ L) (_ha16 : a % 16 = 0) :
    absorbAll (rN R0 R1) (absorbAll (rN R0 R1) A (bytesAt s₁.mem dp (512 * T)))
      (bytesAt s₃.mem (dp + BitVec.ofNat 64 (512 * T)) a) % P =
    accumulate (clamp (leNum (key.take 16))) (msg ++ bytesAt s.mem dp (512 * T + a)) := by
  have hd₁ : bytesAt s₁.mem dp (512 * T) = bytesAt s.mem dp (512 * T) := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => he.e₁ i (by have := List.mem_range.mp hi; omega_arith)
  have hd₃ : bytesAt s₃.mem (dp + BitVec.ofNat 64 (512 * T)) a =
      bytesAt s.mem (dp + BitVec.ofNat 64 (512 * T)) a := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [Offset.add_add, L₃.data _ (by omega_arith), ite_eq_right (by omega_arith), he.e₁ _ (by omega_arith)]
  rw [hd₁, hd₃, he.hr, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.accumulate_append he.len,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega_arith), ← he.hAm,
    Nat.mod_eq_of_lt (VG.Proof.Poly1305.absorbAll_lt (VG.Proof.Poly1305.absorbAll_lt he.hAP _) _)]

/-- `leaveO`, with none or fewer than 64 or more than 256 bytes left. -/
theorem leaveO_fin {T : Nat} {s₃ : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃)
    (hT : L - 512 * T < 257) (hnt : ¬ (193 ≤ L - 512 * T ∧ L - 512 * T ≤ 256)) :
    WP isa (.block leaveO) s₃ fun s' => ∃ T a, BulkOR c dp L s key msg T a s' := by
  have hLe := hl.L_lt
  rw [leaveO_eq]
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₃) fun s₄ ⟨red, k₄⟩ => ?_)
  refine WP.mono (storeO_ok (c := c) (s := s₄) (by rw [k₄.gpr', L₃.rcx]) (by rw [k₄.2.2.2, L₃.wr]; frame_regions))
    fun s₅ ⟨m₅, rbx₅, rbp₅, rdx₅, r12₅, r13₅, r14₅, r15₅, g₅, rd₅, wr₅⟩ => ?_
  have hTL := L₃.le
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have FA : Frame [accR c] s₃.mem s₅.mem := by rw [m₅, ← m₄]; exact accMem_frame _ _ _ _ _
  have S₅ : stateAt s₅.mem (stA c) = stateAt s₃.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame FA (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  have hkey : bytesAt s₅.mem (c + BitVec.ofNat 64 472) 32 = bytesAt s.mem (c + BitVec.ofNat 64 472) 32 := by
    rw [← he.key₃ hl L₃]
    exact bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) FA (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)) (by decide)
  have hslot : s₄.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 (L - 512 * T) := by
    rw [m₄, ← slot_eq, L₃.left]
  have g5 : ∀ r : Reg, r = .rsp ∨ r = .rsi → s₅.gpr r = s₃.gpr r := by
    intro r hr
    rcases hr with rfl | rfl <;>
      rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k₄.gpr']
  refine ⟨T, 0, ⟨lo_t1 hge L₃ (by omega_arith), hTL, by omega_arith, he.data L₃ (fun r hr k hk => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun hc => hl.cd (d := 448) (n := 24) (by decide) _ hc
        (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))) FA,
    by rw [S₅, L₃.cnt, he.S₁], ⟨?_, ?_, ?_⟩, by rw [rbx₅, k₄.gpr', L₃.rsi, Nat.add_zero],
    by rw [rbp₅, hslot, Nat.add_zero], by rw [r12₅, m₄, lo_ctx hl L₃ (d := 520) (by decide) (by decide), he.v12],
    by rw [r13₅, m₄, lo_ctx hl L₃ (d := 528) (by decide) (by decide), he.v13],
    by rw [r14₅, m₄, lo_ctx hl L₃ (d := 536) (by decide) (by decide), he.v14], r15₅,
    by rw [g5 _ (.inl rfl), L₃.rsp], by rw [rd₅, k₄.2.2.1, L₃.rd, he.rd], by rw [wr₅, k₄.2.2.2, L₃.wr, he.wr],
    .inl ⟨rfl, hnt, hT⟩, fun _ k hk => by
      rw [FA _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact x736_nc c (d := 448) (n := 24) (by decide) hk),
        lo_x736 hl L₃ hk, he.x736 k hk]⟩⟩
  · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := he.len; omega_arith
  · rw [psA_24, hkey, ← psA_24]; exact he.krep
  · rw [m₅, accMem_acc]
    show hval s₄ = _
    have e := he.acc L₃ (a := 0) (by omega_arith) rfl
    rw [show bytesAt s₃.mem (dp + BitVec.ofNat 64 (512 * T)) 0 = [] from rfl,
      VG.Proof.Poly1305.absorbAll_nil] at e
    rw [red L₃.acc.h2, L₃.acc.val, e]

/-- `tailO two k`, with `k` the blocks `kOf` chooses for 64 to `128 S` bytes left. -/
theorem tailO_fin (two : Bool) {T : Nat} {s₃ : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃)
    (hT : L - 512 * T < 512) (hlo : 193 ≤ L - 512 * T) (hhi : L - 512 * T ≤ 256)
    (hS : L - 512 * T ≤ 128 * (if two then 2 else 1)) :
    WP isa (tailO two (kOf (L - 512 * T))) s₃ fun s' => ∃ T a, BulkOR c dp L s key msg T a s' := by
  have hLe := hl.L_lt
  have hTL := L₃.le
  have hk16 : 16 * kOf (L - 512 * T) ≤ L - 512 * T := by unfold kOf; split <;> (try split) <;> omega_arith
  have tp : TPO c dp L (512 * T) (L - 512 * T) R0 R1 (absorbAll (rN R0 R1) A (bytesAt s₁.mem dp (512 * T)))
      (s.gpr .rsp) s₃ :=
    ⟨by rw [L₃.wr]; frame_regions, by rw [L₃.wr]; frame_regions, by rw [L₃.wr]; frame_regions, by rw [L₃.wr]; frame_regions, by omega_arith,
      L₃.rdi, L₃.rcx, L₃.rsi, L₃.rsp, L₃.left, L₃.acc⟩
  refine WP.mono (tailOg_ok hl he.hk two (kOf_ok _) hk16 hS tp) fun s' tm => ?_
  have dsj : ∀ r ∈ [accR c, bufR (bfA c)], ∀ k < L, ¬ r.Contains (dp + BitVec.ofNat 64 k) 1 := by
    intro r hr k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fun hc => hl.cd (d := 448) (n := 24) (by decide) _ hc
        (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    · exact fun hc => hl.bf_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
  have S' : stateAt s'.mem (stA c) = stateAt s₃.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame tm.frame (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
      · exact st_bf)
  have hkey : bytesAt s'.mem (c + BitVec.ofNat 64 472) 32 = bytesAt s.mem (c + BitVec.ofNat 64 472) 32 := by
    rw [← he.key₃ hl L₃]
    exact bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) tm.frame (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)) (by decide)
  refine ⟨T, 16 * kOf (L - 512 * T), ⟨lo_t1 hge L₃ hT, hTL, hT, he.data L₃ dsj tm.frame,
    by rw [S', L₃.cnt, he.S₁], ⟨?_, ?_, ?_⟩, tm.rbx, by rw [tm.rbp]; congr 1; omega_arith,
    by rw [tm.r12, lo_ctx hl L₃ (d := 520) (by decide) (by decide), he.v12],
    by rw [tm.r13, lo_ctx hl L₃ (d := 528) (by decide) (by decide), he.v13],
    by rw [tm.r14, lo_ctx hl L₃ (d := 536) (by decide) (by decide), he.v14], tm.r15, tm.rsp,
    by rw [tm.rd, L₃.rd, he.rd], by rw [tm.wr, L₃.wr, he.wr], .inr (.inl ⟨hlo, hhi, rfl, fun i hi => ?_⟩),
    fun _ k hk => by
      rw [tm.frame _ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact x736_nc c (d := 448) (n := 24) (by decide) hk
        · exact x736_nc c (d := 128) (n := 320) (by decide) hk),
        lo_x736 hl L₃ hk, he.x736 k hk]⟩⟩
  · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := he.len; omega_arith
  · rw [psA_24, hkey, ← psA_24]; exact he.krep
  · rw [tm.acc, he.acc L₃ (by omega_arith) (by omega_arith)]
  · rw [tm.ks i hi, L₃.cnt, he.S₁, show 8 * T = 512 * T / 64 by omega_arith,
      ← ks_from _ (by omega_arith) (show 512 * T + i < L by omega_arith) (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      show L - 512 * T = L - 512 * T from rfl]

omit hl hge he in
theorem TailMidKO.pad {o n k : Nat} {X : Nat} {sp : Addr} {t u : State}
    (h : TailMidKO c dp o n k R0 R1 X sp s₁ t) (p : PadPost .rax t u) : TailMidKO c dp o n k R0 R1 X sp s₁ u :=
  ⟨fun i hi => by rw [p.mem]; exact h.ks i hi, by rw [p.mem]; exact h.acc, by rw [p.mem]; exact h.frame,
    by rw [p.gpr _ (by decide)]; exact h.rbx, by rw [p.gpr _ (by decide)]; exact h.rbp,
    by rw [p.gpr _ (by decide)]; exact h.r12, by rw [p.gpr _ (by decide)]; exact h.r13,
    by rw [p.gpr _ (by decide)]; exact h.r14, by rw [p.gpr _ (by decide)]; exact h.r15,
    by rw [p.gpr _ (by decide)]; exact h.rsp, by rw [p.rd]; exact h.rd, by rw [p.wr]; exact h.wr⟩

/-- What `tail3O` or `tailKO` leaves, with `k` the blocks `kOfK` chooses for
257 to 511 bytes left. -/
theorem tailK_fin {T : Nat} {s₃ s' : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃)
    (hT : L - 512 * T < 512) (hlo : 257 ≤ L - 512 * T)
    (tm : TailMidKO c dp (512 * T) (L - 512 * T) (kOfK (L - 512 * T)) R0 R1
      (absorbAll (rN R0 R1) A (bytesAt s₁.mem dp (512 * T))) (s.gpr .rsp) s₃ s') :
    ∃ T a, BulkOR c dp L s key msg T a s' := by
  have hLe := hl.L_lt
  have hTL := L₃.le
  have hk16 := kOfK_le hlo
  have kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  have dsj : ∀ r ∈ [accR c, bufR (bfA c), kR (bfA c)], ∀ k < L, ¬ r.Contains (dp + BitVec.ofNat 64 k) 1 := by
    intro r hr k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fun hc => hl.cd (d := 448) (n := 24) (by decide) _ hc
        (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    · exact fun hc => hl.bf_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    · rw [kc]; exact fun hc => hl.cd (d := 736) (n := 512) (by decide) _ hc
        (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
  have S' : stateAt s'.mem (stA c) = stateAt s₃.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame tm.frame (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
      · exact st_bf
      · rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  have hkey : bytesAt s'.mem (c + BitVec.ofNat 64 472) 32 = bytesAt s.mem (c + BitVec.ofNat 64 472) 32 := by
    rw [← he.key₃ hl L₃]
    exact bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) tm.frame (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
  refine ⟨T, 16 * kOfK (L - 512 * T), ⟨lo_t1 hge L₃ hT, hTL, hT, he.data L₃ dsj tm.frame,
    by rw [S', L₃.cnt, he.S₁], ⟨?_, ?_, ?_⟩, tm.rbx, by rw [tm.rbp]; congr 1; omega_arith,
    by rw [tm.r12, lo_ctx hl L₃ (d := 520) (by decide) (by decide), he.v12],
    by rw [tm.r13, lo_ctx hl L₃ (d := 528) (by decide) (by decide), he.v13],
    by rw [tm.r14, lo_ctx hl L₃ (d := 536) (by decide) (by decide), he.v14], tm.r15, tm.rsp,
    by rw [tm.rd, L₃.rd, he.rd], by rw [tm.wr, L₃.wr, he.wr], .inr (.inr ⟨hlo, rfl, fun i hi => ?_⟩),
    fun h => absurd h (by omega_arith)⟩⟩
  · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := he.len; omega_arith
  · rw [psA_24, hkey, ← psA_24]; exact he.krep
  · rw [tm.acc, he.acc L₃ (by omega_arith) (by omega_arith)]
  · rw [tm.ks i hi, L₃.cnt, he.S₁, show 8 * T = 512 * T / 64 by omega_arith,
      ← ks_from _ (by omega_arith) (show 512 * T + i < L by omega_arith) (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

omit hl hge he in
/-- The bytes left as `tail3O` and `tailKO` start, as `tailO` does. -/
theorem tpo_of {T : Nat} {s₃ : State} (L₃ : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) T s₃) :
    TPO c dp L (512 * T) (L - 512 * T) R0 R1 (absorbAll (rN R0 R1) A (bytesAt s₁.mem dp (512 * T)))
      (s.gpr .rsp) s₃ := by
  have hTL := L₃.le
  exact ⟨by rw [L₃.wr]; frame_regions, by rw [L₃.wr]; frame_regions, by rw [L₃.wr]; frame_regions, by rw [L₃.wr]; frame_regions, by omega_arith,
    L₃.rdi, L₃.rcx, L₃.rsi, L₃.rsp, L₃.left, L₃.acc⟩

end

/-- `enter`, from the arguments of `bulkO` or `wholeO`: what it leaves for
the rest (`OEnt`), and the state before the first chunk (`LO` at 0). -/
theorem enterO_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {s : State}
    (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 L) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa (.block enter) s fun s₁ => ∃ R0 R1 A, OEnt c dp L s key msg R0 R1 A s₁ ∧
      LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) 0 s₁ := by
  refine WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_
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
  have he : OEnt c dp L s key msg R0 R1 A s₁ :=
    ⟨hk, hr, hAm, hAP, enter_data hl F₁, Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ dst, v12, v13, v14,
      enter_key F₁, hrep.1, hrep.2.1, hrd, hwr, fun k hk => F₁ _ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact x736_nc c (d := 128) (n := 320) (by decide) hk
        · exact x736_nc c (d := 520) (n := 32) (by decide) hk⟩
  have h0 : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) 0 s₁ := by
    refine ⟨by rw [rd₁, hrd], by rw [wr₁, hwr], rdi₁, by rw [gk _ (.inl rfl), hrcx],
      by rw [gk _ (.inr (.inl rfl)), hrsi]; simp, gk _ (.inr (.inr rfl)), by omega_arith,
      by rw [sl₁, hrdx, Nat.mul_zero, Nat.sub_zero], by simp [VG.Proof.ChaCha20.ctr_zero], fun k _ => by simp, C₁, ?_, Frame.refl _ _⟩
    rw [show 512 * 0 = 0 from rfl, show bytesAt s₁.mem dp 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
    refine ⟨r8₁.trans hR0, r9₁.trans hR1, by rw [r10₁, r9₁, hR1], ?_, ?_⟩
    · have hP : P = 2 ^ 130 - 5 := rfl
      rw [rbp₁]; omega_using [hA', hAP, hP]
    · simp only [hval, r11₁, rbx₁, rbp₁, hA']
  exact ⟨R0, R1, A, he, h0⟩

theorem bulkO_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) {s : State}
    (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 L) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa (bulkO vl) s fun s' => ∃ T a, BulkOR c dp L s key msg T a s' := by
  have hLe := hl.L_lt
  unfold bulkO
  refine WP.seq (WP.mono (enterO_ok hl hrd hwr hrsi hrdx hrcx hrep) fun s₁ ⟨R0, R1, A, he, h0⟩ => ?_)
  have hk := he.hk
  refine WP.seq (WP.mono (chunksO_ok vl hl hk hge h0) fun s₃ ⟨T, L₃, hT⟩ => ?_)
  unfold restO
  refine WP.seq (WP.mono (restPreO_ok hLe L₃) fun s₄ ⟨L₄, cf₄, rdx₄⟩ => ?_)
  refine WP.ite (decide (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + 319)) (by simp only [eval, cf₄])
    (fun hc => ?_) (fun hc => ?_)
  rotate_left
  · simp only [decide_eq_false_iff_not] at hc
    exact leaveO_fin hl hge he L₄ (by omega_arith) (by omega_arith)
  simp only [decide_eq_true_eq] at hc
  refine WP.seq (WP.mono (restCmpO_ok hLe (n := 64) (by decide) (by decide) L₄ rdx₄)
    fun s₅ ⟨L₅, cf₅, rdx₅⟩ => ?_)
  refine WP.ite (decide (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + 64)) (by simp only [eval, cf₅])
    (fun hc₅ => ?_) (fun hc₅ => ?_)
  · simp only [decide_eq_true_eq] at hc₅
    have ek : kOf (L - 512 * T) = 12 := by unfold kOf; split <;> (try split) <;> omega_arith
    rw [← ek]
    exact tailO_fin hl hge he true L₅ hT hc₅.1 (by omega_arith) (by simp only [ite_true]; omega_arith)
  simp only [decide_eq_false_iff_not] at hc₅
  rw [← rdx₅] at rdx₄
  refine WP.seq (WP.mono (restCmpO_ok hLe (n := 192) (by decide) (by decide) L₅ rdx₄)
    fun s₆ ⟨L₆, cf₆, _⟩ => ?_)
  refine WP.ite (decide (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + 192)) (by simp only [eval, cf₆])
    (fun hc₆ => ?_) (fun hc₆ => ?_)
  · simp only [decide_eq_true_eq] at hc₆
    have ek : kOfK (L - 512 * T) = 16 := by unfold kOfK; split <;> omega_arith
    exact WP.mono (tail3Og_ok hl he.hk (by omega_arith) (by omega_arith) (tpo_of L₆) (by rw [L₆.wr]; frame_regions))
      fun s' tm => tailK_fin hl hge he L₆ hT (by omega_arith) (by rw [ek]; exact tm)
  · simp only [decide_eq_false_iff_not] at hc₆
    have ek : kOfK (L - 512 * T) = 24 := by unfold kOfK; split <;> omega_arith
    exact WP.seq (WP.mono (tailKOg_ok vl hl he.hk (by omega_arith) (by omega_arith) (tpo_of L₆) (by rw [L₆.wr]; frame_regions)
      L₆.consts) fun s₇ tm => WP.mono (padIns_ok .rax (by cases vl <;> decide) s₇)
        fun s' p => tailK_fin hl hge he L₆ hT (by omega_arith) (by rw [ek]; exact tm.pad p))

/-- `vzeroupper` keeps all but the vector registers' upper bits. -/
theorem vzuO_ok (s : State) : WP isa (.block [.vop .vzeroupper]) s fun t =>
    t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `wholeO`, from `s`, with 449 to 511 bytes: the keystream of all of
them at `kA`, the first 448 absorbed, `rbx`, `rbp` the bytes after those, and
the data and the ChaCha20 state kept. -/
structure WholeOR (c dp : Addr) (L : Nat) (s : State) (key msg : List Byte) (s' : State) : Prop where
  data : ∀ k < L, s'.mem (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k)
  st : stateAt s'.mem (stA c) = stateAt s.mem (stA c)
  repr : Repr s'.mem (psA c) key (msg ++ bytesAt s.mem dp 448)
  ks : ∀ i < L, s'.mem (kA (bfA c) + BitVec.ofNat 64 i) = (keystream (stateAt s.mem (stA c)) L).getD i 0
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 448
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L - 448)
  r12 : s'.gpr .r12 = s.gpr .r12
  r13 : s'.gpr .r13 = s.gpr .r13
  r14 : s'.gpr .r14 = s.gpr .r14
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem wholeO_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) (h448 : 448 ≤ L) (hlt : L < 512)
    {s : State} (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 L) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa (wholeO vl) s (WholeOR c dp L s key msg) := by
  have hLe := hl.L_lt
  have t28 : 16 * total true = 448 := rfl
  unfold wholeO
  refine WP.seq (WP.mono (enterO_ok hl hrd hwr hrsi hrdx hrcx hrep) fun s₁ ⟨R0, R1, A, he, h0⟩ => ?_)
  have kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  have dsk : (stR (stA c)).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dbk : (bufR (bfA c)).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dak : (accR c).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dqs : (⟨dp, 16 * total true⟩ : Region).Disjoint (Proof.ChaCha20.X86_64.Avx2.slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right
      (Region.sub_prefix (base := dp) (len := 16 * total true) (by rw [t28]; exact h448))).symm
  have rsi₁ : s₁.gpr .rsi = dp := by rw [h0.rsi]; simp
  have hin : ∀ off n, off + n ≤ 16 * total true → InRegions (s₁.rd ++ s₁.wr) (dp + BitVec.ofNat 64 off) n :=
    fun off n hn => ⟨⟨dp, L⟩, List.mem_append_right _ (by rw [h0.wr]; frame_regions),
      Offset.contains_base _ (by rw [t28] at hn; omega_arith) (by omega_arith)⟩
  have acc₁ : Acc R0 R1 A s₁ := by
    have a := h0.acc
    rwa [show 512 * 0 = 0 from rfl, show bytesAt s₁.mem dp 0 = [] from rfl,
      VG.Proof.Poly1305.absorbAll_nil] at a
  refine WP.seq (WP.mono (tailKMain_ok vl true he.hk h0.rdi h0.rcx rsi₁ (by rw [h0.wr]; frame_regions)
    (by rw [h0.wr]; frame_regions) (by rw [h0.wr]; frame_regions) hin h0.consts st_bf dsk dbk dqs acc₁)
    fun s₂ ⟨d₂, a₂, f₂, g₂, rd₂, wr₂⟩ => ?_)
  rw [leaveTO_eq, List.append_assoc]
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₂) fun s₃ ⟨red, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (storeTO_ok (k := 28) (by decide) (c := c) (s := s₃)
    (by rw [k₃.gpr', g₂ _ (by decide), h0.rcx]) (by rw [k₃.2.2.2, wr₂, h0.wr]; frame_regions))
    fun s₄ ⟨m₄, rbx₄, rbp₄, r12₄, r13₄, r14₄, r15₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.mono (vzuO_ok s₄) fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ => ?_
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  have mA : s₅.mem = accMem s₂.mem c (s₃.gpr .r11) (s₃.gpr .rbx) (s₃.gpr .rbp) := by rw [m₅, m₄, m₃]
  have fa : Frame [accR c] s₂.mem s₅.mem := by rw [mA]; exact accMem_frame _ _ _ _ _
  have F : Frame [Proof.ChaCha20.X86_64.Avx2.slotsR (bfA c), kR (bfA c), accR c] s₁.mem s₅.mem := (f₂.mono (by frame_regions)).trans (fa.mono (by frame_regions))
  have nst : ∀ d, 520 ≤ d → d + 8 ≤ 552 → ∀ r ∈ [Proof.ChaCha20.X86_64.Avx2.slotsR (bfA c), kR (bfA c)],
      (⟨c + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
    · rw [kc]; exact Offset.disjoint c (Or.inl (by omega_arith)) (by omega_arith) (by decide)
  have rd₂' : ∀ d, 520 ≤ d → d + 8 ≤ 552 →
      s₃.mem.readW (c + BitVec.ofNat 64 d) 64 = s₁.mem.readW (c + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [m₃]; exact f₂.readW (Region.contains_self _ _) (nst d h₁ h₂) (by decide)
  have gs : ∀ r, r = .rsi ∨ r = .rsp → s₃.gpr r = s₁.gpr r := by
    intro r hr; rcases hr with rfl | rfl <;> rw [k₃.gpr', g₂ _ (by decide)]
  have g5 : ∀ r, r = .rsp → s₅.gpr r = s₃.gpr r := by
    intro r hr; subst hr
    rw [g₅, g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hd : ∀ r ∈ [Proof.ChaCha20.X86_64.Avx2.slotsR (bfA c), kR (bfA c), accR c], ∀ k < L, ¬ r.Contains (dp + BitVec.ofNat 64 k) 1 := by
    intro r hr k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fun hc => hl.cd (d := 128) (n := 128) (by decide) _ hc
        (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    · rw [kc]; exact fun hc => hl.cd (d := 736) (n := 512) (by decide) _ hc
        (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    · exact fun hc => hl.cd (d := 448) (n := 24) (by decide) _ hc
        (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
  have S₅ : stateAt s₅.mem (stA c) = stateAt s₁.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st_bf.sub_right (Proof.ChaCha20.X86_64.Avx2.slotsR_sub _)
      · exact dsk
      · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  have hkey : bytesAt s₅.mem (c + BitVec.ofNat 64 472) 32 = bytesAt s.mem (c + BitVec.ofNat 64 472) 32 := by
    rw [← he.key₃ hl h0]
    exact bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) F (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)) (by decide)
  have hslot : s₃.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 L := by
    rw [rd₂' 544 (by decide) (by decide), ← slot_eq, h0.left, Nat.mul_zero, Nat.sub_zero]
  refine ⟨fun k hk => ?_, by rw [S₅, he.S₁], ⟨?_, ?_, ?_⟩, fun i hi => ?_, by rw [g₅, rbx₄, gs _ (.inl rfl), rsi₁],
    by rw [g₅, rbp₄, hslot, Offset.ofNat_sub_ofNat h448],
    by rw [g₅, r12₄, rd₂' 520 (by decide) (by decide), he.v12],
    by rw [g₅, r13₄, rd₂' 528 (by decide) (by decide), he.v13],
    by rw [g₅, r14₄, rd₂' 536 (by decide) (by decide), he.v14], by rw [g₅, r15₄],
    by rw [g5 _ rfl, gs _ (.inr rfl), h0.rsp], by rw [rd₅, rd₄, k₃.2.2.1, rd₂, h0.rd, he.rd],
    by rw [wr₅, wr₄, k₃.2.2.2, wr₂, h0.wr, he.wr]⟩
  · rw [F _ (fun r hr => hd r hr k hk), he.e₁ k hk]
  · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := he.len; omega_arith
  · rw [psA_24, hkey, ← psA_24]; exact he.krep
  · rw [mA, accMem_acc]
    show hval s₃ = _
    have e := he.acc h0 (a := 448) (by omega_arith) rfl
    rw [show 512 * 0 = 0 from rfl, show bytesAt s₁.mem dp 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil,
      Nat.zero_add, show dp + BitVec.ofNat 64 0 = dp from BitVec.add_zero _] at e
    rw [red a₂.h2, a₂.val, t28, e]
  · rw [fa _ (fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dak _ hc (kR_contains _ (by omega_arith))), d₂ i (by omega_arith), ← he.S₁,
      Proof.ChaCha20.X86_64.Avx2.plus_block, VG.Proof.ChaCha20.keystream_getD _ hi]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `cryptO`

`Stitch.cryptO`, in `open`'s context, does what `open`'s `macPadLengths`
followed by `crypt` does (`cryptO_ok`): the padded ciphertext and the
lengths block absorbed, and the data decrypted. With at most `fold` bytes it
is that code. Otherwise `bulkO` decrypts and absorbs the whole chunks
(`bulkO_ok`, moved to `open`'s permissions with `RegionModel.wp_narrow`),
or below 512 bytes `wholeO` absorbs the first 448 and leaves the keystream
of all of the data at `ctx + 736` (`wholeO_ok`, `MidO`); `macPadLengths`
absorbs the rest, as it was on entry, and the lengths block; and `decRest`
decrypts the rest: below 512 bytes from that keystream, which it then wipes
(`decWhole_ok`), otherwise as `bulkO` left it or by `vg_chacha20_xor` from
the counter `bulkO` leaves.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

/-- Whether `bulkO` computes the keystream of the rest, `[E, L)`, into `buf`
(`tailO`): from 512 bytes on, with 64 to 256 bytes after the whole chunks. -/
def TailC (L E : Nat) : Prop := 512 ≤ L ∧ 193 ≤ L - E ∧ L - E ≤ 256

/-- Whether `bulkO` computes the keystream of the rest, `[E, L)`, at
`ctx + 736` (`tail3O`, `tailKO`): from 512 bytes on, with 257 to 511 bytes
after the whole chunks. -/
def TailK (L E : Nat) : Prop := 512 ≤ L ∧ 257 ≤ L - E

/-- The bytes absorbed after `wholeO` or `bulkO`, a function of the length:
below 512 bytes the first 448 (`wholeO`); otherwise the whole chunks, and
with `tailO`, `tail3O` or `tailKO` its first blocks of the rest. -/
def Aof (L : Nat) : Nat :=
  if L < 512 then 448 else
    Eof L + if 512 ≤ L ∧ 193 ≤ L - Eof L ∧ L - Eof L ≤ 256 then 16 * kOf (L - Eof L)
      else if 512 ≤ L ∧ 257 ≤ L - Eof L then 16 * kOfK (L - Eof L) else 0

theorem Aof_lt {L : Nat} (h : L < 512) : Aof L = 448 := by
  unfold Aof
  exact ite_eq_left h

theorem Aof_tail {L : Nat} (h : TailC L (Eof L)) : Aof L = Eof L + 16 * kOf (L - Eof L) := by
  unfold Aof
  rw [ite_eq_right (by unfold TailC at h; omega_arith)]
  split
  · rfl
  · next hn => exact absurd h hn

theorem Aof_tailK {L : Nat} (h : TailK L (Eof L)) : Aof L = Eof L + 16 * kOfK (L - Eof L) := by
  unfold Aof
  unfold TailK at h
  rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left h]

theorem Aof_notail {L : Nat} (hge : 512 ≤ L) (h : ¬ TailC L (Eof L)) (hk : ¬ TailK L (Eof L)) :
    Aof L = Eof L := by
  unfold Aof
  rw [ite_eq_right (by omega_arith)]
  split
  · next hc => exact absurd hc h
  · split
    · next hc => exact absurd hc hk
    · rfl

/-- After `cryptO`'s branch on 512 bytes: the first `E` bytes (a multiple of
64, all the whole chunks) decrypted, and the first `A` bytes of ciphertext,
as it was in the state `s` before the branch's arguments, absorbed: below 512
bytes 448, the keystream of all of the data at `ctx + 736` (`wholeO`);
otherwise `E` bytes, or, with `tailO`, `tail3O` or `tailKO`, more, the
keystream of the rest then in `buf` or at `ctx + 736`. -/
structure MidO (s₀ s : State) (key msg : List Byte) (E A : Nat) (s' : State) : Prop where
  rbx : s'.gpr .rbx = dp s₀ + BitVec.ofNat 64 A
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L s₀ - A)
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
  frame : Frame [sub s₀ 64 512, sub s₀ 736 512, dR s₀] s.mem s'.mem
  A16 : A % 16 = 0
  EA : E ≤ A
  AL : A ≤ L s₀
  repr : Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (dp s₀) A)
  tail : (L s₀ < 512 ∧ ∀ i < L s₀,
      s'.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) = (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0) ∨
    (512 ≤ L s₀ ∧ A = E ∧ ¬ TailC (L s₀) E ∧ ¬ TailK (L s₀) E) ∨ (TailC (L s₀) E ∧ ∀ i < L s₀ - E,
      s'.mem (off (cx s₀) 128 + BitVec.ofNat 64 i) = (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (E + i) 0) ∨
    (TailK (L s₀) E ∧ ∀ i < L s₀ - E,
      s'.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) = (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (E + i) 0)
  Aeq : A = Aof (L s₀)
  /-- The keystream `twoKs` left at `ctx + 736` kept. -/
  x736 : TailKs s₀ s.mem → TailKs s₀ s'.mem

/-- `MidO` through a padding of `rax`. -/
theorem MidO.pad {s₀ s : State} {key msg : List Byte} {E A : Nat} {t u : State} (h : MidO s₀ s key msg E A t)
    (p : PadPost .rax t u) : MidO s₀ s key msg E A u := by
  obtain ⟨rbx, rbp, keep, rd, wr, E64, EL, Ediv, st, data, frame, A16, EA, AL, repr, tail, Aeq, x736⟩ := h
  refine ⟨by rw [p.gpr _ (by decide), rbx], by rw [p.gpr _ (by decide), rbp], fun r hr => ?_, by rw [p.rd, rd],
    by rw [p.wr, wr], E64, EL, Ediv, by rw [p.mem, st], fun k hk => by rw [p.mem, data k hk], by rw [p.mem]; exact frame,
    A16, EA, AL, by rw [p.mem]; exact repr, by rw [p.mem]; exact tail, Aeq, fun t => by rw [p.mem]; exact x736 t⟩
  rw [p.gpr _ (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), keep r hr]

/-- Below 512 bytes (449 to 511): `wholeO`, with its permissions. Nothing
is decrypted yet, the first 448 bytes are absorbed, and the keystream of all
of the data is at `ctx + 736`. -/
theorem wholeO_midO (vl : Bool) {s₀ : State} (hp : APre e s₀) {s s₂ : State} (hwr : s.wr = s₀.wr)
    (ha : Args s₀ s s₂) (h15 : s.gpr .r15 = cx s₀) (h448 : 448 ≤ L s₀) (hlt : L s₀ < 512)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (wholeO vl) s₂ (MidO s₀ s key msg 0 448) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hl : Lay (cx s₀) (dp s₀) (L s₀) := ⟨hL9, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have st₂ : stateAt s₂.mem (stA (cx s₀)) = initState (K s₀) 1 (N s₀) := by
    show stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64) = _
    rw [ha.mem, ← off_eq, stateAt_ctr, hst, set12_initState]
  have hw : Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.wr := bulk_covers hp (by rw [ha.wr, hwr])
  have hn : (wholeO vl).noCalls = true := by cases vl <;> lit_decide
  refine regionModel.wp_narrow (r := []) (w := bulkWr (cx s₀) (dp s₀) (L s₀))
    (wholeO_ok vl hl h448 hlt (s := s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) rfl rfl ha.rsi ha.rdx
      (by rw [State.withRegions_gpr, ha.rcx, off_eq])
      (by show Repr _ (cx s₀ + BitVec.ofNat 64 448) _ _
          rw [State.withRegions_mem, ha.mem, ← off_eq]; exact args_repr hrep))
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s₃ _ rd₃ wr₃ f₃ hP => ?_
  obtain ⟨data, st, repr, ks, rbx, rbp, r12, r13, r14, r15, rsp, -, -⟩ := hP
  have f₃' : Frame (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.mem s₃.mem := f₃
  have st' : stateAt s₃.mem (stA (cx s₀)) = stateAt s₂.mem (stA (cx s₀)) := st
  have data' : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s₂.mem (dp s₀ + BitVec.ofNat 64 k) := data
  have ks' : ∀ i < L s₀, s₃.mem (kA (bfA (cx s₀)) + BitVec.ofNat 64 i) =
      (keystream (stateAt s₂.mem (stA (cx s₀))) (L s₀)).getD i 0 := ks
  have hb : bytesAt s₂.mem (dp s₀) 448 = bytesAt s.mem (dp s₀) 448 := by
    simp only [bytesAt]
    refine List.map_congr_left fun k hk => ?_
    have := List.mem_range.mp hk
    rw [ha.mem, args_data hp _ (by omega_arith)]
  refine ⟨rbx, rbp, fun r hr => ?_, (rd₃ : s₃.rd = s₂.rd).trans ha.rd, (wr₃ : s₃.wr = s₂.wr).trans ha.wr, rfl,
    Nat.zero_le _, by omega_arith, ?_, fun k hk => ?_, ?_, rfl, Nat.zero_le _, h448, ?_,
    .inl ⟨hlt, fun i hi => ?_⟩, (Aof_lt hlt).symm, fun _ h => absurd h (by omega_arith)⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (r12 : s₃.gpr .r12 = s₂.gpr .r12).trans (ha.keep _ (.inl rfl))
    · exact (r13 : s₃.gpr .r13 = s₂.gpr .r13).trans (ha.keep _ (.inr (.inl rfl)))
    · exact (r14 : s₃.gpr .r14 = s₂.gpr .r14).trans (ha.keep _ (.inr (.inr (.inl rfl))))
    · exact (r15 : s₃.gpr .r15 = cx s₀).trans h15.symm
    · exact (rsp : s₃.gpr .rsp = s₂.gpr .rsp).trans (ha.keep _ (.inr (.inr (.inr rfl))))
  · rw [off_eq, st', st₂, Nat.zero_div, VG.Proof.ChaCha20.ctr_zero]
  · rw [data' k hk, ha.mem, args_data hp _ hk, ite_eq_right (Nat.not_lt_zero _)]
  · rw [ha.mem] at f₃'
    refine ((args_frame s₀ s.mem).sub fun r hr => ?_).trans (f₃'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have e : sub s₀ 64 512 = ⟨cx s₀ + BitVec.ofNat 64 64, 512⟩ := by rw [sub, off_eq]
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨sub s₀ 736 512, by simp, by
          rw [show kR (bfA (cx s₀)) = sub s₀ 736 512 by simp only [kR, kA, bfA, sub, off_eq, Offset.add_add]]
          exact fun _ h => h⟩
  · rw [off_eq, ← hb]; exact repr
  · rw [show off (cx s₀) 736 = kA (bfA (cx s₀)) by simp only [kA, bfA, off_eq, Offset.add_add], ks' i hi, st₂]

/-- The whole chunks: `bulkO`, with its permissions. -/
theorem bulk_midO (vl : Bool) {s₀ : State} (hp : APre e s₀) {s s₂ : State} (hwr : s.wr = s₀.wr) (ha : Args s₀ s s₂)
    (h15 : s.gpr .r15 = cx s₀) (hge : 512 ≤ L s₀)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (bulkO vl) s₂ fun s₃ => ∃ E A, MidO s₀ s key msg E A s₃ := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hl : Lay (cx s₀) (dp s₀) (L s₀) := ⟨hL9, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have st₂ : stateAt s₂.mem (stA (cx s₀)) = initState (K s₀) 1 (N s₀) := by
    show stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64) = _
    rw [ha.mem, ← off_eq, stateAt_ctr, hst, set12_initState]
  have hw : Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.wr := bulk_covers hp (by rw [ha.wr, hwr])
  have hn : (bulkO vl).noCalls = true := by cases vl <;> lit_decide
  refine regionModel.wp_narrow (r := []) (w := bulkWr (cx s₀) (dp s₀) (L s₀))
    (bulkO_ok vl hl hge (s := s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) rfl rfl ha.rsi ha.rdx
      (by rw [State.withRegions_gpr, ha.rcx, off_eq])
      (by show Repr _ (cx s₀ + BitVec.ofNat 64 448) _ _
          rw [State.withRegions_mem, ha.mem, ← off_eq]; exact args_repr hrep))
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s₃ _ rd₃ wr₃ f₃ hP => ?_
  obtain ⟨T, a, ⟨t1, le, lt, data, cnt, repr, rbx, rbp, r12, r13, r14, r15, rsp, -, -, tail, x736⟩⟩ := hP
  have f₃' : Frame (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.mem s₃.mem := f₃
  have cnt' : stateAt s₃.mem (cx s₀ + BitVec.ofNat 64 64) =
      ctr (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (8 * T) := cnt
  have data' : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = if k < 512 * T then
      s₂.mem (dp s₀ + BitVec.ofNat 64 k) ^^^
        (keystream (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)).getD k 0
      else s₂.mem (dp s₀ + BitVec.ofNat 64 k) := data
  have hb : bytesAt s₂.mem (dp s₀) (512 * T + a) = bytesAt s.mem (dp s₀) (512 * T + a) := by
    simp only [bytesAt]
    refine List.map_congr_left fun k hk => ?_
    have := List.mem_range.mp hk
    rw [ha.mem, args_data hp _ (by
      rcases tail with ⟨rfl, -⟩ | ⟨h1, -, rfl, -⟩ | ⟨h1, rfl, -⟩
      · omega_arith
      · have := kOf_le (n := L s₀ - 512 * T) (by omega_arith); omega_arith
      · have := kOfK_le (n := L s₀ - 512 * T) h1; omega_arith)]
  have ha16 : (512 * T + a) % 16 = 0 ∧ 512 * T + a ≤ L s₀ := by
    rcases tail with ⟨rfl, -⟩ | ⟨h1, h2, rfl, -⟩ | ⟨h1, rfl, -⟩
    · omega_arith
    · have := kOf_le (n := L s₀ - 512 * T) (by omega_arith); omega_arith
    · have := kOfK_le (n := L s₀ - 512 * T) h1; unfold kOfK; split <;> omega_arith
  refine ⟨512 * T, 512 * T + a, rbx, rbp, fun r hr => ?_, (rd₃ : s₃.rd = s₂.rd).trans ha.rd,
    (wr₃ : s₃.wr = s₂.wr).trans ha.wr, by omega_arith, le, by omega_arith, ?_, fun k hk => ?_, ?_, ha16.1, by omega_arith, ha16.2,
    ?_, ?_, ?_, fun t h₁ h₂ h₃ k hk => ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (r12 : s₃.gpr .r12 = s₂.gpr .r12).trans (ha.keep _ (.inl rfl))
    · exact (r13 : s₃.gpr .r13 = s₂.gpr .r13).trans (ha.keep _ (.inr (.inl rfl)))
    · exact (r14 : s₃.gpr .r14 = s₂.gpr .r14).trans (ha.keep _ (.inr (.inr (.inl rfl))))
    · exact (r15 : s₃.gpr .r15 = cx s₀).trans h15.symm
    · exact (rsp : s₃.gpr .rsp = s₂.gpr .rsp).trans (ha.keep _ (.inr (.inr (.inr rfl))))
  · rw [off_eq, cnt', st₂, show 512 * T / 64 = 8 * T by omega_arith]
  · rw [data' k hk, st₂, ha.mem, args_data hp _ hk]
  · rw [ha.mem] at f₃'
    refine ((args_frame s₀ s.mem).sub fun r hr => ?_).trans (f₃'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have e : sub s₀ 64 512 = ⟨cx s₀ + BitVec.ofNat 64 64, 512⟩ := by rw [sub, off_eq]
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨sub s₀ 736 512, by simp, by
          rw [show kR (bfA (cx s₀)) = sub s₀ 736 512 by simp only [kR, kA, bfA, sub, off_eq, Offset.add_add]]
          exact fun _ h => h⟩
  · rw [off_eq, ← hb]; exact repr
  · rcases tail with ⟨a0, nc, nk⟩ | ⟨c1, c2, -, ks⟩ | ⟨c1, -, ks⟩
    · exact .inr (.inl ⟨hge, by omega_arith, fun ⟨_, h1, h2⟩ => nc ⟨h1, h2⟩, fun ⟨_, h1⟩ => by omega_arith⟩)
    · exact .inr (.inr (.inl ⟨⟨hge, c1, c2⟩, fun i hi => by
        rw [off_eq]
        exact (ks i hi).trans (congrArg (fun st => (keystream st (L s₀)).getD (512 * T + i) 0) st₂)⟩))
    · refine .inr (.inr (.inr ⟨⟨hge, c1⟩, fun i hi => ?_⟩))
      rw [show off (cx s₀) 736 = kA (bfA (cx s₀)) by simp only [kA, bfA, off_eq, Offset.add_add]]
      exact (ks i hi).trans (congrArg (fun st => (keystream st (L s₀)).getD (512 * T + i) 0) st₂)
  · have hEo : Eof (L s₀) = 512 * T := by simp only [Eof]; omega_arith
    rcases tail with ⟨rfl, nc, nk⟩ | ⟨c1, c2, rfl, -⟩ | ⟨c1, rfl, -⟩
    · rw [Aof_notail hge (by rw [hEo]; exact fun ⟨_, h1, h2⟩ => nc ⟨h1, h2⟩)
        (by rw [hEo]; exact fun ⟨_, h1⟩ => by omega_arith), hEo]
      rfl
    · rw [Aof_tail (by rw [hEo]; exact ⟨hge, c1, c2⟩), hEo]
    · rw [Aof_tailK (by rw [hEo]; exact ⟨hge, c1⟩), hEo]
  · have this : s₃.mem (cx s₀ + BitVec.ofNat 64 (736 + k)) = s₂.mem (cx s₀ + BitVec.ofNat 64 (736 + k)) :=
      x736 (by omega_arith) k (by omega_arith)
    rw [off_eq, this, ha.mem, ← off_eq]
    exact (t.frame (args_frame s₀ _) (by rdisj_all)) h₁ h₂ h₃ k hk

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

/-- What decrypting the rest, `[E, L)`, leaves (`restCall_ok`, `decRest_ok`). -/
def RestP (s₀ s : State) (E : Nat) (s' : State) : Prop :=
  s'.gpr .rsi = off (cx s₀) 128 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    Frame [sub s₀ 64 384, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s'.mem ∧
    (∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then s.mem (dp s₀ + BitVec.ofNat 64 k)
      else s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0) ∧
    s'.mxcsr = s.mxcsr

/-- The rest, `[E, L)`, decrypted by the implementation `v` of `vg_chacha20_xor`
from the counter the chunks left. -/
theorem restCall_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : Inv s₀ s) {E : Nat} (hE : E % 64 = 0) (hEL : E ≤ L s₀)
    (hrbx : s.gpr .rbx = dp s₀ + BitVec.ofNat 64 E) (hrbp : s.gpr .rbp = BitVec.ofNat 64 (L s₀ - E))
    (hst : stateAt s.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64)) :
    WP isa (.seq (.block restArgs) (.call v.callee.name v.callee.code)) s (RestP s₀ s E) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩ (dR s₀) := Offset.sub_base _ (by omega_arith)
  refine WP.seq (WP.mono_mx (by lit_decide) (restArgs_ok (s₀ := s₀) h.r15)
    fun s₁ ⟨rdi₁, rsi₁, rdx₁, rcx₁, g₁, rd₁, wr₁, m₁⟩ mx₁ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h.rsp]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩, ⟨off (cx s₀) 128, 320⟩]
      s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₁, h.wr]; exact hp.ctx_wr, 64, by simp [off_eq], by show 64 + 64 ≤ 1696; omega_arith⟩
    · exact ⟨dR s₀, by rw [wr₁, h.wr]; exact hp.d_wr, E, rfl, by show E + (L s₀ - E) ≤ L s₀; omega_arith⟩
    · exact ⟨ctxR s₀, by rw [wr₁, h.wr]; exact hp.ctx_wr, 128, by simp [off_eq], by show 128 + 320 ≤ 1696; omega_arith⟩
  refine WP.mono_mx (by simp only [Code.allInstrs, v.mxcsr]) (Q := fun s' => s'.gpr .rsi = off (cx s₀) 128 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      (∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then s.mem (dp s₀ + BitVec.ofNat 64 k)
        else s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0))
    ?_ fun s' h' mx' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1.mono (by frame_regions), h'.2.2.2.2.2,
      by rw [mx', mx₁]⟩
  refine xor_call v (S := off (cx s₀) 64) (D := dp s₀ + BitVec.ofNat 64 E) (B := off (cx s₀) 128)
    rdi₁ (by rw [rsi₁, hrbx]) (by rw [rdx₁, hrbp]) rcx₁ (by omega_arith)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ E (by omega_arith)) _) (by have := hp.wrap_d; omega_arith))
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
      have hin : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.c_d _ (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega) _ hc) hin
      · simp only [Region.Contains] at hc
        rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)] at hc
        split at hc <;> omega_arith
      · exact hp.c_d _ (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega) _ hc) hin
      · exact hp.stk_d _ hc hin
    · have x := xor_at ks' data' (j := k - E) (by omega_arith)
      rw [Offset.add_add, Nat.add_sub_cancel' (by omega_arith), m₁, hst, ks_from _ hE hk (by omega_arith)] at x
      rw [ite_eq_right hkE, x]

theorem RestP.congr {s₀ s s₁ s' : State} {E : Nat} (g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r)
    (m : s₁.mem = s.mem) (rd : s₁.rd = s.rd) (wr : s₁.wr = s.wr) (mx : s₁.mxcsr = s.mxcsr)
    (h : RestP s₀ s₁ E s') : RestP s₀ s E s' := by
  obtain ⟨a, b, c, d, f, dt, x⟩ := h
  refine ⟨a, fun r hr => (b r hr).trans (g r (calleeSaved_ne hr).1), c.trans rd, d.trans wr, m ▸ f,
    fun k hk => ?_, x.trans mx⟩
  rw [dt k hk, m]

theorem RestP.pad {s₀ s t u : State} {E : Nat} (h : RestP s₀ s E t) (p : PadPost .rax t u) : RestP s₀ s E u := by
  obtain ⟨a, b, c, d, f, dt, x⟩ := h
  exact ⟨by rw [p.gpr _ (by decide), a], fun r hr => by rw [p.gpr r (calleeSaved_ne hr).1, b r hr],
    by rw [p.rd, c], by rw [p.wr, d], by rw [p.mem]; exact f, fun k hk => by rw [p.mem, dt k hk], by rw [p.mx, x]⟩

theorem Inv.congr {s₀ s s₁ : State} (h : Inv s₀ s) (g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r)
    (m : s₁.mem = s.mem) (rd : s₁.rd = s.rd) (wr : s₁.wr = s.wr) : Inv s₀ s₁ :=
  ⟨by rw [g _ (by decide), h.r15], by rw [g _ (by decide), h.r14], by rw [g _ (by decide), h.r13],
    by rw [g _ (by decide), h.r12], by rw [g _ (by decide), h.rsp], by rw [rd, h.rd], by rw [wr, h.wr],
    by rw [m]; exact h.saved, by rw [m]; exact h.frame⟩

/-- `xorTail`'s pointers: `r10` at the rest after the whole chunks, `rsi` at
its keystream (`ctx + o`), `rdx` the rest's length. -/
theorem xtArgs_ok {s₀ s : State} (h : Inv s₀ s) {o : Nat} (ho : o < 1696) :
    WP isa (.block (([.mov .rdx (.reg .r13), .alu .and .rdx (.imm 511), .mov .r10 (.reg .r14),
      .alu .add .r10 (.reg .r13), .alu .sub .r10 (.reg .rdx)] : List Instr) ++ ptr .rsi .r15 o)) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (L s₀ % 512) ∧ t.gpr .r10 = dp s₀ + BitVec.ofNat 64 (L s₀ - L s₀ % 512) ∧
      t.gpr .rsi = off (cx s₀) o ∧ (∀ r, r ≠ .rdx → r ≠ .r10 → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem = s.mem := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have x511 : BitVec.signExtend 64 (511 : BitVec 32) = BitVec.ofNat 64 511 := by decide
  have ha : BitVec.ofNat 64 (L s₀) &&& BitVec.ofNat 64 511 = BitVec.ofNat 64 (L s₀ % 512) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.ofNat 64 511).toNat = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      toNat_ofNat_lt hL9, toNat_ofNat_lt (by omega_arith)]
  have hs : dp s₀ + BitVec.ofNat 64 (L s₀) - BitVec.ofNat 64 (L s₀ % 512) =
      dp s₀ + BitVec.ofNat 64 (L s₀ - L s₀ % 512) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (Nat.mod_le _ _)]
  refine WP.block_append (WP.mono (Q := fun (t : State) => t.gpr .rdx = BitVec.ofNat 64 (L s₀ % 512) ∧
      t.gpr .r10 = dp s₀ + BitVec.ofNat 64 (L s₀ - L s₀ % 512) ∧
      (∀ r, r ≠ .rdx → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem = s.mem) ?_
    fun s₁ ⟨d₁, a₁, g₁, rd₁, wr₁, m₁⟩ => WP.mono (ptr_ok .rsi .r15 (k := o) (by lit_omega) s₁)
      fun s₂ ⟨e₂, g₂, rd₂, wr₂, m₂⟩ => ⟨by rw [g₂ _ (by decide), d₁], by rw [g₂ _ (by decide), a₁],
        by rw [e₂, g₁ _ (by decide) (by decide), h.r15], fun r x y z => by rw [g₂ r z, g₁ r x y],
        by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [m₂, m₁]⟩)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ↓reduceIte, x511, h.r13, h.r14, hL, ha, hs]
  exact ⟨trivial, trivial, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial⟩

/-- The rest decrypted from its keystream at `ctx + o`: the one `tailO` left
in `buf` (`o` 128), or `twoKs` (736). -/
theorem xorTail_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : Inv s₀ s) {E : Nat} (hEd : E = 512 * (L s₀ / 512)) {o : Nat} (ho : o = 128 ∨ o = 736)
    (hc : o + (L s₀ - E) ≤ 1696)
    (hks : ∀ i < L s₀ - E, s.mem (off (cx s₀) o + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (E + i) 0) :
    WP isa (xorTail v.callee.wide o) s (RestP s₀ s E) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hm : L s₀ % 512 = L s₀ - E := by rw [hEd]; have := Nat.mod_add_div (L s₀) 512; omega_arith
  have hEL : E ≤ L s₀ := by rw [hEd]; exact Nat.mul_div_le _ _
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩ (dR s₀) := Offset.sub_base _ (by omega_arith)
  refine WP.mono_mx (by rcases wide_of v with h | h | h <;> rcases ho with rfl | rfl <;> (rw [h]; lit_decide))
    (Q := fun s' => s'.gpr .rsi = off (cx s₀) 128 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      (∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then s.mem (dp s₀ + BitVec.ofNat 64 k)
        else s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0))
    ?_ fun s' h' mx' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1.mono (by frame_regions), h'.2.2.2.2.2, mx'⟩
  unfold xorTail
  refine WP.seq (WP.mono (xtArgs_ok h (o := o) (by omega_arith)) fun s₁ ⟨d₁, a₁, rsi₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  rw [hm] at d₁ a₁
  rw [Nat.sub_sub_self hEL] at a₁
  refine WP.seq (WP.mono (ChaCha20.X86_64.XorBufX.xorBufX_ok (wide_of v) (d := .r10) (by decide) a₁ rsi₁ d₁ (by omega_arith)
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := o) (n := L s₀ - E) (by omega_arith))).sub_left dsub)
    ⟨dR s₀, by rw [wr₁, h.wr]; exact hp.d_wr, Offset.contains_base _ (show E + (L s₀ - E) ≤ L s₀ by omega_arith) (by omega_arith)⟩
    ⟨ctxR s₀, by rw [rd₁, wr₁, h.rd, h.wr]; simp [hp.ctx_wr], by
      rw [off_eq]; exact Offset.contains_base _ (show o + (L s₀ - E) ≤ 1696 by omega_arith) (by lit_omega)⟩)
    fun s₂ X => ?_)
  refine WP.mono (ptr_ok .rsi .r15 (k := 128) (by lit_omega) s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  refine ⟨by rw [e₃, X.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide), h.r15], fun r hr => ?_, by rw [rd₃, X.rd, rd₁],
    by rw [wr₃, X.wr, wr₁], ?_, fun k hk => ?_⟩
  · have hne : r ≠ .rax ∧ r ≠ .r8 ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₃ r hne.2.2.2.2.1, X.keep r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.1,
      g₁ r hne.2.2.2.1 hne.2.2.2.2.2.2 hne.2.2.2.2.1]
  · rw [m₃, ← m₁]
    exact X.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, dsub⟩
  · by_cases hkE : k < E
    · rw [ite_eq_left hkE, m₃, ← m₁]
      refine X.frame _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hc
      rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)] at hc
      split at hc <;> omega_arith
    · have x := X.data (k - E) (by omega_arith)
      rw [Offset.add_add, Nat.add_sub_cancel' (by omega_arith), m₁, hks _ (by omega_arith), Nat.add_sub_cancel' (by omega_arith)] at x
      rw [ite_eq_right hkE, m₃, x]

theorem mov576_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.imm 576)]) s fun t => t.gpr .rdx = BitVec.ofNat 64 576 ∧
      (∀ q, q ≠ .rdx → t.gpr q = s.gpr q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨BitVec.eq_of_toNat_eq (by simp only [ite_true, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; rfl), fun q hq => by simp [hq], trivial, trivial, trivial, rfl⟩

/-- The rest, `[E, L)`, decrypted from its keystream at `ctx + 736` (that
`wholeO`, `tail3O` or `tailKO` left), which is then wiped. -/
theorem decK_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : Inv s₀ s) {E : Nat} (hEd : E = 512 * (L s₀ / 512)) (hc : 736 + (L s₀ - E) ≤ 1696)
    (hks : ∀ i < L s₀ - E, s.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (E + i) 0) :
    WP isa (.seq (xorTail v.callee.wide 736) (.seq (.block [.mov32 .rdx (.imm 576)]) (zeroKs v.callee.wide))) s
      (RestP s₀ s E) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (xorTail_ok v hp h hEd (o := 736) (.inr rfl) hc hks) fun s₁ R₁ => ?_)
  obtain ⟨rsi₁, cs₁, rd₁, wr₁, f₁, d₁, mx₁⟩ := R₁
  refine WP.seq (WP.mono (mov576_ok s₁) fun s₂ ⟨d₂, g₂, rd₂, wr₂, m₂, mx₂⟩ => ?_)
  have r15₂ : s₂.gpr .r15 = cx s₀ := by rw [g₂ _ (by decide), cs₁ _ (by decide), h.r15]
  refine WP.mono_mx (by rcases wide_of v with h | h | h <;> (rw [h]; lit_decide))
    (zeroKs_ok (wide_of v) hp (n := 576) (by decide) (by decide) d₂ r15₂ (by rw [wr₂, wr₁, h.wr]))
    fun s₃ ⟨g₃, rd₃, wr₃, f₃, _⟩ mx₃ => ?_
  have f₂₃ : Frame [sub s₀ 672 1024] s₁.mem s₃.mem := by rw [← m₂]; exact f₃
  have nd : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s₁.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => f₂₃ _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.c_d _ (sub_ctx s₀ (k := 672) (n := 1024) (by lit_omega) _ hc)
        (Offset.contains_base _ (show k + 1 ≤ L s₀ by omega_arith) (by omega_arith))
  refine ⟨by rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), rsi₁], fun r hr => ?_, by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], f₁.trans (f₂₃.mono (by frame_regions)), fun k hk => by rw [nd k hk, d₁ k hk],
    by rw [mx₃, mx₂, mx₁]⟩
  have hne : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [g₃ r hne.1 hne.2.1, g₂ r hne.2.2, cs₁ r hr]

/-- Below 512 bytes: the data decrypted from the keystream `wholeO` left at
`ctx + 736`, which is then wiped. -/
theorem decWhole_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : Inv s₀ s) (hlt : L s₀ < 512)
    (hks : ∀ i < L s₀, s.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0) :
    WP isa (.seq (xorTail v.callee.wide 736) (.seq (.block [.mov32 .rdx (.imm 576)]) (zeroKs v.callee.wide))) s
      (RestP s₀ s 0) :=
  decK_ok v hp h (by omega_arith) (by omega_arith) fun i hi => by rw [Nat.zero_add]; exact hks i (by omega_arith)

/-- The keystream `tail3O` or `tailKO` left at `ctx + 736` wiped, after the
rest was decrypted from it, and the padding after it. -/
theorem wipeK_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s t : State}
    (h : Inv s₀ s) {E : Nat} (hr : RestP s₀ s E t) :
    WP isa (.seq (.block [.mov32 .rdx (.imm 576)]) (.seq (zeroKs v.callee.wide) (.block (padIns .rax 3)))) t
      (RestP s₀ s E) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain ⟨rsi₁, cs₁, rd₁, wr₁, f₁, d₁, mx₁⟩ := hr
  refine WP.seq (WP.mono (mov576_ok t) fun s₂ ⟨d₂, g₂, rd₂, wr₂, m₂, mx₂⟩ => ?_)
  have r15₂ : s₂.gpr .r15 = cx s₀ := by rw [g₂ _ (by decide), cs₁ _ (by decide), h.r15]
  refine WP.seq (WP.mono_mx (by rcases wide_of v with h | h | h <;> (rw [h]; lit_decide))
    (zeroKs_ok (wide_of v) hp (n := 576) (by decide) (by decide) d₂ r15₂ (by rw [wr₂, wr₁, h.wr]))
    fun s₃ ⟨g₃, rd₃, wr₃, f₃, _⟩ mx₃ => WP.mono (padIns_ok .rax (by decide) s₃) fun u p => RestP.pad ?_ p)
  have f₂₃ : Frame [sub s₀ 672 1024] t.mem s₃.mem := by rw [← m₂]; exact f₃
  have nd : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = t.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => f₂₃ _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.c_d _ (sub_ctx s₀ (k := 672) (n := 1024) (by lit_omega) _ hc)
        (Offset.contains_base _ (show k + 1 ≤ L s₀ by omega_arith) (by omega_arith))
  refine ⟨by rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), rsi₁], fun r hr => ?_, by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], f₁.trans (f₂₃.mono (by frame_regions)), fun k hk => by rw [nd k hk, d₁ k hk],
    by rw [mx₃, mx₂, mx₁]⟩
  have hne : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [g₃ r hne.1 hne.2.1, g₂ r hne.2.2, cs₁ r hr]

/-- `decRest`: below 512 bytes the data decrypted from the keystream `wholeO`
left at `ctx + 736`, which is then wiped; otherwise the rest decrypted from
`buf` if `tailO` computed its keystream there, from `ctx + 736` if `twoKs`
did, otherwise by the implementation `v` of `vg_chacha20_xor`. -/
theorem decRest_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : Inv s₀ s) {E : Nat} (hE : E % 64 = 0) (hEd : E = 512 * (L s₀ / 512)) (hEL : E ≤ L s₀)
    (hst : stateAt s.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64))
    (ht : (L s₀ < 512 ∧ ∀ i < L s₀, s.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
        (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0) ∨
      (512 ≤ L s₀ ∧ ¬ TailC (L s₀) E ∧ ¬ TailK (L s₀) E ∧ s.gpr .rbx = dp s₀ + BitVec.ofNat 64 E ∧
        s.gpr .rbp = BitVec.ofNat 64 (L s₀ - E)) ∨
      (TailC (L s₀) E ∧ ∀ i < L s₀ - E, s.mem (off (cx s₀) 128 + BitVec.ofNat 64 i) =
        (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (E + i) 0) ∨
      (TailK (L s₀) E ∧ ∀ i < L s₀ - E, s.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
        (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (E + i) 0))
    (hx : TailKs s₀ s.mem) :
    WP isa (decRest v.callee) s (RestP s₀ s E) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have r13L : (s.gpr .r13).toNat = L s₀ := by rw [h.r13]
  have hm : L s₀ % 512 = L s₀ - E := by rw [hEd]; have := Nat.mod_add_div (L s₀) 512; omega_arith
  -- The call, with the rest's own pointers, from a state with `s`'s.
  have call : ∀ s₁ : State, (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) → s₁.mem = s.mem → s₁.rd = s.rd →
      s₁.wr = s.wr → s₁.mxcsr = s.mxcsr → 512 ≤ L s₀ → ¬ TailC (L s₀) E → ¬ TailK (L s₀) E →
      WP isa (.seq (.block restArgs) (.call v.callee.name v.callee.code)) s₁ (RestP s₀ s E) := by
    intro s₁ g₁ m₁ rd₁ wr₁ mx₁ hge nt nk
    have ⟨bx, bp⟩ : s.gpr .rbx = dp s₀ + BitVec.ofNat 64 E ∧ s.gpr .rbp = BitVec.ofNat 64 (L s₀ - E) := by
      rcases ht with ⟨hl, -⟩ | ⟨-, -, -, x, y⟩ | ⟨t, -⟩ | ⟨t, -⟩
      · exact absurd hl (by omega_arith)
      · exact ⟨x, y⟩
      · exact absurd t nt
      · exact absurd t nk
    exact WP.mono (restCall_ok v hp (Inv.congr h g₁ m₁ rd₁ wr₁) hE hEL (by rw [g₁ _ (by decide), bx])
      (by rw [g₁ _ (by decide), bp]) (by rw [m₁, hst])) fun s' h' => RestP.congr g₁ m₁ rd₁ wr₁ mx₁ h'
  unfold decRest
  refine WP.seq (WP.mono (cmp13_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, mx₁⟩ => ?_)
  have g₁' : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r _ => congrFun g₁ r
  refine WP.ite _ c₁ (fun hc => ?_) (fun hc => ?_)
  · simp only [decide_eq_true_eq, r13L] at hc
    have hE0 : E = 0 := by rw [hEd]; omega_arith
    subst hE0
    have ks : ∀ i < L s₀, s₁.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
        (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := by
      rw [m₁]
      rcases ht with ⟨-, ks⟩ | ⟨hge, -⟩ | ⟨t, -⟩ | ⟨t, -⟩
      · exact ks
      · exact absurd hc (by omega_arith)
      · exact absurd t.1 (by omega_arith)
      · exact absurd t.1 (by omega_arith)
    exact WP.mono (decWhole_ok v hp (Inv.congr h g₁' m₁ rd₁ wr₁) hc ks)
      fun s' h' => RestP.congr g₁' m₁ rd₁ wr₁ mx₁ h'
  · simp only [decide_eq_false_iff_not, r13L] at hc
    have hge : 512 ≤ L s₀ := by omega_arith
    refine WP.seq (WP.mono (Q := RestP s₀ s E) ?_ fun t h' =>
      WP.mono (padIns_ok .rax (by decide) t) fun u p => h'.pad p)
    refine WP.seq (WP.mono (restTest_ok (lo := 193) (n := 64) (by decide) (by decide) (by decide) (by decide) s₁)
      fun s₂ ⟨c₂, g₂, m₂, rd₂, wr₂, mx₂⟩ => ?_)
    rw [g₁, r13L, hm] at c₂
    have g₂' : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂ r hr, g₁]
    have m₂' : s₂.mem = s.mem := m₂.trans m₁
    have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
    have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
    have mx₂' : s₂.mxcsr = s.mxcsr := mx₂.trans mx₁
    refine WP.ite _ c₂ (fun hc₂ => ?_) (fun hc₂ => ?_)
    · simp only [decide_eq_true_eq] at hc₂
      rcases ht with ⟨hl, -⟩ | ⟨-, nt, -⟩ | ⟨-, ks⟩ | ⟨t, -⟩
      · exact absurd hl (by omega_arith)
      · exact absurd ⟨by omega_arith, by omega_arith, by omega_arith⟩ nt
      · exact WP.mono (xorTail_ok v hp (Inv.congr h g₂' m₂' rd₂' wr₂') hEd (o := 128) (.inl rfl) (by omega_arith)
          (by rw [m₂']; exact ks)) fun s' h' => RestP.congr g₂' m₂' rd₂' wr₂' mx₂' h'
      · exact absurd t.2 (by omega_arith)
    · simp only [decide_eq_false_iff_not] at hc₂
      have nt : ¬ TailC (L s₀) E := fun t => hc₂ ⟨t.2.1, by have := t.2.2; omega_arith⟩
      refine WP.seq (WP.mono (restTest_ok (lo := 1) (n := 511) (by decide) (by decide) (by decide) (by decide) s₂)
        fun s₃ ⟨c₃, g₃, m₃, rd₃, wr₃, mx₃⟩ => ?_)
      rw [g₂ _ (by decide), g₁, r13L, hm] at c₃
      have g₃' : ∀ r, r ≠ .rax → s₃.gpr r = s.gpr r := fun r hr => by rw [g₃ r hr, g₂' r hr]
      have m₃' : s₃.mem = s.mem := m₃.trans m₂'
      have rd₃' : s₃.rd = s.rd := rd₃.trans rd₂'
      have wr₃' : s₃.wr = s.wr := wr₃.trans wr₂'
      have mx₃' : s₃.mxcsr = s.mxcsr := mx₃.trans mx₂'
      refine WP.ite _ c₃ (fun hc₃ => ?_) (fun hc₃ => ?_)
      · simp only [decide_eq_true_eq] at hc₃
        -- The keystream at `ctx + 736`: the prologue's below 193 bytes, the tail's from 257.
        have ks : ∀ i < L s₀ - E, s₃.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
            (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (E + i) 0 := by
          by_cases hsm : L s₀ - E ≤ 192
          · intro i hi
            rw [m₃', off_eq, Offset.add_add, ← off_eq, hx (by omega_arith) (by omega_arith) (by omega_arith) i (by omega_arith), hEd]
          · rcases ht with ⟨hl, -⟩ | ⟨-, -, nk, -⟩ | ⟨t, -⟩ | ⟨-, ks⟩
            · exact absurd hl (by omega_arith)
            · exact absurd ⟨hge, by omega_arith⟩ nk
            · exact absurd t nt
            · rw [m₃']; exact ks
        refine WP.seq (WP.mono (xorTail_ok v hp (Inv.congr h g₃' m₃' rd₃' wr₃') hEd (o := 736) (.inr rfl)
          (by omega_arith) ks) fun s₄ h₄ => ?_)
        have h₄' := RestP.congr g₃' m₃' rd₃' wr₃' mx₃' h₄
        refine WP.seq (WP.mono (restTest_ok (lo := 257) (n := 255) (by decide) (by decide) (by decide) (by decide)
          s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅, mx₅⟩ => ?_)
        have h₅ : RestP s₀ s E s₅ := h₄'.pad ⟨g₅, m₅, rd₅, wr₅, mx₅⟩
        exact WP.ite _ c₅ (fun _ => wipeK_ok v hp h h₅) (fun _ => WP.block_nil h₅)
      · simp only [decide_eq_false_iff_not] at hc₃
        exact call s₃ g₃' m₃' rd₃' wr₃' mx₃' hge nt fun t => hc₃ ⟨by unfold TailK at t; omega_arith, by omega_arith⟩

/-- The keystream at `ctx + 736` kept through a frame outside it. -/
theorem ks736_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sub s₀ 736 512).Disjoint r) {n : Nat} (hn : n ≤ 512) {f : Nat → Byte}
    (h : ∀ i < n, m (off (cx s₀) 736 + BitVec.ofNat 64 i) = f i) :
    ∀ i < n, m' (off (cx s₀) 736 + BitVec.ofNat 64 i) = f i := by
  intro i hi
  rw [← h i hi]
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (show i + 1 ≤ 512 by omega_arith) (by omega_arith)) hc

/-- The keystream in `buf` kept through a frame outside it. -/
theorem buf_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sub s₀ 128 256).Disjoint r) {n : Nat} (hn : n ≤ 256) {f : Nat → Byte}
    (h : ∀ i < n, m (off (cx s₀) 128 + BitVec.ofNat 64 i) = f i) :
    ∀ i < n, m' (off (cx s₀) 128 + BitVec.ofNat 64 i) = f i := by
  intro i hi
  rw [← h i hi]
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (show i + 1 ≤ 256 by omega_arith) (by omega_arith)) hc

/-- After `cryptO`'s branch, before the keystream is wiped: what `open`'s
`macPadLengths` and `crypt`'s branch leave. -/
structure CryptedO (s₀ s : State) (key msg : List Byte) (s' : State) : Prop where
  rsi : s'.gpr .rsi = off (cx s₀) 128
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .rsp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sub s₀ 64 528, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s'.mem
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
  · rw [g₃, cs₂ _ (by decide), h.r13, hL]
  · rw [g₃, cs₂ _ (by decide), h.r14]
  · rw [g₃, cs₂ r (by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
  · rw [g₃, cs₂ _ (by decide)]

/-- More than `fold` bytes: the whole chunks decrypted and absorbed by
`bulkO` (none below 512 bytes), the rest and the lengths block absorbed, and
the rest decrypted by the implementation `v` of `vg_chacha20_xor`. -/
theorem bigO_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (h448 : 448 ≤ L s₀) (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) (hx : TailKs s₀ s.mem) :
    WP isa (.seq (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
      (.seq (.ite .b (wholeO v.callee.vl) (bulkO v.callee.vl))
      (.seq (.block (padIns .rax 18))
      (.seq (macPadLengths v.poly .rbx .rbp) (decRest v.callee))))) s (CryptedO s₀ s key msg) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono_mx (by lit_decide) (argsCmpO_ok hp h) fun s₂ ⟨ha, h15, cf₂⟩ mx₂ => ?_)
  -- The whole chunks, if any.
  refine WP.seq (WP.mono_mx (by generalize v.callee.vl = vl; cases vl <;> lit_decide)
    (Q := fun (s₃ : State) => ∃ E A, MidO s₀ s key msg E A s₃) ?_ fun s₃₀ ⟨E, A, hm₀⟩ mx₃₀ => ?_)
  · refine WP.ite (decide (L s₀ < 512)) (by simp [eval, cf₂]) (fun hc => ?_) (fun hc' => ?_)
    · exact WP.mono (wholeO_midO v.callee.vl hp h.wr ha h.r15 h448 (by simpa using hc) hst hrep)
        fun s₄ hm₄ => ⟨0, 448, hm₄⟩
    · simp only [decide_eq_false_iff_not] at hc'
      exact bulk_midO v.callee.vl hp h.wr ha h.r15 (by omega_arith) hst hrep
  refine WP.seq (WP.mono (padIns_ok .rax (by decide) s₃₀) fun s₃ p₃ => ?_)
  have hm := hm₀.pad p₃
  have mx₃ : s₃.mxcsr = s₂.mxcsr := p₃.mx.trans mx₃₀
  have hEL := hm.EL
  have i₃ : Inv s₀ s₃ := Inv.step' h hm.keep hm.rd hm.wr hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  -- The rest absorbed, as it was on entry, with the lengths block.
  refine WP.seq (WP.mono (macPadLengths_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩
    (srcRest hp hm.AL) i₃ hm.rbx hm.rbp) fun s₄ ⟨i₄, cs₄, f₄, mx₄, r₄⟩ => ?_)
  have st₄ : stateAt s₄.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64) := by
    rw [stateAt_frame f₄ (by rdisj_all), hm.st]
  -- The rest decrypted.
  refine WP.mono (decRest_ok v hp i₄ hm.E64 hm.Ediv hEL st₄ ?_ ((hm.x736 hx).frame f₄ (by rdisj_all)))
    fun s₅ ⟨rsi₅, cs₅, rd₅, wr₅, f₅, d₅, mx₅⟩ => ?_
  · rcases hm.tail with ⟨hl, ks⟩ | ⟨hge, hA, nt, nk⟩ | ⟨t, ks⟩ | ⟨t, ks⟩
    · exact .inl ⟨hl, ks736_frame f₄ (by rdisj_all) (by omega_arith) ks⟩
    · exact .inr (.inl ⟨hge, nt, nk, by rw [cs₄ _ (by decide), hm.rbx, hA],
        by rw [cs₄ _ (by decide), hm.rbp, hA]⟩)
    · exact .inr (.inr (.inl ⟨t, buf_frame f₄ (by rdisj_all) (by unfold TailC at t; omega_arith) ks⟩))
    · exact .inr (.inr (.inr ⟨t, ks736_frame f₄ (by rdisj_all) (by have := hm.Ediv; omega_arith) ks⟩))
  have dd : ∀ k < L s₀, ∀ r ∈ macR s₀, ¬ r.Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk r hr hc
    have hin : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.c_d _ (sub_ctx s₀ (k := 448) (n := 144) (by lit_omega) _ hc) hin
    · exact hp.stk_d _ hc hin
  have e₄ : ∀ k < L s₀, s₄.mem (dp s₀ + BitVec.ofNat 64 k) = s₃.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => f₄ _ (dd k hk)
  have rest : bytesAt s₃.mem (dp s₀ + BitVec.ofNat 64 A) (L s₀ - A) =
      bytesAt s.mem (dp s₀ + BitVec.ofNat 64 A) (L s₀ - A) := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have := hm.EA
    have := hm.AL
    rw [Offset.add_add, hm.data _ (by omega_arith), ite_eq_right (by omega_arith)]
  have lens : bytesAt s₃.mem (off (cx s₀) 592) 16 = bytesAt s.mem (off (cx s₀) 592) 16 :=
    bytesAt_frame hm.frame (by rdisj_all) (by lit_omega)
  refine ⟨rsi₅, fun r hr => ?_, by rw [rd₅, i₄.rd, h.rd], by rw [wr₅, i₄.wr, h.wr], ?_, ?_, ?_, ?_⟩
  · have hc : r ∈ calleeSaved := by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved]
    rw [cs₅ r hc, cs₄ r hc, hm.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)]
  · refine ((hm.frame.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)).trans (f₅.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨sub s₀ 672 1024, by simp, sub_sub s₀ (by decide) (by decide) (by decide)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
    · simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨sub s₀ 672 1024, by simp, fun _ h => h⟩
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
    rwa [List.append_assoc msg, split_pad _ _ hm.A16 hm.AL] at R₅
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
  refine WP.mono_mx (by rcases wide_of v with h | h | h <;> (rw [h]; lit_decide)) (cryptSmall_ok v.fold_le (wide_of v) hp i₄ hle (ks_frame f₄ (by rdisj_all) hM hks))
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

theorem wipeL_mx (v : Proof.ChaCha20.X86_64.XorImpl) :
    (wipeL v.callee.fold 192).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases v.fold_poly with ⟨hf, -, -⟩ | ⟨hf, -, -⟩ | ⟨hf, -, -⟩ <;> (rw [hf]; lit_decide)

theorem foldM_mx (v : Proof.ChaCha20.X86_64.XorImpl) :
    (foldM v.callee.fold v.callee.pass).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases v.fold_poly with ⟨hf, hpass, -⟩ | ⟨hf, hpass, -⟩ | ⟨hf, hpass, -⟩ <;>
    (rw [hf, hpass]; lit_decide)

/-- `cryptO`: as `open`'s `macPadLengths` and then `crypt`, by any
implementation `v` of `vg_chacha20_xor` and its `vg_poly1305_blocks`. -/
theorem cryptO_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hf448 : v.callee.fold = 448) {s₀ : State} (hp : APre e s₀)
    {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mOf v.callee.fold v.callee.pass (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) (hx : TailKs s₀ s.mem) :
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
      exact smallO_ok v hp h₁ (by omega_arith) (by rw [m₁]; exact hks) (by rw [m₁]; exact hrep)
    · simp only [decide_eq_false_iff_not] at hc
      exact bigO_ok v hp h₁ (by omega_arith) (by rw [m₁]; exact hst) (by rw [m₁]; exact hrep) (by rw [m₁]; exact hx)
  -- The keystream wiped, as in `crypt_ok`.
  refine WP.seq (WP.mono_mx (by lit_decide) (anchor_ok .rsi (k := 128) (by lit_omega) s₂)
    fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_)
  have cs₃ : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp → s₃.gpr r = s.gpr r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [g₃ _ (by decide), c₂.keep _ (.inl rfl), g₁]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inl rfl)), g₁]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inr (.inl rfl))), g₁]
    · rw [e3, c₂.rsi, off_sub, h.r15]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inr (.inr rfl))), g₁]
  have fc : Frame [sub s₀ 64 528, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s₃.mem := by
    rw [m₃, ← m₁]; exact c₂.frame
  have i₃ : Inv s₀ s₃ := Inv.step' h cs₃ (by rw [rd₃, c₂.rd, rd₁]) (by rw [wr₃, c₂.wr, wr₁]) fc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact stk_work s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
      · exact (hp.stk_sub (by lit_omega)).symm)
  refine WP.seq (WP.mono_mx (wipeL_mx v)
    (wipeL_ok (fold := v.callee.fold) (extra := 192) (by lit_omega) (by decide) i₃.r13) fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ mx₄ => ?_)
  refine WP.seq (WP.mono_mx (by lit_decide) (add64_ok (n := wOf v.callee.fold 192 (L s₀)) d₄)
    fun s₅ ⟨d₅, g₅, rd₅, wr₅, m₅⟩ mx₅ => ?_)
  refine WP.mono_mx (by rcases wide_of v with h | h | h <;> (rw [h]; lit_decide)) (zeroKs_ok (wide_of v) hp (n := 64 + wOf v.callee.fold 192 (L s₀)) (by omega_arith)
    (by simp only [wOf]; split <;> lit_omega) d₅ (by rw [g₅ _ (by decide), g₄ _ (by decide), i₃.r15]) (by rw [wr₅, wr₄, i₃.wr]))
    fun s₆ ⟨g₆, rd₆, wr₆, f₆, _⟩ mx₆ => ?_
  have g36 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 => by
    rw [g₆ r h1 h2, g₅ r h3, g₄ r h3]
  have f₅₆ : Frame [sub s₀ 672 1024] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
  have hbd : bytesAt s₆.mem (dp s₀) (L s₀) = bytesAt s₃.mem (dp s₀) (L s₀) :=
    bytesAt_frame f₅₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (by omega_arith)
  refine ⟨Inv.step' i₃ (fun r hr => g36 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
      (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) f₅₆
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    ?_, ?_, ?_, ?_⟩
  · refine (fc.sub fun r hr => ?_).trans (f₅₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 672 1024, by simp, fun _ h => h⟩
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
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

theorem openStitched_correct (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {s₀ : State}
    (hp : APre false s₀) :
    WP isa (openStitched v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  have hX : XPass v.callee.pass := (avx2_of v hv).2.1
  refine WP.seq (WP.mono_mx (by lit_decide) (entry_ok hp) fun s₀' e₀ mx₀ => ?_)
  subst e₀
  refine WP.seq (WP.mono_mx (prologueX_mx v hv hX) (prologueX_ok v hv hX hp) fun s₁ ⟨h₁, X₁⟩ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono_mx (by lit_decide) (lengths_ok hp i₂ (by rw [cs₂ _ (by decide),
    h₁.rbp])) fun s₃ ⟨i₃, _, f₃, len₃⟩ mx₃ => ?_)
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by rw [bytesAt_frame f₃ (by rdisj_all) hL', D₂]
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  have hM := Nat.le_trans (mOf_le v.callee.fold v.callee.pass (L s₀)) v.fold_le
  have ks₃ := ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)
  have R₃ := Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  have X₃ := (X₁.frame f₂ (by rdisj_all)).frame f₃ (by rdisj_all)
  refine WP.seq (WP.mono (cryptO_ok v (avx2_of v hv).1 hp i₃ st₃ ks₃ R₃ X₃) fun s₆ ⟨i₆, f₆, pt₆, R₆, mx₆⟩ => ?_)
  refine WP.seq (WP.mono_mx (by lit_decide) (finalizeTo_ok hp i₆ (out := 48) (.inl (by omega_using [])))
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, rcx₇, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.block_append (WP.mono_mx (by lit_decide) (compare_ok hp rcx₇
    (by rw [cs₇ _ (by decide), i₆.r12]) (by rw [rd₇, i₆.rd])
    (by rw [wr₇, i₆.wr])) fun s₈ ⟨rax₈, g₈, m₈, rd₈, wr₈⟩ mx₈ => ?_)
  refine WP.mono_mx (by lit_decide) (restore_ok hp (by rw [g₈ _ (by decide) (by decide), rdi₇])
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
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
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

theorem chunkO_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (chunkO false) h).isSome = true := by
  taint_decide_sum [sroundsFF]

theorem chunkOVL_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (chunkO true) h).isSome = true := by
  taint_decide_sum [sroundsTF]

theorem leaveO_taint : ∃ h, (taintS.check (τR [.rcx, .rsi, .rsp]) (.block leaveO) h).isSome = true := by
  taint_decide_sum []

theorem restPreO_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp])
    (.block (padIns .rdx 5 ++ ([.mov .rdx (.mem (Impl.ChaCha20.X86_64.at_ .rcx lenOff)), .alu .sub .rdx (.imm 193),
      .alu .cmp .rdx (.imm 319)] : List Instr))) h).isSome = true := by
  taint_decide_sum []

theorem tailO12_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (tailO true 12) h).isSome = true := by
  taint_decide_sum []

theorem tail3O16_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (tail3O 16) h).isSome = true := by
  taint_decide_sum []

theorem tailKO24_taint (vl : Bool) : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp])
    (.seq (tailKO vl 24) (.block (padIns .rax (if vl then 35 else 19)))) h).isSome = true := by
  cases vl <;> taint_decide_sum []

theorem cmp192_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp])
    (.block [.alu .cmp .rdx (.imm 192)]) h).isSome = true := by
  taint_decide_sum []

theorem cmp64_taint : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp])
    (.block [.alu .cmp .rdx (.imm 64)]) h).isSome = true := by
  taint_decide_sum []

section
variable {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) (sp : Addr) (vl : Bool)
include hl hge

/-- The chunks, while at least 512 bytes remain. -/
theorem loopO_rel :
    RelCT isa (fun s₁ s₂ => CO c dp L sp 0 s₁ ∧ CO c dp L sp 0 s₂) (.loop (chunkO vl) .ae)
      fun s₁ s₂ => ∃ T, CO c dp L sp T s₁ ∧ CO c dp L sp T s₂ ∧ L - 512 * T < 512 := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (chunkO vl) h).isSome = true := by
    cases vl
    · exact chunkO_taint
    · exact chunkOVL_taint
  let I : Nat → State → State → Prop := fun n s₁ s₂ =>
    ∃ t, n = L - 512 * t ∧ 512 ≤ L - 512 * t ∧ CO c dp L sp t s₁ ∧ CO c dp L sp t s₂
  have body : ∀ t, RelCT isa (fun s₁ s₂ => 512 ≤ L - 512 * t ∧ CO c dp L sp t s₁ ∧ CO c dp L sp t s₂) (chunkO vl)
      fun s₁ s₂ => (CO c dp L sp (t + 1) s₁ ∧ s₁.cf = some (decide (L - 512 * (t + 1) < 512))) ∧
        (CO c dp L sp (t + 1) s₂ ∧ s₂.cf = some (decide (L - 512 * (t + 1) < 512))) := by
    intro t
    have step : ∀ {s}, 512 ≤ L - 512 * t → CO c dp L sp t s → WP isa (chunkO vl) s fun s' =>
        CO c dp L sp (t + 1) s' ∧ s'.cf = some (decide (L - 512 * (t + 1) < 512)) :=
      fun hge' ⟨R0, R1, A, m₀, hk, hL⟩ => WP.mono (chunkO_ok vl hl hk hge' hL) fun s' ⟨hL', cf'⟩ =>
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
    (fun n => ?_) (L - 512 * 0)).mono (fun _ _ h => ⟨0, rfl, by omega_arith, h.1, h.2⟩) (fun _ _ h => h)
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
    exact ⟨L - 512 * (t + 1), by omega_arith, t + 1, rfl, by omega_arith, h₁, h₂⟩

/-- `CO` with a test of `restO` on the bytes left, `rdx` those bytes less 193. -/
def CRO (c dp : Addr) (L : Nat) (sp : Addr) (T : Nat) (P : Prop) [Decidable P] (s : State) : Prop :=
  ∃ R0 R1 A m₀, Key R0 R1 ∧ LO c dp L R0 R1 A m₀ sp T s ∧ s.cf = some (decide P) ∧
    s.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - BitVec.ofNat 64 193

omit hl hge in
theorem CO.agree {c dp : Addr} {L : Nat} {sp : Addr} {T : Nat} {s₁ s₂ : State}
    (h₁ : CO c dp L sp T s₁) (h₂ : CO c dp L sp T s₂) :
    X86_64.Taint.Agree (τR [.rdi, .rcx, .rsi, .rsp]) s₁ s₂ := by
  obtain ⟨_, _, _, _, _, h₁⟩ := h₁
  obtain ⟨_, _, _, _, _, h₂⟩ := h₂
  refine agree_regs _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.rdi, h₂.rdi]
  · rw [h₁.rcx, h₂.rcx]
  · rw [h₁.rsi, h₂.rsi]
  · rw [h₁.rsp, h₂.rsp]

omit hl hge in
theorem CRO.co {c dp : Addr} {L : Nat} {sp : Addr} {T : Nat} {P : Prop} [Decidable P] {s : State}
    (h : CRO c dp L sp T P s) : CO c dp L sp T s :=
  let ⟨R0, R1, A, m₀, hk, h, _⟩ := h
  ⟨R0, R1, A, m₀, hk, h⟩

omit hl hge in
/-- Code of `open`'s tail, with only the pointers public. -/
theorem tailO_rel {T : Nat} {c' : Prog isa}
    (hc : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) c' h).isSome = true)
    {P : State → State → Prop} (hP : ∀ s₁ s₂, P s₁ s₂ → CO c dp L sp T s₁ ∧ CO c dp L sp T s₂) :
    RelCT isa P c' fun _ _ => True :=
  let ⟨_, hc⟩ := hc
  RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp])
    (fun s₁ s₂ h => CO.agree (hP s₁ s₂ h).1 (hP s₁ s₂ h).2) hc

omit hge in
/-- A later test of `restO`: from `CRO` of `H`, `CRO` of the bytes left from
193 to `192 + n`. -/
theorem restCmpO_rel {T : Nat} {H : Prop} [Decidable H] {i : BitVec 32} {n : Nat} (hn : n ≤ 512)
    (xi : BitVec.signExtend 64 i = BitVec.ofNat 64 n)
    (hc : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp]) (.block [.alu .cmp .rdx (.imm i)]) h).isSome = true)
    (b : Bool) :
    RelCT isa (fun s₁ s₂ => (CRO c dp L sp T H s₁ ∧ CRO c dp L sp T H s₂) ∧ isa.eval .b s₁ = some b)
      (.block [.alu .cmp .rdx (.imm i)])
      (fun s₁ s₂ => CRO c dp L sp T (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + n) s₁ ∧
        CRO c dp L sp T (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + n) s₂) := by
  obtain ⟨_, hc⟩ := hc
  have step : ∀ {s}, CRO c dp L sp T H s → WP isa (.block [.alu .cmp .rdx (.imm i)]) s
      (CRO c dp L sp T (193 ≤ L - 512 * T ∧ L - 512 * T < 193 + n)) :=
    fun ⟨R0, R1, A, m₀, hk, h, _, rdx⟩ => WP.mono (restCmpO_ok hl.L_lt hn xi h rdx)
      fun s' ⟨h', cf, rdx'⟩ => ⟨R0, R1, A, m₀, hk, h', cf, rdx'.trans rdx⟩
  exact ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp])
    (fun s₁ s₂ h => CO.agree h.1.1.co h.1.2.co) hc).wp fun _ _ h => ⟨step h.1.1, step h.1.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

omit hl hge in
theorem CRO.flags {T : Nat} {P : Prop} [Decidable P] {s₁ s₂ : State}
    (h : CRO c dp L sp T P s₁ ∧ CRO c dp L sp T P s₂) : isa.eval .b s₁ = isa.eval .b s₂ := by
  obtain ⟨⟨_, _, _, _, _, _, c₁, _⟩, ⟨_, _, _, _, _, _, c₂, _⟩⟩ := h
  simp only [eval, c₁, c₂]

omit hge in
/-- After the whole chunks of `open`: `tailO`, `tail3O`, `tailKO` or
`leaveO`, by the bytes left, which are public by correctness (`LO`). -/
theorem restO_rel (T : Nat) :
    RelCT isa (fun s₁ s₂ => CO c dp L sp T s₁ ∧ CO c dp L sp T s₂ ∧ L - 512 * T < 512) (restO vl)
      fun _ _ => True := by
  unfold restO
  obtain ⟨_, hP⟩ := restPreO_taint
  obtain ⟨_, hL⟩ := leaveO_taint
  let H : Prop := 193 ≤ L - 512 * T ∧ L - 512 * T < 193 + 319
  have pre : ∀ {s}, CO c dp L sp T s → WP isa (.block (padIns .rdx 5 ++
      ([.mov .rdx (.mem (Impl.ChaCha20.X86_64.at_ .rcx lenOff)), .alu .sub .rdx (.imm 193),
        .alu .cmp .rdx (.imm 319)] : List Instr))) s (CRO c dp L sp T H) :=
    fun ⟨R0, R1, A, m₀, hk, h⟩ => WP.mono (restPreO_ok hl.L_lt h) fun s' ⟨h', cf, rdx⟩ =>
      ⟨R0, R1, A, m₀, hk, h', cf, rdx⟩
  have p := ((RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp]) (P := fun s₁ s₂ =>
      CO c dp L sp T s₁ ∧ CO c dp L sp T s₂ ∧ L - 512 * T < 512) (fun s₁ s₂ h => CO.agree h.1 h.2.1) hP).wp
    (F₁ := CRO c dp L sp T H) (F₂ := CRO c dp L sp T H) fun _ _ h => ⟨pre h.1, pre h.2.1⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  refine p.seq (RelCT.ite (fun s₁ s₂ h => CRO.flags sp h) ?_ ?_)
  · refine (restCmpO_rel hl sp (n := 64) (by decide) (by decide) cmp64_taint true).seq
      (RelCT.ite (fun s₁ s₂ h => CRO.flags sp h) ?_ ?_)
    · -- 193 to 256 bytes left.
      exact tailO_rel sp tailO12_taint fun _ _ h => ⟨h.1.1.co, h.1.2.co⟩
    refine (restCmpO_rel hl sp (n := 192) (by decide) (by decide) cmp192_taint false).seq
      (RelCT.ite (fun s₁ s₂ h => CRO.flags sp h) ?_ ?_)
    · -- 257 to 384 bytes left.
      exact tailO_rel sp tail3O16_taint fun _ _ h => ⟨h.1.1.co, h.1.2.co⟩
    · -- 385 to 511 bytes left.
      exact tailO_rel sp (tailKO24_taint vl) fun _ _ h => ⟨h.1.1.co, h.1.2.co⟩
  · -- Otherwise `leaveO`.
    refine RelCT.taint (A := taintS) (τR [.rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hL
    obtain ⟨⟨⟨_, _, _, _, _, h₁, _⟩, ⟨_, _, _, _, _, h₂, _⟩⟩, -⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.rcx, h₂.rcx]
    · rw [h₁.rsi, h₂.rsi]
    · rw [h₁.rsp, h₂.rsp]

/-- `bulkO`, with its permissions. -/
theorem bulkO_rel :
    RelCT isa (fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂) (bulkO vl) fun _ _ => True := by
  unfold bulkO
  obtain ⟨_, hE⟩ := enter_taint
  have e := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂)
    (τR [.rcx, .rsi, .rsp]) (fun s₁ s₂ h => agree_regs _ ?_) hE).wp
    (F₁ := CO c dp L sp 0) (F₂ := CO c dp L sp 0)
    fun _ _ h => ⟨WP.mono (enter_fc h.1) fun _ h => h.co, WP.mono (enter_fc h.2) fun _ h => h.co⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  · exact e.seq ((loopO_rel hl hge sp vl).seq (RelCT.exists_ (M := isa) (P := fun (T : Nat) (s₁ s₂ : State) =>
      CO c dp L sp T s₁ ∧ CO c dp L sp T s₂ ∧ L - 512 * T < 512) fun T => restO_rel hl sp vl T))
  · obtain ⟨⟨_, _, rsi₁, _, rcx₁, rsp₁, -⟩, ⟨_, _, rsi₂, _, rcx₂, rsp₂, -⟩⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [rcx₁, rcx₂]
    · rw [rsi₁, rsi₂]
    · rw [rsp₁, rsp₂]

end

theorem wholeORest_taint (vl : Bool) : ∃ h, (taintS.check (τR [.rdi, .rcx, .rsi, .rsp])
    (.seq (tailKMain vl true) (.block (leaveTO 28 ++ ([.vop .vzeroupper] : List Instr)))) h).isSome = true := by
  cases vl
  · taint_decide_sum [sroundsFT]
  · taint_decide_sum [sroundsTT]

/-- `wholeO`, with its permissions. -/
theorem wholeO_rel {c dp : Addr} {L : Nat} (sp : Addr) (vl : Bool) :
    RelCT isa (fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂) (wholeO vl) fun _ _ => True := by
  unfold wholeO
  obtain ⟨_, hE⟩ := enter_taint
  obtain ⟨_, hR⟩ := wholeORest_taint vl
  have ag : ∀ s₁ s₂, BP c dp L sp s₁ ∧ BP c dp L sp s₂ → X86_64.Taint.Agree (τR [.rcx, .rsi, .rsp]) s₁ s₂ := by
    rintro s₁ s₂ ⟨⟨_, _, rsi₁, _, rcx₁, rsp₁, -⟩, ⟨_, _, rsi₂, _, rcx₂, rsp₂, -⟩⟩
    refine agree_regs _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [rcx₁, rcx₂]
    · rw [rsi₁, rsi₂]
    · rw [rsp₁, rsp₂]
  have e := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => BP c dp L sp s₁ ∧ BP c dp L sp s₂)
    (τR [.rcx, .rsi, .rsp]) ag hE).wp (F₁ := CO c dp L sp 0) (F₂ := CO c dp L sp 0)
    fun _ _ h => ⟨WP.mono (enter_fc h.1) fun _ h => h.co, WP.mono (enter_fc h.2) fun _ h => h.co⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  exact e.seq (RelCT.taint (A := taintS) (τR [.rdi, .rcx, .rsi, .rsp]) (fun _ _ h => CO.agree h.1 h.2) hR)

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `openStitched` is constant time

As `open_rel`. `cryptO`'s branch for at most `fold` bytes is `open`'s code,
checked as before. With more, `cryptArgs` is checked; `bulkO` is constant
time by `bulkO_rel` (moved to `open`'s permissions by `relCT_narrow`), and
`wholeO` by `wholeO_rel`; the rest's `macPadLengths` and `restArgs` are checked
with `rbx`, `rbp` public, functions of the public length (`PubM`); and the
call of `vg_chacha20_xor` on the rest by the implementation's own proof.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)
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
    (.seq (.ite .b (wholeO x.vl) (bulkO x.vl))
    (.seq (.block (padIns .rax 18))
    (.seq (macPadLengths b .rbx .rbp) (decRest x))))

def iteO (x : Impl.ChaCha20.X86_64.Callee) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .ite .b (smallO x.wide b) (bigO x b)

/-- `openStitched` after the branch: the keystream wiped (`wipeS`), the tag
computed and compared. -/
def openPostS (fold w : Nat) : Prog isa :=
  .seq (wipeS fold 192 w) (.seq (finalizeTo 48) (.block (compare ++ restore)))

theorem openPostS_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τ₁ false) (openPostS fold wide) h).isSome = true := by
  rcases h with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ <;> taint_decide_sum [finalizeSumO]

theorem openS_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa (openStitched x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA x.fold x.pass x.wide) (.seq (xsel x)
      (.seq (sealMid x.fold b) (.seq (iteO x b) (openPostS x.fold x.wide)))))) s t s' := by
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
  ∃ σ, AtIteX fold pass s₀ σ ∧ Args s₀ σ s ∧ s.gpr .r15 = σ.gpr .r15 ∧ s.cf = some (decide (L s₀ < 512)) ∧
    fold < L s₀

/-- After the branch on 512 bytes. -/
def MidSO (s₀ s : State) : Prop := ∃ σ key msg E A, (Inv s₀ σ ∧ TailKs s₀ σ.mem) ∧ MidO s₀ σ key msg E A s

/-- After the rest's `macPadLengths`: with `tailO`, the rest's keystream in
`buf`, and with `twoKs`, at `ctx + 736`. -/
def MacDone (s₀ s : State) : Prop :=
  Inv s₀ s ∧ s.gpr .rbx = dp s₀ + BitVec.ofNat 64 (Aof (L s₀)) ∧
    s.gpr .rbp = BitVec.ofNat 64 (L s₀ - Aof (L s₀)) ∧
    (TailC (L s₀) (Eof (L s₀)) → ∀ i < L s₀ - Eof (L s₀), s.mem (off (cx s₀) 128 + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (Eof (L s₀) + i) 0) ∧ TailKs s₀ s.mem ∧
    (L s₀ < 512 → ∀ i < L s₀, s.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0) ∧
    (TailK (L s₀) (Eof (L s₀)) → ∀ i < L s₀ - Eof (L s₀), s.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (Eof (L s₀) + i) 0)

theorem MacDone.congr {s₀ s t : State} (h : MacDone s₀ s) (g : ∀ r, r ≠ .rax → t.gpr r = s.gpr r)
    (m : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MacDone s₀ t :=
  ⟨Inv.congr h.1 g m rd wr, by rw [g _ (by decide), h.2.1], by rw [g _ (by decide), h.2.2.1],
    fun tc i hi => by rw [m]; exact h.2.2.2.1 tc i hi, by rw [m]; exact h.2.2.2.2.1,
    fun hl i hi => by rw [m]; exact h.2.2.2.2.2.1 hl i hi, fun tk i hi => by rw [m]; exact h.2.2.2.2.2.2 tk i hi⟩

/-- `MacDone` with `CF` the Boolean `b`. -/
def MacC (s₀ : State) (b : Bool) (s : State) : Prop := MacDone s₀ s ∧ isa.eval .b s = some b

/-- `decRest`'s first test: below 512 bytes. -/
abbrev b512 (s₀ : State) : Bool := decide (L s₀ < 512)

/-- `decRest`'s second test: from 193 to 256 bytes after the whole chunks. -/
abbrev bTail (s₀ : State) : Bool := decide (193 ≤ L s₀ % 512 ∧ L s₀ % 512 < 193 + 64)

/-- `decRest`'s third test: from 1 to 511 bytes after the whole chunks. -/
abbrev bKs (s₀ : State) : Bool := decide (1 ≤ L s₀ % 512 ∧ L s₀ % 512 < 1 + 511)

/-- The public registers of those two: the context, the data and its rest. -/
structure PubM (s₀ s : State) : Prop where
  r15 : s.gpr .r15 = cx s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r9
  r14 : s.gpr .r14 = dp s₀
  r12 : s.gpr .r12 = tp s₀
  rbx : s.gpr .rbx = dp s₀ + BitVec.ofNat 64 (Aof (L s₀))
  rbp : s.gpr .rbp = BitVec.ofNat 64 (L s₀ - Aof (L s₀))
  wr : s.wr = s₀.wr

theorem MidSO.pub {s₀ s : State} (h : MidSO s₀ s) : PubM s₀ s := by
  obtain ⟨σ, key, msg, E, A, ⟨hi, -⟩, hm⟩ := h
  exact ⟨by rw [hm.keep _ (.inr (.inr (.inr (.inl rfl)))), hi.r15],
    by rw [hm.keep _ (.inr (.inr (.inr (.inr rfl)))), hi.rsp], by rw [hm.keep _ (.inr (.inl rfl)), hi.r13],
    by rw [hm.keep _ (.inr (.inr (.inl rfl))), hi.r14], by rw [hm.keep _ (.inl rfl), hi.r12],
    by rw [hm.rbx, hm.Aeq], by rw [hm.rbp, hm.Aeq], by rw [hm.wr, hi.wr]⟩

theorem MacDone.pub {s₀ s : State} (h : MacDone s₀ s) : PubM s₀ s :=
  ⟨h.1.r15, h.1.rsp, h.1.r13, h.1.r14, h.1.r12, h.2.1, h.2.2.1, h.1.wr⟩

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
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega_arith
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 64, by simp [off_eq], by show 64 + 64 ≤ 1696; omega_arith⟩
  · exact ⟨dR s₀, by rw [h.wr]; exact hp.d_wr, Eof (L s₀), rfl, by show Eof (L s₀) + (L s₀ - Eof (L s₀)) ≤ L s₀; omega_arith⟩
  · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 128, by simp [off_eq], by show 128 + 320 ≤ 1696; omega_arith⟩

omit hp' hq in
include hp in
theorem XO.pre (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} (h : XO s₀ s) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] (xR s₀)) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega_arith
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (Eof (L s₀)), L s₀ - Eof (L s₀)⟩ (dR s₀) :=
    Offset.sub_base _ (by omega_arith)
  exact xor_pre v h.rdi h.rsi h.rdx h.rcx (by omega_arith)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ _ (by omega_arith)) _) (by have := hp.wrap_d; omega_arith))
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_d.sub_right dsub)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega))

omit hp' hq in
include hp in
theorem XO.call (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} (h : XO s₀ s) :
    WP isa (.call v.callee.name v.callee.code) s (After s₀) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hE : Eof (L s₀) ≤ L s₀ := by simp only [Eof]; omega_arith
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (Eof (L s₀)), L s₀ - Eof (L s₀)⟩ (dR s₀) :=
    Offset.sub_base _ (by omega_arith)
  refine xor_call v h.rdi h.rsi h.rdx h.rcx (by omega_arith)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ _ (by omega_arith)) _) (by have := hp.wrap_d; omega_arith))
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_d.sub_right dsub)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (Covers.right (h.hw hp)) (h.hw hp)
    fun s' _ wr' cs' _ rsi' _ => ⟨rsi', by rw [cs' _ calleeSaved_rsp, h.rsp],
      by rw [cs' _ (by decide), h.r13], by rw [cs' _ (by decide), h.r14],
      by rw [cs' _ (by decide), h.r12], by rw [wr', h.wr]⟩

end

/-! ## Each run -/

theorem smallO_after (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : AtIteX v.callee.fold v.callee.pass s₀ s) (hle : L s₀ ≤ v.callee.fold) : WP isa (smallO v.callee.wide v.poly) s (After s₀) := by
  obtain ⟨hi, -, ⟨key, msg, hrep⟩, -⟩ := h
  exact WP.mono (smallO_ok v hp hi.inv hle hi.ks hrep) fun s' c =>
    ⟨c.rsi, by rw [c.keep _ (.inr (.inr (.inr rfl))), hi.inv.rsp], by rw [c.keep _ (.inr (.inl rfl)), hi.inv.r13],
      by rw [c.keep _ (.inr (.inr (.inl rfl))), hi.inv.r14], by rw [c.keep _ (.inl rfl), hi.inv.r12],
      by rw [c.wr, hi.inv.wr]⟩

theorem argsO_at {fold pass : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtIteX fold pass s₀ s)
    (hgt : fold < L s₀) :
    WP isa (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) s (AtArgsO fold pass s₀) :=
  WP.mono (argsCmpO_ok hp h.1.inv) fun _ ⟨ha, h15, cf⟩ => ⟨_, h, ha, h15, cf, hgt⟩

theorem wholeO_mid {pass : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtArgsO 448 pass s₀ s)
    (hb : isa.eval .b s = some true) (vl : Bool) : WP isa (wholeO vl) s (MidSO s₀) := by
  obtain ⟨σ, ⟨hi, hst, ⟨key, msg, hrep⟩, hks⟩, ha, -, cf, hgt⟩ := h
  simp only [eval, cf, Option.some.injEq, decide_eq_true_eq] at hb
  exact WP.mono (wholeO_midO vl hp hi.inv.wr ha hi.inv.r15 (by omega_arith) hb hst hrep)
    fun _ hm => ⟨σ, key, msg, 0, 448, ⟨hi.inv, hks⟩, hm⟩

theorem bulkO_mid {fold pass : Nat} {s₀ : State} (hp : APre e s₀) {s : State} (h : AtArgsO fold pass s₀ s)
    (hb : isa.eval .b s = some false) (vl : Bool) : WP isa (bulkO vl) s (MidSO s₀) := by
  obtain ⟨σ, ⟨hi, hst, ⟨key, msg, hrep⟩, hks⟩, ha, -, cf, -⟩ := h
  simp only [eval, cf, Option.some.injEq, decide_eq_false_iff_not] at hb
  exact WP.mono (bulk_midO vl hp hi.inv.wr ha hi.inv.r15 (by omega_arith) hst hrep)
    fun _ ⟨E, A, hm⟩ => ⟨σ, key, msg, E, A, ⟨hi.inv, hks⟩, hm⟩

theorem macO_done (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : MidSO s₀ s) : WP isa (macPadLengths b .rbx .rbp) s (MacDone s₀) := by
  obtain ⟨σ, key, msg, E, A, ⟨hi, hks⟩, hm⟩ := h
  have hE : E = Eof (L s₀) := hm.Ediv
  have i : Inv s₀ s := Inv.step' hi hm.keep hm.rd hm.wr hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  exact WP.mono (macPadLengths_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcRest hp hm.AL) i
    hm.rbx hm.rbp) fun _ ⟨i', cs', f', _⟩ => ⟨i', by rw [cs' _ (by decide), hm.rbx, hm.Aeq],
      by rw [cs' _ (by decide), hm.rbp, hm.Aeq], fun t => by
        subst hE
        rcases hm.tail with ⟨hl, -⟩ | ⟨-, -, nt, -⟩ | ⟨-, ks⟩ | ⟨tk, -⟩
        · exact absurd t.1 (by omega_arith)
        · exact absurd t nt
        · exact buf_frame f' (by rdisj_all) (by unfold TailC at t; omega_arith) ks
        · exact absurd t (by unfold TailC; unfold TailK at tk; omega_arith),
      (hm.x736 hks).frame f' (by rdisj_all), fun hl => by
        rcases hm.tail with ⟨-, ks⟩ | ⟨hge, -⟩ | ⟨t, -⟩ | ⟨t, -⟩
        · exact ks736_frame f' (by rdisj_all) (by omega_arith) ks
        · exact absurd hl (by omega_arith)
        · exact absurd t.1 (by omega_arith)
        · exact absurd t.1 (by omega_arith), fun t => by
        subst hE
        rcases hm.tail with ⟨hl, -⟩ | ⟨-, -, -, nk⟩ | ⟨tc, -⟩ | ⟨-, ks⟩
        · exact absurd t.1 (by omega_arith)
        · exact absurd t nk
        · exact absurd t (by unfold TailK; unfold TailC at tc; omega_arith)
        · exact ks736_frame f' (by rdisj_all) (by simp only [Eof]; omega_arith) ks⟩

theorem restO_x {s₀ : State} {s : State} (h : MacDone s₀ s) (hA : Aof (L s₀) = Eof (L s₀)) :
    WP isa (.block restArgs) s (XO s₀) :=
  WP.mono (restArgs_ok (s₀ := s₀) h.1.r15) fun _ ⟨rdi, rsi, rdx, rcx, g, _, wr, _⟩ =>
    ⟨rdi, by rw [rsi, h.2.1, hA], by rw [rdx, h.2.2.1, hA], rcx,
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.1.rsp],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.1.r13],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.1.r14],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.1.r12], by rw [wr, h.1.wr]⟩

theorem cmp13_done {s₀ s : State} (h : MacDone s₀ s) :
    WP isa (.block [.alu .cmp .r13 (.imm 512)]) s (MacC s₀ (b512 s₀)) :=
  WP.mono (cmp13_ok s) fun _ ⟨c, g, m, rd, wr, _⟩ =>
    ⟨h.congr (fun r _ => congrFun g r) m rd wr, by rw [c, h.1.r13]⟩

theorem restTest_done {lo n : Nat} (hlo : lo < 512) (hn : n ≤ 512)
    (xl : BitVec.signExtend 64 (BitVec.ofNat 32 lo) = BitVec.ofNat 64 lo)
    (xn : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n) {s₀ s : State} (h : MacDone s₀ s) :
    WP isa (.block (restTest lo n)) s (MacC s₀ (decide (lo ≤ L s₀ % 512 ∧ L s₀ % 512 < lo + n))) :=
  WP.mono (restTest_ok hlo hn xl xn s) fun _ ⟨c, g, m, rd, wr, _⟩ => ⟨h.congr g m rd wr, by rw [c, h.1.r13]⟩

theorem xorTail_after (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : MacDone s₀ s) (t : TailC (L s₀) (Eof (L s₀))) : WP isa (xorTail v.callee.wide 128) s (After s₀) :=
  WP.mono (xorTail_ok v hp h.1 rfl (.inl rfl) (by unfold TailC at t; simp only [Eof] at t; omega_arith) (h.2.2.2.1 t))
    fun _ ⟨rsi, cs, _, wr, _⟩ => ⟨rsi, by rw [cs _ calleeSaved_rsp, h.1.rsp],
      by rw [cs _ (by decide), h.1.r13], by rw [cs _ (by decide), h.1.r14],
      by rw [cs _ (by decide), h.1.r12], by rw [wr, h.1.wr]⟩

/-- The rest decrypted from the keystream at `ctx + 736`: `twoKs`'s or
`fourKs`'s (1 to 192 bytes after the whole chunks), or `tail3O`'s or
`tailKO`'s (257 to 511), which is then wiped. -/
theorem xorKs_after (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : MacDone s₀ s) (t : 512 ≤ L s₀ ∧ 1 ≤ L s₀ % 512 ∧ L s₀ % 512 < 512)
    (nt : ¬ TailC (L s₀) (Eof (L s₀))) :
    WP isa (.seq (xorTail v.callee.wide 736) (.seq (.block (restTest 257 255))
      (.ite .b (.seq (.block [.mov32 .rdx (.imm 576)]) (.seq (zeroKs v.callee.wide) (.block (padIns .rax 3))))
        (.block [])))) s (After s₀) := by
  have hm : L s₀ % 512 = L s₀ - Eof (L s₀) := by simp only [Eof]; have := Nat.mod_add_div (L s₀) 512; omega_arith
  have ks : ∀ i < L s₀ - Eof (L s₀), s.mem (off (cx s₀) 736 + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (Eof (L s₀) + i) 0 := by
    by_cases hsm : L s₀ % 512 ≤ 192
    · intro i hi
      rw [off_eq, Offset.add_add, ← off_eq, h.2.2.2.2.1 t.1 t.2.1 hsm i (by omega_arith)]
    · exact h.2.2.2.2.2.2 ⟨t.1, by
        unfold TailC at nt; simp only [Eof] at nt hm ⊢; omega_arith⟩
  refine WP.seq (WP.mono (xorTail_ok v hp h.1 rfl (.inr rfl) (by omega_arith) ks) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (restTest_ok (lo := 257) (n := 255) (by decide) (by decide) (by decide) (by decide) s₁)
    fun s₂ ⟨c₂, g₂, m₂, rd₂, wr₂, mx₂⟩ => ?_)
  have h₂ := h₁.pad ⟨g₂, m₂, rd₂, wr₂, mx₂⟩
  have fin : ∀ {u}, RestP s₀ s (Eof (L s₀)) u → After s₀ u := fun ⟨rsi, cs, _, wr, _⟩ =>
    ⟨rsi, by rw [cs _ calleeSaved_rsp, h.1.rsp],
      by rw [cs _ (by decide), h.1.r13], by rw [cs _ (by decide), h.1.r14],
      by rw [cs _ (by decide), h.1.r12], by rw [wr, h.1.wr]⟩
  exact WP.ite _ c₂ (fun _ => WP.mono (wipeK_ok v hp h.1 h₂) fun _ h' => fin h') (fun _ => WP.block_nil (fin h₂))

/-- Below 512 bytes, the data decrypted from the keystream `wholeO` left at
`ctx + 736`, which is then wiped. -/
theorem decWhole_after (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : MacDone s₀ s) (hl : L s₀ < 512) :
    WP isa (.seq (xorTail v.callee.wide 736) (.seq (.block [.mov32 .rdx (.imm 576)]) (zeroKs v.callee.wide))) s
      (After s₀) :=
  WP.mono (decWhole_ok v hp h.1 hl (h.2.2.2.2.2.1 hl))
    fun _ ⟨rsi, cs, _, wr, _⟩ => ⟨rsi, by rw [cs _ calleeSaved_rsp, h.1.rsp],
      by rw [cs _ (by decide), h.1.r13], by rw [cs _ (by decide), h.1.r14],
      by rw [cs _ (by decide), h.1.r12], by rw [wr, h.1.wr]⟩

/-! ## The taint analyses -/

theorem decWhole_taint (v : Proof.ChaCha20.X86_64.XorImpl) : ∃ h, (taintS.check (τM false)
    (.seq (xorTail v.callee.wide 736) (.seq (.block [.mov32 .rdx (.imm 576)]) (zeroKs v.callee.wide))) h).isSome =
      true := by
  rcases wide_of v with h | h | h <;> rw [h] <;> taint_decide_sum []

theorem midO_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τA false) (sealMid fold b) h).isSome = true := by
  rcases h with ⟨rfl, rfl, -, rfl⟩ | ⟨rfl, rfl, -, rfl⟩ | ⟨rfl, rfl, -, rfl | rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksBigAvx2O, blocksBigAvx512O, blocksBigIfmaO]

theorem smallO_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τS false) (smallO wide b) h).isSome = true := by
  rcases h with ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl | rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksSmallO, blocksBigAvx2O, blocksSmallAvx2O, blocksBigAvx512O,
      blocksSmallAvx512O, blocksBigIfmaO, blocksSmallIfmaO]

theorem argsO_taint :
    ∃ h, (taintS.check (τS false) (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) h).isSome =
      true := by
  taint_decide_sum []

theorem macO_taint {fold pass wide : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold pass wide b) :
    ∃ h, (taintS.check (τM false) (macPadLengths b .rbx .rbp) h).isSome = true := by
  rcases h with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl | rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksSmallO, blocksBigAvx2O, blocksSmallAvx2O, blocksBigAvx512O,
      blocksSmallAvx512O, blocksBigIfmaO, blocksSmallIfmaO]

theorem restO_taint : ∃ h, (taintS.check (τM false) (.block restArgs) h).isSome = true := by
  taint_decide_sum []

theorem pad18_taint : ∃ h, (taintS.check (τR []) (.block (padIns .rax 18)) h).isSome = true := by
  taint_decide_sum []

theorem pad20_taint : ∃ h, (taintS.check (τR []) (.block (padIns .rax 20)) h).isSome = true := by
  taint_decide_sum []

theorem cmp13_taint : ∃ h, (taintS.check (τM false) (.block [.alu .cmp .r13 (.imm 512)]) h).isSome = true := by
  taint_decide_sum []

theorem tailTest_taint : ∃ h, (taintS.check (τM false) (.block (restTest 193 64)) h).isSome = true := by
  taint_decide_sum []

theorem ksTest_taint : ∃ h, (taintS.check (τM false) (.block (restTest 1 511)) h).isSome = true := by
  taint_decide_sum []

theorem xorKs_taint (v : Proof.ChaCha20.X86_64.XorImpl) : ∃ h, (taintS.check (τM false)
    (.seq (xorTail v.callee.wide 736) (.seq (.block (restTest 257 255))
      (.ite .b (.seq (.block [.mov32 .rdx (.imm 576)]) (.seq (zeroKs v.callee.wide) (.block (padIns .rax 3))))
        (.block [])))) h).isSome = true := by
  rcases wide_of v with h | h | h <;> rw [h] <;> taint_decide_sum []

theorem xorTail_taint (v : Proof.ChaCha20.X86_64.XorImpl) {o : Nat} (ho : o = 128 ∨ o = 736) :
    ∃ h, (taintS.check (τM false) (xorTail v.callee.wide o) h).isSome = true := by
  rcases wide_of v with h | h | h <;> rcases ho with rfl | rfl <;> rw [h] <;> taint_decide_sum []

/-! ## The branch with more than `fold` bytes -/

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State} (hp : APre false s₀) (hp' : APre false s₀')
  (hq : pubX86_64 s₀ s₀')
include hp hp' hq

theorem bigO_rel (hf448 : v.callee.fold = 448) :
    RelCT isa (fun s₁ s₂ => (AtIteX v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteX v.callee.fold v.callee.pass s₀' s₂) ∧
      isa.eval .b s₁ = some false) (bigO v.callee v.poly) fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, -, p9⟩ := hq'
  have eL : L s₀' = L s₀ := by simp only [L, p6]
  have ec : cx s₀' = cx s₀ := by simp only [cx, p9]
  have ed : dp s₀' = dp s₀ := by simp only [dp, p5]
  obtain ⟨_, hA⟩ := argsO_taint
  obtain ⟨_, hM⟩ := macO_taint v.fold_poly
  obtain ⟨_, hR⟩ := restO_taint
  have args := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (AtIteX v.callee.fold v.callee.pass s₀ s₁ ∧
      AtIteX v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some false) (τS false)
      (fun _ _ h => agreeS hp hp' hq h.1.1.1 h.1.2.1) hA).wp
    (F₁ := AtArgsO v.callee.fold v.callee.pass s₀) (F₂ := AtArgsO v.callee.fold v.callee.pass s₀') fun _ _ h => by
      have hgt : v.callee.fold < L s₀ := by
        have e := h.2
        simp only [eval, h.1.1.1.cf, Option.some.injEq, decide_eq_false_iff_not] at e
        omega_arith
      exact ⟨argsO_at hp h.1.1 hgt, argsO_at hp' h.1.2 (by rw [eL]; exact hgt)⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have hcf : ∀ s₁ s₂, (AtArgsO v.callee.fold v.callee.pass s₀ s₁ ∧ AtArgsO v.callee.fold v.callee.pass s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    obtain ⟨⟨_, -, -, -, c₁, -⟩, ⟨_, -, -, -, c₂, -⟩⟩ := h
    simp only [eval, c₁, c₂, eL]
  have hl : Lay (cx s₀) (dp s₀) (L s₀) :=
    ⟨(s₀.gpr .r9).isLt, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have wh : RelCT isa (fun s₁ s₂ => (AtArgsO v.callee.fold v.callee.pass s₀ s₁ ∧
      AtArgsO v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some true) (wholeO v.callee.vl)
      fun s₁ s₂ => MidSO s₀ s₁ ∧ MidSO s₀' s₂ := by
    by_cases hlt : L s₀ < 512
    · refine ((relCT_narrow (c := wholeO v.callee.vl) (fun _ => bulkWr (cx s₀) (dp s₀) (L s₀)) ?_
        (wholeO_rel (c := cx s₀) (dp := dp s₀) (L := L s₀) (s₀.gpr .rsp) v.callee.vl)).wp (F₁ := MidSO s₀)
        (F₂ := MidSO s₀') ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      · rintro s₁ s₂ ⟨⟨⟨σ₁, ⟨hi₁, -, ⟨key₁, msg₁, hrep₁⟩, -⟩, ha₁, -, -, hg₁⟩,
          ⟨σ₂, ⟨hi₂, -, ⟨key₂, msg₂, hrep₂⟩, -⟩, ha₂, -, -, -⟩⟩, -⟩
        have h448 : 448 ≤ L s₀ := by rw [hf448] at hg₁; omega_arith
        have b₁ := bulk_bp ha₁ hi₁.inv hrep₁
        have b₂ := bulk_bp ha₂ hi₂.inv hrep₂
        rw [ec, ed, eL, ← p7] at b₂
        obtain ⟨rd₁, wr₁, rsi₁, rdx₁, rcx₁, -, _, _, r₁⟩ := id b₁
        obtain ⟨rd₂, wr₂, rsi₂, rdx₂, rcx₂, -, _, _, r₂⟩ := id b₂
        exact ⟨bulk_covers hp (by rw [ha₁.wr, hi₁.inv.wr]), by
          rw [← ec, ← ed, ← eL]; exact bulk_covers hp' (by rw [ha₂.wr, hi₂.inv.wr]),
          ⟨_, wholeO_ok _ hl h448 hlt rd₁ wr₁ rsi₁ rdx₁ rcx₁ r₁⟩,
          ⟨_, wholeO_ok _ hl h448 hlt rd₂ wr₂ rsi₂ rdx₂ rcx₂ r₂⟩, b₁, b₂⟩
      · exact fun _ _ h => ⟨wholeO_mid hp (by rw [← hf448]; exact h.1.1) h.2 _,
          wholeO_mid hp' (by rw [← hf448]; exact h.1.2) (by rw [← hcf _ _ h.1]; exact h.2) _⟩
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, _, c₁, _⟩, _⟩, hb⟩ => ?_
      simp only [eval, c₁, Option.some.injEq, decide_eq_true_eq] at hb
      exact hlt hb
  have bk : RelCT isa (fun s₁ s₂ => (AtArgsO v.callee.fold v.callee.pass s₀ s₁ ∧ AtArgsO v.callee.fold v.callee.pass s₀' s₂) ∧
      isa.eval .b s₁ = some false) (bulkO v.callee.vl) fun s₁ s₂ => MidSO s₀ s₁ ∧ MidSO s₀' s₂ := by
    by_cases hge : 512 ≤ L s₀
    · refine ((relCT_narrow (c := bulkO v.callee.vl) (fun _ => bulkWr (cx s₀) (dp s₀) (L s₀)) ?_
        (bulkO_rel hl hge (s₀.gpr .rsp) v.callee.vl)).wp (F₁ := MidSO s₀) (F₂ := MidSO s₀') ?_).mono (fun _ _ h => h)
        fun _ _ h => h.2
      · rintro s₁ s₂ ⟨⟨⟨σ₁, ⟨hi₁, -, ⟨key₁, msg₁, hrep₁⟩, -⟩, ha₁, -⟩, ⟨σ₂, ⟨hi₂, -, ⟨key₂, msg₂, hrep₂⟩, -⟩, ha₂, -⟩⟩, -⟩
        have b₁ := bulk_bp ha₁ hi₁.inv hrep₁
        have b₂ := bulk_bp ha₂ hi₂.inv hrep₂
        rw [ec, ed, eL, ← p7] at b₂
        obtain ⟨rd₁, wr₁, rsi₁, rdx₁, rcx₁, -, _, _, r₁⟩ := id b₁
        obtain ⟨rd₂, wr₂, rsi₂, rdx₂, rcx₂, -, _, _, r₂⟩ := id b₂
        exact ⟨bulk_covers hp (by rw [ha₁.wr, hi₁.inv.wr]), by
          rw [← ec, ← ed, ← eL]; exact bulk_covers hp' (by rw [ha₂.wr, hi₂.inv.wr]),
          ⟨_, bulkO_ok _ hl hge rd₁ wr₁ rsi₁ rdx₁ rcx₁ r₁⟩, ⟨_, bulkO_ok _ hl hge rd₂ wr₂ rsi₂ rdx₂ rcx₂ r₂⟩, b₁, b₂⟩
      · exact fun _ _ h => ⟨bulkO_mid hp h.1.1 h.2 _, bulkO_mid hp' h.1.2 (by rw [← hcf _ _ h.1]; exact h.2) _⟩
    · refine RelCT.of_false fun s₁ s₂ ⟨⟨⟨_, _, _, _, c₁, _⟩, _⟩, hb⟩ => ?_
      simp only [eval, c₁, Option.some.injEq, decide_eq_false_iff_not] at hb
      omega_arith
  obtain ⟨_, hP18⟩ := pad18_taint
  have midPad : ∀ {σ₀ s : State}, MidSO σ₀ s → WP isa (.block (padIns .rax 18)) s (MidSO σ₀) :=
    fun ⟨σ, key, msg, E, A, hi, hm⟩ => WP.mono (padIns_ok .rax (by decide) _) fun _ p =>
      ⟨σ, key, msg, E, A, hi, hm.pad p⟩
  have pd := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => MidSO s₀ s₁ ∧ MidSO s₀' s₂) (τR [])
      (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hP18).wp
    (F₁ := MidSO s₀) (F₂ := MidSO s₀') fun _ _ h => ⟨midPad h.1, midPad h.2⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have mac := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => MidSO s₀ s₁ ∧ MidSO s₀' s₂) (τM false)
      (fun _ _ h => agreeM hp hp' hq h.1.pub h.2.pub) hM).wp
    (F₁ := MacDone s₀) (F₂ := MacDone s₀') fun _ _ h =>
      ⟨macO_done v.poly hp h.1, macO_done v.poly hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have callR : ∀ {P : State → State → Prop}, (∀ s₁ s₂, P s₁ s₂ →
      (MacDone s₀ s₁ ∧ MacDone s₀' s₂) ∧ 512 ≤ L s₀ ∧ ¬ TailC (L s₀) (Eof (L s₀)) ∧ ¬ TailK (L s₀) (Eof (L s₀))) →
      RelCT isa P (.seq (.block restArgs) (.call v.callee.name v.callee.code))
        fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
    intro P hP
    have rest := ((RelCT.taint (A := taintS) (P := P) (τM false)
        (fun _ _ h => agreeM hp hp' hq (hP _ _ h).1.1.pub (hP _ _ h).1.2.pub) hR).wp
      (F₁ := XO s₀) (F₂ := XO s₀') fun _ _ h => ⟨restO_x (hP _ _ h).1.1
          (Aof_notail (hP _ _ h).2.1 (hP _ _ h).2.2.1 (hP _ _ h).2.2.2),
        restO_x (hP _ _ h).1.2 (Aof_notail (by rw [eL]; exact (hP _ _ h).2.1) (by rw [eL]; exact (hP _ _ h).2.2.1)
          (by rw [eL]; exact (hP _ _ h).2.2.2))⟩).mono
      (fun _ _ h => h)
      fun _ _ h => h.2
    have call := (RelCT.callEx (n := v.callee.name) (P := fun s₁ s₂ => XO s₀ s₁ ∧ XO s₀' s₂) v.ok v.ct
      fun s₁ s₂ ⟨m₁, m₂⟩ => ⟨[], _, [], _, m₁.pre hp v, m₂.pre hp' v, ?_, Covers.right (m₁.hw hp),
        m₁.hw hp, Covers.right (m₂.hw hp'), m₂.hw hp', by rw [m₁.rsp, m₂.rsp, p7]⟩).wp
      (F₁ := After s₀) (F₂ := After s₀') fun _ _ h => ⟨h.1.call hp v, h.2.call hp' v⟩
    · exact rest.seq (call.mono (fun _ _ h => h) fun _ _ h => h.2)
    · simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
        State.callEntry_rsp, callEntry_gpr' s₁ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₁ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rcx ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rcx ≠ .rsp), m₁.rdi, m₁.rsi, m₁.rdx, m₁.rcx, m₁.rsp, m₂.rdi, m₂.rsi,
        m₂.rdx, m₂.rcx, m₂.rsp, eL, ec, ed, p7]
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  -- The rest decrypted: by the call, from `buf` after `tailO`, or from `ctx + 736` after `twoKs`.
  obtain ⟨_, hC⟩ := cmp13_taint
  obtain ⟨_, hT⟩ := tailTest_taint
  obtain ⟨_, hT₂⟩ := ksTest_taint
  obtain ⟨_, hX⟩ := xorTail_taint v (.inl rfl)
  obtain ⟨_, hX₂⟩ := xorKs_taint v
  obtain ⟨_, hDW⟩ := decWhole_taint v
  have c13 := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => MacDone s₀ s₁ ∧ MacDone s₀' s₂) (τM false)
      (fun _ _ h => agreeM hp hp' hq h.1.pub h.2.pub) hC).wp
    (F₁ := MacC s₀ (b512 s₀)) (F₂ := MacC s₀' (b512 s₀')) fun _ _ h =>
      ⟨cmp13_done h.1, cmp13_done h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have tt := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (MacC s₀ (b512 s₀) s₁ ∧ MacC s₀' (b512 s₀') s₂) ∧
      isa.eval .b s₁ = some false) (τM false)
      (fun _ _ h => agreeM hp hp' hq h.1.1.1.pub h.1.2.1.pub) hT).wp
    (F₁ := fun s => MacC s₀ (bTail s₀) s ∧ 512 ≤ L s₀) (F₂ := MacC s₀' (bTail s₀')) fun _ _ h =>
      ⟨WP.mono (restTest_done (by decide) (by decide) (by decide) (by decide) h.1.1.1) fun _ t => ⟨t, by
        have := h.1.1.2.symm.trans h.2
        simp only [b512, Option.some.injEq, decide_eq_false_iff_not] at this
        omega_arith⟩, restTest_done (by decide) (by decide) (by decide) (by decide) h.1.2.1⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have xr := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => ((MacC s₀ (bTail s₀) s₁ ∧ 512 ≤ L s₀) ∧
      MacC s₀' (bTail s₀') s₂) ∧ isa.eval .b s₁ = some true) (τM false)
      (fun _ _ h => agreeM hp hp' hq h.1.1.1.1.pub h.1.2.1.pub) hX).wp
    (F₁ := After s₀) (F₂ := After s₀') fun _ _ h => by
      have t : TailC (L s₀) (Eof (L s₀)) := by
        have := h.1.1.1.2.symm.trans h.2
        simp only [bTail, Option.some.injEq, decide_eq_true_eq] at this
        have := h.1.1.2
        unfold TailC
        simp only [Eof]
        omega_arith
      exact ⟨xorTail_after v hp h.1.1.1.1 t, xorTail_after v hp' h.1.2.1 (by rw [eL]; exact t)⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have tt₂ := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => ((MacC s₀ (bTail s₀) s₁ ∧ 512 ≤ L s₀) ∧
      MacC s₀' (bTail s₀') s₂) ∧ isa.eval .b s₁ = some false) (τM false)
      (fun _ _ h => agreeM hp hp' hq h.1.1.1.1.pub h.1.2.1.pub) hT₂).wp
    (F₁ := fun s => MacC s₀ (bKs s₀) s ∧ 512 ≤ L s₀ ∧ ¬ TailC (L s₀) (Eof (L s₀)))
    (F₂ := MacC s₀' (bKs s₀')) fun _ _ h =>
      ⟨WP.mono (restTest_done (by decide) (by decide) (by decide) (by decide) h.1.1.1.1) fun _ t => ⟨t, h.1.1.2,
        fun tc => by
          have := h.1.1.1.2.symm.trans h.2
          simp only [bTail, Option.some.injEq, decide_eq_false_iff_not] at this
          unfold TailC at tc
          simp only [Eof] at tc
          omega_arith⟩,
        restTest_done (by decide) (by decide) (by decide) (by decide) h.1.2.1⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have xk := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => ((MacC s₀ (bKs s₀) s₁ ∧ 512 ≤ L s₀ ∧
      ¬ TailC (L s₀) (Eof (L s₀))) ∧ MacC s₀' (bKs s₀') s₂) ∧ isa.eval .b s₁ = some true) (τM false)
      (fun _ _ h => agreeM hp hp' hq h.1.1.1.1.pub h.1.2.1.pub) hX₂).wp
    (F₁ := After s₀) (F₂ := After s₀') fun _ _ h => by
      have t : 512 ≤ L s₀ ∧ 1 ≤ L s₀ % 512 ∧ L s₀ % 512 < 512 := by
        have := h.1.1.1.2.symm.trans h.2
        simp only [bKs, Option.some.injEq, decide_eq_true_eq] at this
        have := h.1.1.2.1
        omega_arith
      exact ⟨xorKs_after v hp h.1.1.1.1 t h.1.1.2.2,
        xorKs_after v hp' h.1.2.1 (by rw [eL]; exact t) (by rw [eL]; exact h.1.1.2.2)⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have dec : RelCT isa (fun s₁ s₂ => MacDone s₀ s₁ ∧ MacDone s₀' s₂) (decRest v.callee)
      fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
    unfold decRest
    obtain ⟨_, hP20⟩ := pad20_taint
    have afterPad : ∀ {σ₀ s : State}, After σ₀ s → WP isa (.block (padIns .rax 20)) s (After σ₀) :=
      fun h => WP.mono (padIns_ok .rax (by decide) _) fun _ p =>
        ⟨by rw [p.gpr _ (by decide), h.rsi], by rw [p.gpr _ (by decide), h.rsp], by rw [p.gpr _ (by decide), h.r13],
          by rw [p.gpr _ (by decide), h.r14], by rw [p.gpr _ (by decide), h.r12], by rw [p.wr, h.wr]⟩
    have pd20 := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) (τR [])
        (fun _ _ _ => agree_regs [] fun _ h => by simp at h) hP20).wp
      (F₁ := After s₀) (F₂ := After s₀') fun _ _ h => ⟨afterPad h.1, afterPad h.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
    have xw := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => (MacC s₀ (b512 s₀) s₁ ∧ MacC s₀' (b512 s₀') s₂) ∧
        isa.eval .b s₁ = some true) (τM false)
        (fun _ _ h => agreeM hp hp' hq h.1.1.1.pub h.1.2.1.pub) hDW).wp
      (F₁ := After s₀) (F₂ := After s₀') fun _ _ h => by
        have hl : L s₀ < 512 := by
          have := h.1.1.2.symm.trans h.2
          simpa only [b512, Option.some.injEq, decide_eq_true_eq] using this
        exact ⟨decWhole_after v hp h.1.1.1 hl, decWhole_after v hp' h.1.2.1 (by rw [eL]; exact hl)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
    exact c13.seq (RelCT.ite (fun s₁ s₂ h => by rw [h.1.2, h.2.2, b512, b512, eL]) xw ((tt.seq (RelCT.ite (fun s₁ s₂ h => by
        rw [h.1.1.2, h.2.2, bTail, bTail, eL]) xr (tt₂.seq (RelCT.ite (fun s₁ s₂ h => by
          rw [h.1.1.2, h.2.2, bKs, bKs, eL]) xk
          (callR fun s₁ s₂ h => ⟨⟨h.1.1.1.1, h.1.2.1⟩, h.1.1.2.1, h.1.1.2.2, fun tk => by
            have := h.1.1.1.2.symm.trans h.2
            simp only [bKs, Option.some.injEq, decide_eq_false_iff_not] at this
            unfold TailK at tk
            simp only [Eof] at tk
            omega_arith⟩))))).seq pd20))
  exact args.seq ((RelCT.ite hcf wh bk).seq (pd.seq (mac.seq dec)))

end

/-! ## `openStitched` -/

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {s₀ s₀' : State}
include hv

theorem openS_rel (h₀ : preX86_64 false s₀) (h₀' : preX86_64 false s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (openStitched v.callee v.poly) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  have hfl := v.fold_le
  have hX : XPass v.callee.pass := (avx2_of v hv).2.1
  obtain ⟨_, hA⟩ := prologueA_taint false v.fold_poly
  obtain ⟨_, hmid⟩ := midO_taint v.fold_poly
  obtain ⟨_, hS⟩ := smallO_taint v.fold_poly
  obtain ⟨_, hpost⟩ := openPostS_taint v.fold_poly
  have pA := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ false)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq) hA).wp
    (F₁ := FArgs v.callee.fold v.callee.pass s₀) (F₂ := FArgs v.callee.fold v.callee.pass s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok hfl (pass_of v) (wide_of v) hp, by rw [h.2]; exact prologueA_ok hfl (pass_of v) (wide_of v) hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have mid := ((RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AfterF v.callee.fold v.callee.pass s₀ s₁ ∧ TailKs s₀ s₁.mem) ∧
      (AfterF v.callee.fold v.callee.pass s₀' s₂ ∧ TailKs s₀' s₂.mem)) (τA false)
    (fun _ _ h => agreeA hp hp' hq h.1.1 h.2.1) hmid).wp (F₁ := AtIteX v.callee.fold v.callee.pass s₀)
    (F₂ := AtIteX v.callee.fold v.callee.pass s₀') fun _ _ h =>
      ⟨sealMidX_ok hfl v.poly hp h.1.1 h.1.2, sealMidX_ok hfl v.poly hp' h.2.1 h.2.2⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have hc : ∀ s₁ s₂, (AtIteX v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteX v.callee.fold v.callee.pass s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    have : L s₀ = L s₀' := by simp only [L, hq.2.2.2.2.2.1]
    simp [eval, h.1.1.cf, h.2.1.cf, this]
  have small := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteX v.callee.fold v.callee.pass s₀ s₁ ∧ AtIteX v.callee.fold v.callee.pass s₀' s₂) ∧ isa.eval .b s₁ = some true)
    (τS false) (fun _ _ h => agreeS hp hp' hq h.1.1.1 h.1.2.1) hS).wp (F₁ := After s₀) (F₂ := After s₀')
    fun s₁ s₂ h => by
      have e₁ := h.2
      have e₂ := (hc _ _ h.1).symm.trans h.2
      simp only [eval, h.1.1.1.cf, h.1.2.1.cf, Option.some.injEq, decide_eq_true_eq] at e₁ e₂
      exact ⟨smallO_after v hp h.1.1 (by omega_arith), smallO_after v hp' h.1.2 (by omega_arith)⟩
  have ite := RelCT.ite hc (small.mono (fun _ _ h => h) fun _ _ h => h.2) (bigO_rel v hp hp' hq (avx2_of v hv).1)
  have post := RelCT.taint (A := taintS) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) (τ₁ false)
    (fun _ _ h => agree₁ hp hp' hq h.1 h.2) hpost
  have := (entry_rel hp hp' hq).seq (pA.seq ((xsel_rel v hv hX hp hp' hq).seq (mid.seq (ite.seq post))))
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
open VG.Impl.ChaCha20.X86_64.XorBuf (xData xBody xorBufX)

theorem twoKs_spSafe (vl : Bool) : (twoKs vl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases vl <;> exact Code.all_of_allInstrs (by lit_decide)

theorem twoKsB_spSafe (vl : Bool) : (twoKsB vl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases vl <;> exact Code.all_of_allInstrs (by lit_decide)

theorem fourKs_spSafe (vl : Bool) : (fourKs vl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases vl <;> exact Code.all_of_allInstrs (by lit_decide)

theorem wholeO_spSafe (vl : Bool) : (wholeO vl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases vl <;> exact Code.all_of_allInstrs (by lit_decide)

theorem openS_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    (openStitched v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  obtain ⟨hf, hpass, hw⟩ := avx2_of v hv
  have hc := v.spSafe
  have hb := blocks_spSafe v.poly
  have ho := bulkO_spSafe v.callee.vl
  have hk := twoKs_spSafe v.callee.vl
  have hk4 := fourKs_spSafe v.callee.vl
  have hwo := wholeO_spSafe v.callee.vl
  have hkB := twoKsB_spSafe v.callee.vl
  generalize hP : (fun i => !X86_64.isa.writesSp i) = P at hc hb ho hk hk4 hwo hkB ⊢
  rw [hv] at hb ⊢
  rcases Bool.eq_false_or_eq_true v.callee.vl with hl | hl <;> rw [hl] at ho hk hk4 hwo hkB <;>
  simp only [dataCopy, openStitched, prologueX, xsel, xselV, xselA, hl, ↓reduceIte, Bool.false_eq_true, cryptO,
    decRest, xorTail, Code.all, hc, hb, ho, hk, hk4, hkB, hwo, hf, hpass, hw, macPad, macPadLengths, Code.iteCold,
    wholeBlocks, padRest, Bool.cond_false, padCopy, padTail, absorbLengths, Bool.and_true, Bool.true_and] <;>
  subst hP <;> lit_decide

theorem openS_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa (openStitched v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' :=
  openStitched_correct v hv (APre.of s hs)

theorem openS_ct (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    ConstantTime isa openX86_64.pre openX86_64.pub (openStitched v.callee v.poly) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (openS_rel v hv h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem openS_implies : openX86_64.Implies (openScratchContract X86_64.abi 212 24) :=
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

theorem openS_verified (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    Verified X86_64.target (openStitched v.callee v.poly) (openScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (openS_ok v hv) (openS_ct v hv) openS_implies

theorem bulkO_xdepth (vl : Bool) : (bulkO vl).x86_64Depth = 0 := by cases vl <;> lit_decide

theorem wholeO_xdepth (vl : Bool) : (wholeO vl).x86_64Depth = 0 := by cases vl <;> lit_decide

theorem xorTail_xdepth (w : Nat) : (xorBufX w .r10).x86_64Depth = 0 := by
  have : (Impl.ChaCha20.X86_64.XorBuf.xorBuf .rdi .rsi).x86_64Depth = 0 := by decide
  simp only [xorBufX, Code.x86_64Depth, this, Nat.max_self]

theorem openS_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) :
    (openStitched v.callee v.poly).x86_64Depth ≤ 24 := by
  have hx := v.xdepth
  have hb := blocks_xdepth v.poly
  have hc := padRest_xdepth (dataCopy v.poly) v.poly 2
  have ha := padSite_xdepth (dataCopy v.poly) v.poly .rbx .rbp
  rcases Bool.eq_false_or_eq_true v.callee.vl with hl | hl <;>
  simp only [openStitched, prologueX, xsel, xselV, xselA, hl, ↓reduceIte, Bool.false_eq_true, twoKsB_xdepth,
    prologueA, prologueB, zeroKs, macPad, macPadLengths, Code.iteCold, wholeBlocks,
    padRest, padCopy, padTail, cryptO, decRest, xorTail, absorbLengths, finalizeTo, finalizeWith, Code.x86_64Depth, xorBuf_xdepth,
    xorTail_xdepth, foldM_xdepth, wipeL_xdepth, init_xdepth,
    finalize_xdepth, bulkO_xdepth, wholeO_xdepth, twoKs_xdepth, fourKs_xdepth, Nat.max_le] at hc ha ⊢ <;>
  omega_arith

theorem openS_framed (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1728 1 42 (openStitched v.callee v.poly))
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 1752) :=
  X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 212) (post := Spec.ChaCha20Poly1305.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1728) (k := 42) (openS_verified v hv) (by decide) (by decide) (by decide)
    (openS_spSafe v hv) (openS_xdepth v) (by decide) (pre_local _ _) (openPost_local _) (openPost_out _)
    openFrameSat_pre

/-! ## Short data with the AVX2 code

`openSmall big`, as `sealSmall`: the comparison changes only the flags,
which `open`'s contract does not read either. -/

/-- The comparison of `len` with `openLim` and the window. -/
abbrev cmpOpen (vl : Bool) : List Instr := smallTest (openLim vl)

/-- What the comparison leaves, from `s`. -/
def CmpedO (vl : Bool) (s t : State) : Prop :=
  isa.eval .b t = some (decide ((s.gpr .r9).toNat < openLim vl ∨
    (winLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < winHi))) ∧ FlagsOnly s t

theorem cmpOpen_ok (vl : Bool) (s : State) : WP isa (.block (cmpOpen vl)) s (CmpedO vl s) :=
  WP.mono (smallTest_ok (by cases vl <;> decide) (by cases vl <;> decide) (by cases vl <;> decide) s)
    fun _ ⟨e, g, m, rd, wr, mx⟩ => ⟨e, g, m, rd, wr, mx⟩

theorem FlagsOnly.preO {s t : State} (h : FlagsOnly s t) (hs : openX86_64.pre s) : openX86_64.pre t := by
  show preX86_64 false t
  have ha := h.arg
  have hb := h.argAddr
  simp only [preX86_64, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp, h.rd, h.wr, ha, hb] at hs ⊢
  exact hs

/-- `open`'s postcondition, through what it reads of the state before. -/
def openPostAt (m : Mem) (key nonce aad al data len : Addr) (tag : BitVec 64) (z : State) : Prop :=
  match Spec.ChaCha20Poly1305.decrypt (Spec.Poly1305.bytesAt m key 32) (Spec.Poly1305.bytesAt m nonce 12)
      (Spec.Poly1305.bytesAt m aad al.toNat) (Spec.Poly1305.bytesAt m data len.toNat)
      (Spec.Poly1305.bytesAt m tag 16) with
  | some pt => (z.gpr .rax).setWidth 32 = 1 ∧ Spec.Poly1305.bytesAt z.mem data len.toNat = pt
  | none => (z.gpr .rax).setWidth 32 = 0

theorem openPost_at (s z : State) :
    openX86_64.post s z = openPostAt s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)
      (s.gpr .r9) (stackArg s 0) z := rfl

theorem FlagsOnly.postO {s t z : State} (h : FlagsOnly s t) (hz : openX86_64.post t z) :
    openX86_64.post s z := by
  rw [openPost_at] at hz ⊢
  rw [h.mem, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.arg] at hz
  exact hz

theorem FlagsOnly.pubO {s₁ s₂ t₁ t₂ : State} (h₁ : FlagsOnly s₁ t₁) (h₂ : FlagsOnly s₂ t₂)
    (hp : openX86_64.pub s₁ s₂) : openX86_64.pub t₁ t₂ := by
  show pubX86_64 t₁ t₂
  simp only [pubX86_64, h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.rsp, h₂.rdi, h₂.rsi, h₂.rdx,
    h₂.rcx, h₂.r8, h₂.r9, h₂.rsp, h₁.arg, h₂.arg]
  exact hp

theorem openSmall_ok (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : ∀ s, openX86_64.pre s → ∃ t s', Exec isa big s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s')
    (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa (openSmall u.callee big) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  have hw : WP isa (openSmall u.callee big) s fun z => abiPreserved s z ∧ openX86_64.post s z := by
    refine WP.seq (WP.mono (cmpOpen_ok u.callee.vl s) fun e ⟨he, hf⟩ => ?_)
    refine WP.ite _ he (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨t, s', ex, ha, hp⟩ := openS_ok u hu e (hf.preO hs)
      rw [hu] at ex
      exact ⟨t, s', ex, hf.abi ha, hf.postO hp⟩
    · obtain ⟨t, s', ex, ha, hp⟩ := hb e (hf.preO hs)
      exact ⟨t, s', ex, hf.abi ha, hf.postO hp⟩
  obtain ⟨t, s', he, hq⟩ := hw
  exact ⟨t, s', he, hq⟩

/-- Pairs of states that `open`'s contract allows, with the same public data. -/
abbrev PPO (s₁ s₂ : State) : Prop := openX86_64.pre s₁ ∧ openX86_64.pre s₂ ∧ openX86_64.pub s₁ s₂

theorem rel_cmpedO {vl : Bool} {c : Prog isa} (hc : ConstantTime isa openX86_64.pre openX86_64.pub c)
    {R : State → State → Prop}
    (hR : ∀ a b, R a b → ∃ σ₁ σ₂, PPO σ₁ σ₂ ∧ CmpedO vl σ₁ a ∧ CmpedO vl σ₂ b) :
    RelCT isa R c fun _ _ => True := by
  intro a b t₁ t₂ a' b' hr e₁ e₂
  obtain ⟨σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, f₁⟩, ⟨-, f₂⟩⟩ := hR a b hr
  exact ⟨hc _ _ _ _ _ _ (f₁.preO p₁) (f₂.preO p₂) (FlagsOnly.pubO f₁ f₂ hp) e₁ e₂, trivial⟩

theorem openSmall_ct (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa} (hb : ConstantTime isa openX86_64.pre openX86_64.pub big) :
    ConstantTime isa openX86_64.pre openX86_64.pub (openSmall u.callee big) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have hblk : RelCT isa PPO (.block (cmpOpen u.callee.vl)) fun _ _ => True := by
    obtain ⟨_, hc⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r9]) (.block (cmpOpen u.callee.vl)) hc).isSome = true := by
      generalize u.callee.vl = vl; cases vl <;> exact ⟨_, by taint_decide⟩
    exact RelCT.taint (A := taint) (Taint.ofRegs [.r9]) (fun s₁ s₂ h => Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2.2.2.2.2.1)) hc
  refine RelCT.seq (RelCT.wpDep (F := CmpedO u.callee.vl) hblk fun s₁ s₂ _ => ⟨cmpOpen_ok _ s₁, cmpOpen_ok _ s₂⟩) ?_
  refine RelCT.ite (fun a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, ⟨e₁, _⟩, ⟨e₂, _⟩⟩ => ?_) ?_ ?_
  · rw [e₁, e₂, show σ₁.gpr .r9 = σ₂.gpr .r9 from hp.2.2.2.2.2.1]
  · have hs := openS_ct u hu
    rw [hu] at hs
    exact rel_cmpedO hs
      fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩
  · exact rel_cmpedO hb fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩

theorem openSmall_verified (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : ∀ s, openX86_64.pre s → ∃ t s', Exec isa big s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s')
    (hc : ConstantTime isa openX86_64.pre openX86_64.pub big) :
    Verified X86_64.target (openSmall u.callee big) (openScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (openSmall_ok u hu hb) (openSmall_ct u hu hc) openS_implies

theorem openSmall_spSafe (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa} (hb : big.all (fun i => !X86_64.isa.writesSp i) = true) :
    (openSmall u.callee big).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := openS_spSafe u hu
  rw [hu] at h
  simp only [openSmall, Code.all, hb, Bool.and_true]
  exact Bool.and_eq_true_iff.mpr ⟨by generalize u.callee.vl = vl; cases vl <;> decide, h⟩

theorem openSmall_xdepth (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa} (hb : big.x86_64Depth ≤ 24) : (openSmall u.callee big).x86_64Depth ≤ 24 := by
  have h := openS_xdepth u
  rw [hu] at h
  simp only [openSmall, Code.x86_64Depth, Nat.max_le]
  exact ⟨by decide, h, hb⟩

/-! ## The IFMA instance's window with the AVX2 code

`openWin big`, as `openSmall`: the comparison writes only `rax` and the
flags. -/

/-- What `ifmaTest` leaves, from `s`. -/
def CmpedW (s t : State) : Prop :=
  isa.eval .b t = some (decide (ifmaLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < ifmaHi)) ∧ FlagsOnly s t

theorem cmpWin_ok (s : State) : WP isa (.block ifmaTest) s (CmpedW s) :=
  WP.mono (ifmaTest_ok s) fun _ ⟨e, g, m, rd, wr, mx⟩ => ⟨e, ⟨fun r h _ => g r h, m, rd, wr, mx⟩⟩

theorem openWin_ok (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : ∀ s, openX86_64.pre s → ∃ t s', Exec isa big s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s')
    (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa (openWin u.callee big) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  have hw : WP isa (openWin u.callee big) s fun z => abiPreserved s z ∧ openX86_64.post s z := by
    refine WP.seq (WP.mono (cmpWin_ok s) fun e ⟨he, hf⟩ => ?_)
    refine WP.ite _ he (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨t, s', ex, ha, hp⟩ := openS_ok u hu e (hf.preO hs)
      rw [hu] at ex
      exact ⟨t, s', ex, hf.abi ha, hf.postO hp⟩
    · obtain ⟨t, s', ex, ha, hp⟩ := hb e (hf.preO hs)
      exact ⟨t, s', ex, hf.abi ha, hf.postO hp⟩
  obtain ⟨t, s', he, hq⟩ := hw
  exact ⟨t, s', he, hq⟩

theorem rel_cmpedW {c : Prog isa} (hc : ConstantTime isa openX86_64.pre openX86_64.pub c)
    {R : State → State → Prop}
    (hR : ∀ a b, R a b → ∃ σ₁ σ₂, PPO σ₁ σ₂ ∧ CmpedW σ₁ a ∧ CmpedW σ₂ b) :
    RelCT isa R c fun _ _ => True := by
  intro a b t₁ t₂ a' b' hr e₁ e₂
  obtain ⟨σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, f₁⟩, ⟨-, f₂⟩⟩ := hR a b hr
  exact ⟨hc _ _ _ _ _ _ (f₁.preO p₁) (f₂.preO p₂) (FlagsOnly.pubO f₁ f₂ hp) e₁ e₂, trivial⟩

theorem openWin_ct (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : ConstantTime isa openX86_64.pre openX86_64.pub big) :
    ConstantTime isa openX86_64.pre openX86_64.pub (openWin u.callee big) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have hblk : RelCT isa PPO (.block ifmaTest) fun _ _ => True := by
    obtain ⟨_, hc⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r9]) (.block ifmaTest) hc).isSome = true :=
      ⟨_, by taint_decide⟩
    exact RelCT.taint (A := taint) (Taint.ofRegs [.r9]) (fun s₁ s₂ h => Taint.agree_ofRegs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.2.2.2.2.2.1)) hc
  refine RelCT.seq (RelCT.wpDep (F := CmpedW) hblk fun s₁ s₂ _ => ⟨cmpWin_ok s₁, cmpWin_ok s₂⟩) ?_
  refine RelCT.ite (fun a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, ⟨e₁, _⟩, ⟨e₂, _⟩⟩ => ?_) ?_ ?_
  · rw [e₁, e₂, show σ₁.gpr .r9 = σ₂.gpr .r9 from hp.2.2.2.2.2.1]
  · have hs := openS_ct u hu
    rw [hu] at hs
    exact rel_cmpedW hs
      fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩
  · exact rel_cmpedW hb fun a b ⟨⟨_, σ₁, σ₂, hp, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, hp, h₁, h₂⟩

theorem openWin_verified (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : ∀ s, openX86_64.pre s → ∃ t s', Exec isa big s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s')
    (hc : ConstantTime isa openX86_64.pre openX86_64.pub big) :
    Verified X86_64.target (openWin u.callee big) (openScratchContract X86_64.abi 212 24) :=
  Verified.of_correct (openWin_ok u hu hb) (openWin_ct u hu hc) openS_implies

theorem openWin_spSafe (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : big.all (fun i => !X86_64.isa.writesSp i) = true) :
    (openWin u.callee big).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := openS_spSafe u hu
  rw [hu] at h
  simp only [openWin, Code.all, hb, Bool.and_true]
  exact Bool.and_eq_true_iff.mpr ⟨by decide, h⟩

theorem openWin_xdepth (u : Proof.ChaCha20.X86_64.XorImpl) (hu : u.poly = .avx2) {big : Prog isa}
    (hb : big.x86_64Depth ≤ 24) : (openWin u.callee big).x86_64Depth ≤ 24 := by
  have h := openS_xdepth u
  rw [hu] at h
  simp only [openWin, Code.x86_64Depth, Nat.max_le]
  exact ⟨by decide, h, hb⟩

/-! ## The `open` of an instance -/

theorem openFor_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) :
    (openFor v.callee v.poly).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h₁ := open_spSafe v
  cases hb : v.poly with
  | avx2 => have h₂ := openS_spSafe v hb; rw [hb] at h₂; exact h₂
  | avx512 =>
    rw [hb] at h₁
    have := openSmall_spSafe v.small v.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | ifma =>
    rw [hb] at h₁
    have := openWin_spSafe Proof.ChaCha20.X86_64.XorImpl.avx512vl.small
      Proof.ChaCha20.X86_64.XorImpl.avx512vl.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | _ => rw [hb] at h₁; exact h₁

theorem openFor_framed (v : Proof.ChaCha20.X86_64.XorImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWipedX 1728 1 42 (openFor v.callee v.poly))
      (Spec.ChaCha20Poly1305.openContract X86_64.abi 1752) := by
  have h₁ := open_framed v
  cases hb : v.poly with
  | avx2 => have h₂ := openS_framed v hb; rw [hb] at h₂; exact h₂
  | avx512 =>
    have ho := open_ok v
    have hc := open_ct v
    have hs := open_spSafe v
    have hd := open_xdepth v
    rw [hb] at ho hc hs hd
    have hv := openSmall_verified v.small v.small_poly ho hc
    have hs' := openSmall_spSafe v.small v.small_poly hs
    have hd' := openSmall_xdepth v.small v.small_poly hd
    rw [Proof.ChaCha20.X86_64.XorImpl.small_callee] at hv hs' hd'
    exact X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
      (n := 212) (post := Spec.ChaCha20Poly1305.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
      (bytes := 1728) (k := 42) hv (by decide) (by decide) (by decide) hs' hd' (by decide) (pre_local _ _) (openPost_local _) (openPost_out _)
      openFrameSat_pre
  | ifma =>
    have ho := open_ok v
    have hc := open_ct v
    have hs := open_spSafe v
    have hd := open_xdepth v
    rw [hb] at ho hc hs hd
    have hp := Proof.ChaCha20.X86_64.XorImpl.avx512vl.small_poly
    have hv := openWin_verified _ hp ho hc
    have hs' := openWin_spSafe _ hp hs
    have hd' := openWin_xdepth _ hp hd
    rw [Proof.ChaCha20.X86_64.XorImpl.small_callee] at hv hs' hd'
    exact X86_64.Verified.stackArgScratchWipedX (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
      (n := 212) (post := Spec.ChaCha20Poly1305.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
      (bytes := 1728) (k := 42) hv (by decide) (by decide) (by decide) hs' hd' (by decide) (pre_local _ _) (openPost_local _) (openPost_out _)
      openFrameSat_pre
  | _ => rw [hb] at h₁; exact h₁

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
