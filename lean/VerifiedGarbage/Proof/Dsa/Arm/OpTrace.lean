module

import VerifiedGarbage.Proof.Dsa.Arm.CoreTrace
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Proof.Dsa.Arm.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# DSA on 32-bit ARM: the traces of the entry, the dispatch and the exit

The entry reads the stack arguments, the same in both runs, and stores
through `r12`, which it loads from them. The dispatch compares the public
widths in the header, the same in both runs; the exit (`Tail`) loads the
saved registers through `r12`. Each part of the dispatch is followed by the
exit (`widthDispatch_trace`), so that the proof of each width's code goes on
to it with what that code's correctness says of both runs.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)

/-- The operation after the dispatch: the registers restored. -/
abbrev Tail : Prog isa := .seq (.block Entry.restore) (.block [])

theorem tail_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (h₁ : Ws s₁ base size₁)
    (h₂ : Ws s₂ base size₂) : SameTrace isa Tail s₁ s₂ :=
  SameTrace.of_relCT (RelCT.seq (block_relCT_T0 _ rfl) (RelCT.block_nil (Q := fun _ _ => True) fun _ _ _ => trivial))
    (agree0 h₁ h₂)

/-- An entry: its stack arguments are the same and apart from the writable regions. -/
theorem entry_relCT (n : Nat) (is : List Instr)
    (h : (taint.checkBlock (argTaint [] n) is).map (taint.le (argTaint [] n)) = some true) :
    RelCT isa (VG.Arm.Taint.Agree (argTaint [] n)) (.block is) (fun _ _ => True) :=
  (relCT_of_check (h := .block []) h).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem agree_args {s₁ s₂ : State} {n : Nat} (hsp : s₁.sp = s₂.sp) (hf : s₁.sp.toNat + 4 * n ≤ 2 ^ 32)
    (ha : ∀ i < n, stackArg s₁ i = stackArg s₂ i)
    (hw₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨State.addr s₁.sp, 4 * n⟩ r)
    (hw₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨State.addr s₂.sp, 4 * n⟩ r) :
    VG.Arm.Taint.Agree (argTaint [] (4 * n)) s₁ s₂ :=
  agree_argTaint (fun _ h => (List.not_mem_nil h).elim) hsp ⟨hf, hw₁⟩ ⟨hsp ▸ hf, hw₂⟩ (argMem_of hsp hf ha)

/-! ## The dispatch -/

theorem widthMatch_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ pLen wp wq : Nat}
    (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁) (hz₂ : 120 ≤ size₂)
    (hp₁ : (hdr base s₁ 100).toNat = pLen) (hp₂ : (hdr base s₂ 100).toNat = pLen)
    (bp : wp < 2 ^ 16) :
    SameTrace isa (Entry.widthMatch wp wq) s₁ s₂ := by
  unfold Entry.widthMatch
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (σ := T0) (c₀ := .block [.ldr .r4 .r12 0, .movw .r5 0,
      .cmp .r4 (.reg .r5)]) (VG.Taint.hintOf taint T0 (.block [.ldr .r4 .r12 0, .movw .r5 0, .cmp .r4 (.reg .r5)]))
      rfl (wsT_noBase _ _) rfl) (agree0 h₁ h₂))
    (matchOne_ok (d := 100) h₁ (by decide) (by omega) bp) (matchOne_ok (d := 100) h₂ (by decide) (by omega) bp)
    fun u₁ u₂ ⟨Z₁, R₁, _⟩ ⟨Z₂, R₂, _⟩ => ?_
  have w₁ := h₁.of_rest R₁ (by decide)
  have w₂ := h₂.of_rest R₂ (by decide)
  refine SameTrace.ite (by rw [eval_eq, eval_eq, Z₁, Z₂, hp₁, hp₂]) (fun _ => ?_) (fun _ => ?_)
  · exact SameTrace.of_relCT (erased_relCT (σ := T0) (c₀ := .block [.ldr .r4 .r12 0, .movw .r5 0,
      .cmp .r4 (.reg .r5)]) (VG.Taint.hintOf taint T0 (.block [.ldr .r4 .r12 0, .movw .r5 0, .cmp .r4 (.reg .r5)]))
      rfl (wsT_noBase _ _) rfl) (agree0 w₁ w₂)
  · exact SameTrace.of_relCT (block_relCT_T0 _ rfl) (agree0 w₁ w₂)

theorem widthDispatch_trace (signing : Bool) (widths : List (Nat × Nat))
    {s₁ s₂ : State} {base : Addr} {size₁ size₂ pLen qLen : Nat}
    (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁) (hz₂ : 120 ≤ size₂)
    (member : (pLen, qLen) ∈ widths) (bound : ∀ w ∈ widths, w.1 < 2 ^ 16 ∧ w.2 < 2 ^ 16)
    (hp₁ : (hdr base s₁ 100).toNat = pLen) (hq₁ : (hdr base s₁ 104).toNat = qLen)
    (hp₂ : (hdr base s₂ 100).toNat = pLen) (hq₂ : (hdr base s₂ 104).toNat = qLen)
    (body : ∀ t₁ t₂, Rest [.r4, .r5] s₁ t₁ → t₁.mem = s₁.mem → Rest [.r4, .r5] s₂ t₂ → t₂.mem = s₂.mem →
      SameTrace isa (.seq (Entry.sized signing pLen qLen) Tail) t₁ t₂) :
    SameTrace isa (.seq (Entry.widthDispatch signing widths) Tail) s₁ s₂ := by
  induction widths generalizing s₁ s₂ with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    unfold Entry.widthDispatch
    refine SameTrace.assoc_left (SameTrace.seq (widthMatch_trace h₁ h₂ hz₁ hz₂ hp₁ hp₂ B.1)
      (widthMatch_ok h₁ hz₁ hp₁ hq₁ B.1 B.2) (widthMatch_ok h₂ hz₂ hp₂ hq₂ B.1 B.2)
      fun t₁ t₂ ⟨Z₁, R₁, M₁⟩ ⟨Z₂, R₂, M₂⟩ => ?_)
    refine SameTrace.seq_ite (by rw [eval_eq, eval_eq, Z₁, Z₂]) (fun ht => ?_) (fun hf => ?_)
    · have Both : pLen = wp ∧ qLen = wq := of_decide_eq_true (by rw [eval_eq, Z₁] at ht; exact Option.some.inj ht)
      rw [← Both.1, ← Both.2]
      exact body t₁ t₂ R₁ M₁ R₂ M₂
    · have Both : ¬ (pLen = wp ∧ qLen = wq) :=
        of_decide_eq_false (by rw [eval_eq, Z₁] at hf; exact Option.some.inj hf)
      exact ih (h₁.of_rest R₁ (by decide)) (h₂.of_rest R₂ (by decide))
        (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member)
        (fun w hw => bound w (List.mem_cons_of_mem _ hw))
        (by simp only [hdr, M₁]; exact hp₁) (by simp only [hdr, M₁]; exact hq₁)
        (by simp only [hdr, M₂]; exact hp₂) (by simp only [hdr, M₂]; exact hq₂)
        fun u₁ u₂ Ru₁ Mu₁ Ru₂ Mu₂ => body u₁ u₂ (R₁.trans Ru₁) (Mu₁.trans M₁) (R₂.trans Ru₂) (Mu₂.trans M₂)

/-! ## The failure -/

theorem failureHead_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size) :
    WP isa (.block [.ldr .r11 .r12 (Layout.field .out), .ldr .r4 .r12 (Layout.field .qLen),
      .dp .add .lr .r11 (.reg .r4), .dp .add .lr .lr (.reg .r4), .mov .r4 (.imm 0)]) s fun t =>
      t.gpr .r11 = hdr base s 96 ∧ t.gpr .lr = hdr base s 96 + hdr base s 104 + hdr base s 104 ∧
      Ws t base size := by
  refine wp_ldr12 hs (d := 96) (by decide) (by omega) fun u₁ v₁ => ?_
  refine wp_ldr12 (hs.of_upd v₁ (by decide)) (d := 104) (by decide) (by omega) fun u₂ v₂ => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u₃ v₃ =>
    VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u₄ v₄ =>
    VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u₅ v₅ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v₅.other .r11 (by decide), v₄.other .r11 (by decide), v₃.other .r11 (by decide),
      v₂.other .r11 (by decide), v₁.gpr]
  · rw [v₅.other .lr (by decide), v₄.gpr, VG.Proof.X25519.Arm.dpVal, v₃.gpr, VG.Proof.X25519.Arm.dpVal,
      v₃.other .r4 (by decide), v₂.gpr, v₂.other .r11 (by decide), v₁.gpr,
      show hdr base u₁ 104 = hdr base s 104 by simp only [hdr, v₁.mem]]
  · exact ((((hs.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄ (by decide)).of_upd
      v₅ (by decide)

theorem failure_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (signing : Bool)
    (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁) (hz₂ : 120 ≤ size₂)
    (ho : signing = true → hdr base s₁ 96 = hdr base s₂ 96)
    (hq : signing = true → hdr base s₁ 104 = hdr base s₂ 104) :
    SameTrace isa (.seq (Entry.failure signing) Tail) s₁ s₂ := by
  cases signing
  · exact SameTrace.of_relCT (RelCT.seq (block_relCT_T0 _ rfl) (RelCT.seq (block_relCT_T0 _ rfl)
      (RelCT.block_nil (Q := fun _ _ => True) fun _ _ _ => trivial))) (agree0 h₁ h₂)
  · simp only [Entry.failure, ↓reduceIte, Core.sequence, List.foldr]
    refine SameTrace.assoc_left (SameTrace.seq (SameTrace.of_relCT (block_relCT_T0 _ rfl) (agree0 h₁ h₂))
      (failureHead_ok h₁ hz₁) (failureHead_ok h₂ hz₂) fun u₁ u₂ ⟨A₁, L₁, w₁⟩ ⟨A₂, L₂, w₂⟩ => ?_)
    exact SameTrace.of_relCT ((relCT_of_check (σ := Taint.ofRegs []) (h := VG.Taint.hintOf taint (wsT true true)
      (.seq (.seq (.loop (.block [.strb .r4 .r11 0, .dp .add .r11 .r11 (.imm 1), .cmp .r11 (.reg .lr)]) .ne)
        (.seq (.block [.mov .r0 (.imm 0)]) (.block []))) Tail)) rfl).mono (fun _ _ h => h) fun _ _ _ => trivial)
      (agreeWs true true w₁ w₂ (fun _ => by rw [A₁, A₂, ho rfl]) (fun _ => by rw [L₁, L₂, ho rfl, hq rfl]))

end VG.Proof.Dsa.Arm
