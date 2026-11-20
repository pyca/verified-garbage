module

public import VerifiedGarbage.Proof.Mcdt.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMx
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueMx
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
meta import VerifiedGarbage.Proof.Mcdt.X86_64
meta import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.CallBody

/-!
# A call of `vg_mcdt_enter` as an operation of the taint analyses (x86-64)

Code that calls `vg_mcdt_enter` itself (`Spec/Mcdt.lean`, `Rust.mcdtOpen`)
and branches on its result is constant time only because MXCSR, on which
its timing and result depend, is public (`abi.pub`). The taint analyses do
not follow MXCSR, nor its frame of a pushed register: so a call of it is an
operation (`Taint.Op`) whose soundness is proven of its code
(`enter_exec`, `enter_trace`, from `enter_wpX` and `enter_ct`):

* `enterOpMx`, for constant time (`X86_64.taintMx`): from two states that
  agree on `rsp` and MXCSR it leaks the same trace, returns the same `rax`
  and leaves MXCSR the same, and it writes no other register than `rax`,
  `rcx` and `rdx`, no vector register and no writable region, but the stack
  below `rsp` (`enterT`: `rax` public, `rcx`, `rdx`, the flags and the
  public slots forgotten).
* `enterOpR`, for the residue analysis (`X86_64.rtaintMx`): the same, and
  the 16 bytes it writes below `rsp` (its return address, and its frame,
  which it leaves holding MXCSR) hold the same in both runs.
-/

@[expose] public section

namespace VG.Proof.Mcdt.X86_64

open VG VG.X86_64 VG.Impl.Mcdt.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-! ## Its runs -/

theorem pushRegs_unk : ∀ (s : State) (rs : List Reg), (pushRegs s rs).unknowns = s.unknowns
  | _, [] => rfl
  | _, _ :: rs => (pushRegs_unk _ rs).trans rfl

theorem popReg_unk : ∀ (s : State) (d : Reg) (k : Nat), (popReg s d k).unknowns = s.unknowns
  | _, _, 0 => rfl
  | _, d, k + 1 => (popReg_unk _ d k).trans rfl

/-- Every run of `vg_mcdt_enter`: as `enter_wpX` says, keeping the vector
registers. -/
theorem body_exec {s s' : State} {t : List Leak} (h : Exec isa enter s t s') :
    8 ≤ (s.gpr .rsp).toNat ∧ s'.mxcsr = flagged s.mxcsr ∧ s'.gpr .rax = res s.mxcsr ∧
      s'.gpr .rsp = s.gpr .rsp ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = lose (slotW (pushed [.rax] s).mem (s.gpr .rsp - 8) s.mxcsr) (s.gpr .rsp - 8) 8 s.unknowns ∧
      s'.xmm = s.xmm ∧ s'.unknowns = fun n => s.unknowns (n + 2) := by
  have hS : 8 ≤ (s.gpr .rsp).toNat := by
    have h' : Exec isa (.frame (.push [.rax]) body (.pop .rcx 1)) s t s' := h
    cases h' with
    | frame hp _ _ =>
      simp only [isa, push] at hp
      split at hp <;> [rename_i hc; cases hp]
      simpa using hc.2.2
  obtain ⟨_, u, he, hq⟩ := enter_wpX s hS
  obtain ⟨-, e⟩ := Exec.det h he
  subst e
  exact ⟨hS, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2.1,
    Residue.Exec.xmmKeep (c := enter) (by decide) h, hq.2.2.2.2.2.2.2⟩

theorem covers_nil (rs : List Region) : Covers [] rs := fun _ _ ⟨_, h, _⟩ => nomatch h

/-- Two runs of `enter` from states that agree on `rsp` and MXCSR leak the
same trace. -/
theorem body_trace {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak} (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hmx : s₁.mxcsr = s₂.mxcsr) (e₁ : Exec isa enter s₁ t₁ s₁') (e₂ : Exec isa enter s₂ t₂ s₂') :
    t₁ = t₂ := by
  have p₁ : contract.pre (s₁.withRegions [] []) := ⟨rfl, rfl, (body_exec e₁).1⟩
  have p₂ : contract.pre (s₂.withRegions [] []) := ⟨rfl, rfl, (body_exec e₂).1⟩
  obtain ⟨_, f₁⟩ := trace_narrow enter_correct p₁ (covers_nil _) (covers_nil _) e₁
  obtain ⟨_, f₂⟩ := trace_narrow enter_correct p₂ (covers_nil _) (covers_nil _) e₂
  exact enter_ct _ _ _ _ _ _ p₁ p₂ ⟨hsp, hmx⟩ f₁ f₂

/-! ## The clearing after it -/

theorem tail₁_ok (u : State) :
    WP isa (.block [.xop (.bin .pxor .xmm0 .xmm0), .alu32 .xor .r11 (.reg .r11)]) u
      fun v => (v.gpr .r11 = 0 ∧ v.mem = u.mem ∧ v.mxcsr = u.mxcsr ∧ v.unknowns = u.unknowns) ∧
        Keep [.r11] u v :=
  WP.keep [.r11] (Q := fun v => v.gpr .r11 = 0 ∧ v.mem = u.mem ∧ v.mxcsr = u.mxcsr ∧ v.unknowns = u.unknowns)
    (by xrun []; exact ⟨by simp, rfl, rfl, rfl⟩) rfl

theorem tail₃_ok (u : State) :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu32 .xor .rcx (.reg .rcx), .alu32 .xor .rdx (.reg .rdx)]) u
      fun v => (v.gpr .rax = ((u.gpr .rax).setWidth 32).setWidth 64 ∧ v.mem = u.mem ∧ v.mxcsr = u.mxcsr ∧
        v.unknowns = u.unknowns) ∧ Keep [.rax, .rcx, .rdx] u v :=
  WP.keep [.rax, .rcx, .rdx] (Q := fun v => v.gpr .rax = ((u.gpr .rax).setWidth 32).setWidth 64 ∧
    v.mem = u.mem ∧ v.mxcsr = u.mxcsr ∧ v.unknowns = u.unknowns) (by xrun []; exact ⟨rfl, rfl⟩) rfl

theorem tail₂_ok (u : State) (hS : 8 ≤ (u.gpr .rsp).toNat) :
    WP isa (.frame (.alloc 8) (.seq (.block [.store slot .r11]) (.block [])) (.free 8)) u fun v =>
      v.gpr = u.gpr ∧
      v.mem = lose (u.mem.writeW (u.gpr .rsp - BitVec.ofNat 64 8) (u.gpr .r11)) (u.gpr .rsp - BitVec.ofNat 64 8) 8
        u.unknowns ∧ v.mxcsr = u.mxcsr ∧
      v.unknowns = (fun n => u.unknowns (n + 2)) ∧ v.rd = u.rd ∧ v.wr = u.wr := by
  refine alloc_frame_okMem (by decide) hS ?_
  have hw : InRegions (allocState 8 u).wr ((allocState 8 u).gpr .rsp) 8 :=
    ⟨_, List.mem_cons_self, by simp [allocState, Region.Contains, RegUpd.gpr_setReg_self]⟩
  have hr11 : (allocState 8 u).gpr .r11 = u.gpr .r11 := by
    show (u.setReg .rsp (u.gpr .rsp - BitVec.ofNat 64 8)).gpr .r11 = _
    exact RegUpd.gpr_setReg_of_ne _ _ (by decide)
  refine WP.seq (WP.mono (Q := fun t : State => t.gpr = (allocState 8 u).gpr ∧ t.wr = (allocState 8 u).wr ∧
    t.mem = (allocState 8 u).mem.writeW ((allocState 8 u).gpr .rsp) (u.gpr .r11) ∧ t.mxcsr = u.mxcsr ∧
    t.unknowns = u.unknowns ∧ t.rd = u.rd) (by xrun [ea_slot, hw, hr11]; exact ⟨rfl, rfl, rfl⟩) fun t ht => ?_)
  obtain ⟨g, w, m, x, k, r⟩ := ht
  refine WP.block_nil (M := isa) ⟨by rw [g], w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    show (t.setReg .rsp (t.gpr .rsp + BitVec.ofNat 64 8)).gpr q = _
    by_cases hq : q = .rsp
    · subst hq; rw [RegUpd.gpr_setReg_self, g]; exact BitVec.sub_add_cancel _ _
    · rw [RegUpd.gpr_setReg_of_ne _ _ hq, g]; exact RegUpd.gpr_setReg_of_ne _ _ hq
  · show lose t.mem (t.gpr .rsp) 8 t.unknowns = _; rw [m, g, k]; rfl
  · exact x
  · show (fun n => t.unknowns (n + 8 / 4)) = _; rw [k]
  · show t.rd = _; exact r
  · show t.wr.tail = _; rw [w]; rfl

/-- `scrubTail`: `rax`, `rcx`, `rdx` and `r11` written, its 8 bytes of stack
zeroed, nothing else but vector registers written. -/
theorem tail_wp (u : State) (hS : 8 ≤ (u.gpr .rsp).toNat) :
    WP isa scrubTail u fun v => v.gpr .rax = ((u.gpr .rax).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → v.gpr r = u.gpr r) ∧ v.mxcsr = u.mxcsr ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧
      v.mem = lose (u.mem.writeW (u.gpr .rsp - BitVec.ofNat 64 8) (0 : BitVec 64)) (u.gpr .rsp - BitVec.ofNat 64 8) 8
        u.unknowns ∧
      v.unknowns = (fun n => u.unknowns (n + 2)) := by
  unfold scrubTail
  refine WP.seq (WP.mono (tail₁_ok u) fun u₁ ⟨⟨r₁, m₁, x₁, k₁⟩, K₁⟩ => ?_)
  refine WP.seq (WP.block_nil (M := isa) ?_)
  have sp₁ : u₁.gpr .rsp = u.gpr .rsp := K₁.gpr (by decide)
  refine WP.seq (WP.mono (tail₂_ok u₁ (by rw [sp₁]; exact hS)) fun u₂ ⟨g₂, m₂, x₂, k₂, rd₂, wr₂⟩ => ?_)
  refine WP.mono (tail₃_ok u₂) fun v ⟨⟨a₃, m₃, x₃, k₃⟩, K₃⟩ => ?_
  refine ⟨by rw [a₃, g₂, K₁.gpr (by decide)], fun r h1 h2 h3 h4 => ?_, by rw [x₃, x₂, x₁], by rw [K₃.2.1, rd₂, K₁.2.1],
    by rw [K₃.2.2, wr₂, K₁.2.2], by rw [m₃, m₂, m₁, sp₁, r₁, k₁], by rw [k₃, k₂, k₁]⟩
  rw [K₃.gpr (by simp [h1, h2, h3]), g₂, K₁.gpr (by simp [h4])]

/-- Two runs of `scrubTail` from states that agree on `rsp` leak the same trace. -/
theorem tail_rel :
    RelCT isa (fun a b => a.gpr .rsp = b.gpr .rsp ∧ 8 ≤ (a.gpr .rsp).toNat) scrubTail fun _ _ => True := by
  unfold scrubTail
  let P : State → State → Prop := fun a b => a.gpr .rsp = b.gpr .rsp ∧ 8 ≤ (a.gpr .rsp).toNat
  have h₁ := RelCT.taintRegs (P := P)
    (c := .block [.xop (.bin .pxor .xmm0 .xmm0), .alu32 .xor .r11 (.reg .r11)])
    (τ := Taint.ofRegs [.rsp]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact h.1) [.rsp] (by taint_decide)
  have w₁ : ∀ a b, P a b →
      WP isa (.block [.xop (.bin .pxor .xmm0 .xmm0), .alu32 .xor .r11 (.reg .r11)]) a
        (fun t => t.gpr .rsp = a.gpr .rsp) ∧
      WP isa (.block [.xop (.bin .pxor .xmm0 .xmm0), .alu32 .xor .r11 (.reg .r11)]) b
        (fun t => t.gpr .rsp = b.gpr .rsp) :=
    fun a b _ => ⟨WP.mono (tail₁_ok a) fun _ h => h.2.gpr (by decide), WP.mono (tail₁_ok b) fun _ h => h.2.gpr (by decide)⟩
  have s₁ : RelCT isa P (.block [.xop (.bin .pxor .xmm0 .xmm0), .alu32 .xor .r11 (.reg .r11)]) P :=
    (h₁.wpDep (F := fun (σ t : State) => t.gpr .rsp = σ.gpr .rsp) w₁).mono (fun _ _ h => h) fun x y h => by
      obtain ⟨-, σ₁, σ₂, ⟨e, h8⟩, r₁, r₂⟩ := h
      exact ⟨by rw [r₁, r₂, e], by rw [r₁]; exact h8⟩
  have hnil : RelCT isa P (.block []) P := fun _ _ _ _ _ _ hp e₁ e₂ => by
    cases e₁ with
    | block b₁ => cases e₂ with
      | block b₂ =>
        simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at b₁ b₂
        obtain ⟨rfl, rfl⟩ := b₁; obtain ⟨rfl, rfl⟩ := b₂
        exact ⟨rfl, hp⟩
  have hfr : RelCT isa P (.frame (.alloc 8) (.seq (.block [.store slot .r11]) (.block [])) (.free 8))
      fun _ _ => True := by
    refine RelCT.alloc (R := fun _ _ => True) (fun x y t₁ t₂ x' y' ⟨σ₁, σ₂, ⟨e, _⟩, hx, hy⟩ e₁ e₂ => ?_)
    subst hx hy
    exact RelCT.taint (A := taint) (P := fun a b => a.gpr .rsp = b.gpr .rsp) (Taint.ofRegs [.rsp])
      (fun _ _ h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact h)
      (c := .seq (.block [.store slot .r11]) (.block [])) (by taint_decide) _ _ _ _ _ _
      (by simp only [allocState, RegUpd.gpr_setReg_self, e]) e₁ e₂
  have hfr' : RelCT isa P (.frame (.alloc 8) (.seq (.block [.store slot .r11]) (.block [])) (.free 8)) P :=
    (hfr.wpDep (F := fun (σ t : State) => t.gpr .rsp = σ.gpr .rsp) fun a b h =>
      ⟨WP.mono (tail₂_ok a h.2) fun _ q => by rw [q.1], WP.mono (tail₂_ok b (by rw [← h.1]; exact h.2))
        fun _ q => by rw [q.1]⟩).mono (fun _ _ h => h) fun x y h => by
      obtain ⟨-, σ₁, σ₂, ⟨e, h8⟩, r₁, r₂⟩ := h
      exact ⟨by rw [r₁, r₂, e], by rw [r₁]; exact h8⟩
  exact s₁.seq (hnil.seq (hfr'.seq (RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs fun _ h => by cases h)
    (c := .block [.mov32 .rax (.reg .rax), .alu32 .xor .rcx (.reg .rcx), .alu32 .xor .rdx (.reg .rdx)])
    (by taint_decide))))

/-- Every run of a call's code of `vg_mcdt_enter` (`enterCall`): MXCSR
`flagged`, `rax` its result, no register but `rax`, `rcx`, `rdx` and `r11`
written, nor any memory but the 8 bytes below `rsp`, which it zeroes and the
release of its frame then loses. -/
theorem enter_exec {s s' : State} {t : List Leak} (h : Exec isa enterCall s t s') :
    8 ≤ (s.gpr .rsp).toNat ∧ s'.mxcsr = flagged s.mxcsr ∧
      s'.gpr .rax = ((res s.mxcsr).setWidth 32).setWidth 64 ∧ s'.gpr .rsp = s.gpr .rsp ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = lose ((lose (slotW (pushed [.rax] s).mem (s.gpr .rsp - 8) s.mxcsr) (s.gpr .rsp - 8) 8
        s.unknowns).writeW (s.gpr .rsp - BitVec.ofNat 64 8) (0 : BitVec 64)) (s.gpr .rsp - BitVec.ofNat 64 8) 8
        (fun n => s.unknowns (n + 2)) ∧
      s'.unknowns = (fun n => s.unknowns (n + 4)) := by
  have h' : Exec isa (.seq enter scrubTail) s t s' := h
  cases h' with
  | seq e₁ e₂ =>
    rename_i u _ _
    obtain ⟨hS, mx, ax, sp, g, rd, wr, m, -, k⟩ := body_exec e₁
    obtain ⟨_, v, he, q⟩ := tail_wp u (by rw [sp]; exact hS)
    obtain ⟨-, rfl⟩ := Exec.det e₂ he
    obtain ⟨ax', g', mx', rd', wr', m', k'⟩ := q
    refine ⟨hS, by rw [mx', mx], by rw [ax', ax], by rw [g' _ (by decide) (by decide) (by decide) (by decide), sp],
      fun r h1 h2 h3 h4 => by rw [g' r h1 h2 h3 h4, g r h1 h2 h3], by rw [rd', rd], by rw [wr', wr],
      by rw [m', m, sp, k], by rw [k', k]⟩

/-- Two runs of a call's code of `vg_mcdt_enter` from states that agree on
`rsp` and MXCSR leak the same trace. -/
theorem enter_trace {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak} (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hmx : s₁.mxcsr = s₂.mxcsr) (e₁ : Exec isa enterCall s₁ t₁ s₁') (e₂ : Exec isa enterCall s₂ t₂ s₂') :
    t₁ = t₂ := by
  have f₁ : Exec isa (.seq enter scrubTail) s₁ t₁ s₁' := e₁
  have f₂ : Exec isa (.seq enter scrubTail) s₂ t₂ s₂' := e₂
  cases f₁ with
  | seq a₁ b₁ =>
    cases f₂ with
    | seq a₂ b₂ =>
      obtain ⟨h8, -, -, sp₁, -⟩ := body_exec a₁
      obtain ⟨-, -, -, sp₂, -⟩ := body_exec a₂
      rw [body_trace hsp hmx a₁ a₂,
        (tail_rel _ _ _ _ _ _ ⟨by rw [sp₁, sp₂, hsp], by rw [sp₁]; exact h8⟩ b₁ b₂).1]

/-! ## For constant time -/

namespace Op

open VG.X86_64.Taint

/-- What `vg_mcdt_enter` leaves public of `τ` (at its entry): `rax`, its
result, but not `rcx` and `rdx`, nor the flags or any public slot. -/
def enterT (τ : T) : T :=
  ⟨(((τ.regs.erase .rcx).erase .rdx).erase .r11).insert .rax, false, τ.lens,
    τ.bases.filter (fun p => !regEq p.1 .rax && !regEq p.1 .rcx && !regEq p.1 .rdx && !regEq p.1 .r11), [],
    .empty, .empty⟩

/-- The analysis of the body of `vg_mcdt_enter`, from `rsp` public. -/
def bodyMx (τ : T) : Option T := if pub τ .rsp then some (enterT τ) else none

theorem not_rax_of {p : Reg × Nat × Nat}
    (h : (!regEq p.1 .rax && !regEq p.1 .rcx && !regEq p.1 .rdx && !regEq p.1 .r11) = true) :
    p.1 ≠ .rax ∧ p.1 ≠ .rcx ∧ p.1 ≠ .rdx ∧ p.1 ≠ .r11 := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', regEq_eq, beq_eq_false_iff_ne] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Two states after `vg_mcdt_enter` agree on what `enterT τ` says is public,
from states that agree on `τ` with `rsp` public: they have kept every register
but `rax`, `rcx` and `rdx`, the vector registers and the writable regions, and
agree on `rax`. -/
theorem agree_enterT {τ : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (g₁ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s₁'.gpr r = s₁.gpr r)
    (g₂ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s₂'.gpr r = s₂.gpr r)
    (hax : s₁'.gpr .rax = s₂'.gpr .rax) (wr₁ : s₁'.wr = s₁.wr) (wr₂ : s₂'.wr = s₂.wr) :
    Agree (enterT τ) s₁' s₂' := by
  have kb : ∀ {s s' : State}, (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.wr = s.wr → Wf τ s → Wf (enterT τ) s' := by
    intro s s' g hw w
    refine ⟨fun hl => hw ▸ w.1 hl, fun p hp' => ?_⟩
    obtain ⟨hp₁, hp₂⟩ := List.mem_filter.mp (show p ∈ τ.bases.filter _ from hp')
    obtain ⟨n₁, n₂, n₃, n₄⟩ := not_rax_of hp₂
    rw [g _ n₁ n₂ n₃ n₄, show region s' p.2.1 = region s p.2.1 by simp only [region, hw]]
    exact w.2 p hp₁
  refine ⟨⟨fun r hr => ?_, fun h => (by cases h)⟩, fun hl => ?_, kb g₁ wr₁ ha.wf₁,
    kb g₂ wr₂ ha.wf₂, fun _ h => (by cases h), fun _ h => (by cases h), noLo, noXr⟩
  · have hr' : r = .rax ∨ (r ≠ .r11 ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ∈ τ.regs) := by
      simpa only [enterT, RegSet.mem_insert, RegSet.mem_erase, and_assoc] using hr
    rcases hr' with rfl | ⟨n₄, n₂, n₃, hr⟩
    · exact hax
    · by_cases n₁ : r = .rax
      · subst n₁; exact hax
      · rw [g₁ r n₁ n₃ n₂ n₄, g₂ r n₁ n₃ n₂ n₄]; exact ha.rf.1 r hr
  · rw [wr₁, wr₂]; exact ha.wr hl

theorem bodyMx_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak} (hb : bodyMx τ = some τ')
    (ha : AgreeMx τ s₁ s₂) (e₁ : Exec isa enterCall s₁ t₁ s₁') (e₂ : Exec isa enterCall s₂ t₂ s₂') :
    t₁ = t₂ ∧ AgreeMx τ' s₁' s₂' := by
  unfold bodyMx at hb
  split at hb <;> [rename_i hp; cases hb]
  cases hb
  obtain ⟨-, mx₁, ax₁, -, g₁, -, wr₁, -⟩ := enter_exec e₁
  obtain ⟨-, mx₂, ax₂, -, g₂, -, wr₂, -⟩ := enter_exec e₂
  exact ⟨enter_trace (ha.1.reg hp) ha.2 e₁ e₂,
    agree_enterT ha.1 g₁ g₂ (by rw [ax₁, ax₂, ha.2]) wr₁ wr₂, by rw [mx₁, mx₂, ha.2]⟩

theorem enterT_mono {τ σ : T} (h : Le τ σ) : Le (enterT τ) (enterT σ) := by
  refine ⟨⟨RegSet.insert_mono (RegSet.erase_mono (RegSet.erase_mono (RegSet.erase_mono h.regs _) _) _) _,
    fun e => (by cases e), ?_, fun x hx => ?_, fun _ hx => (by cases hx), RegSet.empty_subset _,
    RegSet.empty_subset _⟩, h.fn.filter _⟩
  · rcases h.lens with e | ⟨e, -⟩
    · exact .inl e
    · exact .inr ⟨e, rfl⟩
  · obtain ⟨hx₁, hx₂⟩ := List.mem_filter.mp (show x ∈ τ.bases.filter _ from hx)
    exact List.mem_filter.mpr ⟨h.bases x hx₁, hx₂⟩

/-- What a frame `F` that holds none of `rcx`, `rdx` and `r11` (and only
registers) says is public stays public. -/
theorem enterT_keeps {F Φ σ : T} (hk : regOnly F = true)
    (hcx : F.regs.mem .rcx = false) (hdx : F.regs.mem .rdx = false) (h11 : F.regs.mem .r11 = false)
    (hΦF : Le Φ F) (hΦ : Le Φ σ) : Le Φ (enterT σ) :=
  le_of_frame hk hΦF (RegSet.subset_insert_of (RegSet.subset_erase_of hΦF.regs (RegSet.subset_erase_of hΦF.regs
    (RegSet.subset_erase_of hΦF.regs hΦ.regs hcx) hdx) h11) _) (hΦ.fn.filter _)

end Op

open Op Taint in
/-- A call of `vg_mcdt_enter`, as an operation of `taintMx`. -/
def enterOpMx : VG.Taint.Op isa taintMx.T where
  code := .call "vg_mcdt_enter" enterCall
  f τ := (callStep τ).bind fun τ₁ => (bodyMx τ₁).bind retStep
  keeps F := regOnly F && !F.regs.mem .rcx && !F.regs.mem .rdx && !F.regs.mem .r11

open Op Taint in
theorem enterOpMx_ok : VG.Taint.OpOk taintMx enterOpMx := by
  refine ⟨fun τ τ' hf => ?_, fun {τ σ τ'} hle hf => ?_, fun {F Φ σ σ'} hk hΦF hΦ hf => ?_⟩
  · have hf : ((callStep τ).bind fun τ₁ => (bodyMx τ₁).bind retStep) = some τ' := hf
    obtain ⟨τ₁, h₁, h₂'⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨τ₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h₂'
    intro s₁ s₂ t₁ t₂ s₁' s₂' ha e₁ e₂
    cases e₁ with
    | call hc₁ b₁ hr₁ =>
      cases e₂ with
      | call hc₂ b₂ hr₂ =>
        obtain ⟨a₁, ha₁⟩ := taintMx.call_sound ha h₁ hc₁ hc₂
        obtain ⟨rfl, ha₂⟩ := bodyMx_sound h₂ ha₁ b₁ b₂
        obtain ⟨a₃, ha₃⟩ := taintMx.ret_sound ha₂ h₃ hr₁ hr₂
        exact ⟨by rw [a₁, a₃], ha₃⟩
  · have hl : Le τ σ := leS_iff.mp hle
    have hf : ((callStep τ).bind fun τ₁ => (bodyMx τ₁).bind retStep) = some τ' := hf
    obtain ⟨τ₁, h₁, h₂'⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨τ₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h₂'
    obtain ⟨σ₁, h₁', hl₁⟩ := callStep_mono hl h₁
    unfold bodyMx at h₂
    split at h₂ <;> [rename_i hp; cases h₂]
    cases h₂
    obtain ⟨σ₃, h₃', hl₃⟩ := retStep_mono (enterT_mono hl₁) h₃
    refine ⟨σ₃, ?_, leS_iff.mpr hl₃⟩
    show ((callStep σ).bind fun τ₁ => (bodyMx τ₁).bind retStep) = some σ₃
    rw [h₁', Option.bind_some, bodyMx]
    simp only [hl₁.toLeW.pubM hp, ↓reduceIte, Option.bind_some, h₃']
  · simp only [enterOpMx, Bool.and_eq_true, Bool.not_eq_true'] at hk
    obtain ⟨⟨⟨hk, hcx⟩, hdx⟩, h11⟩ := hk
    have hf : ((callStep σ).bind fun τ₁ => (bodyMx τ₁).bind retStep) = some σ' := hf
    obtain ⟨σ₁, h₁, h₂'⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨σ₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h₂'
    have k₁ := VG.Taint.LeFrame.call_keeps (A := taintS) (F := F) hk hΦF hΦ h₁
    unfold bodyMx at h₂
    split at h₂ <;> [skip; cases h₂]
    cases h₂
    have k₂ := enterT_keeps hk hcx hdx h11 (leS_iff.mp hΦF) (leS_iff.mp k₁)
    exact VG.Taint.LeFrame.ret_keeps (A := taintS) (F := F) hk hΦF (leS_iff.mpr k₂) h₃

/-! ## For the residue analysis -/

namespace Op

open VG.X86_64.Taint VG.X86_64.RTaint

/-- What `vg_mcdt_enter` leaves of `τ` (at its entry), in the residue
analysis: `enterT` of its base taint, and no bounds or flags known of the
registers it writes. -/
def enterR (τ : FT) : FT :=
  let ub := τ.ub.filter (fun p => p.1 != .rax && p.1 != .rcx && p.1 != .rdx && p.1 != .r11)
  { τ with t := enterT τ.t, ub := ub, fl := none }

/-- The residue analysis of the body of `vg_mcdt_enter`, which writes the 8
bytes below `rsp` (in the window). -/
def bodyR (τ : FT) : Option FT := if τ.ok && 8 ≤ τ.room then some (enterR τ) else none

/-- What a call's code of `vg_mcdt_enter` leaves in memory: the 8 bytes below
`rsp`, zeroed, and nothing else. -/
theorem enter_mem {s s' : State} {t : List Leak} (h : Exec isa enterCall s t s') :
    ∀ y, ¬ (y - (s.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s'.mem y = s.mem y := by
  intro y hy
  obtain ⟨-, -, -, -, -, -, -, hm, -⟩ := enter_exec h
  have hy' : ¬ (y - (s.gpr .rsp - 8)).toNat < 8 := by simpa using hy
  have h4 : ¬ (y - (s.gpr .rsp - 8)).toNat < 32 / 8 := fun h => hy' (by omega)
  have h8 : ¬ (y - (s.gpr .rsp - 8)).toNat < 64 / 8 := fun h => hy' (by omega)
  have hp : (pushed [.rax] s).mem = s.mem.writeW (s.gpr .rsp - 8) (s.gpr .rax) := rfl
  rw [hm, lose_out (a := s.gpr .rsp - BitVec.ofNat 64 8) (n := 8) (x := y) (by omega),
    writeW_out (by simpa using hy), lose_out (a := s.gpr .rsp - 8) (n := 8) (x := y) (by omega), hp]
  unfold slotW
  split <;> simp only [writeW_out h4, writeW_out h8]

theorem enter_slot {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak} (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hu : s₁.unknowns = s₂.unknowns)
    (e₁ : Exec isa enterCall s₁ t₁ s₁') (e₂ : Exec isa enterCall s₂ t₂ s₂') :
    ∀ y, (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s₁'.mem y = s₂'.mem y := by
  intro y hy
  obtain ⟨-, -, -, -, -, -, -, hm₁, -⟩ := enter_exec e₁
  obtain ⟨-, -, -, -, -, -, -, hm₂, -⟩ := enter_exec e₂
  have hy' : ((y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 64 / 8) = True := eq_true hy
  rw [hm₁, hm₂, ← hsp, ← hu]
  exact lose_congr _ _ _ (by simp only [Mem.writeW, Mem.write, hy', ↓reduceIte])

theorem bodyR_sound {τ τ' : FT} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak} (hb : bodyR τ = some τ')
    (ha : AgreeMx τ s₁ s₂) (e₁ : Exec isa enterCall s₁ t₁ s₁') (e₂ : Exec isa enterCall s₂ t₂ s₂') :
    t₁ = t₂ ∧ AgreeMx τ' s₁' s₂' := by
  unfold bodyR at hb
  split at hb <;> [rename_i hc; cases hb]
  cases hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hok, h8⟩ := hc
  have inv := ha.1 hok
  obtain ⟨-, mx₁, ax₁, sp₁, g₁, -, wr₁, -, u₁⟩ := enter_exec e₁
  obtain ⟨-, mx₂, ax₂, sp₂, g₂, -, wr₂, -, u₂⟩ := enter_exec e₂
  refine ⟨enter_trace inv.rsp ha.2 e₁ e₂, fun _ => ?_, by rw [mx₁, mx₂, ha.2]⟩
  have hroom := inv.room
  have hout₁ := enter_mem e₁
  have hout₂ : ∀ y, ¬ (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s₂'.mem y = s₂.mem y := by
    rw [inv.rsp]; exact enter_mem e₂
  have hin := enter_slot inv.rsp inv.unk e₁ e₂
  have hm : ∀ y, (s₁'.mem y = s₁.mem y ∧ s₂'.mem y = s₂.mem y) ∨ s₁'.mem y = s₂'.mem y := by
    intro y
    by_cases hy : (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8
    · exact .inr (hin y hy)
    · exact .inl ⟨hout₁ y hy, hout₂ y hy⟩
  have hfree₁ := below_free' inv (n := 8) h8
  have hrg : ∀ i, region s₁' i = region s₁ i := fun i => by simp only [region, wr₁]
  have hwa₁ : ∀ (σ : FT) j, σ.room = τ.room → wa s₁' σ j = wa s₁ τ j := fun σ j h => by
    simp only [wa, wb, sp₁, h]
  have hwa₂ : ∀ (σ : FT) j, σ.room = τ.room → wa s₂' σ j = wa s₂ τ j := fun σ j h => by
    simp only [wa, wb, sp₂, h]
  have haa₁ : aa s₁' (enterR τ) = aa s₁ τ := funext fun o => hwa₁ _ _ rfl
  have haa₂ : aa s₂' (enterR τ) = aa s₂ τ := funext fun o => hwa₂ _ _ rfl
  have hwa8 : wa s₁ τ (τ.room - 8) = s₁.gpr .rsp - BitVec.ofNat 64 8 := by
    simp only [wa, wb]; rw [← Offset.sub_ofNat_eq _ h8]
  have hm₁ : ∀ k < τ.an, s₁'.mem (aa s₁ τ k) = s₁.mem (aa s₁ τ k) := fun k hk =>
    hout₁ _ (by rw [← hwa8]; exact aa_sep inv.room (inv.aTop (by omega_using [hk])) hk (by omega_using []))
  have hm₂ : ∀ k < τ.an, s₂'.mem (aa s₁ τ k) = s₂.mem (aa s₁ τ k) := fun k hk =>
    hout₂ _ (by rw [← hwa8]; exact aa_sep inv.room (inv.aTop (by omega_using [hk])) hk (by omega_using []))
  have hreg₁ : ∀ y, (∃ r ∈ s₁.wr, r.Contains y 1) → s₁'.mem y = s₁.mem y :=
    fun y ⟨r, hr, hc⟩ => hout₁ y (fun hy => hfree₁ y hy r hr hc)
  have hreg₂ : ∀ y, (∃ r ∈ s₂.wr, r.Contains y 1) → s₂'.mem y = s₂.mem y :=
    fun y ⟨r, hr, hc⟩ => hout₂ y (fun hy => hfree₁ y hy r (inv.wr ▸ hr) hc)
  have one : ∀ {s s' : State}, (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.wr = s.wr → (∀ y, (∃ r ∈ s.wr, r.Contains y 1) → s'.mem y = s.mem y) →
      (∀ k < τ.an, s'.mem (aa s τ k) = s.mem (aa s τ k)) → aa s' (enterR τ) = aa s τ →
      Wf τ.t s → One τ s → One (enterR τ) s' := by
    intro s s' g hw hr hk ha' hwf o
    refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), mb_out (τ := τ) hwf o inv.mbFit hw hr,
      sp_keep o inv.spFit hk hw ha' rfl⟩
    simp only [enterR, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
    rw [g _ hp.2.1.1.1 hp.2.1.1.2 hp.2.1.2 hp.2.2]; exact o.ub p hp.1
  refine ⟨agree_enterT inv.base g₁ g₂ (by rw [ax₁, ax₂, ha.2]) wr₁ wr₂,
    by rw [sp₁, sp₂, inv.rsp], by rw [u₁, u₂, inv.unk], by rw [wr₁, wr₂, inv.wr],
    fun h => by rw [wr₁]; exact inv.lens h, by rw [wr₁]; exact inv.nfr,
    by rw [sp₁]; exact inv.room, by rw [sp₁]; exact inv.top, fun i hi => by rw [hrg, sp₁]; exact inv.frames i hi,
    fun i h₁ h₂ => ?_, inv.rasIn, inv.rasSorted, fun j hj i hi => ?_, fun j hj hn hw => ?_, inv.mbFit,
    one g₁ wr₁ hreg₁ hm₁ haa₁ inv.base.wf₁ inv.one₁,
    one g₂ wr₂ hreg₂ (by rw [← aa_eq inv.rsp]; exact hm₂) haa₂ inv.base.wf₂ inv.one₂,
    fun i hi => by rw [hrg, hwa₁ (enterR τ) _ rfl]; exact inv.fw i hi, fun h => by rw [sp₁]; exact inv.aTop h,
    aFree_of haa₁ rfl fun k hk r hr => inv.aFree k hk r (by rwa [wr₁] at hr),
    inv.saFit, sa_keep inv hm₁ hm₂ haa₁ haa₂ rfl, inv.spFit,
    inv.pb.out inv.base.wf₁ inv.base.wf₂ wr₁ wr₂ hreg₁ hreg₂ rfl rfl⟩
  · rw [wr₁] at h₂
    have := inv.others i h₁ h₂
    simp only [wb] at this ⊢
    rw [hrg, sp₁]
    exact this
  · simp only [raSlot]
    rw [hwa₁ (enterR τ) _ rfl, hrg]
    exact inv.rasFr j hj i hi
  · rw [wr₁] at hw
    rw [hwa₁ (enterR τ) _ rfl] at hw ⊢
    rw [hwa₂ (enterR τ) _ rfl, ← wa_eq inv.rsp]
    rcases hm (wa s₁ τ j) with ⟨h₁, h₂⟩ | h
    · rw [h₁, h₂]
      have := inv.dead j hj hn hw
      rwa [← wa_eq inv.rsp] at this
    · exact h

end Op

/-- A call of `vg_mcdt_enter`, from a state with 16 bytes of stack below
`rsp` (its return address and its frame): MXCSR `flagged`, every register
but `rax`, `rcx`, `rdx` and `r11` kept, and nothing written but those 16
bytes. -/
theorem call_enter_wp (s : State) (hS : 16 ≤ (s.gpr .rsp).toNat) :
    WP isa (.call "vg_mcdt_enter" enterCall) s fun t =>
      t.gpr .rsp = s.gpr .rsp ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.mxcsr = flagged s.mxcsr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ∀ y, ¬ (y - (s.gpr .rsp - 16)).toNat < 16 → t.mem y = s.mem y := by
  apply WP.callBody
  have hce : s.callEntry.gpr .rsp = s.gpr .rsp - 8 := State.callEntry_rsp s
  have hS' : 8 ≤ (s.callEntry.gpr .rsp).toNat := by
    rw [hce, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, toNat_sub_ofNat (by omega)]; omega
  obtain ⟨_, u₀, he₀, hq₀⟩ := enter_wpX s.callEntry hS'
  obtain ⟨_, u, he₁, -⟩ := tail_wp u₀ (by rw [hq₀.2.2.1]; exact hS')
  have he : Exec isa enterCall s.callEntry _ u := Exec.seq he₀ he₁
  obtain ⟨-, hmx, -, hsp, hg, hrd, hwr, -, -⟩ := enter_exec he
  have hmem := Op.enter_mem he
  rw [hce] at hmem
  have hcm : ∀ y, ¬ (y - (s.gpr .rsp - 8)).toNat < 8 → s.callEntry.mem y = s.mem y := fun y hy => by
    rw [State.callEntry_mem]; exact RTaint.writeW_out (by simpa using hy)
  refine ⟨_, u, he, by rw [hsp, hce], ?_, ?_⟩
  · rw [Mem.readW_congr (m' := s.callEntry.mem) fun i hi => hmem _ (by simp at hi ⊢; bv_omega),
      State.callEntry_mem, Mem.readW_writeW_self64]
  · refine ⟨RegUpd.gpr_setReg_self (s := u) _ _, fun r h1 h2 h3 h4 => ?_, by rw [RegUpd.mxcsr_setReg, hmx]; rfl,
      by rw [RegUpd.rd_setReg, hrd]; rfl, by rw [RegUpd.wr_setReg, hwr]; rfl, fun y hy => ?_⟩
    · by_cases hr : r = .rsp
      · subst hr; exact RegUpd.gpr_setReg_self (s := u) _ _
      · rw [RegUpd.gpr_setReg_of_ne (s := u) _ hr, hg r h1 h2 h3 h4, State.callEntry_gpr _ hr]
    · rw [RegUpd.mem_setReg, hmem y (by simp at hy ⊢; bv_omega), hcm y (by simp at hy ⊢; bv_omega)]

open Op RTaint in
/-- A call of `vg_mcdt_enter`, as an operation of `rtaintMx`. -/
def enterOpR : VG.Taint.Op isa rtaintMx.T where
  code := .call "vg_mcdt_enter" enterCall
  f τ := (callF τ).bind fun τ₁ => (bodyR τ₁).bind retF

open Op RTaint in
theorem enterOpR_sound : VG.Taint.OpSound rtaintMx enterOpR := by
  intro τ τ' hf
  have hf : ((callF τ).bind fun τ₁ => (bodyR τ₁).bind retF) = some τ' := hf
  obtain ⟨τ₁, h₁, h₂'⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨τ₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h₂'
  intro s₁ s₂ t₁ t₂ s₁' s₂' ha e₁ e₂
  cases e₁ with
  | call hc₁ b₁ hr₁ =>
    cases e₂ with
    | call hc₂ b₂ hr₂ =>
      obtain ⟨a₁, ha₁⟩ := rtaintMx.call_sound ha h₁ hc₁ hc₂
      obtain ⟨rfl, ha₂⟩ := bodyR_sound h₂ ha₁ b₁ b₂
      obtain ⟨a₃, ha₃⟩ := rtaintMx.ret_sound ha₂ h₃ hr₁ hr₂
      exact ⟨by rw [a₁, a₃], ha₃⟩

end VG.Proof.Mcdt.X86_64
