module

import VerifiedGarbage.Proof.AesSiv.X86_64.Crypt
public import VerifiedGarbage.Proof.AesSiv.X86_64.Ctr
public import VerifiedGarbage.Proof.AesSiv.X86_64.FinishShort
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Impl.AesSiv.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.Proof.AesSiv.X86_64.Common
import VerifiedGarbage.Proof.CmacAes.X86_64.Subkeys
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
import VerifiedGarbage.Proof.AesSiv.X86_64.FinishLong
import VerifiedGarbage.Proof.AesSiv.X86_64.Call
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesSiv.X86_64.FinishShort
meta import VerifiedGarbage.Proof.AesSiv.X86_64.FinishLong
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Call
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Common
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesSiv.X86_64.Finish`, which this module and modules that import it used -/

section

/-!
# AES-SIV on x86-64: finishing S2V (`finish`)

`finish` branches on `L < 16` to the short case (`finishShort_wp`) or the
long one (`finishLong_wp`), which leave S2V's end at `W + out`. Every
branch and loop in it is on `L`, and the arguments of its calls are the same
in two runs with the same pointers and lengths (`finish_rel`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (k0 zero2 frame_store2)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable {g : Lay} {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem cmp16_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .cmp .r14 (imm 16)] s = some s' ∧ s'.cf = some (decide (L < 16)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cf_arithFlags, h14, sx_ofNat (by decide), toNat_ofNat hL, toNat_ofNat (by decide)]
  all_goals rfl

theorem FinPost.of_mem {s₁ s s' : State} {out : Nat} (hm : s₁.mem = s.mem) (h : FinPost g s₀ C D P W R L out s₁ s') :
    FinPost g s₀ C D P W R L out s s' :=
  ⟨h.regs, hm ▸ h.frame, hm ▸ h.out⟩

theorem finish_wp (v : UpdateImpl) (K : Calls v g) (h : Env g s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s)
    {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish g.x v.callee v.ctr.callee v.ctr.suffix out) s (FinPost g s₀ C D P W R L out s) := by
  obtain ⟨s₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := cmp16_ok hr.r14 h.lt
  have hr₁ : Regs s₀ C D P W R L s₁ := hr.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (L < 16)) cf₁ (fun hb => ?_) (fun hb => ?_)
  · exact WP.mono (finishShort_wp v.ctr K.toCCalls h hr₁ (of_decide_eq_true hb) hout) fun _ p => p.of_mem m₁
  · exact WP.mono (finishLong_wp v K h hr₁ (by have := of_decide_eq_false hb; omega_using [this]) hout) fun _ p => p.of_mem m₁

/-! ## Constant time -/

/-- A slot of the working space below `W + 160`, apart from the state at
`W + out`, keeps its value across an update. -/
theorem upd_keep (v : UpdateImpl) (K : Calls v g) (h : Env g s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) {Q : Addr} {n : Nat}
    (hu : UA g s C (W + BitVec.ofNat 64 out) Q W R n)
    (S : Nat → Prop) (hS : ∀ d, S d → 144 ≤ d ∧ d + 8 ≤ 160) :
    WP isa (.call v.callee.name v.callee.code) s fun s' => Regs s₀ C D P W R L s' ∧
      ∀ d, S d → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
  refine WP.mono (K.upd hu) fun s' h' => ⟨hr.keep h'.saved h'.rd h'.wr, fun d hd => ?_⟩
  have := hS d hd
  have hwW := h.wW
  refine h'.frame.readW (Region.contains_self _ 8) (fun r hr' => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact Offset.disjoint W (by omega_using [hout, this]) (by omega_using [this]) (by omega_using [hout])
  · exact h.dX (by omega_using [this])
  · rw [hr.rsp]; exact (h.stk_w.sub_right (h.sW (by omega_using [this]))).symm

/-- The pair of runs, with the same arguments. -/
abbrev RR (s₀ s₀' : State) (C D P W : Addr) (R L : Nat) (a b : State) : Prop :=
  Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b

theorem short_rel (v : Ctr32Impl) (K : CCalls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hL : L < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (.seq shortTail (shortMac g.x v.callee v.suffix out)) (RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) shortTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hB' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15,
      .rsp]) (.block (zero16 .r15 o ++
        [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm o),
         .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
         .alu .add .r9 (.imm g.x)])) hc).isSome = true := by
    rintro o (rfl | rfl) <;> rcases h.lay with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ := hB' out hout
  have t₁ := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (shortTail_wp h hab.1 hL) fun _ p => p.1, WP.mono (shortTail_wp h' hab.2 hL) fun _ p => p.1⟩
  have mpre {σ x : State} (hσ : Env g σ C D P W R L) (hx : Regs σ C D P W R L x) :
      WP isa (.block (zero16 .r15 out ++
        [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm out),
         .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .mov32 .r8 (imm 16), .mov .r9 (.reg .r15),
         .alu .add .r9 (.imm g.x)])) x fun y => Regs σ C D P W R L y ∧
        FA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W 16 R := by
    obtain ⟨y, run, hy, fa, _⟩ := macPre_ok hσ hx hout
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  have t₂ := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hB).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      FA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W 16 R)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      FA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W 16 R)
    fun a b hab => ⟨mpre h hab.1, mpre h' hab.2⟩
  have t₃ := (K.finRel ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun a b => (Regs s₀ C D P W R L a ∧
      FA g a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W 16 R) ∧
      Regs s₀' C D P W R L b ∧
      FA g b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W 16 R)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2, hab.2.2, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (K.fin _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.rd p.wr,
      WP.mono (K.fin _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.rd p.wr⟩
  exact (t₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((t₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (t₃.mono (fun _ _ h => h) fun _ _ h => h.2))

theorem long_rel (v : UpdateImpl) (K : Calls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (.seq longTail (longMac g.x v.callee v.ctr.callee v.ctr.suffix out)) (RR s₀ s₀' C D P W R L) := by
  have hlt := h.lt
  have hj1 := jOf_le L
  have hwW := h.wW
  obtain ⟨_, hT⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) longTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hM1' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block (zero16 .r15 o ++
        [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
         .mov .rdx (.reg .r15), .alu .add .rdx (imm o), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
         .alu .add .r9 (.imm g.x)])) hc).isSome = true := by
    rintro o (rfl | rfl) <;> rcases h.lay with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM1⟩ := hM1' out hout
  have hM3' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm o), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
        .mov .r9 (.reg .r15), .alu .add .r9 (.imm g.x), .store (at_ .r15 (dbOff + 8)) .r8]) hc).isSome = true := by
    rintro o (rfl | rfl) <;> rcases h.lay with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM3⟩ := hM3' out hout
  have hM4' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14,
      .r15, .rsp]) (.block [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm o), .mov .r9 (.reg .r15), .alu .add .r9 (.imm g.x)]) hc).isSome = true := by
    rintro o (rfl | rfl) <;> rcases h.lay with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM4⟩ := hM4' out hout
  obtain ⟨_, hM2⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hI0⟩ : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hI1⟩ : ∃ hc, (taint.check (Taint.ofRegs []) (.block [.mov32 .r8 (imm 1)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  -- What each run keeps between the calls.
  let A := fun (x : State) => x.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * kOf L)
  let J := fun (x : State) => x.mem.readW (W + BitVec.ofNat 64 (dbOff + 8)) 64 = BitVec.ofNat 64 (jOf L)
  have wT {σ x : State} (hσ : Env g σ C D P W R L) (hx : Regs σ C D P W R L x) :
      WP isa longTail x fun y => Regs σ C D P W R L y ∧ A y :=
    WP.mono (longTail_wp hσ hx hL16) fun _ p => ⟨p.regs, p.a⟩
  have wM1 {σ x : State} (hσ : Env g σ C D P W R L) (hx : Regs σ C D P W R L x) (ha : A x) :
      WP isa (.block (zero16 .r15 out ++
        [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
         .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
         .alu .add .r9 (.imm g.x)])) x fun y => Regs σ C D P W R L y ∧
        UA g y C (W + BitVec.ofNat 64 out) P W R (kOf L) ∧ A y := by
    obtain ⟨y, run, hy, u, m⟩ := m1_ok hσ hx hout hL16 ha
    refine WP.of_runBlock ⟨y, run, hy, u, ?_⟩
    show y.mem.readW _ 64 = _
    rw [m, zero2, (frame_store2 _ _ _).readW (w := 64) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (d := dbOff) (n := 8) (e := out) (k := 16) (by simp only [dbOff]; omega_using [hout])
        (by simp only [dbOff]; omega_using []) (by omega_using [hout])) (by decide)]
    exact ha
  have wU1 {σ x : State} (hσ : Env g σ C D P W R L) (hx : Regs σ C D P W R L x)
      (hu : UA g x C (W + BitVec.ofNat 64 out) P W R (kOf L)) (ha : A x) :
      WP isa (.call v.callee.name v.callee.code) x fun y => Regs σ C D P W R L y ∧ A y :=
    WP.mono (upd_keep v K hσ hx hout hu (fun d => d = dbOff) (fun d hd => by subst hd; decide))
      fun _ p => ⟨p.1, (p.2 dbOff rfl).trans ha⟩
  have wM2 {σ x : State} (hx : Regs σ C D P W R L x) (ha : A x) :
      WP isa (.block [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)]) x fun y => Regs σ C D P W R L y ∧
        y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y := by
    obtain ⟨y, run, r8, cf, g, m, rd, wr⟩ := m2_ok hx.r14 hlt
    exact WP.of_runBlock ⟨y, run, hx.keep (fun r hr => g r (by rintro rfl; simp [calleeSaved] at hr)) rd wr, r8, cf,
      by show y.mem.readW _ 64 = _; rw [m]; exact ha⟩
  have wI {σ x : State} (hx : Regs σ C D P W R L x) (h8 : x.gpr .r8 = 0)
      (hcf : x.cf = some (decide (L < 17))) (ha : A x) :
      WP isa (.ite .b (.block []) (.block [.mov32 .r8 (imm 1)])) x fun y => Regs σ C D P W R L y ∧
        y.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A y :=
    WP.mono (jIte_wp h8 hcf) fun y ⟨r8, g, m, rd, wr⟩ =>
      ⟨hx.keep (fun r hr => g r (by rintro rfl; simp [calleeSaved] at hr)) rd wr, r8,
        by show y.mem.readW _ 64 = _; rw [m]; exact ha⟩
  have wM3 {σ x : State} (hσ : Env g σ C D P W R L) (hx : Regs σ C D P W R L x)
      (h8 : x.gpr .r8 = BitVec.ofNat 64 (jOf L)) (ha : A x) :
      WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
        .mov .r9 (.reg .r15), .alu .add .r9 (.imm g.x), .store (at_ .r15 (dbOff + 8)) .r8]) x fun y => Regs σ C D P W R L y ∧
        UA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W R (jOf L) ∧
        A y ∧ J y := by
    obtain ⟨y, run, hy, u, m⟩ := m3_ok hσ hx hout h8
    refine WP.of_runBlock ⟨y, run, hy, u, ?_, ?_⟩
    · show y.mem.readW _ 64 = _
      rw [m, Mem.readW_writeW_sep (Offset.sep W (d := dbOff) (n := 8) (e := dbOff + 8) (k := 8) (by decide)
        (by decide) (by decide)) (by decide)]
      exact ha
    · show y.mem.readW _ 64 = _
      rw [m, Mem.readW_writeW_self64]
  have wU2 {σ x : State} (hσ : Env g σ C D P W R L) (hx : Regs σ C D P W R L x)
      (hu : UA g x C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W R (jOf L))
      (ha : A x) (hj : J x) :
      WP isa (.call v.callee.name v.callee.code) x fun y => Regs σ C D P W R L y ∧ A y ∧ J y :=
    WP.mono (upd_keep v K hσ hx hout hu (fun d => d = dbOff ∨ d = dbOff + 8)
        (fun d hd => by rcases hd with rfl | rfl <;> decide))
      fun _ p => ⟨p.1, (p.2 dbOff (Or.inl rfl)).trans ha, (p.2 (dbOff + 8) (Or.inr rfl)).trans hj⟩
  have wM4 {σ x : State} (hσ : Env g σ C D P W R L) (hx : Regs σ C D P W R L x) (ha : A x) (hj : J x) :
      WP isa (.block [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .r9 (.reg .r15), .alu .add .r9 (.imm g.x)]) x fun y => Regs σ C D P W R L y ∧
        FA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) W
          (L - 16 * kOf L - 16 * jOf L) R := by
    obtain ⟨y, run, hy, fa, _⟩ := m4_ok hσ hx hout hL16 ha hj
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  -- The relations, segment by segment.
  have rT := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hT).wp (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ A y) (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ A y)
    fun a b hab => ⟨wT h hab.1, wT h' hab.2⟩
  have rM1 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ A a) ∧ Regs s₀' C D P W R L b ∧ A b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hM1).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      UA g y C (W + BitVec.ofNat 64 out) P W R (kOf L) ∧ A y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      UA g y C (W + BitVec.ofNat 64 out) P W R (kOf L) ∧ A y)
    fun a b hab => ⟨wM1 h hab.1.1 hab.1.2, wM1 h' hab.2.1 hab.2.2⟩
  have rU1 := (K.updRel
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      UA g a C (W + BitVec.ofNat 64 out) P W R (kOf L) ∧ A a) ∧
      Regs s₀' C D P W R L b ∧ UA g b C (W + BitVec.ofNat 64 out) P W R (kOf L) ∧ A b)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2.1, hab.2.2.1, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ A y) (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ A y)
    fun a b hab => ⟨wU1 h hab.1.1 hab.1.2.1 hab.1.2.2, wU1 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rM2 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ A a) ∧ Regs s₀' C D P W R L b ∧ A b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hM2).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ y.gpr .r8 = 0 ∧ y.cf = some (decide (L < 17)) ∧ A y)
    fun a b hab => ⟨wM2 hab.1.1 hab.1.2, wM2 hab.2.1 hab.2.2⟩
  have rI := (RelCT.ite (P := fun (a b : State) =>
      (Regs s₀ C D P W R L a ∧ a.gpr .r8 = 0 ∧ a.cf = some (decide (L < 17)) ∧ A a) ∧
      Regs s₀' C D P W R L b ∧ b.gpr .r8 = 0 ∧ b.cf = some (decide (L < 17)) ∧ A b)
    (fun a b hab => by show a.cf = b.cf; rw [hab.1.2.2.1, hab.2.2.2.1])
    (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun _ h => absurd h List.not_mem_nil) hI0)
    (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun _ h => absurd h List.not_mem_nil) hI1)).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ y.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ y.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A y)
    fun a b hab => ⟨wI hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2, wI hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩
  have rM3 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ a.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A a) ∧
      Regs s₀' C D P W R L b ∧ b.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ A b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hM3).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      UA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W R (jOf L) ∧ A y ∧ J y)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      UA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W R (jOf L) ∧ A y ∧ J y)
    fun a b hab => ⟨wM3 h hab.1.1 hab.1.2.1 hab.1.2.2, wM3 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rU2 := (K.updRel
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      UA g a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W R (jOf L) ∧ A a ∧ J a) ∧
      Regs s₀' C D P W R L b ∧
      UA g b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) W R (jOf L) ∧ A b ∧ J b)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2.1, hab.2.2.1, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ A y ∧ J y) (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ A y ∧ J y)
    fun a b hab => ⟨wU2 h hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2, wU2 h' hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩
  have rM4 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧ A a ∧ J a) ∧ Regs s₀' C D P W R L b ∧ A b ∧ J b) _
    (fun a b hab => regs_agree hq hab.1.1 hab.2.1) hM4).wp
    (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧
      FA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) W
        (L - 16 * kOf L - 16 * jOf L) R)
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧
      FA g y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) W
        (L - 16 * kOf L - 16 * jOf L) R)
    fun a b hab => ⟨wM4 h hab.1.1 hab.1.2.1 hab.1.2.2, wM4 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rF := (K.finRel ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun (a b : State) => (Regs s₀ C D P W R L a ∧
      FA g a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) W
        (L - 16 * kOf L - 16 * jOf L) R) ∧ Regs s₀' C D P W R L b ∧
      FA g b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) W
        (L - 16 * kOf L - 16 * jOf L) R)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.2, hab.2.2, by rw [hab.1.1.rsp, hab.2.1.rsp, hq]⟩).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (K.fin _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.rd p.wr,
      WP.mono (K.fin _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.rd p.wr⟩
  exact (rT.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM1.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rU1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rI.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM3.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rU2.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM4.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (rF.mono (fun _ _ h => h) fun _ _ h => h.2))))))))

theorem finish_rel (v : UpdateImpl) (K : Calls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (RR s₀ s₀' C D P W R L) (finish g.x v.callee v.ctr.callee v.ctr.suffix out) (RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block [.alu .cmp .r14 (imm 16)]) hc).isSome = true := ⟨_, by taint_decide⟩
  have w {σ x : State} (hx : Regs σ C D P W R L x) :
      WP isa (.block [.alu .cmp .r14 (imm 16)]) x fun y => Regs σ C D P W R L y ∧ y.cf = some (decide (L < 16)) := by
    obtain ⟨y, run, cf, g, _, rd, wr⟩ := cmp16_ok hx.r14 h.lt
    exact WP.of_runBlock ⟨y, run, hx.keep (fun r _ => by rw [g]) rd wr, cf⟩
  have a := (RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _ (fun a b hab => regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := fun (y : State) => Regs s₀ C D P W R L y ∧ y.cf = some (decide (L < 16)))
    (F₂ := fun (y : State) => Regs s₀' C D P W R L y ∧ y.cf = some (decide (L < 16)))
    fun a b hab => ⟨w hab.1, w hab.2⟩
  refine (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq (RelCT.ite (fun a b hab => by
    show a.cf = b.cf; rw [hab.1.2, hab.2.2]) ?_ ?_)
  · by_cases hL : L < 16
    · exact (short_rel v.ctr K.toCCalls h h' hq hL hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [show isa.eval .b a = a.cf from rfl, hab.1.1.2] at e; simp [hL] at e
  · by_cases hL : L < 16
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [show isa.eval .b a = a.cf from rfl, hab.1.1.2] at e; simp [hL] at e
    · exact (long_rel v K h h' hq (by omega_using [hL]) hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p

end VG.Proof.AesSiv.X86_64

end

end

/-! ### `AesSiv.X86_64.S2vAd`, which this module and modules that import it used -/

section

/-!
# AES-SIV on x86-64: a step of S2V over the associated data

After the CMAC of a component into the working space (`cmacOf_wp`), the code
doubles `D` in place and XORs the CMAC into it, so `D` is then
`dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_wp`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 dblMem dbl_ok dblMem_bytes)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem saved_le : ∀ p ∈ saved, p.2 + 8 ≤ 208 := by decide

theorem saved_ge : ∀ p ∈ saved, 160 ≤ p.2 := by decide

theorem saved_slots : Spill.Slots saved := by decide

theorem saved_all : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ saved.map Prod.fst := by decide

variable {D W : Addr}

theorem one_out' {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw


theorem xorD_ok {s : State} (h12 : s.gpr .r12 = D) (h15 : s.gpr .r15 = W)
    (w₀ : InRegions s.wr D 8) (w₁ : InRegions s.wr (D + BitVec.ofNat 64 8) 8)
    (r₀ : InRegions (s.rd ++ s.wr) D 8) (r₁ : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 8) 8)
    (q₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 128) 8)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 136) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)),
        .store (at_ .r12 0) .rax, .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))),
        .store (at_ .r12 8) .rax] s = some s' ∧
      s'.mem = (s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).writeW
        (D + BitVec.ofNat 64 8)
        ((s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).readW
            (D + BitVec.ofNat 64 8) 64 ^^^
          (s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).readW
            (W + BitVec.ofNat 64 136) 64) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, stOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, k0, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      ite_true, ite_false, h12, h15, w₀, w₁, r₀, r₁, q₀, q₁]
    rfl, ?_⟩
  refine ⟨rfl, fun r hr => ?_, rfl, rfl⟩
  simp [gpr_setReg, hr]

theorem adTail_ok {s : State} (h15 : s.gpr .r15 = W) (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 224) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 112) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 120) 8) (w₂ : InRegions s.wr (W + BitVec.ofNat 64 120) 8) :
    ∃ s', runBlock isa [.mov .rbx (.mem (at_ .r15 ctxOff)),
        .mov .rax (.mem (at_ .r15 adsOff)), .alu .add .rax (imm 16), .store (at_ .r15 adsOff) .rax,
        .mov .rax (.mem (at_ .r15 leftOff)), .alu .sub .rax (imm 1), .store (at_ .r15 leftOff) .rax] s = some s' ∧
      s'.gpr .rbx = s.mem.readW (W + BitVec.ofNat 64 224) 64 ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).writeW
        (W + BitVec.ofNat 64 120)
        ((s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
          (W + BitVec.ofNat 64 120) 64 - 1) ∧
      s'.zf = some ((s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
          (W + BitVec.ofNat 64 120) 64 - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ctxOff, adsOff, leftOff, tOff, imm, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h15, r₀, r₁, w₁, r₂, w₂]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, ite_true, ite_false]
  · simp only [sx_ofNat (show 16 < 2 ^ 31 by decide),
      sx_ofNat (show 1 < 2 ^ 31 by decide)]
    rfl
  · simp only [sx_ofNat (show 16 < 2 ^ 31 by decide), sx_ofNat (show 1 < 2 ^ 31 by decide)]
    rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- `adStep`: `dbl(D)` in place with the CMAC state XORed into it (the
context kept at `W + 224` while `rbx` holds `D`), then the descriptor pointer
at `W + 112` advanced by 16 and the count at `W + 120` decremented, ZF set
when it reaches 0. -/
theorem adStep_wp {s : State} (h12 : s.gpr .r12 = D) (h15 : s.gpr .r15 = W)
    {nW : Nat} (hnW : 256 ≤ nW) (hDw : (⟨D, 16⟩ : Region) ∈ s.wr) (hWw : (⟨W, nW⟩ : Region) ∈ s.wr)
    (hDW : (⟨D, 16⟩ : Region).Disjoint ⟨W, nW⟩) (_wD : D.toNat + 16 ≤ 2 ^ 64) (_wW : W.toNat + nW ≤ 2 ^ 64) :
    WP isa (.block adStep) s fun s' => s'.gpr .rbx = s.gpr .rbx ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 - 1 == 0) ∧
      Spec.Aes.bytesAt s'.mem D 16 =
        Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 128) 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 adsOff) 64 = s.mem.readW (W + BitVec.ofNat 64 adsOff) 64 + 16 ∧
      s'.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 - 1 ∧
      Frame [⟨D, 16⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem := by
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (D + BitVec.ofNat 64 d) 8 :=
    ⟨_, hDw, Offset.contains_base D hd (by omega_arith)⟩
  have inW (d : Nat) (hd : d + 8 ≤ 256) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 :=
    ⟨_, hWw, Offset.contains_base W (by omega_using [hd, hnW]) (by omega_using [hd])⟩
  have rr {a : Addr} (h : InRegions s.wr a 8) : InRegions (s.rd ++ s.wr) a 8 :=
    let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩
  have cD (d : Nat) (hd : d + 8 ≤ 16) : (⟨D, 16⟩ : Region).Contains (D + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base D hd (by omega_arith)
  have dW {d n : Nat} (hd : d + n ≤ 256) (r : Region) (hr : r ∈ [(⟨D, 16⟩ : Region)]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact hDW.symm.sub_left (Offset.sub_base W (by omega_using [hd, hnW]))
  -- The context saved, and `rbx` holding `D`.
  obtain ⟨s₁, run₁, m₁, b₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.store (at_ .r15 ctxOff) .rbx,
      .mov .rbx (.reg .r12)] s = some s₁ ∧ s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 224) (s.gpr .rbx) ∧
      s₁.gpr .rbx = D ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [ctxOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea,
        offset_nat, Option.map_some, h15, inW 224 (by decide), ite_true]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rw [gpr_setReg_self]; exact h12
    · intro r hr; rw [gpr_setReg_of_ne _ _ hr]
    all_goals rfl
  -- The doubling.
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := dbl_ok s₁ b₁ (src := 0) (dst := 0)
    (by rw [rd₁, wr₁]; exact rr (inD 0 (by decide))) (by rw [rd₁, wr₁]; exact rr (inD (0 + 8) (by decide)))
    (by rw [wr₁]; exact inD 0 (by decide)) (by rw [wr₁]; exact inD (0 + 8) (by decide))
  have r12₂ : s₂.gpr .r12 = D := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h12]
  have r15₂ : s₂.gpr .r15 = W := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h15]
  have i₀ := inD 0 (by decide)
  rw [k0] at i₀
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := xorD_ok r12₂ r15₂ (by rw [wr₂, wr₁]; exact i₀)
    (by rw [wr₂, wr₁]; exact inD 8 (by decide)) (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr i₀)
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inD 8 (by decide)))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inW 128 (by decide)))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inW 136 (by decide)))
  have r15₃ : s₃.gpr .r15 = W := by rw [g₃ _ (by decide), r15₂]
  have e₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]
  have ew : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  obtain ⟨s₄, run₄, b₄, m₄, z₄, g₄, rd₄, wr₄⟩ := adTail_ok r15₃ (by rw [e₃]; exact rr (inW 224 (by decide)))
    (by rw [e₃]; exact rr (inW 112 (by decide))) (by rw [ew]; exact inW 112 (by decide))
    (by rw [e₃]; exact rr (inW 120 (by decide))) (by rw [ew]; exact inW 120 (by decide))
  -- What the doubling and the XOR write.
  have fd : Frame [⟨D, 16⟩] s₁.mem s₂.mem := by
    rw [m₂, dblMem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cD 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (cD (0 + 8) (by decide))
  have f₃ : Frame [⟨D, 16⟩] s₁.mem s₃.mem := by
    have c₀ := cD 0 (by decide)
    rw [k0] at c₀
    rw [m₃]
    exact (fd.writeW (List.mem_singleton_self _) _ c₀).writeW (List.mem_singleton_self _) _ (cD 8 (by decide))
  have f₁ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  have f₄ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₃.mem s₄.mem := by
    rw [m₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains W (d := 112) (e := 112) (n := 8)
      (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 120) (e := 112) (n := 8) (k := 16) (by decide)
        (by decide) (by decide))
  -- The slots at `W + 112` and `W + 120` before the tail.
  have sl {d : Nat} (hd : d + 8 ≤ 224) : s₃.mem.readW (W + BitVec.ofNat 64 d) 64 =
      s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (dW (by omega_arith)) (by decide), f₁.readW (Region.contains_self _ _)
      (one_out' (Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith))) (by decide)]
  have sep : Mem.Sep (W + BitVec.ofNat 64 120) (64 / 8) (W + BitVec.ofNat 64 112) (64 / 8) :=
    Offset.sep W (d := 120) (n := 8) (e := 112) (k := 8) (by decide) (by decide) (by decide)
  have l₃ : (s₃.mem.writeW (W + BitVec.ofNat 64 112) (s₃.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
      (W + BitVec.ofNat 64 120) 64 = s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 := by
    rw [Mem.readW_writeW_sep sep (by decide), sl (by decide)]; rfl
  rw [show adsOff = 112 from rfl, show leftOff = 120 from rfl]
  refine WP.of_runBlock ⟨s₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show adStep = [.store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r12)] ++ Impl.CmacAes.X86_64.dbl 0 0 ++
      [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)), .store (at_ .r12 0) .rax,
       .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))), .store (at_ .r12 8) .rax] ++
      [.mov .rbx (.mem (at_ .r15 ctxOff)), .mov .rax (.mem (at_ .r15 adsOff)), .alu .add .rax (imm 16),
       .store (at_ .r15 adsOff) .rax, .mov .rax (.mem (at_ .r15 leftOff)), .alu .sub .rax (imm 1),
       .store (at_ .r15 leftOff) .rax] from rfl, runBlock_append, runBlock_append, runBlock_append, run₁,
      Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄]
  · rw [b₄, f₃.readW (Region.contains_self _ _) (dW (by decide)) (by decide), m₁, Mem.readW_writeW_self64]
  · intro r h₁ h₂ h₃ h₄ h₅
    rw [g₄ r h₁ h₅, g₃ r h₁, g₂ r h₁ h₂ h₃ h₄, g₁ r h₅]
  · rw [rd₄, rd₃, rd₂, rd₁]
  · rw [wr₄, wr₃, wr₂, wr₁]
  · rw [z₄, l₃]; rfl
  · -- The XOR, a word at a time, of `dbl(D)` and the state.
    have sepD : Mem.Sep (D + BitVec.ofNat 64 8) (64 / 8) D (64 / 8) := by
      simpa using Offset.sep D (d := 8) (n := 8) (e := 0) (k := 8) (by decide) (by decide) (by decide)
    have fw : Frame [⟨D, 16⟩] s₂.mem (s₂.mem.writeW D (s₂.mem.readW D 64 ^^^
        s₂.mem.readW (W + BitVec.ofNat 64 128) 64)) := by
      have c₀ := cD 0 (by decide)
      rw [k0] at c₀
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀
    have e136 : W + BitVec.ofNat 64 136 = W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8 := by
      rw [Offset.add_add]
    have d₄ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨D, 16⟩ : Region).Disjoint r :=
      one_out' (hDW.sub_right (Offset.sub_base W (by omega_using [hnW])))
    rw [bytesAt_frame f₄ d₄ (by decide), m₃, Proof.Cmac.bytesAt_store2, Mem.readW_writeW_sep sepD (by decide),
      fw.readW (Region.contains_self _ _) (fun r hr => dW (d := 136) (n := 8) (by decide) r hr) (by decide), e136,
      Proof.Cmac.xor_words]
    have hd := dblMem_bytes s₁.mem D 0 0
    rw [k0] at hd
    have dD : ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)], (⟨D, 16⟩ : Region).Disjoint r :=
      one_out' (hDW.sub_right (Offset.sub_base W (by omega_using [hnW])))
    have d128 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)],
        (⟨W + BitVec.ofNat 64 128, 16⟩ : Region).Disjoint r :=
      one_out' (Offset.disjoint W (by decide) (by omega_arith) (by omega_arith))
    rw [bytesAt_frame fd (fun r hr => dW (d := 128) (n := 16) (by decide) r hr) (by decide), m₂, hd,
      bytesAt_frame f₁ dD (by decide), bytesAt_frame f₁ d128 (by decide), Spec.Siv.dbl, Siv.xor_eq]
  · rw [m₄, Mem.readW_writeW_sep (Offset.sep W (d := 112) (n := 8) (e := 120) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, sl (by decide)]
  · rw [m₄, Mem.readW_writeW_self64, l₃]; rfl
  · refine ((f₁.mono ?_).trans (f₃.mono ?_)).trans (f₄.mono ?_) <;> intro r hr <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;> simp

end VG.Proof.AesSiv.X86_64

end

end

/-!
# AES-SIV on x86-64: the end of `vg_aes_siv_encrypt`

From S2V's state of the associated data on, `encrypt` finishes S2V with the
plaintext into the first 16 bytes of the working space (`finish_wp`), sets
the counter from that IV (`counter_ok`), encrypts the data in place with CTR
(`ctr_wp`) and restores the registers: the working space then starts with
the IV and the data is the ciphertext (`sealTail_wp`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (bytesAt_frame k0)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable {g : Lay} {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## What each step writes -/

/-- The regions the counter's two words are written to. -/
abbrev cntRegions (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 cntOff, 8⟩, ⟨W + BitVec.ofNat 64 (cntOff + 8), 8⟩]

theorem counter_frame (m : Mem) (W : Addr) (a b : BitVec 64) :
    Frame (cntRegions W) m ((m.writeW (W + BitVec.ofNat 64 cntOff) a).writeW (W + BitVec.ofNat 64 (cntOff + 8)) b) :=
  ((Frame.refl _ _).writeW List.mem_cons_self a (Region.contains_self (W + BitVec.ofNat 64 cntOff) 8)).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) b (Region.contains_self (W + BitVec.ofNat 64 (cntOff + 8)) 8)

/-! ## Ranges outside them -/

/-- A range of the working space outside what `finish` writes. -/
theorem fin_dis (h : Env g s₀ C D P W R L) {out d n : Nat} (hout : out + 16 ≤ 256) (hd : d + n ≤ 2560)
    (h1 : out + 16 ≤ d ∨ d + n ≤ out) (h2 : d + n ≤ 32 ∨ 64 ≤ d) (h3 : d + n ≤ 144 ∨ 160 ≤ d)
    (h4 : d + n ≤ 224 ∨ 232 ≤ d) (h5 : d + n ≤ 256) :
    ∀ r ∈ finRegions g W out (s₀.gpr .rsp), Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [hout])
  · exact Offset.disjoint W (by omega_using [h2]) (by omega_using [hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h3]) (by omega_using [hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h4]) (by omega_using [hd]) (by omega_using [])
  · exact h.dX h5
  · exact (h.stk_w.sub_right (h.sW h5)).symm

/-- A region outside the working space and the stack, outside what `finish` writes. -/
theorem fin_out (h : Env g s₀ C D P W R L) {X : Region} {out : Nat} (hout : out + 16 ≤ 256) (hw : X.Disjoint ⟨W, g.n⟩)
    (hs : (below (s₀.gpr .rsp) 16).Disjoint X) : ∀ r ∈ finRegions g W out (s₀.gpr .rsp), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (h.sW hout)
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right h.sX
  · exact hs.symm

/-- A range of the working space outside what CTR writes. -/
theorem ctr_dis (h : Env g s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 256) (h1 : d + n ≤ 64 ∨ 112 ≤ d) :
    ∀ r ∈ ctrRegions g W P L (s₀.gpr .rsp), Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega_using [hd]))
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])
  · exact h.dX hd
  · exact (h.stk_w.sub_right (h.sW (by omega_using [hd]))).symm

/-- A region outside the data, the working space and the stack, outside what CTR writes. -/
theorem ctr_out (h : Env g s₀ C D P W R L) {X : Region} (hp : X.Disjoint ⟨P, L⟩) (hw : X.Disjoint ⟨W, g.n⟩)
    (hs : (below (s₀.gpr .rsp) 16).Disjoint X) : ∀ r ∈ ctrRegions g W P L (s₀.gpr .rsp), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right h.sX
  · exact hs.symm

/-- A range of the working space outside the counter. -/
theorem cnt_dis {d n : Nat} (hd : d + n ≤ 2560) (h1 : d + n ≤ 64 ∨ 80 ≤ d) :
    ∀ r ∈ cntRegions W, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [cntOff, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])

/-- A region outside the working space, outside the counter. -/
theorem cnt_out (h : Env g s₀ C D P W R L) {X : Region} (hw : X.Disjoint ⟨W, g.n⟩) :
    ∀ r ∈ cntRegions W, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right (h.sW (by decide))

theorem one_out {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw

/-! ## From S2V's end to the restore -/

/-- The registers, and the data pointer and length in their slots. -/
structure SPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : Regs s₀ C D P W R L s
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

/-- What `encrypt`'s and `decrypt`'s ends write: the data, the working space
and the stack. -/
abbrev endRegions (g : Lay) (W P : Addr) (L : Nat) (sp : Addr) : List Region := [⟨P, L⟩, ⟨W, g.n⟩, below sp 16]

theorem fin_sub (h : Env g s₀ C D P W R L) {out : Nat} (hout : out + 16 ≤ 256) :
    ∀ r ∈ finRegions g W out (s₀.gpr .rsp), ∃ r' ∈ endRegions g W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by omega_using [hout])⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sX⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem cnt_sub (h : Env g s₀ C D P W R L) :
    ∀ r ∈ cntRegions W, ∃ r' ∈ endRegions g W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

theorem ctr_sub (h : Env g s₀ C D P W R L) :
    ∀ r ∈ ctrRegions g W P L (s₀.gpr .rsp), ∃ r' ∈ endRegions g W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sX⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

/-- `encrypt` from S2V's state of the associated data at `D` on: S2V's end
with the plaintext into the first 16 bytes of the working space
(`finish_wp`), the counter from that IV (`counter_ok`), CTR over the data in
place (`ctr_wp`) and the restore of the registers saved in the working space. -/
theorem sealTail_wp (v : UpdateImpl) (K : Calls v g) (h : Env g s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hs : SPre s₀ C D P W R L s) {gs : Reg → BitVec 64}
    (hsv : Spill.Saved s.mem W gs saved) :
    WP isa (.seq (finish g.x v.callee v.ctr.callee v.ctr.suffix 0) (.seq (.block (counter 0)) (.seq (ctr g.x v.ctr.callee) (.block restore)))) s
      fun s' => (∀ r ∈ saved.map Prod.fst, s'.gpr r = gs r) ∧ s'.gpr .rsp = s₀.gpr .rsp ∧
        Frame (endRegions g W P L (s₀.gpr .rsp)) s.mem s'.mem ∧
        Spec.Siv.sealWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
          (Spec.Aes.bytesAt s.mem P L) = (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_using [h]
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega_using [this]
  refine WP.seq (WP.mono (finish_wp v K h hs.regs (Or.inl rfl)) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := counter_ok h h₂.regs.r15 h₂.regs.rd h₂.regs.wr
  have f₃ : Frame (cntRegions W) s₂.mem s₃.mem := m₃ ▸ counter_frame _ _ _ _
  have hr₃ : Regs s₀ C D P W R L s₃ := h₂.regs.keep (fun r hr => g₃ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  -- The data pointer and its length, kept in their slots.
  have hslot {d : Nat} (hd : 208 ≤ d) (hd' : d + 8 ≤ 224) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (cnt_dis (by omega_using [hd']) (by omega_using [hd])) (by decide),
      f₂.readW (Region.contains_self _ _) (fin_dis h (by decide) (by omega_using [hd']) (by omega_using [hd]) (by omega_using [hd]) (by omega_using [hd])
        (by omega_using [hd']) (by omega_using [hd'])) (by decide)]
  have h208 : s₃.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P := by
    rw [hslot (by decide) (by decide), hs.d208]
  have h216 : s₃.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
    rw [hslot (by decide) (by decide), hs.d216]
  have hcnt : ∃ hi lo : BitVec 64, s₃.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s₃.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s₂.mem W 16)) := by
    rw [m₃]; exact counter_cnt s₂.mem W
  refine WP.seq (WP.mono (ctr_wp v.ctr K.toCCalls h hcp hPw hr₃ (length_counter _) (counter_low _) hcnt h208 h216)
    fun s₄ h₄ => ?_)
  have f₄ := h₄.frame
  -- The saved registers.
  have hsv₄ : Spill.Saved s₄.mem W gs saved := by
    have hb (p : Reg × Nat) (hp : p ∈ saved) : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := ⟨saved_ge p hp, saved_le p hp⟩
    refine (((hsv.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame f₄ fun p hp => ?_)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega_using [this]) (by omega_using [this]) (by omega_using [this]) (by omega_using [this]) (by omega_using [this]) (by omega_using [this])
    · have := hb p hp; exact cnt_dis (by omega_using [this]) (by omega_using [this])
    · have := hb p hp; exact ctr_dis h (by omega_using [this]) (by omega_using [this])
  refine WP.mono (Spill.restore_ok .r15 saved gs s₄ (by decide) (fun p hp => by
      rw [h₄.regs.r15, h₄.regs.rd, h₄.regs.wr]; exact h.inRW rfl rfl (by have := saved_le p hp; omega_using [this]))
    (by rw [h₄.regs.r15]; exact hsv₄)) fun s₅ ⟨h₅a, h₅b, m₅, _, _⟩ => ?_
  have c₀ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
  have d₀ := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
  rw [k0] at c₀ d₀
  -- The IV: S2V's end.
  have hv : Spec.Aes.bytesAt s₅.mem W 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L) := by
    have o₂ := h₂.out
    rw [k0] at o₂
    rw [m₅, bytesAt_frame f₄ c₀ (by decide), bytesAt_frame f₃ d₀ (by decide), o₂]
  -- The ciphertext: CTR of the data from the IV's counter.
  have hc : Spec.Aes.bytesAt s₅.mem P L =
      Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₅.mem W 16))
        (Spec.Aes.bytesAt s.mem P L) := by
    rw [m₅, h₄.data, bytesAt_frame f₄ c₀ (by decide), bytesAt_frame f₃ d₀ (by decide),
      ctxCiph_frame f₃ (cnt_out h h.c_w) hRb, ctxCiph_frame f₂ (fin_out h (by decide) h.c_w h.stk_c) hRb,
      bytesAt_frame f₃ (cnt_out h h.p_w) hL, bytesAt_frame f₂ (fin_out h (by decide) h.p_w h.stk_p) hL]
  refine ⟨h₅a, by rw [h₅b _ (by decide), h₄.regs.rsp], ?_, by rw [hc, hv]; rfl⟩
  rw [m₅]
  exact ((f₂.sub (fin_sub h (by decide))).trans (f₃.sub (cnt_sub h))).trans (f₄.sub (ctr_sub h))

end VG.Proof.AesSiv.X86_64
