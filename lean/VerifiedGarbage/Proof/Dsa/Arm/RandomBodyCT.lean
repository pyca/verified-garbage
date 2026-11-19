module

import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.Arm.RandomAttempt
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomAttempt
import VerifiedGarbage.Proof.Dsa.Arm.SignCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Dsa.Arm.SignCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
public import VerifiedGarbage.Proof.Dsa.Arm.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomCopy
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Dsa.RandomSign
meta import VerifiedGarbage.Proof.Dsa.RandomSignResult
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Dsa.Arm.Leaves
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Impl.Dsa.Arm.Context
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Weierstrass.PointContract
meta import VerifiedGarbage.Impl.Dsa.Arm.Context

/-! ### `Dsa.Arm.RandomTwo`, which this module and modules that import it used -/

section

/-!
# Relating two runs of the randomized signer by their public data (32-bit ARM)

As on x86 (`Proof/Dsa/X86/RandomTwo.lean`): `Two Φ` relates two runs in
which both states satisfy `Φ a` for the same public data `a`. Straight code
is checked by the taint analysis from the registers `Φ` pins (`two_taint`),
what correctness gives after it is carried along (`two_post`), and branches
and loops on conditions `Φ` fixes are related case by case (`two_ite`,
`two_loop`).

`pubOf s₀`: the entry's stack pointer, its register and stack arguments and
q's bytes, which two runs with related entry states share. Everything the
code uses as an address or count is a function of it (`pub_*`); in
particular the frame's base, which `r11` holds (`pins_r11`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random

/-! ## Two runs -/

/-- Both runs satisfy `Φ a`, for the same `a`. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂⟩

/-- `Φ a` fixes the registers `rs`. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂⟩ => Taint.agree_ofRegs (hpin a _ _ h₁ h₂)) h

/-- A piece checked by the taint analysis, with what correctness gives after it. -/
theorem two_piece {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) : RelCT isa (Two Φ) c (Two Ψ) :=
  two_post (two_taint rs hpin h) hw

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨g a, h _ _ h₁, h _ _ h₂⟩) fun _ _ h => h

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩

/-- A loop of `N a` iterations, its `j`-th from a state satisfying `Φ a j`,
whose condition after iteration `j` is whether `j + 1 < N a`. -/
theorem two_loop {α : Type} {Φ : α → Nat → State → Prop} {Ψ : α → State → Prop} (N : α → Nat)
    {body : Prog isa} {cond : isa.Cond}
    (hct : RelCT isa (Two fun (p : α × Nat) s => p.2 < N p.1 ∧ Φ p.1 p.2 s) body fun _ _ => True)
    (hw : ∀ a j s, j < N a → Φ a j s → WP isa body s fun s' =>
      isa.eval cond s' = some (decide (j + 1 < N a)) ∧ (j + 1 < N a → Φ a (j + 1) s') ∧
      (j + 1 = N a → Ψ a s')) :
    RelCT isa (Two fun a s => 0 < N a ∧ Φ a 0 s) (.loop body cond) (Two Ψ) := by
  have key := RelCT.loop (M := isa) (body := body) (c := cond) (Q := Two Ψ)
    (fun n s₁ s₂ => ∃ a j, n = N a - j ∧ j < N a ∧ Φ a j s₁ ∧ Φ a j s₂) (fun n => by
      have hp := two_post (Φ := fun (p : α × Nat) s => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ Φ p.1 p.2 s)
        (Ψ := fun p s' => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ isa.eval cond s' = some (decide (p.2 + 1 < N p.1)) ∧
          (p.2 + 1 < N p.1 → Φ p.1 (p.2 + 1) s') ∧ (p.2 + 1 = N p.1 → Ψ p.1 s'))
        (two_map id (fun p s h => ⟨h.1, h.2.2⟩) hct)
        fun p s h => WP.mono (hw p.1 p.2 s h.1 h.2.2) fun s' h' => ⟨h.1, h.2.1, h'⟩
      refine hp.mono (fun s₁ s₂ ⟨a, j, hn, hj, h₁, h₂⟩ => ⟨(a, j), ⟨hj, hn, h₁⟩, hj, hn, h₂⟩) ?_
      rintro s₁ s₂ ⟨⟨a, j⟩, ⟨hj, hn, e₁, f₁, g₁⟩, ⟨-, -, e₂, f₂, g₂⟩⟩
      refine ⟨by rw [e₁, e₂], fun h => ?_, fun h => ?_⟩
      · have : ¬ j + 1 < N a := by rw [e₁] at h; simpa using h
        have hjN : j + 1 = N a := by simp only at hj this; omega_using [hj, this]
        exact ⟨a, g₁ hjN, g₂ hjN⟩
      · have hlt : j + 1 < N a := by rw [e₁] at h; simpa using h
        exact ⟨N a - (j + 1), by simp only at hn; omega_using [hn, hlt], a, j + 1, rfl, hlt, f₁ hlt, f₂ hlt⟩)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a, ⟨h0, h₁⟩, ⟨-, h₂⟩⟩ := hp
  exact key (N a - 0) _ _ _ _ _ _ ⟨a, 0, rfl, h0, h₁, h₂⟩ e₁ e₂

/-! ## What two runs share -/

/-- The public data of an entry state. -/
structure Pub where
  sp : BitVec 32
  regs : List (BitVec 32)
  args : List (BitVec 32)
  qBytes : List Byte

def pubOf (s₀ : State) : Pub :=
  ⟨s₀.sp, [s₀.gpr .r0, s₀.gpr .r1, s₀.gpr .r2, s₀.gpr .r3], (List.range 9).map (stackArg s₀), rQBytes s₀⟩

/-- Some entry state with public data `a` relates to `t` by `P`. -/
def At (P : State → State → Prop) (a : Pub) (t : State) : Prop :=
  ∃ s₀, RandomABI s₀ ∧ pubOf s₀ = a ∧ P s₀ t

section
variable {s₁ s₂ : State} (h : pubOf s₁ = pubOf s₂)
include h

theorem pub_sp : s₁.sp = s₂.sp := congrArg Pub.sp h
theorem pub_reg (i : Nat) : [s₁.gpr .r0, s₁.gpr .r1, s₁.gpr .r2, s₁.gpr .r3][i]? =
    [s₂.gpr .r0, s₂.gpr .r1, s₂.gpr .r2, s₂.gpr .r3][i]? := congrArg (fun a => a.regs[i]?) h
theorem pub_r0 : s₁.gpr .r0 = s₂.gpr .r0 := Option.some.inj (pub_reg h 0)
theorem pub_r1 : s₁.gpr .r1 = s₂.gpr .r1 := Option.some.inj (pub_reg h 1)
theorem pub_r2 : s₁.gpr .r2 = s₂.gpr .r2 := Option.some.inj (pub_reg h 2)
theorem pub_r3 : s₁.gpr .r3 = s₂.gpr .r3 := Option.some.inj (pub_reg h 3)
theorem pub_arg (j : Nat) (hj : j < 9) : stackArg s₁ j = stackArg s₂ j := by
  have := congrArg (fun a => a.args[j]?) h
  simpa only [pubOf, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] using this
theorem pub_qBytes : rQBytes s₁ = rQBytes s₂ := congrArg Pub.qBytes h
theorem pub_rLow : rLow s₁ = rLow s₂ := by rw [rLow, rLow, pub_sp h]
theorem pub_rBase : rBase s₁ = rBase s₂ := by rw [rBase, rBase, pub_rLow h]
theorem pub_rQ : rQ s₁ = rQ s₂ := by rw [rQ, rQ, pub_r3 h, pub_arg h 1 (by decide)]
theorem pub_rWidth : rWidth s₁ = rWidth s₂ := by rw [rWidth, rWidth, pub_qBytes h]
theorem pub_rq : rq s₁ = rq s₂ := by rw [rq, rq, pub_qBytes h]
theorem pub_randLen : (rInput s₁).rand.length = (rInput s₂).rand.length := by
  simp only [rInput, rBytes_length, pub_arg h 6 (by decide)]
theorem pub_drawPlace : drawPlace s₁ = drawPlace s₂ := by
  simp only [drawPlace, pub_qBytes h, pub_rWidth h]
end

theorem addr_inj32 {a b : BitVec 32} (h : State.addr a = State.addr b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← VG.Proof.X25519.Arm.addr_toNat a, ← VG.Proof.X25519.Arm.addr_toNat b, h]

/-- Two states whose frames have the same base agree on `r11`. -/
theorem r11_of_rf {t₁ t₂ : State} {B : Addr} (h₁ : RF t₁ B) (h₂ : RF t₂ B) : t₁.gpr .r11 = t₂.gpr .r11 :=
  addr_inj32 (h₁.base.trans h₂.base.symm)

theorem At.r11 {P : State → State → Prop} (hr : ∀ s₀ t, P s₀ t → RReady s₀ t) {a : Pub} {t₁ t₂ : State}
    (h₁ : At P a t₁) (h₂ : At P a t₂) : t₁.gpr .r11 = t₂.gpr .r11 := by
  obtain ⟨s₁, -, e₁, p₁⟩ := h₁
  obtain ⟨s₂, -, e₂, p₂⟩ := h₂
  exact r11_of_rf (hr _ _ p₁).rf ((pub_rBase (e₁.trans e₂.symm)) ▸ (hr _ _ p₂).rf)

/-- `r11` is pinned. -/
theorem pins_r11 {α : Type} {Φ : α → State → Prop} (f : α → Pub) {P : α → State → State → Prop}
    (hΦ : ∀ a t, Φ a t → At (P a) (f a) t) (hr : ∀ a s₀ t, P a s₀ t → RReady s₀ t) : Pins Φ [.r11] := by
  intro a t₁ t₂ h₁ h₂ r hr'
  rw [List.mem_singleton] at hr'; subst hr'
  exact At.r11 (hr a) (hΦ a t₁ h₁) (hΦ a t₂ h₂)

/-- `r11` is pinned by a predicate about the frame. -/
theorem pins_at {α : Type} {P : α → State → State → Prop} (f : α → Pub)
    (hr : ∀ a s₀ t, P a s₀ t → RReady s₀ t) : Pins (fun a => At (P a) (f a)) [.r11] :=
  pins_r11 f (fun _ _ h => h) hr

/-- `r11` is pinned in a branch. -/
theorem pins_at' {α : Type} {P : α → State → State → Prop} {X : α → State → Prop} (f : α → Pub)
    (hr : ∀ a s₀ t, P a s₀ t → RReady s₀ t) : Pins (fun a s => At (P a) (f a) s ∧ X a s) [.r11] :=
  pins_r11 (P := P) f (fun _ _ h => h.1) hr

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.RandomBody`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.RandomFinish`, which this module and modules that import it used -/

section

/-!
# The randomized signer's exit (32-bit ARM)

`finish` zeros `out` unless signing succeeded (`zeroOut_ok`), clears the
nonce, publishes the consumption to `used`, returns the status and restores
the callee-saved registers, `r11` last (`rfinish_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_str wp_strb op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

/-- Registers but `r11` and memory where the body may write change. -/
theorem RReady.congrW {s₀ t u : State} {ws : List Reg} {rs : List Region} (h : RReady s₀ t) (R : Rest ws t u)
    (hm : Frame rs t.mem u.mem) (hrs : ∀ r ∈ rs, r ∈ rWrites s₀) (h11 : .r11 ∉ ws := by decide) : RReady s₀ u :=
  ⟨h.rf.of_rest R h11, R.sp.trans h.sp, R.rd.trans h.rd, R.wr.trans h.wr, h.frame.trans (hm.mono hrs)⟩

/-! ## Zeroing the output -/

/-- The output, after `k` of its bytes are zeroed. -/
structure ZeroInv (s₀ t₀ : State) (k : Nat) (t : State) : Prop where
  ready : RReady s₀ t
  r1 : t.gpr .r1 = s₀.gpr .r0 + BitVec.ofNat 32 k
  r2 : t.gpr .r2 = BitVec.ofNat 32 ((s₀.gpr .r1).toNat - k)
  r0 : t.gpr .r0 = 0
  frame : Frame [rOut s₀] t₀.mem t.mem
  zero : ∀ i < k, t.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) = 0
  rest : Rest [.r0, .r1, .r2] t₀ t

theorem zeroStep_ok {s₀ t₀ t : State} (A : RandomABI s₀) {k : Nat} (hk : k < (s₀.gpr .r1).toNat)
    (I : ZeroInv s₀ t₀ k t) :
    WP isa (.block [.strb .r0 .r1 0, .dp .add .r1 .r1 (.imm 1), .subs .r2 .r2 (.imm 1)]) t
      fun u => ZeroInv s₀ t₀ (k + 1) u ∧ u.z = decide ((s₀.gpr .r1).toNat - (k + 1) = 0) := by
  have hb := A.outBound
  obtain hw : InRegions t.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k) 1 :=
    ⟨rOut s₀, by rw [I.ready.wr, A.wr]; simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine wp_strb (by decide) (by rw [BitVec.add_zero, I.r1, VG.Arm.addr_add (by omega_arith)]) hw fun u₁ m₁ =>
    wp_inc fun u₂ v₂ => wp_dec fun u₃ v₃ z₃ => WP.block_nil ?_
  obtain hv : (t.gpr .r0).setWidth 8 = 0 := by rw [I.r0]; rfl
  rw [hv] at m₁
  obtain R : Rest [.r0, .r1, .r2] t u₃ := (m₁.rest _).trans ((v₂.rest (by decide)).trans (v₃.rest (by decide)))
  obtain mem₃ : u₃.mem = t.mem.writeW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  obtain fr : Frame [rOut s₀] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨⟨I.ready.congrW R fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites]),
    ?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.rest.trans R⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.r1, Offset.add_ofNat_add_one]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.r2, ofNat_sub_one (by omega_arith)]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.r0]
  · rw [mem₃]
    by_cases hik : i = k
    · subst hik; exact writeW8_self _ _ _
    · have ho : ofs (State.addr (s₀.gpr .r0)) (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) = i := by
        rw [ofs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
      rw [show State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k = off (State.addr (s₀.gpr .r0)) k from rfl,
        writeW8_outside _ _ (d := k) _ (by omega_arith) _ (by rw [ho]; omega_arith)]
      exact I.zero i (by omega_arith)
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.r2, ofNat_sub_one (by omega_arith), ofNat_beq_zero (by omega_arith),
      Nat.sub_sub]

theorem zeroOut_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa zeroOut t fun u => RReady s₀ u ∧ Frame [rOut s₀] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        List.replicate (s₀.gpr .r1).toNat 0 ∧ Rest [.r0, .r1, .r2] t u := by
  obtain hL : 0 < (s₀.gpr .r1).toNat := by
    have := A.outLength; have := A.lengths; unfold Spec.Dsa.lengthsValid at *; omega_arith
  unfold zeroOut
  refine WP.seq (wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun t₃ u₃ => WP.block_nil ?_)
  obtain R₃ : Rest [.r0, .r1, .r2] t t₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  obtain m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain I₀ : ZeroInv s₀ t 0 t₃ := ⟨h.congr R₃ (by rw [m₃]; exact Frame.refl _ _),
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, sv.2.1, BitVec.add_zero],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, sv.2.2.1, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    u₃.gpr, by rw [m₃]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), R₃⟩
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = (s₀.gpr .r1).toNat - k ∧
      k < (s₀.gpr .r1).toNat ∧ ZeroInv s₀ t k u) (fun n u hu => ?_) _ t₃ ⟨0, rfl, hL, I₀⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok A hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : (s₀.gpr .r1).toNat - (k + 1) = 0
  · left
    refine ⟨by rw [eval_ne, z, decide_eq_true he]; rfl, J.ready, J.frame, ?_, J.rest⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero i (by omega_arith)
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false he]; rfl, _, by omega_arith, k + 1, rfl, by omega_arith, J⟩

/-- A write apart from the stack keeps the frame's slots. -/
theorem apart_slot {s₀ : State} {m m' : Mem} {r : Region} (hf : Frame [r] m m') (hd : (rStack s₀).Disjoint r)
    {d : Nat} (hd' : d + 4 ≤ frameBytes) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  hf.readW (r := ⟨off (rBase s₀) d, 4⟩)
    (by have := Offset.contains_base (off (rBase s₀) d) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        rwa [BitVec.add_zero] at this)
    (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      refine hd.sub_left ?_
      rw [rBase_off]; exact Offset.sub_base _ (by unfold frameBytes at hd'; omega_arith)) (by decide)

/-! ## The exit -/

/-- After the attempts, ready to finish. -/
structure RFin (s₀ t : State) : Prop where
  ready : RReady s₀ t
  usedW : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used
  status : slot t.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status
  out : (rResult s₀).status = 1 → Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).signature.getD (List.replicate (s₀.gpr .r1).toNat 0)
  saved : Saved s₀ t.mem

theorem Done.rfin {s₀ t : State} (D : Done s₀ t) : RFin s₀ t :=
  let ⟨_, S⟩ := D.smp
  ⟨S.ready, S.usedW, D.status, D.out, D.saved⟩

/-- What the signer returns, writes and publishes, before the frame is freed. -/
structure Finished (s₀ u : State) : Prop where
  sp : u.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : u.rd = s₀.rd
  wr : u.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem u.mem
  r0 : u.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status
  regs : ∀ r ∈ preserved, u.gpr r = s₀.gpr r
  out : Spec.Rsa.bytesAt u.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).signature.getD (List.replicate (s₀.gpr .r1).toNat 0)
  usedLo : slot u.mem (State.addr (s₀.gpr .r2)) 0 = BitVec.ofNat 32 (rResult s₀).used
  usedHi : slot u.mem (State.addr (s₀.gpr .r2)) 4 = 0

theorem restore_eq : ((savedRegs.zipIdx.filter (·.1 != .r11)).map (fun (r, i) => ld r (4 * i)) : List Instr) =
    [ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32] := rfl

theorem clearMem_frame (s₀ : State) (m : Mem) : ∀ k, k ≤ 8 → Frame [rStack s₀] m (clearMem m (rBase s₀) k)
  | 0, _ => Frame.refl _ _
  | k + 1, hk => (clearMem_frame s₀ m k (by omega_arith)).trans
      (frame_store s₀ _ (d := oNonce + 4 * k) (by unfold oNonce frameBytes; omega_arith) 0)

/-- The last block: clear the nonce, publish the consumption, restore the registers. -/
abbrev finalList : List Instr :=
  [ld .r4 oUsedPtr, ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0), .str .r0 .r4 4, ld .r0 oStatus,
    ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32, ld .r11 28]

theorem finalBlock_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem)
    {used st : BitVec 32} (hu : slot t.mem (rBase s₀) oUsed = used)
    (hs : slot t.mem (rBase s₀) oStatus = st) :
    WP isa (.block (clearNonce ++ finalList)) t fun u =>
      u.sp = t.sp ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ Frame [rStack s₀, rUsed s₀] t.mem u.mem ∧ u.gpr .r0 = st ∧
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧ slot u.mem (State.addr (s₀.gpr .r2)) 0 = used ∧
      slot u.mem (State.addr (s₀.gpr .r2)) 4 = 0 := by
  have hub := A.usedBound
  refine clearNonce_ok h fun t₁ h₁ m₁ k₁ _ => ?_
  obtain fr₁ : Frame [rStack s₀] t.mem t₁.mem := by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide)
  obtain o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  obtain sv₁ : Saved s₀ t₁.mem := sv.of_outs o₁ (by decide)
  obtain sl₁ : ∀ d, d + 4 ≤ oNonce → slot t₁.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Nat.le_refl _) hd
      (by unfold oNonce at hd; omega_arith)
  refine wp_ld h₁ (by decide) fun t₂ u₂ => wp_ld (h₁.upd u₂) (by decide) fun t₃ u₃ => ?_
  obtain h₃ := (h₁.upd u₂).upd u₃
  obtain r4₃ : t₃.gpr .r4 = s₀.gpr .r2 := by rw [u₃.other _ (by decide), u₂.gpr]; exact sv₁.2.2.2.1
  obtain r0₃ : t₃.gpr .r0 = used := by rw [u₃.gpr, u₂.mem, sl₁ _ (by decide), hu]
  obtain hU : (rUsed s₀) ∈ t₃.wr := by rw [h₃.wr, A.wr]; simp
  refine wp_str (a := State.addr (s₀.gpr .r2)) (by decide) (by rw [BitVec.add_zero, r4₃])
    ⟨_, hU, by
      have := Offset.contains_base (State.addr (s₀.gpr .r2)) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩ fun t₄ m₄ => wp_mov (op2_imm (by decide)) fun t₅ u₅ => ?_
  refine wp_str (a := State.addr (s₀.gpr .r2) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₅.other _ (by decide), m₄.gpr, r4₃, VG.Arm.addr_add (by omega_arith)])
    ⟨_, by rw [u₅.wr, m₄.wr]; exact hU, Offset.contains_base _ (by decide) (by decide)⟩ fun t₆ m₆ => ?_
  obtain mem₆ : t₆.mem = (t₃.mem.writeW (off (State.addr (s₀.gpr .r2)) 0) used).writeW
      (off (State.addr (s₀.gpr .r2)) 4) (0 : BitVec 32) := by
    rw [m₆.mem, u₅.gpr, u₅.mem, m₄.mem, r0₃, off, BitVec.add_zero]
  obtain fu : Frame [rUsed s₀] t₃.mem t₆.mem := by
    rw [mem₆]
    exact (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain ap : ∀ d, d + 4 ≤ frameBytes → slot t₆.mem (rBase s₀) d = slot t₃.mem (rBase s₀) d := fun d hd =>
    apart_slot fu A.stackUsed hd
  obtain m₃ : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  obtain h₆ : RReady s₀ t₆ := h₃.congrW (ws := [.r0]) ((m₄.rest _).trans ((u₅.rest (by decide)).trans (m₆.rest _))) fu
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])
  obtain sv₆ : Saved s₀ t₆.mem := sv₁.of_slots fun d _ hd => by rw [ap d hd, m₃]
  obtain hst₆ : slot t₆.mem (rBase s₀) oStatus = st := by rw [ap _ (by decide), m₃, sl₁ _ (by decide), hs]
  obtain ⟨sr, -⟩ := sv₆
  refine wp_ld h₆ (by decide) fun t₇ u₇ => ?_
  obtain h₇ := h₆.upd u₇
  refine wp_ld h₇ (by decide) fun t₈ u₈ => wp_ld (h₇.upd u₈) (by decide) fun t₉ u₉ =>
    wp_ld ((h₇.upd u₈).upd u₉) (by decide) fun t₁₀ u₁₀ =>
    wp_ld (((h₇.upd u₈).upd u₉).upd u₁₀) (by decide) fun t₁₁ u₁₁ =>
    wp_ld ((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁) (by decide) fun t₁₂ u₁₂ =>
    wp_ld (((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂) (by decide) fun t₁₃ u₁₃ =>
    wp_ld ((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃) (by decide) fun t₁₄ u₁₄ =>
    wp_ld (((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃).upd u₁₄) (by decide) fun t₁₅ u₁₅ =>
    wp_ld ((((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃).upd u₁₄).upd u₁₅) (by decide)
      fun t₁₆ u₁₆ => WP.block_nil ?_
  obtain mm : t₁₆.mem = t₆.mem := by
    rw [u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  obtain R : Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] t₆ t₁₆ :=
    (u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
      ((u₁₁.rest (by decide)).trans ((u₁₂.rest (by decide)).trans ((u₁₃.rest (by decide)).trans
      ((u₁₄.rest (by decide)).trans ((u₁₅.rest (by decide)).trans (u₁₆.rest (by decide))))))))))
  obtain R₆ : Rest [.r0, .r2, .r4] t t₆ := ((k₁.mono (by decide)).trans ((u₂.rest (by decide)).trans
    (u₃.rest (by decide)))).trans ((m₄.rest _).trans ((u₅.rest (by decide)).trans (m₆.rest _)))
  obtain hm : ∀ t' : State, t'.mem = t₆.mem → ∀ i < 9, slot t'.mem (rBase s₀) (4 * i) =
      s₀.gpr (savedRegs.getD i .r0) := fun t' e i hi => by rw [e]; exact sr i hi
  refine ⟨by rw [R.sp, R₆.sp], by rw [R.rd, R₆.rd], by rw [R.wr, R₆.wr], ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [mm]; exact (fr₁.mono (by simp)).trans ((show Frame [rUsed s₀] t₁.mem t₆.mem by rw [← m₃]; exact fu).mono
      (by simp))
  · rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.gpr, hst₆]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, u₁₀.get, u₉.get, reduceCtorEq, ↓reduceIte,
        u₈.gpr, u₇.mem]
      exact hm t₆ rfl 0 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, u₁₀.get, reduceCtorEq, ↓reduceIte, u₉.gpr]
      exact hm t₈ (by rw [u₈.mem, u₇.mem]) 1 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, reduceCtorEq, ↓reduceIte, u₁₀.gpr]
      exact hm t₉ (by rw [u₉.mem, u₈.mem, u₇.mem]) 2 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, reduceCtorEq, ↓reduceIte, u₁₁.gpr]
      exact hm t₁₀ (by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 3 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, reduceCtorEq, ↓reduceIte, u₁₂.gpr]
      exact hm t₁₁ (by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 4 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, reduceCtorEq, ↓reduceIte, u₁₃.gpr]
      exact hm t₁₂ (by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 5 (by decide)
    · simp only [u₁₆.get, u₁₅.get, reduceCtorEq, ↓reduceIte, u₁₄.gpr]
      exact hm t₁₃ (by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 6 (by decide)
    · rw [u₁₆.gpr]
      exact hm t₁₅ (by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 7
        (by decide)
    · simp only [u₁₆.get, reduceCtorEq, ↓reduceIte, u₁₅.gpr]
      exact hm t₁₄ (by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 8 (by decide)
  · rw [mm, mem₆, slot_write_ne _ _ _ (by decide) (by decide) (by decide), slot_write_self]
  · rw [mm, mem₆, slot_write_self]

theorem finishBlock_eq : (clearNonce ++ [ld .r4 oUsedPtr, ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0),
    .str .r0 .r4 4, ld .r0 oStatus] ++ (savedRegs.zipIdx.filter (·.1 != .r11)).map (fun (r, i) => ld r (4 * i)) ++
    [ld .r11 28] : List Instr) = clearNonce ++ finalList := by
  rw [restore_eq]; rfl

theorem rfinish_ok {s₀ t : State} (A : RandomABI s₀) (F : RFin s₀ t) (hR : (rResult s₀).status ≤ 2)
    (hsig : (rResult s₀).status ≠ 1 → (rResult s₀).signature = none) :
    WP isa finish t fun u => Finished s₀ u := by
  have h := F.ready
  have hb := A.outBound
  obtain hout : ∀ {m m' : Mem}, Frame [rStack s₀, rUsed s₀] m m' →
      Spec.Rsa.bytesAt m' (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        Spec.Rsa.bytesAt m (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat := fun hf =>
    rBytes_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.stackOut.symm
      · exact A.outUsed) (by omega_arith)
  unfold finish
  rw [finishBlock_eq]
  refine WP.seq (wp_ld h (by decide) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_)
  obtain h₂ := (h.upd u₁).fupd f₂
  obtain m₂ : t₂.mem = t.mem := by rw [f₂.mem, u₁.mem]
  obtain R₂ : Rest [.r0] t t₂ := (u₁.rest (by decide)).trans (f₂.rest _)
  rw [u₁.gpr, F.status, one_beq (by omega_arith)] at z₂
  obtain fin : ∀ v : State, RReady s₀ v → Rest [.r0, .r1, .r2] t v → Frame (rWrites s₀) t.mem v.mem →
      Saved s₀ v.mem → slot v.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used →
      slot v.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status →
      Spec.Rsa.bytesAt v.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        (rResult s₀).signature.getD (List.replicate (s₀.gpr .r1).toNat 0) →
      WP isa (.block (clearNonce ++ finalList)) v fun u => Finished s₀ u := fun v hv Rv fv sv hu hs ho =>
    WP.mono (finalBlock_ok A hv sv hu hs) fun u ⟨sp, rd, wr, fr, r0, regs, lo, hi⟩ =>
      ⟨by rw [sp, Rv.sp, h.sp], by rw [rd, Rv.rd, h.rd], by rw [wr, Rv.wr, h.wr],
        hv.frame.trans (fr.mono (by simp [rWrites])), r0, regs, by rw [hout fr]; exact ho, lo, hi⟩
  by_cases h1 : (rResult s₀).status = 1
  · refine WP.seq (WP.ite false (by rw [eval_ne, z₂, decide_eq_true h1]; rfl)
      (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_))
    exact fin t₂ h₂ (R₂.mono (by decide)) (by rw [m₂]; exact Frame.refl _ _) (by rw [m₂]; exact F.saved)
      (by rw [m₂]; exact F.usedW) (by rw [m₂]; exact F.status) (by rw [m₂]; exact F.out h1)
  · refine WP.seq (WP.ite true (by rw [eval_ne, z₂, decide_eq_false h1]; rfl)
      (fun _ => WP.mono (zeroOut_ok A h₂ (by rw [m₂]; exact F.saved)) fun v ⟨hv, fv, zv, Rv⟩ => ?_)
      (fun e => Bool.noConfusion e))
    obtain ap : ∀ d, d + 4 ≤ frameBytes → slot v.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd => by
      rw [apart_slot fv A.stackOut hd, m₂]
    exact fin v hv ((R₂.mono (by decide)).trans Rv) (by rw [← m₂]; exact fv.mono (by simp [rWrites]))
      (F.saved.of_slots fun d _ hd => ap d hd) (by rw [ap _ (by decide)]; exact F.usedW)
      (by rw [ap _ (by decide)]; exact F.status) (by rw [zv, hsig h1]; rfl)

end VG.Proof.Dsa.Arm

end

end

/-!
# The randomized signer's body (32-bit ARM)

From the reserved frame, `entry` saves the callee-saved registers and the
register arguments (`Saved`) and starts the counts (`entry_ok`); `prepare`
scans q, and the attempts run until one returns a status other than 4,
which `finish` returns (`body_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_str op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

/-! ## The specification's result -/

/-- With valid lengths, the result is the signing loop's. -/
theorem rResult_loop {s₀ : State} (A : RandomABI s₀) :
    rResult s₀ = Spec.Dsa.randomSignLoop (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (rInput s₀).digest 8
      (rInput s₀).rand := by
  obtain hk : (rInput s₀).key.length = 3 * (rInput s₀).pLen + 2 * (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  simp only [rResult, Spec.Dsa.randomSignBytes, hk, hl, decide_true, Bool.not_true, bne_self_eq_false,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte]

/-- q ≤ 1 fails without consuming input. -/
theorem rResult_small {s₀ : State} (A : RandomABI s₀) (hq : ¬ 1 < rq s₀) :
    rResult s₀ = ⟨none, 0, 0, [4]⟩ := by
  rw [rResult_loop A, Spec.Dsa.randomSignLoop]
  obtain hs : Spec.Dsa.Random.sample (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen
      (rInput s₀).key).params.q 128 (rInput s₀).rand = ⟨none, 0, [4]⟩ := by
    obtain h1 : (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key).params.q ≤ 1 := by
      rw [← rQ_decode]; exact Nat.le_of_not_lt hq
    rw [Spec.Dsa.Random.sample]; simp only [h1, ↓reduceIte]
  simp only [hs]
  rfl

theorem rResult_status_le {s₀ : State} (A : RandomABI s₀) : (rResult s₀).status ≤ 2 := by
  rw [rResult_loop A]; exact VG.Proof.Dsa.randomSignLoop_status_le _ _ _ _ _ _

theorem rResult_signature {s₀ : State} (A : RandomABI s₀) :
    (rResult s₀).status ≠ 1 → (rResult s₀).signature = none := by
  rw [rResult_loop A]
  intro h
  have := (not_congr (VG.Proof.Dsa.randomSignLoop_success _ _ _ _ _ _)).mp h
  simpa using this

theorem rResult_used_le {s₀ : State} : (rResult s₀).used ≤ (rInput s₀).rand.length :=
  VG.Proof.Dsa.randomSignBytes_used_le _ _ _ _ _

/-! ## The entry -/

/-- Before `r11` holds the frame's base, `r12` does. -/
structure PreR (s₀ t : State) : Prop where
  r12 : t.gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes
  sp : t.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

/-- `str r, [r12, #d]`, a slot of the frame. -/
theorem wp_strP {s₀ t : State} (A : RandomABI s₀) (P : PreR s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, PreR s₀ u → u.mem = t.mem.writeW (off (rBase s₀) d) (t.gpr r) → u.gpr = t.gpr →
      WP isa (.block is) u Q) :
    WP isa (.block (.str r .r12 d :: is)) t Q := by
  obtain hb := rBase_toNat A
  have hs := A.stackBound
  have hl := A.stackLow
  obtain ha : State.addr (t.gpr .r12 + BitVec.ofNat 32 d) = off (rBase s₀) d := by
    rw [P.r12, VG.Arm.addr_add (by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_arith),
      alloc_base A]
  refine wp_str (by unfold frameBytes at hd; omega_arith) ha
    ⟨_, by rw [P.wr]; exact List.mem_cons_self, Offset.contains_base _ hd (by unfold frameBytes at *; omega_arith)⟩
    fun u m => k u ⟨by rw [m.gpr]; exact P.r12, m.sp.trans P.sp, m.rd.trans P.rd, m.wr.trans P.wr,
      P.frame.trans (by
        rw [m.mem]
        exact (frame_store s₀ t.mem hd (t.gpr r)).mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; simp [rWrites])⟩ m.mem m.gpr

theorem entry_eq : entry = [.addSp .r12 0, .str .r4 .r12 0, .str .r5 .r12 4, .str .r6 .r12 8, .str .r7 .r12 12,
    .str .r8 .r12 16, .str .r9 .r12 20, .str .r10 .r12 24, .str .r11 .r12 28, .str .lr .r12 32,
    .mov .r11 (.reg .r12), st .r0 oOut, st .r1 oOutLen, st .r2 oUsedPtr, st .r3 oKey,
    .mov .r0 (.imm 0), st .r0 oUsed, .mov .r0 (.imm 8), st .r0 oAttempts] := rfl

/-- Save the callee-saved registers and the register arguments, and start the counts. -/
theorem entry_ok {s₀ : State} (A : RandomABI s₀) :
    WP isa (.block entry) (allocated frameBytes s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oAttempts = 8 ∧
      (∀ r, r ≠ .r0 → r ≠ .r11 → r ≠ .r12 → u.gpr r = s₀.gpr r) := by
  rw [entry_eq]
  refine VG.Proof.X25519.Arm.WP.cons (s' := (allocated frameBytes s₀).setReg .r12
    ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) (by simp [exec]) ?_
  obtain P₀ : PreR s₀ ((allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) :=
    ⟨by simp [State.setReg, allocated], rfl, rfl, by
      show ⟨State.addr (s₀.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ :: s₀.wr = _; rw [alloc_base A],
      Frame.refl _ _⟩
  obtain g₀ : ∀ r, r ≠ .r12 → ((allocated frameBytes s₀).setReg .r12
      ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)).gpr r = s₀.gpr r := fun r h => by
    simp [State.setReg, allocated, h]
  refine wp_strP A P₀ (by decide) fun t₁ P₁ m₁ g₁ => wp_strP A P₁ (by decide) fun t₂ P₂ m₂ g₂ =>
    wp_strP A P₂ (by decide) fun t₃ P₃ m₃ g₃ => wp_strP A P₃ (by decide) fun t₄ P₄ m₄ g₄ =>
    wp_strP A P₄ (by decide) fun t₅ P₅ m₅ g₅ => wp_strP A P₅ (by decide) fun t₆ P₆ m₆ g₆ =>
    wp_strP A P₆ (by decide) fun t₇ P₇ m₇ g₇ => wp_strP A P₇ (by decide) fun t₈ P₈ m₈ g₈ =>
    wp_strP A P₈ (by decide) fun t₉ P₉ m₉ g₉ => wp_mov (op2_reg _ _) fun t₁₀ u₁₀ => ?_
  obtain gg : ∀ r, r ≠ .r12 → t₉.gpr r = s₀.gpr r := fun r h => by
    rw [g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁]; exact g₀ r h
  obtain nw : (rBase s₀).toNat + frameBytes + 36 ≤ 2 ^ 32 := by
    rw [rBase_toNat A]; have := A.stackBound; have := A.stackLow; unfold frameBytes; omega_arith
  obtain h₁₀ : RReady s₀ t₁₀ :=
    ⟨⟨by rw [u₁₀.gpr, P₉.r12, alloc_base A], by rw [u₁₀.wr, P₉.wr]; exact List.mem_cons_self,
      by rw [u₁₀.rd, P₉.rd, A.rd, rBase_args A]; simp, nw⟩,
      u₁₀.sp.trans P₉.sp, u₁₀.rd.trans P₉.rd, u₁₀.wr.trans P₉.wr, by rw [u₁₀.mem]; exact P₉.frame⟩
  refine wp_st h₁₀ (by decide) fun t₁₁ m₁₁ h₁₁ => wp_st h₁₁ (by decide) fun t₁₂ m₁₂ h₁₂ =>
    wp_st h₁₂ (by decide) fun t₁₃ m₁₃ h₁₃ => wp_st h₁₃ (by decide) fun t₁₄ m₁₄ h₁₄ =>
    wp_mov (op2_imm (by decide)) fun t₁₅ u₁₅ => wp_st (h₁₄.upd u₁₅) (by decide) fun t₁₆ m₁₆ h₁₆ =>
    wp_mov (op2_imm (by decide)) fun t₁₇ u₁₇ => wp_st (h₁₆.upd u₁₇) (by decide) fun t₁₈ m₁₈ h₁₈ => WP.block_nil ?_
  obtain e₁₄ : ∀ r, r ≠ .r11 → r ≠ .r12 → t₁₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [m₁₄.gpr, m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ h]; exact gg r h'
  obtain hm : t₁₈.mem = ((((((((((((((s₀.mem.writeW (off (rBase s₀) 0) (s₀.gpr .r4)).writeW
      (off (rBase s₀) 4) (s₀.gpr .r5)).writeW (off (rBase s₀) 8) (s₀.gpr .r6)).writeW
      (off (rBase s₀) 12) (s₀.gpr .r7)).writeW (off (rBase s₀) 16) (s₀.gpr .r8)).writeW
      (off (rBase s₀) 20) (s₀.gpr .r9)).writeW (off (rBase s₀) 24) (s₀.gpr .r10)).writeW
      (off (rBase s₀) 28) (s₀.gpr .r11)).writeW (off (rBase s₀) 32) (s₀.gpr .lr)).writeW
      (off (rBase s₀) oOut) (s₀.gpr .r0)).writeW (off (rBase s₀) oOutLen) (s₀.gpr .r1)).writeW
      (off (rBase s₀) oUsedPtr) (s₀.gpr .r2)).writeW (off (rBase s₀) oKey) (s₀.gpr .r3)).writeW
      (off (rBase s₀) oUsed) (0 : BitVec 32)).writeW (off (rBase s₀) oAttempts) (8 : BitVec 32) := by
    obtain v0 : t₁₀.gpr .r0 = s₀.gpr .r0 := by rw [u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v1 : t₁₁.gpr .r1 = s₀.gpr .r1 := by rw [m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v2 : t₁₂.gpr .r2 = s₀.gpr .r2 := by
      rw [m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v3 : t₁₃.gpr .r3 = s₀.gpr .r3 := by
      rw [m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    rw [m₁₈.mem, u₁₇.gpr, u₁₇.mem, m₁₆.mem, u₁₅.gpr, u₁₅.mem, m₁₄.mem, m₁₃.mem, m₁₂.mem, m₁₁.mem, v0, v1, v2, v3,
      u₁₀.mem, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    simp only [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, g₀ _ (by decide : Reg.r4 ≠ .r12), g₀ _ (by decide : Reg.r5 ≠ .r12),
      g₀ _ (by decide : Reg.r6 ≠ .r12), g₀ _ (by decide : Reg.r7 ≠ .r12), g₀ _ (by decide : Reg.r8 ≠ .r12),
      g₀ _ (by decide : Reg.r9 ≠ .r12), g₀ _ (by decide : Reg.r10 ≠ .r12), g₀ _ (by decide : Reg.r11 ≠ .r12),
      g₀ _ (by decide : Reg.lr ≠ .r12)]
    rfl
  refine ⟨h₁₈, ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun r h0 h11 h12 => ?_⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 := by omega_arith
    all_goals (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; rfl)
  all_goals first
    | (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; done)
    | skip
  rw [m₁₈.gpr, u₁₇.other _ h0, m₁₆.gpr, u₁₅.other _ h0]; exact e₁₄ r h11 h12

theorem Att.mem {s₀ t u : State} (A : RandomABI s₀) {used f : Nat} (T : Att s₀ used f t) (hr : RReady s₀ u)
    (hm : u.mem = t.mem) : Att s₀ used f u :=
  let ⟨d, S⟩ := T.smp
  ⟨⟨d, S.mem A hr hm⟩, by rw [hm]; exact T.attempts, by rw [hm]; exact T.saved, T.rel⟩

theorem Done.mem {s₀ t u : State} (A : RandomABI s₀) (D : Done s₀ t) (hr : RReady s₀ u) (hm : u.mem = t.mem) :
    Done s₀ u :=
  let ⟨d, S⟩ := D.smp
  ⟨⟨d, S.mem A hr hm⟩, by rw [hm]; exact D.status, by rw [hm]; exact D.out, by rw [hm]; exact D.saved⟩

theorem body_ok (S : Signer) (name : String) {s₀ : State} (A : RandomABI s₀) (V : RValid S s₀) :
    WP isa (body name S.code) (allocated frameBytes s₀) fun u => Finished s₀ u := by
  obtain hql := rQBytes_le A
  obtain hfit := rWidth_le s₀
  obtain hR := rResult_status_le A
  unfold body
  refine WP.seq (WP.mono (entry_ok A) fun t₁ ⟨h₁, sv₁, us₁, at₁, _⟩ => ?_)
  refine WP.seq (WP.mono (prepare_ok A h₁ sv₁.2.2.2.2) fun t₂ ⟨ax₂, P₂, h₂, o₂, _⟩ => ?_)
  obtain lo₂ : ∀ d, d + 4 ≤ oQ → slot t₂.mem (rBase s₀) d = slot t₁.mem (rBase s₀) d := fun d hd =>
    outs_low o₂ (by decide) hd (by unfold oQ at hd; omega_arith)
  refine WP.seq (wp_cmp0 fun t₃ f₃ z₃ => WP.block_nil ?_)
  obtain h₃ := h₂.fupd f₃
  have m₃ : t₃.mem = t₂.mem := f₃.mem
  obtain sv₃ : Saved s₀ t₃.mem := by rw [m₃]; exact sv₁.of_outs o₂ (by decide)
  obtain us₃ : slot t₃.mem (rBase s₀) oUsed = 0 := by rw [m₃, lo₂ _ (by decide)]; exact us₁
  obtain at₃ : slot t₃.mem (rBase s₀) oAttempts = 8 := by rw [m₃, lo₂ _ (by decide)]; exact at₁
  rw [ax₂] at z₃
  suffices H : WP isa (.ite .eq (.block [st .r0 oStatus])
      (.loop (.seq (attempt name S.code) (.block [ld .r0 oStatus, .cmp .r0 (.imm 4)])) .eq))
      t₃ (RFin s₀) from WP.seq (WP.mono H fun u hu => rfinish_ok A hu hR (rResult_signature A))
  by_cases hq : 1 < rq s₀
  · simp only [hq, ↓reduceIte] at z₃
    obtain P := P₂ hq
    refine WP.ite false (by rw [eval_eq, z₃]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
    obtain T₀ : Att s₀ 0 8 t₃ := by
      refine ⟨⟨(slot t₃.mem (rBase s₀) oDraws).toNat, ⟨h₃, by rw [m₃]; exact P.q, by rw [m₃]; exact P.width,
        by rw [m₃]; exact P.mask, us₃, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
        fun i hi => by rw [m₃]; exact P.nonce i (by omega_arith), Nat.zero_le _⟩⟩, at₃, sv₃, ?_⟩
      obtain e : VG.Proof.Dsa.randomSignRemaining (rInput s₀) 0 8 = rResult s₀ := by
        rw [rResult_loop A]; rfl
      exact ⟨by rw [e], by rw [e], by rw [e]⟩
    refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ used, 1 ≤ n ∧ n ≤ 8 ∧ Att s₀ used n u)
      (fun n u hu => ?_) 8 t₃ ⟨0, by decide, by decide, T₀⟩
    obtain ⟨used, hn1, hn8, T⟩ := hu
    obtain ⟨f, rfl⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega_arith⟩
    refine WP.seq (WP.mono (attempt_ok S name A T hn8 hq V) fun v hv => ?_)
    obtain hrv : RReady s₀ v := by
      rcases hv with ⟨_, _, T', _⟩ | ⟨_, D, _⟩
      · obtain ⟨_, S⟩ := T'.smp; exact S.ready
      · obtain ⟨_, S⟩ := D.smp; exact S.ready
    refine wp_ld hrv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
    obtain hv₂ := (hrv.upd uv₁).fupd fv₂
    obtain mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
    rw [uv₁.gpr] at zv₂
    rcases hv with ⟨st, h1f, T', _⟩ | ⟨st, D, _⟩
    · right
      refine ⟨by rw [eval_eq, zv₂, st]; rfl, f, by omega_arith, _, h1f, by omega_arith, T'.mem A hv₂ mv₂⟩
    · left
      refine ⟨?_, (D.mem A hv₂ mv₂).rfin⟩
      obtain hz : (slot v.mem (rBase s₀) oStatus - 4 == 0) = false := by
        rw [D.status, status_beq (by omega_arith), decide_eq_false (by omega_arith)]
      rw [eval_eq, zv₂, hz]
  · simp only [hq, ↓reduceIte] at z₃
    obtain hR' := rResult_small A hq
    refine WP.ite true (by rw [eval_eq, z₃]; rfl) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine wp_st h₃ (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
    obtain r0 : t₃.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status := by
      rw [f₃.gpr, ax₂, hR']; simp only [hq, ↓reduceIte]; rfl
    rw [r0] at m₄
    refine ⟨h₄, ?_, by rw [m₄.mem, slot_write_self], fun e => by rw [hR'] at e; exact absurd e (by decide),
      sv₃.of_slots fun d hd _ => by rw [m₄.mem, slot_write_ne _ _ _ (by unfold oStatus; omega_arith) (by omega_arith)
        (by decide)]⟩
    rw [m₄.mem, slot_write_ne _ _ _ (by decide) (by decide) (by decide), us₃, hR']; rfl

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.RandomPrepareCT`, which only this module used -/

section

/-!
# Preparing leaks only public data (32-bit ARM)

`prepare` branches on q's bytes, which are public: the scan's registers
after `j` bytes are a function of them (`scanAfter`), so two runs with the
same public data take the same branches.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_ldrb op2_imm op2_reg eval_eq eval_ne)
open VG.Proof.Dsa (scanAfter scanNext)

/-- The scan before byte `j`. -/
def ScanAt (j : Nat) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ ScanState t (rQ s₀ + BitVec.ofNat 32 j) ((rQBytes s₀).drop j) (scanAfter (rQBytes s₀) j)

/-- After loading byte `j`. -/
def ScanLoaded (j : Nat) (s₀ t : State) : Prop :=
  ScanAt j s₀ t ∧ t.gpr .r0 = ((rQBytes s₀).getD j 0).setWidth 32

theorem scanAt_pins {j : Nat} {a : Pub} {t₁ t₂ : State} (h₁ : At (ScanLoaded j) a t₁) (h₂ : At (ScanLoaded j) a t₂) :
    ∀ r ∈ [Reg.r0, .r1, .r2, .r3, .r4], t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, -, e₁, ⟨-, S₁⟩, x₁⟩ := h₁
  obtain ⟨s₂, -, e₂, ⟨-, S₂⟩, x₂⟩ := h₂
  have e := e₁.trans e₂.symm
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [x₁, x₂, pub_qBytes e]
  · rw [S₁.r1, S₂.r1, pub_rQ e]
  · rw [S₁.r2, S₂.r2, pub_qBytes e]
  · rw [S₁.r3, S₂.r3, pub_qBytes e]
  · rw [S₁.r4, S₂.r4, pub_qBytes e]

theorem scanAt_r1 {j : Nat} {a : Pub} {t₁ t₂ : State} (h₁ : At (ScanAt j) a t₁) (h₂ : At (ScanAt j) a t₂) :
    t₁.gpr .r1 = t₂.gpr .r1 := by
  obtain ⟨s₁, -, e₁, -, S₁⟩ := h₁
  obtain ⟨s₂, -, e₂, -, S₂⟩ := h₂
  rw [S₁.r1, S₂.r1, pub_rQ (e₁.trans e₂.symm)]

theorem loadByte_ok {s₀ t : State} {j : Nat} (h : ScanAt j s₀ t) (hj : j < (rQBytes s₀).length) :
    WP isa (.block [.ldrb .r0 .r1 0]) t (ScanLoaded j s₀) := by
  obtain ⟨hr, S⟩ := h
  have hb := S.bytes
  have hl : 0 < ((rQBytes s₀).drop j).length := by rw [List.length_drop]; omega_using [hj]
  refine wp_ldrb (a := State.addr (rQ s₀ + BitVec.ofNat 32 j) + BitVec.ofNat 64 0) (by decide)
    (by rw [BitVec.add_zero, S.r1, BitVec.add_zero]) (hb.rd 0 hl) fun u v => WP.block_nil ?_
  have hv := hb.val 0 hl
  simp only [List.getElem_drop, Nat.add_zero] at hv
  rw [hv] at v
  refine ⟨⟨hr.upd v, ⟨by rw [v.other _ (by decide)]; exact S.r1,
    by rw [v.other _ (by decide)]; exact S.r2, by rw [v.other _ (by decide)]; exact S.r3,
    by rw [v.other _ (by decide)]; exact S.r4, hb.congr v.mem v.rd v.wr, S.bound, S.zero⟩⟩, ?_⟩
  rw [v.gpr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

theorem scanStep_ok {s₀ t : State} (A : RandomABI s₀) {j : Nat} (h : ScanAt j s₀ t)
    (hj : j < (rQBytes s₀).length) :
    WP isa significantByte t fun u => isa.eval .ne u = some (decide (j + 1 < (rQBytes s₀).length)) ∧
      ScanAt (j + 1) s₀ u := by
  obtain ⟨hr, S⟩ := h
  have hql := rQBytes_le A
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, (rQBytes s₀).drop j = b :: rest :=
    ⟨_, _, List.drop_eq_getElem_cons hj⟩
  have hrl : rest.length + 1 = (rQBytes s₀).length - j := by
    have := congrArg List.length hbr; simp only [List.length_drop, List.length_cons] at this; omega_using [this]
  rw [hbr] at S
  refine WP.mono (significantByte_ok S (by omega_using [hql, hrl])) fun u ⟨S', z, m, k⟩ => ?_
  have hb : b = (rQBytes s₀).getD j 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    have := congrArg List.head? hbr
    rw [List.head?_drop, List.head?_cons] at this
    rw [List.getElem?_eq_getElem hj] at this
    exact (Option.some.inj this).symm
  have hd : (rQBytes s₀).drop (j + 1) = rest := by
    rw [← List.drop_drop, hbr, List.drop_one, List.tail_cons]
  refine ⟨?_, hr.congr k (by rw [m]; exact Frame.refl _ _), ?_⟩
  · rw [eval_ne, z]
    by_cases h0 : rest.length = 0
    · rw [decide_eq_true h0, decide_eq_false (by omega_using [hrl, h0])]; rfl
    · rw [decide_eq_false h0, decide_eq_true (by omega_using [hrl, h0])]; rfl
  · rw [hd, show rQ s₀ + BitVec.ofNat 32 (j + 1) = rQ s₀ + BitVec.ofNat 32 j + 1 by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
    show ScanState u _ rest (scanNext (scanAfter (rQBytes s₀) j) ((rQBytes s₀).length - j)
      ((rQBytes s₀).getD j 0))
    rw [← hrl, ← hb]; exact S'

/-- Before the scan. -/
def ScanPre (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.gpr .r1 = rQ s₀ ∧ t.gpr .r2 = BitVec.ofNat 32 (rQBytes s₀).length

theorem significant_ct :
    RelCT isa (Two (At ScanPre)) Random.significant (Two fun a => At (ScanAt a.qBytes.length) a) := by
  unfold Random.significant
  refine RelCT.seq (two_piece (Ψ := fun a t => 0 < a.qBytes.length ∧ At (ScanAt 0) a t) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
  · rintro a t ⟨s₀, A, e, hr, h1, h2⟩
    refine wp_mov (op2_imm (by decide)) fun u₁ v₁ => wp_mov (op2_imm (by decide)) fun u₂ v₂ => WP.block_nil ?_
    have R : Rest [.r3, .r4] t u₂ := (v₁.rest (by decide)).trans (v₂.rest (by decide))
    refine ⟨by rw [← e]; exact rQBytes_pos A, s₀, A, e, hr.congr R (by rw [v₂.mem, v₁.mem]; exact Frame.refl _ _),
      ⟨?_, ?_, ?_, ?_, ?_, by simp [scanAfter], fun _ => rfl⟩⟩
    · rw [BitVec.add_zero, R.gpr _ (by decide)]; exact h1
    · rw [List.drop_zero, R.gpr _ (by decide)]; exact h2
    · rw [v₂.other _ (by decide), v₁.gpr]; rfl
    · rw [v₂.gpr]; rfl
    · rw [BitVec.add_zero, List.drop_zero]
      exact (hr.q A).congr (by rw [v₂.mem, v₁.mem]) (by rw [R.rd]) (by rw [R.wr])
  · refine two_loop (Φ := fun a j => At (ScanAt j) a) (Ψ := fun a => At (ScanAt a.qBytes.length) a)
      (fun a => a.qBytes.length) ?_ ?_
    · unfold significantByte
      refine RelCT.seq (two_piece (Ψ := fun p => At (ScanLoaded p.2) p.1) [.r1]
        (fun p t₁ t₂ h₁ h₂ r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact scanAt_r1 h₁.2 h₂.2) (by taint_decide) ?_) ?_
      · rintro ⟨a, j⟩ t ⟨hj, s₀, A, e, h⟩
        subst e
        exact WP.mono (loadByte_ok h hj) fun u hu => ⟨s₀, A, rfl, hu⟩
      · exact two_taint [.r0, .r1, .r2, .r3, .r4] (fun p t₁ t₂ h₁ h₂ => scanAt_pins h₁ h₂) (by taint_decide)
    · rintro a j t hj ⟨s₀, A, e, h⟩
      subst e
      refine WP.mono (scanStep_ok A h hj) fun u ⟨z, hu⟩ => ⟨z, fun _ => ⟨s₀, A, rfl, hu⟩, fun he => ?_⟩
      have he' : j + 1 = (rQBytes s₀).length := he
      exact ⟨s₀, A, rfl, by show ScanAt (rQBytes s₀).length s₀ u; rw [← he']; exact hu⟩

theorem prepHead_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t)
    (hk : slot t.mem (rBase s₀) oKey = s₀.gpr .r3) :
    WP isa (.block (clearNonce ++ ([ld .r1 oKey, ld .r0 (Random.arg aPLen), .dp .add .r1 .r1 (.reg .r0),
      ld .r2 (Random.arg aQLen)] : List Instr))) t (ScanPre s₀) := by
  have hqn := rQBytes_length A
  refine clearNonce_ok h fun t₁ h₁ m₁ k₁ _ => ?_
  have hk₁ : slot t₁.mem (rBase s₀) oKey = s₀.gpr .r3 := by
    rw [m₁, slot_outs (Outs.of_outside (clearMem_outside t.mem _ 8 (by decide)) (List.mem_singleton_self _))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; decide), hk]
  refine wp_ld h₁ (by decide) fun t₂ u₂ => wp_ldArg A (h₁.upd u₂) (j := 1) (by decide) fun t₃ u₃ =>
    wp_dp (op2_reg _ _) fun t₄ u₄ => wp_ldArg A (((h₁.upd u₂).upd u₃).upd u₄) (j := 2) (by decide)
      fun t₅ u₅ => WP.block_nil ?_
  refine ⟨(((((h₁.upd u₂).upd u₃).upd u₄).upd u₅)), ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr]
    show t₃.gpr .r1 + t₃.gpr .r0 = _
    rw [u₃.other _ (by decide), u₃.gpr, u₂.gpr, hk₁]; rfl
  · rw [u₅.gpr, hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- After the scan. -/
def Scanned (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.gpr .r3 = BitVec.ofNat 32 (scanAfter (rQBytes s₀) (rQBytes s₀).length).1 ∧
    t.gpr .r4 = (scanAfter (rQBytes s₀) (rQBytes s₀).length).2.setWidth 32

theorem prepStore_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) :
    WP isa (.block [ld .r1 oKey, ld .r0 (Random.arg aPLen), .dp .add .r1 .r1 (.reg .r0), ld .r0 (Random.arg aQLen),
      .dp .add .r1 .r1 (.reg .r0), .dp .sub .r1 .r1 (.reg .r3), st .r1 oQ, st .r3 oWidth]) t fun u =>
      RReady s₀ u ∧ u.gpr .r3 = t.gpr .r3 ∧ u.gpr .r4 = t.gpr .r4 := by
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ldArg A (h.upd u₁) (j := 1) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_ldArg A (((h.upd u₁).upd u₂).upd u₃) (j := 2) (by decide) fun t₄ u₄ =>
    wp_dp (op2_reg _ _) fun t₅ u₅ => wp_dp (op2_reg _ _) fun t₆ u₆ =>
    wp_st ((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆) (by decide) fun t₇ m₇ h₇ =>
    wp_st h₇ (by decide) fun t₈ m₈ h₈ => WP.block_nil ?_
  have R : Rest [.r0, .r1] t t₈ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans
    ((m₇.rest _).trans (m₈.rest _)))))))
  exact ⟨h₈, R.gpr _ (by decide), R.gpr _ (by decide)⟩

/-- Before preparing. -/
def PrepPre (s₀ t : State) : Prop := RReady s₀ t ∧ slot t.mem (rBase s₀) oKey = s₀.gpr .r3

theorem prepare_ct : RelCT isa (Two (At PrepPre)) Random.prepare fun _ _ => True := by
  unfold Random.prepare
  refine RelCT.seq (two_piece (Ψ := At ScanPre) [.r11] (pins_at (P := fun _ => PrepPre) id fun _ _ _ h => h.1)
    (by taint_decide)
    fun a t ⟨s₀, A, e, h, hk⟩ => WP.mono (prepHead_ok A h hk) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (significant_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  refine RelCT.seq (two_piece (Ψ := At Scanned) [.r11]
    (pins_r11 (Φ := fun a => At (ScanAt a.qBytes.length) a) id (P := fun a => ScanAt a.qBytes.length)
      (fun _ _ h => h) fun _ _ _ h => h.1) (by taint_decide) ?_) ?_
  · rintro a t ⟨s₀, A, e, hr, S⟩
    subst e
    refine WP.mono (prepStore_ok A hr) fun u ⟨hu, h3, h4⟩ => ⟨s₀, A, rfl, hu, ?_, ?_⟩
    · rw [h3]; exact S.r3
    · rw [h4]; exact S.r4
  · refine two_taint [.r11, .r3, .r4] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
    obtain ⟨s₁, -, e₁, r₁, b₁, d₁⟩ := h₁
    obtain ⟨s₂, -, e₂, r₂, b₂, d₂⟩ := h₂
    have e := e₁.trans e₂.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact r11_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
    · rw [b₁, b₂, pub_qBytes e]
    · rw [d₁, d₂, pub_qBytes e]

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.RandomAttemptCT`, which only this module used -/

section

/-! ### `Dsa.Arm.RandomSampleCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.RandomDrawCT`, which only this module used -/

section

/-!
# A draw leaks only its public bounds and its decision (32-bit ARM)

Two runs of `draw` with the same public data, consumption and budget, whose
complete draws are both accepted or both rejected (`DrawPub.acc`), take
the same branches and addresses: the candidate's bytes reach neither.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd eval_eq eval_ne)
open VG.Proof.Dsa (maskValue copied copiedList copiedList_length copiedList_getD)

/-- The candidate of the draw at `used`. -/
abbrev drawCand (s₀ : State) (used : Nat) : List Byte :=
  copiedList (drawBytes s₀ used) (maskValue (rLead s₀).toNat) (rWidth s₀)

/-- What two runs of a draw share. -/
structure DrawPub where
  pub : Pub
  used : Nat
  draws : Nat
  /-- Whether a complete draw is accepted. -/
  acc : Bool

/-- A draw's entry. -/
structure DrawPre (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ a.used a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  acc : a.used + rWidth s₀ ≤ (rInput s₀).rand.length → accepts s₀ (drawCand s₀ a.used) = a.acc

theorem width_pos {s₀ : State} (hq : 1 < rq s₀) : 1 ≤ rWidth s₀ :=
  Nat.pos_of_ne_zero ((VG.Proof.Dsa.random_valid_scan (rQBytes s₀)).mp hq).1

/-- After the head: the tape's length against the width. -/
def DrawHead (a : DrawPub) (s₀ t : State) : Prop :=
  DrawPre a s₀ t ∧ t.z = decide ((rInput s₀).rand.length - a.used < rWidth s₀)

/-- A complete draw. -/
def DrawFull (a : DrawPub) (s₀ t : State) : Prop :=
  DrawPre a s₀ t ∧ a.used + rWidth s₀ ≤ (rInput s₀).rand.length

/-- After the copy's header and first byte. -/
def CopyHead (a : DrawPub) (s₀ t : State) : Prop :=
  (∃ t₀, CopyInv s₀ t₀ (stackArg s₀ 5 + BitVec.ofNat 32 a.used) (drawPlace s₀) (drawBytes s₀ a.used)
    (maskValue (rLead s₀).toNat) 1 t) ∧ t.z = decide (rWidth s₀ - 1 = 0) ∧
  (drawBytes s₀ a.used).length = rWidth s₀

/-- After the copy's header. -/
def CopyHdr (a : DrawPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.gpr .r1 = stackArg s₀ 5 + BitVec.ofNat 32 a.used ∧ t.gpr .r2 = BitVec.ofNat 32 (rWidth s₀) ∧
    t.gpr .r4 = t.gpr .r11 + BitVec.ofNat 32 (drawPlace s₀)

theorem copyInit_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub) (.block copyInit) fun _ _ => True := by
  unfold copyInit
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun a => At (CopyHdr a) a.pub) [.r11]
    (pins_at DrawPub.pub fun _ _ _ h => h.1.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, D, _⟩ => WP.mono (copyHeader_ok A D.smp.ready D.smp.usedW D.smp.width)
      fun u ⟨h, _, _, x, c, d⟩ => ⟨s₀, A, e, h, x, c, d⟩) ?_
  refine two_taint [.r11, .r1, .r2, .r4] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, x₁, c₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, x₂, c₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  have r11 := r11_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact r11
  · rw [x₁, x₂, pub_arg e 5 (by decide)]
  · rw [c₁, c₂, pub_rWidth e]
  · rw [d₁, d₂, r11, pub_drawPlace e]

theorem copy_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (two_post (Ψ := fun a => At (CopyHead a) a.pub) copyInit_ct
    fun a t ⟨s₀, A, e, D, hf⟩ => ?_) ?_
  · exact WP.mono (copyInit_ok A D.smp.ready D.smp.usedW D.smp.width D.smp.mask hf (width_pos D.q))
      fun u ⟨I, z⟩ => ⟨s₀, A, e, ⟨t, I⟩, z, drawBytes_length hf⟩
  unfold copyRest
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, e₁, _, z₁, _⟩ ⟨s₂, _, e₂, _, z₂, _⟩ => by
    rw [eval_ne, eval_ne, z₁, z₂, pub_rWidth (e₁.trans e₂.symm)]) ?_ ?_
  · refine two_taint [.r1, .r2, .r4] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
    obtain ⟨⟨s₁, _, e₁, ⟨_, I₁⟩, _, l₁⟩, _⟩ := h₁
    obtain ⟨⟨s₂, _, e₂, ⟨_, I₂⟩, _, l₂⟩, _⟩ := h₂
    have e := e₁.trans e₂.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [I₁.r1, I₂.r1, pub_arg e 5 (by decide)]
    · rw [I₁.r2, I₂.r2, l₁, l₂, pub_rWidth e]
    · rw [I₁.r4, I₂.r4, r11_of_rf I₁.ready.rf (pub_rBase e ▸ I₂.ready.rf), pub_drawPlace e]
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

/-- After the copy. -/
structure Copied (a : DrawPub) (s₀ t : State) : Prop where
  pre : DrawPre a s₀ t
  full : a.used + rWidth s₀ ≤ (rInput s₀).rand.length
  bytes : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
    copied (drawBytes s₀ a.used) (maskValue (rLead s₀).toNat) i

/-- After consuming the draw. -/
structure Consumed (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ (a.used + rWidth s₀) a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  acc : accepts s₀ (drawCand s₀ a.used) = a.acc
  bytes : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
    copied (drawBytes s₀ a.used) (maskValue (rLead s₀).toNat) i

/-- Before the comparison's loop. -/
def RangeHead (s₀ t : State) : Prop := ∃ t₀ cs, RangeInv s₀ t₀ cs (rWidth s₀) t

theorem inRange_ct : RelCT isa (Two fun a => At (Consumed a) a.pub) inRange fun _ _ => True := by
  unfold inRange
  refine RelCT.seq (two_piece (Ψ := fun a => At RangeHead a.pub) [.r11]
    (pins_at DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (rangeInit_ok A C.smp.ready (cs := drawCand s₀ a.used) C.smp.q
      C.smp.width (copiedList_length _ _ _)) fun u ⟨I, _⟩ => ⟨s₀, A, e, t, _, I⟩) ?_
  refine two_taint [.r1, .r2, .r4] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, _, _, I₁⟩ := h₁
  obtain ⟨s₂, _, e₂, _, _, I₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [I₁.r1, I₂.r1, pub_rQ e, pub_qBytes e, pub_rWidth e]
  · rw [I₁.r2, I₂.r2, pub_rWidth e]
  · rw [I₁.r4, I₂.r4, r11_of_rf I₁.ready.rf (pub_rBase e ▸ I₂.ready.rf), pub_drawPlace e, pub_rWidth e]

/-- Before the decision. -/
structure Decided (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ (a.used + rWidth s₀) a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  z : t.z = !a.acc

/-- After spending a draw. -/
def Spent (a : DrawPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = decide (a.draws - 1 = 0)

theorem drawFinish_ct : RelCT isa (Two fun a => At (Decided a) a.pub) drawFinish fun _ _ => True := by
  unfold drawFinish
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, D₁⟩ ⟨_, _, _, D₂⟩ => by rw [eval_ne, eval_ne, D₁.z, D₂.z]) ?_ ?_
  · exact two_taint [.r11] (pins_at' DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
  refine RelCT.seq (two_piece (Ψ := fun a => At (Spent a) a.pub) [.r11]
    (pins_at' DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨⟨s₀, A, e, D⟩, _⟩ => WP.mono (drawDec_ok A D.smp D.pos D.le)
      fun u ⟨_, _, _, h, z, _⟩ => ⟨s₀, A, e, h, z⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by rw [eval_eq, eval_eq, z₁, z₂]) ?_ ?_
  · exact two_taint [.r11] (pins_at' DrawPub.pub fun _ _ _ h => h.1) (by taint_decide)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

/-- After the comparison, the decision: the draw's acceptance. -/
theorem inRange_decided {a : DrawPub} {s₀ t : State} (A : RandomABI s₀) (C : Consumed a s₀ t) :
    WP isa inRange t (Decided a s₀) :=
  WP.mono (inRange_ok A C.smp.ready (cs := drawCand s₀ a.used) C.smp.q C.smp.width (copiedList_length _ _ _)
    (width_pos C.q) fun i hi => by rw [copiedList_getD _ _ hi]; exact C.bytes i hi)
    fun u ⟨_, z, m, h, _⟩ => ⟨C.smp.congr A h (by rw [m]; exact Outs.refl _ _ _) (by rw [m]) (by rw [m]),
      C.pos, C.le, by rw [z, C.acc]⟩

theorem full_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub)
    (.seq copy (.seq (.block [ld .r0 oUsed, ld .r7 oWidth, .dp .add .r0 .r0 (.reg .r7), st .r0 oUsed])
      (.seq inRange drawFinish))) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := fun a => At (Copied a) a.pub) copy_ct
    fun a t ⟨s₀, A, e, D, hf⟩ => WP.mono (drawCopy_ok A D.smp hf (width_pos D.q))
      fun u ⟨S, hc, _, _⟩ => ⟨s₀, A, e, { D with smp := S }, hf, hc⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun a => At (Consumed a) a.pub) [.r11]
    (pins_at DrawPub.pub fun _ _ _ h => h.pre.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (drawUsed_ok A C.pre.smp C.full)
      fun u ⟨S, hm, _⟩ => ⟨s₀, A, e, S, C.pre.pos, C.pre.le, C.pre.q, C.pre.acc C.full,
        drawUsed_bytes A hm C.bytes⟩) ?_
  exact RelCT.seq (two_post (Ψ := fun a => At (Decided a) a.pub) inRange_ct
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (inRange_decided A C) fun u D => ⟨s₀, A, e, D⟩) drawFinish_ct

theorem draw_ct : RelCT isa (Two fun a => At (DrawPre a) a.pub) draw fun _ _ => True := by
  unfold draw
  refine RelCT.seq (two_piece (Ψ := fun a => At (DrawHead a) a.pub) [.r11]
    (pins_at DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, D⟩ => WP.mono (drawHead_ok A D.smp)
      fun u ⟨S, _, _, c⟩ => ⟨s₀, A, e, { D with smp := S }, c⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, e₁, _, c₁⟩ ⟨s₂, _, e₂, _, c₂⟩ => by
    have e := e₁.trans e₂.symm
    rw [eval_eq, eval_eq, c₁, c₂, pub_randLen e, pub_rWidth e]) ?_ ?_
  · exact two_taint [.r11] (pins_at' DrawPub.pub fun _ _ _ h => h.1.smp.ready) (by taint_decide)
  · refine two_map id (fun a t ⟨⟨s₀, A, e, D, c⟩, hb⟩ => ⟨s₀, A, e, D, ?_⟩) full_ct
    have := D.smp.usedBound
    show a.used + rWidth s₀ ≤ (rInput s₀).rand.length
    rw [eval_eq, c, Option.some.injEq, decide_eq_false_iff_not] at hb
    omega_using [hb, this]

end VG.Proof.Dsa.Arm

end

end

/-!
# Sampling leaks only its trace (32-bit ARM)

Two runs of the sampler whose specification traces agree draw alike: each
draw's decision is the trace's head (`LoopAt.drawPre`), so they take the
same branches; after a rejection the rest of the trace is the next draw's.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)

/-- The width of q's significant bytes. -/
def Pub.width (a : Pub) : Nat := (VG.Proof.Dsa.significant a.qBytes).1

theorem pub_width {s₀ : State} {a : Pub} (e : pubOf s₀ = a) : a.width = rWidth s₀ := by
  rw [← e]; rfl

/-- What two runs share before a draw of the sampling loop. -/
structure LoopPub where
  pub : Pub
  used : Nat
  draws : Nat
  tr : List Nat

/-- Before a draw of the sampling loop, whose trace is `tr`. -/
structure LoopAt (a : LoopPub) (s₀ t : State) : Prop where
  smp : Smp s₀ a.used a.draws t
  status : slot t.mem (rBase s₀) oStatus = 4
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  tr : (spl s₀ a.draws a.used).trace = a.tr

/-- Whether the loop draws again: a rejection, and draws left. -/
def LoopPub.cont (a : LoopPub) : Bool := (a.tr.head? == some 0) && decide (2 ≤ a.draws)

def LoopPub.next (a : LoopPub) : LoopPub := ⟨a.pub, a.used + a.pub.width, a.draws - 1, a.tr.tail⟩

/-- The draw's decision is the trace's. -/
theorem LoopAt.drawPre {a : LoopPub} {s₀ t : State} (L : LoopAt a s₀ t) :
    DrawPre ⟨a.pub, a.used, a.draws, a.tr.head? == some 1⟩ s₀ t := by
  refine ⟨L.smp, L.pos, L.le, L.q, fun hfull => ?_⟩
  dsimp only at hfull
  obtain ⟨d', hd'⟩ : ∃ d', a.draws = d' + 1 := ⟨a.draws - 1, by have := L.pos; omega_using [this]⟩
  have hdw : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ := rWidth_eq s₀
  have hdl : (drawBytes s₀ a.used).length = rWidth s₀ := drawBytes_length hfull
  have htr := L.tr
  rw [hd'] at htr
  show accepts s₀ (drawCand s₀ a.used) = (a.tr.head? == some 1)
  rw [accepts_candidate hdl (width_pos L.q), ← htr, spl,
    VG.Proof.Dsa.Random.sample_trace_head _ _ _ L.q (by rw [hdw, List.length_drop]; omega_using [hfull]), hdw]

def sampleBody : Prog isa := .seq draw (.block [ld .r0 oStatus, .cmp .r0 (.imm 4)])

/-- After a draw and the loop's test. -/
def StepPost (a : LoopPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = a.cont ∧ (a.cont = true → LoopAt a.next s₀ t)

theorem sub_four_ne {x : BitVec 32} (h : x ≠ 4) : (x - 4 == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h'
  apply h
  calc x = x - 4 + 4 := (BitVec.sub_add_cancel x 4).symm
    _ = 4 := by rw [h']; rfl

theorem step_ok {a : LoopPub} {s₀ t : State} (A : RandomABI s₀) (e : pubOf s₀ = a.pub) (L : LoopAt a s₀ t) :
    WP isa sampleBody t (StepPost a s₀) := by
  unfold sampleBody
  refine WP.seq (WP.mono (draw_ok A L.smp L.pos L.le L.q L.status) fun v ⟨hv, _, _, hcase⟩ => ?_)
  refine wp_ld hv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
  have hv₂ : RReady s₀ v₂ := (hv.upd uv₁).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  have htr := L.tr
  rcases hcase with ⟨stv, h2, Sv, _, hspl⟩ | ⟨stv, _, hh⟩
  · have hc : a.cont = true := by
      simp only [LoopPub.cont, ← htr, hspl, List.head?_cons, beq_self_eq_true, Bool.true_and,
        decide_eq_true_eq]
      exact h2
    refine ⟨hv₂, by rw [zv₂, uv₁.gpr, stv, hc]; rfl, fun _ => ⟨?_, by rw [mv₂]; exact stv,
      by show 1 ≤ a.draws - 1; omega_using [h2], by show a.draws - 1 ≤ 128; have := L.le; omega_using [this], L.q, ?_⟩⟩
    · show Smp s₀ (a.used + a.pub.width) (a.draws - 1) v₂
      rw [pub_width e]; exact Sv.mem A hv₂ mv₂
    · show (spl s₀ (a.draws - 1) (a.used + a.pub.width)).trace = a.tr.tail
      rw [pub_width e, ← htr, hspl]; rfl
  · have hc : a.cont = false := by
      simp only [LoopPub.cont, ← htr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      rcases hh with hh | hh
      · exact .inl hh
      · exact .inr (by omega_using [hh])
    refine ⟨hv₂, by rw [zv₂, uv₁.gpr, sub_four_ne stv, hc], fun h => by rw [hc] at h; cases h⟩

theorem sampleLoop_ct (n : Nat) :
    RelCT isa (Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) (.loop sampleBody .eq)
      (Two fun (a : Pub) => At (fun s₀ t => RReady s₀ t) a) := by
  refine RelCT.loop (M := isa) (fun n => Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) (fun n => ?_) n
  have hct : RelCT isa (Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) sampleBody fun _ _ => True := by
    unfold sampleBody
    refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => RReady s₀ t) a.pub)
      (two_map (fun a => (⟨a.pub, a.used, a.draws, a.tr.head? == some 1⟩ : DrawPub))
        (fun a t ⟨_, s₀, A, e, L⟩ => ⟨s₀, A, e, L.drawPre⟩) draw_ct)
      (fun a t ⟨_, s₀, A, e, L⟩ => WP.mono (draw_ok A L.smp L.pos L.le L.q L.status)
        fun u h => ⟨s₀, A, e, h.1⟩)) ?_
    exact two_taint [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t) LoopPub.pub fun _ _ _ h => h)
      (by taint_decide)
  have hp := two_post (Ψ := fun a t => a.draws = n ∧ At (StepPost a) a.pub t) hct
    fun a t ⟨hn, s₀, A, e, L⟩ => WP.mono (step_ok A e L) fun u h => ⟨hn, s₀, A, e, h⟩
  refine hp.mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨a, ⟨hn, s₁, A₁, e₁, r₁, z₁, c₁⟩, ⟨_, s₂, A₂, e₂, r₂, z₂, c₂⟩⟩
  refine ⟨by rw [eval_eq, eval_eq, z₁, z₂], fun _ => ⟨a.pub, ⟨s₁, A₁, e₁, r₁⟩, ⟨s₂, A₂, e₂, r₂⟩⟩, fun hc => ?_⟩
  have hc' : a.cont = true := by rw [eval_eq, z₁, Option.some.injEq] at hc; exact hc
  have h2 : 2 ≤ a.draws := by
    simp only [LoopPub.cont, Bool.and_eq_true, decide_eq_true_eq] at hc'; exact hc'.2
  exact ⟨n - 1, by omega, a.next, ⟨by show a.draws - 1 = n - 1; omega_using [hn], s₁, A₁, e₁, c₁ hc'⟩,
    ⟨by show a.draws - 1 = n - 1; omega_using [hn], s₂, A₂, e₂, c₂ hc'⟩⟩

/-- What two runs of the sampler share. -/
structure SmpPub where
  pub : Pub
  used : Nat
  tr : List Nat

/-- The sampler's entry. -/
def SamplePre (a : SmpPub) (s₀ t : State) : Prop :=
  (∃ d, Smp s₀ a.used d t) ∧ 1 < rq s₀ ∧ (spl s₀ 128 a.used).trace = a.tr

theorem sample_ct : RelCT isa (Two fun a => At (SamplePre a) a.pub) sample fun _ _ => True := by
  unfold sample
  refine RelCT.seq (two_piece (Ψ := fun a => At (LoopAt ⟨a.pub, a.used, 128, a.tr⟩) a.pub) [.r11]
    (pins_at SmpPub.pub fun _ _ _ h => h.1.choose_spec.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, ⟨d, S⟩, hq, htr⟩ => WP.mono (sampleInit_ok A S)
      fun u ⟨S', st, _, _⟩ => ⟨s₀, A, e, S', st, (by decide : 1 ≤ 128), (by decide : 128 ≤ 128), hq, htr⟩) ?_
  refine RelCT.seq (two_map (fun a => (⟨a.pub, a.used, 128, a.tr⟩ : LoopPub)) (fun _ _ h => ⟨rfl, h⟩)
    (sampleLoop_ct 128)) ?_
  exact two_taint [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t) id fun _ _ _ h => h) (by taint_decide)

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.RandomCallCT`, which only this module used -/

section

/-!
# The signer's call leaks only what its contract allows (32-bit ARM)

Two runs push the same public words and call `vg_dsa_sign` with the same
public arguments, public key bytes and signing status (`call_pub`), which
its contract's constant time covers (`callSigner_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign

theorem pub_callRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callRd s₁ = callRd s₂ := by
  simp only [callRd, nonceR, rKeyR, rDigestR, pub_r3 e, pub_arg e 0 (by decide), pub_arg e 2 (by decide),
    pub_arg e 3 (by decide), pub_arg e 4 (by decide), pub_rLow e, pub_rBase e]

theorem pub_callWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callWr s₁ = callWr s₂ := by
  simp only [callWr, rOut, rScratch, pub_r0 e, pub_r1 e, pub_arg e 7 (by decide), pub_arg e 8 (by decide)]

/-- What the signer may leak: the public key bytes and its status. -/
theorem signLeak_call {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u) :
    signLeak (callEntryOf s₀ u) = keyLeak s₀ ++ [Spec.Dsa.signStatus (callResult s₀ u)] := by
  have hf := call_push_frame A h
  have ek : Spec.Rsa.bytesAt (pushed callPush u).mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat =
      (rInput s₀).key := by
    rw [rBytes_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (A.stackKey.sub_left (low_sub s₀ (by decide))).symm)
      (by have := (stackArg s₀ 0).isLt; omega_using []), callKey A h]
  unfold signLeak
  rw [signRes_call A h C]
  simp only [State.withRegions_mem, State.callEntry_mem, ce_r2 C, ce_r3 C, ce_a0 A h C, ce_a2 A h C, ek]
  rfl

/-- Two runs about to call the signer alike. -/
def CallRel (S : Signer) (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, RandomABI s₁ ∧ RandomABI s₂ ∧ RValid S s₁ ∧ RValid S s₂ ∧ pubOf s₁ = pubOf s₂ ∧ keyLeak s₁ = keyLeak s₂ ∧
    RReady s₁ t₁ ∧ RReady s₂ t₂ ∧ CallRegs s₁ t₁ ∧ CallRegs s₂ t₂ ∧
    Spec.Dsa.signStatus (callResult s₁ t₁) = Spec.Dsa.signStatus (callResult s₂ t₂)

theorem call_pub {s₁ s₂ t₁ t₂ : State} (A₁ : RandomABI s₁) (A₂ : RandomABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : keyLeak s₁ = keyLeak s₂) (h₁ : RReady s₁ t₁) (h₂ : RReady s₂ t₂) (C₁ : CallRegs s₁ t₁)
    (C₂ : CallRegs s₂ t₂)
    (hr : Spec.Dsa.signStatus (callResult s₁ t₁) = Spec.Dsa.signStatus (callResult s₂ t₂)) :
    signArm.pub (callEntryOf s₁ t₁) (callEntryOf s₂ t₂) := by
  have r11 := r11_of_rf h₁.rf (pub_rBase e ▸ h₂.rf)
  have ea : ∀ i (hi : i < 8), stackArg (callEntryOf s₁ t₁) i = t₁.gpr callPush[i] ∧
      stackArg (callEntryOf s₂ t₂) i = t₂.gpr callPush[i] :=
    fun i hi => ⟨callEntry_arg A₁ h₁ hi, callEntry_arg A₂ h₂ hi⟩
  refine ⟨?_, by rw [signLeak_call A₁ h₁ C₁, signLeak_call A₂ h₂ C₂, hk, hr], by rw [ce_r0 C₁, ce_r0 C₂, pub_r0 e],
    by rw [ce_r1 C₁, ce_r1 C₂, pub_r1 e], by rw [ce_r2 C₁, ce_r2 C₂, pub_r3 e],
    by rw [ce_r3 C₁, ce_r3 C₂, pub_arg e 0 (by decide)], fun i hi => ?_⟩
  · show (pushed callPush t₁).sp = (pushed callPush t₂).sp
    rw [pushed_sp, pushed_sp, h₁.sp, h₂.sp, pub_sp e]
  · show stackArg (callEntryOf s₁ t₁) i = stackArg (callEntryOf s₂ t₂) i
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
      omega_using [hi]
    · rw [(ea 0 (by decide)).1, (ea 0 (by decide)).2]
      exact C₁.r4.trans ((pub_arg e 1 (by decide)).trans C₂.r4.symm)
    · rw [(ea 1 (by decide)).1, (ea 1 (by decide)).2]
      exact C₁.r5.trans (by rw [r11]; exact C₂.r5.symm)
    · rw [(ea 2 (by decide)).1, (ea 2 (by decide)).2]
      exact C₁.r6.trans ((pub_arg e 2 (by decide)).trans C₂.r6.symm)
    · rw [(ea 3 (by decide)).1, (ea 3 (by decide)).2]
      exact C₁.r7.trans ((pub_arg e 3 (by decide)).trans C₂.r7.symm)
    · rw [(ea 4 (by decide)).1, (ea 4 (by decide)).2]
      exact C₁.r8.trans ((pub_arg e 4 (by decide)).trans C₂.r8.symm)
    · rw [(ea 5 (by decide)).1, (ea 5 (by decide)).2]
      exact C₁.r9.trans ((pub_arg e 7 (by decide)).trans C₂.r9.symm)
    · rw [(ea 6 (by decide)).1, (ea 6 (by decide)).2]
      exact C₁.r10.trans ((pub_arg e 8 (by decide)).trans C₂.r10.symm)

theorem callSigner_ct (S : Signer) (name : String) : RelCT isa (CallRel S) (callSigner name S.code)
    fun _ _ => True := by
  unfold callSigner
  refine RelCT.frame (fun t₁ t₂ ⟨s₁, s₂, _, _, _, _, e, _, h₁, h₂, _⟩ => by rw [h₁.sp, h₂.sp, pub_sp e]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨s₁, s₂, A₁, A₂, V₁, V₂, e, hk, h₁, h₂, C₁, C₂, hr⟩, p₁, p₂⟩ := hp
  rw [push_pushed (by decide) (call_sp_le A₁ h₁), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (call_sp_le A₂ h₂), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := signArmWith S.valid)
    S.correct S.constantTime
    (callRd s₁) (callWr s₁) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := call_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := call_covers A₂ h₂
  have p₂ : (signArmWith S.valid).pre ((pushed callPush t₂).callEntry.withRegions (callRd s₂) (callWr s₂)) :=
    call_pre_with S A₂ h₂ C₂ V₂
  have pb : signArm.pub ((pushed callPush t₁).callEntry.withRegions (callRd s₁) (callWr s₁))
      ((pushed callPush t₂).callEntry.withRegions (callRd s₂) (callWr s₂)) := call_pub A₁ A₂ e hk h₁ h₂ C₁ C₂ hr
  rw [← pub_callRd e, ← pub_callWr e] at p₂ c₂ pb
  rw [← pub_callWr e] at w₂
  exact ⟨call_pre_with S A₁ h₁ C₁ V₁, p₂, pb, c₁, w₁, c₂, w₂⟩

end VG.Proof.Dsa.Arm

end

end

/-!
# An attempt leaks only its trace (32-bit ARM)

The rest of the specification's signing (`randomSignRemaining`) has a trace
that records the attempt's sampling (`randomSamplingTrace`), whether it
found a nonce (`AttPub.ok`) and whether signing with it succeeded
(`AttPub.signed`). Two runs with the same public data, consumption,
attempts and trace take the same branches.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

variable {S : Signer}

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)
open VG.Proof.Dsa (randomSignRemaining randomSamplingTrace randomSigningTrace)

/-- What two runs share before an attempt. -/
structure AttPub where
  pub : Pub
  leak : List Nat
  used : Nat
  fuel : Nat
  tr : List Nat
  /-- The overall status. -/
  status : Nat

/-- Whether the attempt's sampling finds a nonce. -/
def AttPub.ok (a : AttPub) : Bool := (randomSamplingTrace a.tr).getLast? == some 1

/-- Whether signing with it succeeds. -/
def AttPub.signed (a : AttPub) : Bool := randomSigningTrace a.tr == [5]

/-- What the attempt keeps of its entry. -/
structure AttFacts (S : Signer) (a : AttPub) (s₀ : State) : Prop where
  q : 1 < rq s₀
  pos : 1 ≤ a.fuel
  le : a.fuel ≤ 8
  leak : keyLeak s₀ = a.leak
  tr : (randomSignRemaining (rInput s₀) a.used a.fuel).trace = a.tr
  valid : RValid S s₀

/-- Before an attempt. -/
def AttAt (S : Signer) (a : AttPub) (s₀ t : State) : Prop := AttFacts S a s₀ ∧ Att s₀ a.used a.fuel t

theorem AttFacts.spl_trace {a : AttPub} {s₀ : State} (F : AttFacts S a s₀) :
    (spl s₀ 128 a.used).trace = randomSamplingTrace a.tr := by
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := F.pos; omega_using [this]⟩
  rw [← F.tr, hf]
  exact (VG.Proof.Dsa.random_sign_trace_draw _ _ _).symm

theorem AttFacts.ok {a : AttPub} {s₀ : State} (F : AttFacts S a s₀) :
    (spl s₀ 128 a.used).scalar.isSome = a.ok := by
  rw [(VG.Proof.Dsa.Random.sample_trace_result _ _ _).2, F.spl_trace]; rfl

theorem AttFacts.status {a : AttPub} {s₀ : State} (F : AttFacts S a s₀) :
    decide (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used) = 1) = a.ok := by
  rw [← F.ok]
  unfold VG.Proof.Dsa.Random.sampleStatus
  split
  · next h => simp [h]
  · next h => simp only [h, Option.isSome_none]; split <;> decide

theorem AttFacts.signed {a : AttPub} {s₀ : State} (F : AttFacts S a s₀) {k : Nat}
    (hk : (spl s₀ 128 a.used).scalar = some k) :
    (Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest).isSome = a.signed := by
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := F.pos; omega_using [this]⟩
  have htr := F.tr
  rw [hf] at htr
  unfold AttPub.signed
  rw [← htr]
  cases hs : Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest with
  | some sig => rw [VG.Proof.Dsa.random_sign_trace_success _ _ _ _ hk hs]; rfl
  | none => rw [VG.Proof.Dsa.random_sign_trace_retry _ _ _ _ hk hs]; simp

/-- After sampling. -/
structure Sampled (S : Signer) (a : AttPub) (s₀ t : State) : Prop where
  facts : AttFacts S a s₀
  out : SampleOut s₀ a.used (spl s₀ 128 a.used) t
  ready : RReady s₀ t
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel
  saved : Saved s₀ t.mem

theorem sample_sampled {a : AttPub} {s₀ t : State} (A : RandomABI s₀) (h : AttAt S a s₀ t) :
    WP isa sample t fun u => Sampled S a s₀ u ∧
      u.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used)) := by
  obtain ⟨F, T⟩ := h
  obtain ⟨d₀, Sm⟩ := T.smp
  exact WP.mono (sample_ok A Sm F.q) fun u₁ ⟨O, r0₁, h₁, o₁, _⟩ =>
    ⟨⟨F, O, h₁, (slot_outs o₁ (by decide) (by decide)).trans T.attempts, T.saved.of_outs o₁ (by decide)⟩, r0₁⟩

/-- After the test of the sampling's status. -/
def Tested (S : Signer) (a : AttPub) (s₀ t : State) : Prop := Sampled S a s₀ t ∧ t.z = a.ok

/-- After loading the signer's arguments. -/
structure Args (S : Signer) (a : AttPub) (s₀ t : State) : Prop where
  facts : AttFacts S a s₀
  ready : RReady s₀ t
  regs : CallRegs s₀ t
  nonce : ∃ k, (spl s₀ 128 a.used).scalar = some k ∧
    Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length = Spec.Dsa.encodeBE (rQBytes s₀).length k
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem args_ok {a : AttPub} {s₀ t : State} (A : RandomABI s₀) (h : Tested S a s₀ t)
    (hok : a.ok = true) : WP isa (.block callArgs) t (Args S a s₀) := by
  obtain ⟨S, -⟩ := h
  obtain ⟨k, hk⟩ : ∃ k, (spl s₀ 128 a.used).scalar = some k := by
    have := S.facts.ok
    rw [hok] at this
    exact Option.isSome_iff_exists.mp this
  exact WP.mono (callArgs_ok A S.ready S.saved) fun u₃ ⟨h₃, m₃, C₃, _⟩ =>
    ⟨S.facts, h₃, C₃, ⟨k, hk, by rw [m₃]; exact S.out.nonce k hk⟩, by rw [m₃]; exact S.attempts⟩

/-- After the call. -/
structure Called (a : AttPub) (s₀ t : State) : Prop where
  pos : 1 ≤ a.fuel
  le : a.fuel ≤ 8
  ready : RReady s₀ t
  r0 : t.gpr .r0 = BitVec.ofNat 32 (if a.signed then 1 else 0)
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem Args.status {a : AttPub} {s₀ t : State} (A : RandomABI s₀) (h : Args S a s₀ t) :
    Spec.Dsa.signStatus (callResult s₀ t) = if a.signed then 1 else 0 := by
  obtain ⟨k, hk, hn⟩ := h.nonce
  rw [callResult_eq A h.ready hn, Spec.Dsa.signStatus, h.facts.signed hk]

theorem call_called (S : Signer) (name : String) {a : AttPub} {s₀ t : State} (A : RandomABI s₀)
    (h : Args S a s₀ t) :
    WP isa (callSigner name S.code) t (Called a s₀) :=
  WP.mono (callSigner_ok S A h.ready h.regs h.facts.valid name) fun u ⟨h₄, f₄, _, r0₄, _⟩ =>
    ⟨h.facts.pos, h.facts.le, h₄, by rw [r0₄, h.status A],
      by rw [call_frame_slot A f₄ (by decide)]; exact h.attempts⟩

/-- After recording the signer's status. -/
def Recorded (a : AttPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = !a.signed ∧ slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel ∧
    1 ≤ a.fuel ∧ a.fuel ≤ 8

/-- After spending an attempt. -/
def Spent' (a : AttPub) (s₀ t : State) : Prop := RReady s₀ t ∧ t.z = decide (a.fuel - 1 = 0)

theorem callFinish_ct : RelCT isa (Two fun a => At (Called a) a.pub) callFinish fun _ _ => True := by
  unfold callFinish
  refine RelCT.seq (two_piece (Ψ := fun a => At (Recorded a) a.pub) [.r11]
    (pins_at AttPub.pub fun _ _ _ h => h.ready) (by taint_decide) fun a t ⟨s₀, A, e, C⟩ => ?_) ?_
  · refine WP.mono (finHead_ok C.ready (k := if a.signed then 1 else 0) (by split <;> decide) C.r0)
      fun u ⟨h, _, m, z⟩ => ⟨s₀, A, e, h, ?_, ?_, C.pos, C.le⟩
    · rw [z]; cases a.signed <;> rfl
    · rw [m, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact C.attempts
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁, _⟩ ⟨_, _, _, _, z₂, _⟩ => by rw [eval_eq, eval_eq, z₁, z₂]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun a => At (Spent' a) a.pub) [.r11]
      (pins_at' AttPub.pub fun _ _ _ h => h.1) (by taint_decide)
      fun a t ⟨⟨s₀, A, e, h, _, ha, hp, hl⟩, _⟩ => ?_) ?_
    · obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by omega_using [hp]⟩
      rw [hf] at ha hl
      refine WP.mono (finDec_ok h ha hl) fun u ⟨h', _, _, z⟩ => ⟨s₀, A, e, h', ?_⟩
      rw [z, hf, Nat.add_sub_cancel]
    · refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by rw [eval_ne, eval_ne, z₁, z₂]) ?_ ?_
      · exact two_taint [.r11] (pins_at' AttPub.pub fun _ _ _ h => h.1) (by taint_decide)
      · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

theorem signerCall_ct (S : Signer) (name : String) :
    RelCT isa (Two fun a => At (Args S a) a.pub) (callSigner name S.code) fun _ _ => True :=
  (callSigner_ct S name).mono (fun t₁ t₂ ⟨a, ⟨s₁, A₁, e₁, h₁⟩, ⟨s₂, A₂, e₂, h₂⟩⟩ =>
    ⟨s₁, s₂, A₁, A₂, h₁.facts.valid, h₂.facts.valid, e₁.trans e₂.symm, h₁.facts.leak.trans h₂.facts.leak.symm, h₁.ready, h₂.ready,
      h₁.regs, h₂.regs, by rw [h₁.status A₁, h₂.status A₂]⟩) fun _ _ h => h

theorem attempt_ct (S : Signer) (name : String) :
    RelCT isa (Two fun a => At (AttAt S a) a.pub) (attempt name S.code) fun _ _ => True := by
  unfold attempt
  refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => Sampled S a s₀ t ∧
      t.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used))) a.pub)
    (two_map (fun a => (⟨a.pub, a.used, randomSamplingTrace a.tr⟩ : SmpPub))
      (fun a t ⟨s₀, A, e, F, T⟩ => ⟨s₀, A, e, T.smp, F.q, F.spl_trace⟩) sample_ct)
    fun a t ⟨s₀, A, e, h⟩ => WP.mono (sample_sampled A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun a => At (Tested S a) a.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
    fun a t ⟨s₀, A, e, S, r0⟩ => wp_cmp (op2_imm (by decide)) fun u fu z => WP.block_nil ⟨s₀, A, e, ?_, ?_⟩) ?_
  · exact ⟨S.facts, ⟨let ⟨d, Sd⟩ := S.out.smp; ⟨d, Sd.mem A (S.ready.fupd fu) fu.mem⟩,
      by rw [fu.mem]; exact S.out.status, by rw [fu.mem]; exact S.out.nonce⟩, S.ready.fupd fu,
      by rw [fu.mem]; exact S.attempts, by rw [fu.mem]; exact S.saved⟩
  · have hle := sampleStatus_le (spl s₀ 128 a.used)
    rw [z, r0, one_beq (by omega_using [hle]), S.facts.status]
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by rw [eval_eq, eval_eq, z₁, z₂]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun a => At (Args S a) a.pub) [.r11]
      (pins_at' AttPub.pub fun _ _ _ h => h.1.ready) (by taint_decide)
      fun a t ⟨⟨s₀, A, e, h⟩, hb⟩ => WP.mono (args_ok A h (by
        rw [eval_eq, h.2, Option.some.injEq] at hb; exact hb)) fun u hu => ⟨s₀, A, e, hu⟩) ?_
    exact RelCT.seq (two_post (Ψ := fun a => At (Called a) a.pub) (signerCall_ct S name)
      fun a t ⟨s₀, A, e, h⟩ => WP.mono (call_called S name A h) fun u hu => ⟨s₀, A, e, hu⟩) callFinish_ct
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

end VG.Proof.Dsa.Arm

end

end

/-!
# The randomized signer's body leaks only its public data (32-bit ARM)

The entry computes the frame's base from `sp` (`entry_ct`). The attempts
continue after a retry with attempts left, which the signing trace records
(`AttPub.cont`); the next attempt's trace is the rest of it. `finish`
branches on the overall status, and writes through the public `out` and
`used` pointers.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

variable {S : Signer}

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)
open VG.Proof.Dsa (randomSignRemaining randomSamplingTrace randomSigningTrace)

/-! ## The attempts -/

/-- Whether another attempt follows: a retry, with attempts left. -/
def AttPub.cont (a : AttPub) : Bool := ((randomSigningTrace a.tr).head? == some 6) && decide (2 ≤ a.fuel)

def AttPub.next (a : AttPub) : AttPub :=
  ⟨a.pub, a.leak, a.used + a.pub.width * (randomSamplingTrace a.tr).countP (· ≤ 1), a.fuel - 1,
    (randomSigningTrace a.tr).tail, a.status⟩

/-- The test of the attempt's status. -/
abbrev attTest : Prog isa := .block [ld .r0 oStatus, .cmp .r0 (.imm 4)]

theorem AttemptOut.ready {s₀ u : State} {used f : Nat} (h : AttemptOut s₀ used f u) : RReady s₀ u := by
  rcases h with ⟨_, _, T, _⟩ | ⟨_, D, _⟩
  · obtain ⟨_, S⟩ := T.smp; exact S.ready
  · obtain ⟨_, S⟩ := D.smp; exact S.ready

/-- After an attempt and its test. -/
def AStep (S : Signer) (a : AttPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = a.cont ∧ (a.cont = true → AttAt S a.next s₀ t) ∧ (a.cont = false → RFin s₀ t)

theorem astep_ok (S : Signer) (name : String) {a : AttPub} {s₀ t : State} (A : RandomABI s₀)
    (e : pubOf s₀ = a.pub) (L : AttAt S a s₀ t) :
    WP isa (.seq (attempt name S.code) attTest) t (AStep S a s₀) := by
  obtain ⟨Fa, T⟩ := L
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := Fa.pos; omega_using [this]⟩
  have hf8 : f + 1 ≤ 8 := hf ▸ Fa.le
  rw [hf] at T
  refine WP.seq (WP.mono (attempt_ok S name A T hf8 Fa.q Fa.valid) fun v hv => ?_)
  have hrv := hv.ready
  refine wp_ld hrv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
  have hv₂ := (hrv.upd uv₁).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  rw [uv₁.gpr] at zv₂
  have htr := Fa.tr
  rw [hf] at htr
  rcases hv with ⟨st, h1f, T', hs⟩ | ⟨st, D, hh⟩
  · have hc : a.cont = true := by
      simp only [AttPub.cont, ← htr, hs, List.head?_cons, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
      omega_using [hf, h1f]
    refine ⟨hv₂, by rw [zv₂, st, hc]; rfl, fun _ => ?_, fun h => Bool.noConfusion (hc.symm.trans h)⟩
    have hu : a.pub.width * (randomSamplingTrace a.tr).countP (· ≤ 1) = (spl s₀ 128 a.used).used := by
      rw [(VG.Proof.Dsa.Random.sample_trace_result _ _ _).1, Fa.spl_trace, pub_width e, rWidth_eq]
    refine ⟨⟨Fa.q, by show 1 ≤ a.fuel - 1; omega_using [hf, h1f], by show a.fuel - 1 ≤ 8; omega_using [hf, hf8], Fa.leak, ?_, Fa.valid⟩, ?_⟩
    · show (randomSignRemaining (rInput s₀) (a.used + a.pub.width * _) (a.fuel - 1)).trace =
        (randomSigningTrace a.tr).tail
      rw [hu, hf, Nat.add_sub_cancel, ← htr, hs]; rfl
    · show Att s₀ (a.used + a.pub.width * _) (a.fuel - 1) v₂
      rw [hu, hf, Nat.add_sub_cancel]; exact T'.mem A hv₂ mv₂
  · have hc : a.cont = false := by
      simp only [AttPub.cont, ← htr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        decide_eq_false_iff_not]
      by_cases h6 : (randomSigningTrace (randomSignRemaining (rInput s₀) a.used (f + 1)).trace).head? = some 6
      · exact .inr fun h2 => hh ⟨h6, by omega⟩
      · exact .inl h6
    exact ⟨hv₂, by rw [zv₂, sub_four_ne st, hc], fun h => Bool.noConfusion (hc.symm.trans h),
      fun _ => (D.mem A hv₂ mv₂).rfin⟩

/-- At the end: the frame's slots, and the overall status `p.2`. -/
def FinAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => RFin s₀ t ∧ (rResult s₀).status = p.2) p.1

/-- Before an attempt, with the overall status. -/
def LoopAt' (S : Signer) (a : AttPub) : State → Prop := At (fun s₀ t => AttAt S a s₀ t ∧ (rResult s₀).status = a.status) a.pub

theorem attemptLoop_ct (S : Signer) (name : String) (n : Nat) :
    RelCT isa (Two fun a t => a.fuel = n ∧ LoopAt' S a t)
      (.loop (.seq (attempt name S.code) attTest) .eq) (Two FinAt) := by
  refine RelCT.loop (M := isa) (fun n => Two fun a t => a.fuel = n ∧ LoopAt' S a t) (fun n => ?_) n
  have hct : RelCT isa (Two fun a t => a.fuel = n ∧ LoopAt' S a t)
      (.seq (attempt name S.code) attTest) fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => RReady s₀ t) a.pub)
      (two_map id (fun a t ⟨_, s₀, A, e, L, _⟩ => ⟨s₀, A, e, L⟩) (attempt_ct S name))
      (fun a t ⟨_, s₀, A, e, ⟨Fa, T⟩, _⟩ => ?_)) ?_
    · obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := Fa.pos; omega_using [this]⟩
      have hf8 : f + 1 ≤ 8 := hf ▸ Fa.le
      rw [hf] at T
      exact WP.mono (attempt_ok S name A T hf8 Fa.q Fa.valid) fun u h => ⟨s₀, A, e, h.ready⟩
    · exact two_taint [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t) AttPub.pub fun _ _ _ h => h)
        (by taint_decide)
  have hp := two_post (Ψ := fun a t => a.fuel = n ∧ At (fun s₀ t => AStep S a s₀ t ∧
      (rResult s₀).status = a.status) a.pub t) hct
    fun a t ⟨hn, s₀, A, e, L, st⟩ => WP.mono (astep_ok S name A e L) fun u h => ⟨hn, s₀, A, e, h, st⟩
  refine hp.mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨a, ⟨hn, s₁, A₁, e₁, ⟨r₁, z₁, c₁, d₁⟩, st₁⟩, ⟨_, s₂, A₂, e₂, ⟨r₂, z₂, c₂, d₂⟩, st₂⟩⟩
  refine ⟨by rw [eval_eq, eval_eq, z₁, z₂], fun hc => ?_, fun hc => ?_⟩
  · have hc' : a.cont = false := by rw [eval_eq, z₁, Option.some.injEq] at hc; exact hc
    exact ⟨(a.pub, a.status), ⟨s₁, A₁, e₁, d₁ hc', st₁⟩, ⟨s₂, A₂, e₂, d₂ hc', st₂⟩⟩
  · have hc' : a.cont = true := by rw [eval_eq, z₁, Option.some.injEq] at hc; exact hc
    have h2 : 2 ≤ a.fuel := by
      simp only [AttPub.cont, Bool.and_eq_true, decide_eq_true_eq] at hc'; exact hc'.2
    exact ⟨n - 1, by omega, a.next, ⟨by show a.fuel - 1 = n - 1; omega_using [hn], s₁, A₁, e₁, c₁ hc', st₁⟩,
      ⟨by show a.fuel - 1 = n - 1; omega_using [hn], s₂, A₂, e₂, c₂ hc', st₂⟩⟩

/-! ## The end -/

/-- Test the overall status. -/
theorem finTest_ok {s₀ t : State} (A : RandomABI s₀) (F : RFin s₀ t) :
    WP isa (.block [ld .r0 oStatus, .cmp .r0 (.imm 1)]) t fun u =>
      RReady s₀ u ∧ Saved s₀ u.mem ∧ u.z = decide ((rResult s₀).status = 1) := by
  have hR := rResult_status_le A
  refine wp_ld F.ready (by decide) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_
  rw [u₁.gpr, F.status, one_beq (by omega_using [hR])] at z₂
  exact ⟨(F.ready.upd u₁).fupd f₂, by rw [f₂.mem, u₁.mem]; exact F.saved, z₂⟩

/-- Ready, with public data `p.1`. -/
def ReadyAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) p.1

/-- The output's address and length. -/
theorem zeroHead_ok {s₀ t : State} (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block [ld .r1 oOut, ld .r2 oOutLen, .mov .r0 (.imm 0)]) t fun u =>
      u.gpr .r1 = s₀.gpr .r0 ∧ u.gpr .r2 = s₀.gpr .r1 := by
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    VG.Proof.X25519.Arm.wp_mov (op2_imm (by decide)) fun t₃ u₃ => WP.block_nil ⟨?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, sv.2.1]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, sv.2.2.1]

theorem zeroOut_ct : RelCT isa (Two fun p s => ReadyAt p s ∧ isa.eval .ne s = some true) zeroOut
    fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => t.gpr .r1 = s₀.gpr .r0 ∧ t.gpr .r2 = s₀.gpr .r1) p.1)
    [.r11] (pins_at' (P := fun _ s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) Prod.fst fun _ _ _ h => h.1)
    (by taint_decide) fun p t ⟨⟨s₀, A, e, h, sv⟩, _⟩ => WP.mono (zeroHead_ok h sv) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.r1, .r2] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, x₁, c₁⟩ := h₁
  obtain ⟨s₂, _, e₂, x₂, c₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x₁, x₂, pub_r0 e]
  · rw [c₁, c₂, pub_r1 e]

/-- The nonce cleared, and the address of `used`. -/
theorem finPrefix_ok {s₀ t : State} (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block (clearNonce ++ ([ld .r4 oUsedPtr] : List Instr))) t fun u =>
      RReady s₀ u ∧ u.gpr .r4 = s₀.gpr .r2 := by
  refine clearNonce_ok h fun t₁ h₁ m₁ _ _ => ?_
  have o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  have sv₁ : Saved s₀ t₁.mem := sv.of_outs o₁ (by decide)
  exact wp_ld h₁ (by decide) fun t₂ u₂ => WP.block_nil ⟨h₁.upd u₂, by rw [u₂.gpr]; exact sv₁.2.2.2.1⟩

theorem finalBlock_ct : RelCT isa (Two ReadyAt) (.block (clearNonce ++ finalList)) fun _ _ => True := by
  show RelCT isa _ (.block ((clearNonce ++ [ld .r4 oUsedPtr]) ++
    [ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0), .str .r0 .r4 4, ld .r0 oStatus,
      ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32, ld .r11 28])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => RReady s₀ t ∧ t.gpr .r4 = s₀.gpr .r2) p.1)
    [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) Prod.fst fun _ _ _ h => h.1)
    (by taint_decide) fun p t ⟨s₀, A, e, h, sv⟩ => WP.mono (finPrefix_ok h sv) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.r11, .r4] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact r11_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  · rw [d₁, d₂, pub_r2 e]

theorem finish_ct : RelCT isa (Two FinAt) finish fun _ _ => True := by
  unfold finish
  rw [finishBlock_eq]
  refine RelCT.seq (two_piece (Ψ := fun (p : Pub × Nat) => At (fun s₀ t => RReady s₀ t ∧ Saved s₀ t.mem ∧
      t.z = decide (p.2 = 1)) p.1) [.r11]
    (pins_at (P := fun p s₀ t => RFin s₀ t ∧ (rResult s₀).status = p.2) Prod.fst fun _ _ _ h => h.1.ready)
    (by taint_decide) fun p t ⟨s₀, A, e, Fi, st⟩ => WP.mono (finTest_ok A Fi)
      fun u ⟨h, sv, z⟩ => ⟨s₀, A, e, h, sv, by rw [z, st]⟩) ?_
  refine RelCT.seq (R := Two ReadyAt) (two_ite (fun p t₁ t₂ ⟨s₁, _, e₁, _, _, z₁⟩ ⟨s₂, _, e₂, _, _, z₂⟩ => by
    rw [eval_ne, eval_ne, z₁, z₂]) ?_ ?_) finalBlock_ct
  · exact two_post (Ψ := ReadyAt) (two_map id (fun p t ⟨⟨s₀, A, e, h, sv, _⟩, hb⟩ => ⟨⟨s₀, A, e, h, sv⟩, hb⟩)
      zeroOut_ct) fun p t ⟨⟨s₀, A, e, h, sv, _⟩, _⟩ => WP.mono (zeroOut_ok A h sv)
        fun u ⟨hv, fv, _, _⟩ => ⟨s₀, A, e, hv, sv.of_slots fun d _ hd => apart_slot fv A.stackOut hd⟩
  · exact two_post (Ψ := ReadyAt) (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
      fun p t ⟨⟨s₀, A, e, h, sv, _⟩, _⟩ => WP.block_nil ⟨s₀, A, e, h, sv⟩

/-! ## The body -/

/-- What two runs of the body share: the public data and key bytes, and
the overall status and trace. -/
structure BodyPub where
  pub : Pub
  leak : List Nat
  status : Nat
  tr : List Nat

structure BodyFacts (S : Signer) (b : BodyPub) (s₀ : State) : Prop where
  leak : keyLeak s₀ = b.leak
  status : (rResult s₀).status = b.status
  tr : (rResult s₀).trace = b.tr
  valid : RValid S s₀

/-- The body's entry, after the frame's allocation. -/
def BodyEntry (S : Signer) (b : BodyPub) (s₀ t : State) : Prop := BodyFacts S b s₀ ∧ t = allocated frameBytes s₀

/-- After the entry's first instruction, which puts the frame's base in `r12`. -/
def entryBase (s₀ : State) : State :=
  (allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)

def Based (S : Signer) (b : BodyPub) (s₀ t : State) : Prop := BodyFacts S b s₀ ∧ t = entryBase s₀

/-- After the entry block. -/
def Entered (S : Signer) (b : BodyPub) (s₀ t : State) : Prop :=
  BodyFacts S b s₀ ∧ RReady s₀ t ∧ Saved s₀ t.mem ∧ slot t.mem (rBase s₀) oUsed = 0 ∧
    slot t.mem (rBase s₀) oAttempts = 8

theorem exec_entryBase (s₀ : State) : isa.exec (.addSp .r12 0) (allocated frameBytes s₀) = some (entryBase s₀) := by
  simp [exec, entryBase]

theorem entryRest_ok {s₀ : State} (A : RandomABI s₀) :
    WP isa (.block entry.tail) (entryBase s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oAttempts = 8 := by
  have h := entry_ok A
  rw [show entry = .addSp .r12 0 :: entry.tail from rfl, WP.block_cons_iff] at h
  obtain ⟨s', hs, W⟩ := h
  rw [exec_entryBase, Option.some.injEq] at hs
  subst hs
  exact WP.mono W fun u ⟨a, b, c, d, _⟩ => ⟨a, b, c, d⟩

theorem entryBase_r12 (s₀ : State) : (entryBase s₀).gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes := by
  simp [entryBase, State.setReg, allocated]

theorem entry_ct (S : Signer) : RelCT isa (Two fun b => At (BodyEntry S b) b.pub) (.block entry)
    (Two fun b => At (Entered S b) b.pub) := by
  rw [show entry = [.addSp .r12 0] ++ entry.tail from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun b => At (Based S b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide) fun b t ⟨s₀, A, e, Fb, ht⟩ => ?_)
    (two_piece [.r12] (fun b t₁ t₂ ⟨s₁, _, e₁, _, h₁⟩ ⟨s₂, _, e₂, _, h₂⟩ r hr => ?_) (by taint_decide)
      fun b t ⟨s₀, A, e, Fb, ht⟩ => ?_))
  · subst ht
    exact VG.Proof.X25519.Arm.WP.cons (exec_entryBase s₀) (WP.block_nil ⟨s₀, A, e, Fb, rfl⟩)
  · rw [List.mem_singleton] at hr; subst hr h₁ h₂
    rw [entryBase_r12, entryBase_r12, pub_sp (e₁.trans e₂.symm)]
  · subst ht
    exact WP.mono (entryRest_ok A) fun u ⟨h, sv, us, at₁⟩ => ⟨s₀, A, e, Fb, h, sv, us, at₁⟩

/-- After `prepare`. -/
structure Prepped (S : Signer) (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts S b s₀
  ready : RReady s₀ t
  r0 : t.gpr .r0 = if 1 < rq s₀ then 1 else 0
  prep : 1 < rq s₀ → Prepared s₀ t
  saved : Saved s₀ t.mem
  used : slot t.mem (rBase s₀) oUsed = 0
  attempts : slot t.mem (rBase s₀) oAttempts = 8

theorem Prepped.fupd {b : BodyPub} {s₀ t u : State} (h : Prepped S b s₀ t) (f : Fupd t u) : Prepped S b s₀ u := by
  have hr := h.ready.fupd f
  have hm : u.mem = t.mem := f.mem
  refine ⟨h.facts, hr, by rw [f.gpr]; exact h.r0, fun hq => ?_, by rw [hm]; exact h.saved,
    by rw [hm]; exact h.used, by rw [hm]; exact h.attempts⟩
  have P := h.prep hq
  exact ⟨hr, by rw [hm]; exact P.q, by rw [hm]; exact P.width, by rw [hm]; exact P.mask,
    by rw [hm]; exact P.nonce⟩

theorem prepped_ok {b : BodyPub} {s₀ t : State} (A : RandomABI s₀) (E : Entered S b s₀ t) :
    WP isa prepare t (Prepped S b s₀) := by
  obtain ⟨Fb, h₁, sv₁, us₁, at₁⟩ := E
  refine WP.mono (prepare_ok A h₁ sv₁.2.2.2.2) fun t₂ ⟨ax₂, P₂, h₂, o₂, _⟩ => ?_
  have lo₂ : ∀ d, d + 4 ≤ oQ → slot t₂.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₂ (by decide) hd (by unfold oQ at hd; omega_using [hd])
  exact ⟨Fb, h₂, ax₂, P₂, sv₁.of_outs o₂ (by decide), by rw [lo₂ _ (by decide)]; exact us₁,
    by rw [lo₂ _ (by decide)]; exact at₁⟩

/-- After the test of q. -/
def Checked (S : Signer) (b : BodyPub) (s₀ t : State) : Prop := Prepped S b s₀ t ∧ t.z = !decide (1 < rq s₀)

/-- q ≤ 1: the status, and the end. -/
theorem small_fin {b : BodyPub} {s₀ t : State} (A : RandomABI s₀) (C : Checked S b s₀ t) (hq : ¬ 1 < rq s₀) :
    WP isa (.block [st .r0 oStatus]) t fun u => RFin s₀ u ∧ (rResult s₀).status = b.status := by
  obtain ⟨Pp, _⟩ := C
  have hR := rResult_small A hq
  have r0 : t.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status := by
    rw [Pp.r0, hR]; simp only [hq, ↓reduceIte]; rfl
  refine wp_st Pp.ready (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
  rw [r0] at m₄
  refine ⟨⟨h₄, ?_, by rw [m₄.mem, slot_write_self], fun e => by rw [hR] at e; exact absurd e (by decide),
    Pp.saved.of_slots fun d hd _ => by rw [m₄.mem, slot_write_ne _ _ _ (by unfold oStatus; omega_using [hd]) (by omega_arith)
      (by decide)]⟩, Pp.facts.status⟩
  rw [m₄.mem, slot_write_ne _ _ _ (by decide) (by decide) (by decide), Pp.used, hR]; rfl

theorem body_ct (S : Signer) (name : String) :
    RelCT isa (Two fun b => At (BodyEntry S b) b.pub) (body name S.code) fun _ _ => True := by
  unfold body
  refine RelCT.seq (entry_ct S) ?_
  refine RelCT.seq (two_post (Ψ := fun b => At (Prepped S b) b.pub)
    (two_map BodyPub.pub (fun b t ⟨s₀, A, e, E⟩ => ⟨s₀, A, e, E.2.1, E.2.2.1.2.2.2.2⟩) prepare_ct)
    fun b t ⟨s₀, A, e, E⟩ => WP.mono (prepped_ok A E) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (Checked S b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
    fun b t ⟨s₀, A, e, Pp⟩ => wp_cmp0 fun u f z => WP.block_nil ⟨s₀, A, e, Pp.fupd f, ?_⟩) ?_
  · rw [z, Pp.r0]
    by_cases hq : 1 < rq s₀ <;> simp [hq]
  refine RelCT.seq (R := Two FinAt) (two_ite (fun b t₁ t₂ ⟨s₁, _, e₁, _, z₁⟩ ⟨s₂, _, e₂, _, z₂⟩ => by
    rw [eval_eq, eval_eq, z₁, z₂, pub_rq (e₁.trans e₂.symm)]) ?_ ?_) finish_ct
  · refine (two_post (Ψ := fun (b : BodyPub) => At (fun s₀ t => RFin s₀ t ∧ (rResult s₀).status = b.status) b.pub)
      (two_taint [.r11] (pins_at' BodyPub.pub fun _ _ _ h => h.1.ready) (by taint_decide))
      fun b t ⟨⟨s₀, A, e, C⟩, hb⟩ => WP.mono (small_fin A C (by
        rw [eval_eq, C.2, Option.some.injEq] at hb
        simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hb)) fun u hu => ⟨s₀, A, e, hu⟩).mono
      (fun _ _ h => h) fun _ _ ⟨b, h₁, h₂⟩ => ⟨(b.pub, b.status), h₁, h₂⟩
  · refine two_map (fun b => (⟨b.pub, b.leak, 0, 8, b.tr, b.status⟩ : AttPub))
      (fun b t ⟨⟨s₀, A, e, Pp, z⟩, hb⟩ => ⟨rfl, s₀, A, e, ?_, Pp.facts.status⟩) (attemptLoop_ct S name 8)
    have hq : 1 < rq s₀ := by
      rw [eval_eq, z, Option.some.injEq] at hb
      simpa only [Bool.not_eq_false', decide_eq_true_eq] using hb
    have P := Pp.prep hq
    have hql := rQBytes_le A
    have hfit := rWidth_le s₀
    have er : randomSignRemaining (rInput s₀) 0 8 = rResult s₀ := by rw [rResult_loop A]; rfl
    refine ⟨⟨hq, (by decide : 1 ≤ 8), (by decide : 8 ≤ 8), Pp.facts.leak, by
      show (randomSignRemaining (rInput s₀) 0 8).trace = b.tr; rw [er]; exact Pp.facts.tr, Pp.facts.valid⟩, ?_⟩
    refine ⟨⟨(slot t.mem (rBase s₀) oDraws).toNat, ⟨Pp.ready, P.q, P.width, P.mask, Pp.used,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], fun i hi => P.nonce i (by omega_using [hql, hi]), Nat.zero_le _⟩⟩,
      Pp.attempts, Pp.saved, ?_⟩
    exact ⟨by rw [er], by rw [er], by rw [er]⟩

end VG.Proof.Dsa.Arm
