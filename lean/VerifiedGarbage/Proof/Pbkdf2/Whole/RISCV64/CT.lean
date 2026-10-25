module

import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Correct
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Block
import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Loop
import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Contract

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: constant time

As on PPC64LE (`Proof/Pbkdf2/Whole/PPC64LE/CT.lean`): two runs from states
whose public arguments agree (`PubEq`) are related piece by piece. The code
between the calls of HMAC's functions and of `iterate`, the calls of the
streaming `update` included, is checked by the taint analysis (`Checks`,
which the kernel evaluates for each hash function), from the registers that
hold pointers and lengths; the calls of HMAC's `init` and `finalize` and of
`iterate`, whose callees restore the callee-saved registers from memory,
are related by their contracts (`hi_rel`, `hf_rel`, `it_rel`), with the
arguments each run's correctness gives. Each run's correctness then says
what the registers hold after a piece (`RelCT.wp`), so that they agree
again. The branches and the loop depend only on `out_len`; the frames'
`alloc` and `free` leak nothing (`rel_alloc`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (eval_zero eval_nonzero ofNat_beq_zero)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open Spec.Hmac (xorPad ipad opad)
open Spec.Sha256 (bytesAt)

/-- A piece of code the taint analysis accepts with the registers `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- The arguments public in the prologue, and the registers public in the loop. -/
abbrev inRegs : List Reg := [.a0, .a1, .a2, .a3, .a5, .a6]
abbrev lpRegs : List Reg := [.s1, .s2, .s4, .s5, .s6, .s7]

/-- The taint checks of the pieces of `pbkdf2` between the calls of HMAC's
functions and of `iterate`. -/
structure Checks (F : Fns) : Prop where
  pro : Ck inRegs (.block F.prologue)
  li : Ck [.s1] (.block Fns.loopInit)
  b1 : Ck lpRegs (.block F.saltArgs)
  upd : Ck (lpRegs ++ [.a0, .a1, .a2, .a3]) F.H.callUpd
  b3 : Ck lpRegs (.block F.updArgs)
  b5 : Ck lpRegs (.block F.finArgs)
  b7 : Ck lpRegs (.block F.iterArgs)
  tail : Ck lpRegs (.seq F.outLen (.seq F.outLoop (.block Fns.advance)))
  restore : Ck [.s1] (.block Fns.restore)

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  a0 : s₀.gpr .a0 = s₀'.gpr .a0
  a1 : s₀.gpr .a1 = s₀'.gpr .a1
  a2 : s₀.gpr .a2 = s₀'.gpr .a2
  a3 : s₀.gpr .a3 = s₀'.gpr .a3
  a4 : (s₀.gpr .a4).setWidth 32 = (s₀'.gpr .a4).setWidth 32
  a5 : s₀.gpr .a5 = s₀'.gpr .a5
  a6 : s₀.gpr .a6 = s₀'.gpr .a6
  sp : s₀.sp = s₀'.sp

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.sA (o : Nat) : sA s₀' o = sA s₀ o := by simp only [RISCV64.sA, hq.sp]
theorem PubEq.ol : ol s₀' = ol s₀ := by simp only [RISCV64.ol, hq.a6]
theorem PubEq.out : out s₀' = out s₀ := by simp only [RISCV64.out, hq.a5]
theorem PubEq.nbk : nbk s₀' (F := F) = nbk s₀ (F := F) := by simp only [RISCV64.nbk, hq.ol]
theorem PubEq.dn (k : Nat) : dn s₀' (F := F) k = dn s₀ (F := F) k := by simp only [RISCV64.dn, hq.ol]

end

/-- Code the taint analysis accepts from the registers `rs`, in two runs
whose single-run facts `G₁` and `G₂` agree on them. -/
theorem rel_agree {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa} {rs : List Reg}
    (hag : ∀ s s', P₁ s → P₂ s' → s.sp = s'.sp ∧ ∀ r ∈ rs, s.gpr r = s'.gpr r) (hc : Ck rs c)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' := by
  obtain ⟨_, hc⟩ := hc
  refine ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => ?_) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨e, g⟩ := hag s s' h.1 h.2
  exact ⟨e, fun r hr => g r (Taint.mem_ofRegs.mp hr)⟩

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun _ _ => True)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

/-- The registers public in the loop agree in two runs after the same
number of blocks. -/
theorem ag_lp {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (h' : Inv hF s₀' k s') :
    s.sp = s'.sp ∧ ∀ r ∈ lpRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.kr.sp, h'.kr.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.kr.s1, h'.kr.s1, hq.sp]
  · rw [h.kr.s2, h'.kr.s2, hq.a3]
  · rw [h.s4, h'.s4, hq.out, hq.dn]
  · rw [h.s5, h'.s5, hq.ol, hq.dn]
  · rw [h.kr.s6, h'.kr.s6, salt, salt, hq.a2]
  · rw [h.s7, h'.s7]

end

/-! ## A block -/

section
variable (hF : FnsOK F) (k : Nat) (t₀ : State)

/-- What holds after each piece of a block, in one run from `t₀`. -/
def G1 (t : State) : Prop :=
  Inv hF t₀ k t ∧ hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad) ∧ t.gpr .a0 = sA t₀ F.stWO ∧
    t.gpr .a1 = BitVec.ofNat 64 F.H.B ∧ t.gpr .a2 = salt t₀ ∧ t.gpr .a3 = t₀.gpr .a3
def G2 (t : State) : Prop :=
  Inv hF t₀ k t ∧ hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀)
def G3 (t : State) : Prop :=
  Inv hF t₀ k t ∧ hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀) ∧
    bytesAt t.mem (sA t₀ F.intO) 4 = Spec.Pbkdf2.int (k + 1) ∧
    t.gpr .a0 = sA t₀ F.stWO ∧ t.gpr .a1 = BitVec.ofNat 64 (F.H.B + sl t₀) ∧ t.gpr .a2 = sA t₀ F.intO ∧
    t.gpr .a3 = BitVec.ofNat 64 4
def G4 (t : State) : Prop :=
  Inv hF t₀ k t ∧
    hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
def G5 (t : State) : Prop :=
  Inv hF t₀ k t ∧
    hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    t.gpr .a0 = sA t₀ F.stWO ∧ t.gpr .a1 = sA t₀ F.st1O ∧ t.gpr .a2 = BitVec.ofNat 64 (F.H.B + (sl t₀ + 4)) ∧
    t.gpr .a3 = sA t₀ F.uO
def G6 (t : State) : Prop :=
  Inv hF t₀ k t ∧ bytesAt t.mem (sA t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
def G7 (t : State) : Prop :=
  Inv hF t₀ k t ∧ bytesAt t.mem (sA t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt t.mem (sA t₀ F.tO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    t.gpr .a0 = sA t₀ Fns.st0O ∧ t.gpr .a1 = sA t₀ F.uO ∧ t.gpr .a2 = t₀.gpr .a4 - BitVec.ofNat 64 1 ∧
    t.gpr .a3 = sA t₀ F.tO ∧ t.gpr .a4 = sA t₀ F.frB
def G8 (t : State) : Prop := Inv hF t₀ k t ∧ bytesAt t.mem (sA t₀ F.tO) F.H.D = Tk hF t₀ (k + 1)

end

section
variable {hF : FnsOK F} {k : Nat} {t₀ : State} (hp : Pre F t₀)
include hp

theorem st1 {s : State} (h : Inv hF t₀ k s) : WP isa (.block F.saltArgs) s (G1 hF k t₀) :=
  b1_ok hp h
theorem st2 {s : State} (h : G1 hF k t₀ s) : WP isa F.H.callUpd s (G2 hF k t₀) :=
  b2_ok hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
theorem st3 (hk : k + 1 < 2 ^ 32) {s : State} (h : G2 hF k t₀ s) : WP isa (.block F.updArgs) s (G3 hF k t₀) :=
  b3_ok hp hk h.1 h.2
theorem st4 {s : State} (h : G3 hF k t₀ s) : WP isa F.H.callUpd s (G4 hF k t₀) :=
  b4_ok hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
theorem st5 {s : State} (h : G4 hF k t₀ s) : WP isa (.block F.finArgs) s (G5 hF k t₀) :=
  WP.mono (b5_ok hp h.1) fun _ ⟨i, m, a0, a1, a2, a3⟩ => ⟨i, by rw [m]; exact h.2, a0, a1, a2, a3⟩
theorem st6 {s : State} (h : G5 hF k t₀ s) : WP isa F.callHf s (G6 hF k t₀) :=
  b6_ok hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
theorem st7 {s : State} (h : G6 hF k t₀ s) : WP isa (.block F.iterArgs) s (G7 hF k t₀) :=
  WP.mono (b7_ok hp h.1) fun _ ⟨i, hu, ht, a0, a1, a2, a3, a4⟩ =>
    ⟨i, by rw [hu]; exact h.2, by rw [ht]; exact h.2, a0, a1, a2, a3, a4⟩
theorem st8 {s : State} (h : G7 hF k t₀ s) : WP isa F.callIt s (G8 hF k t₀) :=
  WP.mono (b8_ok hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)
    fun _ ⟨i, t⟩ => ⟨i, by rw [t]; rfl⟩

end

/-- The low word of `x - 1` is the low word of `x`, less one. -/
theorem lo32_pred (x : BitVec 64) : (x - BitVec.ofNat 64 1).setWidth 32 = x.setWidth 32 - BitVec.ofNat 32 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
  (hc : Checks F)
include hp hp' hq hc

/-- Two runs of a block. -/
theorem block_rel {k : Nat} (hk : k < nbk s₀ (F := F)) :
    RelCT isa (fun s s' => Inv hF s₀ k s ∧ Inv hF s₀' k s') F.block
      fun s s' => Inv hF s₀ (k + 1) s ∧ Inv hF s₀' (k + 1) s' := by
  have hk' : k < nbk s₀' (F := F) := by rw [hq.nbk]; exact hk
  have hk32 : k + 1 < 2 ^ 32 := by have := nbk_lt (hF := hF) hp; omega
  have sl' : sl s₀' = sl s₀ := by simp only [RISCV64.sl, hq.a3]
  unfold Fns.block
  have r1 := rel_agree (fun s s' (h : Inv hF s₀ k s) (h' : Inv hF s₀' k s') => ag_lp hq h h') hc.b1
    (fun s h => st1 hp h) (fun s h => st1 hp' h)
  have r2 := rel_agree (fun s s' (h : G1 hF k s₀ s) (h' : G1 hF k s₀' s') => by
      obtain ⟨e, g⟩ := ag_lp hq h.1 h'.1
      refine ⟨e, fun r hr => ?_⟩
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact g r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.2.2.1, h'.2.2.1, hq.sA]
      · rw [h.2.2.2.1, h'.2.2.2.1]
      · rw [h.2.2.2.2.1, h'.2.2.2.2.1, salt, salt, hq.a2]
      · rw [h.2.2.2.2.2, h'.2.2.2.2.2, hq.a3]) hc.upd
    (fun s h => st2 hp h) (fun s h => st2 hp' h)
  have r3 := rel_agree (fun s s' (h : G2 hF k s₀ s) (h' : G2 hF k s₀' s') => ag_lp hq h.1 h'.1) hc.b3
    (fun s h => st3 hp hk32 h) (fun s h => st3 hp' hk32 h)
  have r4 := rel_agree (fun s s' (h : G3 hF k s₀ s) (h' : G3 hF k s₀' s') => by
      obtain ⟨e, g⟩ := ag_lp hq h.1 h'.1
      refine ⟨e, fun r hr => ?_⟩
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact g r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.2.2.2.1, h'.2.2.2.1, hq.sA]
      · rw [h.2.2.2.2.1, h'.2.2.2.2.1, sl']
      · rw [h.2.2.2.2.2.1, h'.2.2.2.2.2.1, hq.sA]
      · rw [h.2.2.2.2.2.2, h'.2.2.2.2.2.2]) hc.upd
    (fun s h => st4 hp h) (fun s h => st4 hp' h)
  have r5 := rel_agree (fun s s' (h : G4 hF k s₀ s) (h' : G4 hF k s₀' s') => ag_lp hq h.1 h'.1) hc.b5
    (fun s h => st5 hp h) (fun s h => st5 hp' h)
  have r6 : RelCT isa (fun s s' => G5 hF k s₀ s ∧ G5 hF k s₀' s') F.callHf
      fun s s' => G6 hF k s₀ s ∧ G6 hF k s₀' s' :=
    rel_wp (hf_rel hF fun s s' ⟨h, h'⟩ => by
        have a' := b6_args hp' h'.1 h'.2.2.1 h'.2.2.2.1 h'.2.2.2.2.2
        rw [hq.sA, hq.sA, hq.sA] at a'
        exact ⟨b6_args hp h.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2, a',
          by rw [h.1.kr.sp, h'.1.kr.sp, hq.sp], by rw [h.2.2.2.2.1, h'.2.2.2.2.1, sl']⟩)
      (fun s h => st6 hp h) (fun s h => st6 hp' h)
  have r7 := rel_agree (fun s s' (h : G6 hF k s₀ s) (h' : G6 hF k s₀' s') => ag_lp hq h.1 h'.1) hc.b7
    (fun s h => st7 hp h) (fun s h => st7 hp' h)
  have r8 : RelCT isa (fun s s' => G7 hF k s₀ s ∧ G7 hF k s₀' s') F.callIt
      fun s s' => G8 hF k s₀ s ∧ G8 hF k s₀' s' :=
    rel_wp (it_rel hF fun s s' ⟨h, h'⟩ => by
        have a' := b8_args hp' h'.1 h'.2.2.2.1 h'.2.2.2.2.1 h'.2.2.2.2.2.2.1 h'.2.2.2.2.2.2.2
        rw [hq.sA, hq.sA, hq.sA, hq.sA] at a'
        exact ⟨b8_args hp h.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2, a',
          by rw [h.1.kr.sp, h'.1.kr.sp, hq.sp],
          by rw [h.2.2.2.2.2.1, h'.2.2.2.2.2.1, lo32_pred, lo32_pred, hq.a4]⟩)
      (fun s h => st8 hp h) (fun s h => st8 hp' h)
  have r9 := rel_agree (fun s s' (h : G8 hF k s₀ s) (h' : G8 hF k s₀' s') => ag_lp hq h.1 h'.1) hc.tail
    (fun s h => tail_ok hp hk h.1 h.2) (fun s h => tail_ok hp' hk' h.1 h.2)
  exact r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))

end

/-! ## The loop and `pbkdf2` -/

/-- Two runs of an empty block. -/
theorem rel_nil {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  rw [← e₁.2, ← e₂.2]; exact ⟨rfl, trivial⟩

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
  (hc : Checks F)
include hp hp' hq hc

/-- Two runs of the loop over the blocks. -/
theorem loop_rel :
    RelCT isa (fun s s' => Inv hF s₀ 0 s ∧ Inv hF s₀' 0 s')
      (.ite (.zero .s5) (.block []) (.loop F.block (.nonzero .s5)))
      fun s s' => Inv hF s₀ (nbk s₀ (F := F)) s ∧ Inv hF s₀' (nbk s₀' (F := F)) s' := by
  have ev : ∀ {c : Cond} {r : Reg} {s s' : State}, s.gpr r = s'.gpr r → (c = .zero r ∨ c = .nonzero r) →
      isa.eval c s = isa.eval c s' := by
    intro c r s s' e hc'
    rcases hc' with rfl | rfl
    · rw [eval_zero, eval_zero, e]
    · rw [eval_nonzero, eval_nonzero, e]
  have r5 : ∀ {k : Nat} {s s' : State}, Inv hF s₀ k s → Inv hF s₀' k s' → s.gpr .s5 = s'.gpr .s5 :=
    fun h h' => (ag_lp hq h h').2 _ (by simp)
  refine (RelCT.ite (fun s s' h => ev (r5 h.1 h.2) (.inl rfl)) rel_nil ?_).wp
    (F₁ := Inv hF s₀ (nbk s₀ (F := F))) (F₂ := Inv hF s₀' (nbk s₀' (F := F)))
    (fun s s' h => ⟨loop_ok hp h.1, loop_ok hp' h.2⟩) |>.mono (fun _ _ h => h) fun _ _ h => h.2
  · refine (RelCT.loop (Q := fun _ _ => True)
      (fun n s s' => ∃ k, n = nbk s₀ (F := F) - k ∧ k < nbk s₀ (F := F) ∧ Inv hF s₀ k s ∧ Inv hF s₀' k s')
      (fun n => RelCT.exists_ fun k => ?_) (nbk s₀ (F := F))).mono (fun s s' ⟨⟨h, h'⟩, hz⟩ => ⟨0, rfl, ?_, h, h'⟩)
      fun _ _ _ => trivial
    · by_cases hk : n = nbk s₀ (F := F) - k ∧ k < nbk s₀ (F := F)
      · obtain ⟨rfl, hk⟩ := hk
        refine (block_rel hp hp' hq hc hk).mono (fun s s' h => ⟨h.2.2.1, h.2.2.2⟩) fun t t' ⟨i, i'⟩ =>
          ⟨ev (r5 i i') (.inr rfl), fun _ => trivial, fun ht => ?_⟩
        have e : isa.eval (.nonzero .s5) t = some (decide (k + 1 < nbk s₀ (F := F))) := by
          rw [eval_nonzero, i.s5, left_ne (hF := hF) hp (k := k + 1) hk]
        rw [e] at ht
        have h1 := of_decide_eq_true (Option.some.inj ht)
        exact ⟨nbk s₀ (F := F) - (k + 1), by omega, k + 1, rfl, h1, i, i'⟩
      · exact RelCT.of_false fun s s' h => hk ⟨h.1, h.2.1⟩
    · have hD := (sizes hF).D
      have e : isa.eval (.zero .s5) s = some (decide (ol s₀ = 0)) := by
        rw [eval_zero, h.s5, ofNat_beq_zero (by have := ol_lt (hF := hF) hp; omega)]
        congr 2; show (ol s₀ - min (0 * F.H.D) (ol s₀) = 0) = _; simp
      rw [e] at hz
      have := of_decide_eq_false (Option.some.inj hz)
      have : nbk s₀ (F := F) ≠ 0 := fun h' => this ((Whole.nb_zero hD.1).1 h')
      omega

include hF in
/-- Two runs of `pbkdf2` in its frames. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') F.main fun _ _ => True := by
  unfold Fns.main
  have rp := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (fun s s' h h' => by
      subst h h'
      refine ⟨hq.sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hq.a0, hq.a1, hq.a2, hq.a3, hq.a5, hq.a6]) hc.pro
    (G₁ := Pro F s₀) (G₂ := Pro F s₀') (fun s h => by rw [h]; exact prologue_ok hF hp)
    (fun s h => by rw [h]; exact prologue_ok hF hp')
  have rh : RelCT isa (fun s s' => Pro F s₀ s ∧ Pro F s₀' s') F.callHi
      fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' :=
    rel_wp (hi_rel hF fun s s' ⟨h, h'⟩ => by
        have a' := hi_args hF hp' h'
        rw [hq.sA, hq.sA, show pw s₀' = pw s₀ by simp only [RISCV64.pw, hq.a0],
          show pwl s₀' = pwl s₀ by simp only [RISCV64.pwl, hq.a1]] at a'
        exact ⟨hi_args hF hp h, a', by rw [h.kr.sp, h'.kr.sp, hq.sp]⟩)
      (fun s h => hi_ok' hF hp h) (fun s h => hi_ok' hF hp' h)
  have ri := rel_agree (fun s s' (h : Keyed hF s₀ s) (h' : Keyed hF s₀' s') => by
      refine ⟨by rw [h.kr.sp, h'.kr.sp, hq.sp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [h.kr.s1, h'.kr.s1, hq.sp]) hc.li
    (fun s h => loopInit_ok h) (fun s h => loopInit_ok h)
  have rl := loop_rel (hF := hF) hp hp' hq hc
  obtain ⟨_, hr⟩ := hc.restore
  have rr : RelCT isa (fun s s' => Inv hF s₀ (nbk s₀ (F := F)) s ∧ Inv hF s₀' (nbk s₀' (F := F)) s')
      (.block Fns.restore) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.s1]) (fun s s' ⟨h, h'⟩ => ⟨by rw [h.kr.sp, h'.kr.sp, hq.sp],
      fun r hr => by
        rw [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr
        rw [h.kr.s1, h'.kr.s1, hq.sp]⟩) hr
  exact rp.seq (rh.seq (ri.seq (rl.seq rr)))

end

/-- Two runs of a frame allocating `n` bytes, which leaks nothing itself. -/
theorem rel_alloc {n : Nat} {body : Prog isa} {P : State → State → Prop}
    (h : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocd n s₁ ∧ b = allocd n s₂) body fun _ _ => True) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hpush : ∀ {s a : State}, isa.push (.alloc n) s = some a → a = allocd n s := by
    intro s a h'
    simp only [isa, push] at h'
    split at h' <;> cases h'
    rfl
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea := hpush p₁
      have eb := hpush p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

variable (hF : FnsOK F)

/-- `pbkdf2` is constant time, given the taint checks of its pieces. -/
theorem ct (hc : Checks F) :
    ConstantTime isa (pbkR hF.hH.SH (F.itB + F.frB + F.X)).pre (pbkR hF.hH.SH (F.itB + F.frB + F.X)).pub
      F.pbkdf2 := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc hF h; have hp' := pre_alloc hF h'
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, qsp⟩ := hpub
  have hq : PubEq (allocd F.frB (allocd F.itB e)) (allocd F.frB (allocd F.itB e')) :=
    ⟨q0, q1, q2, q3, q4, q5, q6, by simp only [allocd, qsp]⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = P
  suffices hr : RelCT isa P F.pbkdf2 fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold Fns.pbkdf2
  refine rel_alloc (rel_alloc ((main_rel (hF := hF) hp hp' hq hc).mono ?_ fun _ _ h => h))
  rintro x y ⟨u, v, ⟨w, z, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Pbkdf2.Whole.RISCV64
