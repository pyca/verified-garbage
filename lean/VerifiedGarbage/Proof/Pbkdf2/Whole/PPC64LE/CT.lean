module

import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Correct
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Block
import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Loop

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: constant time

As on ARMv7 (`Proof/Pbkdf2/Whole/Arm/CT.lean`): two runs from states whose
public arguments agree (`PubEq`) are related piece by piece. The code between
the calls of HMAC's functions and of `iterate`, the calls of the streaming
`update` included (they never write `r20`–`r25`), is checked by the taint
analysis (`Checks`, which the kernel evaluates for each hash function), from
the registers that hold pointers and lengths (`piece`); the calls of HMAC's
`init` and `finalize` and of `iterate`, which save and restore `r20`–`r25`,
are related by their contracts (`hi_rel`, `hf_rel`, `it_rel`), with the
arguments each run's correctness gives. Each run's correctness then says
what the registers hold after a piece (`RelCT.wp`), so that they agree
again. The branches and the loop depend only on `out_len`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open Spec.Hmac (xorPad ipad opad)
open Spec.Sha256 (bytesAt)

/-- A piece of code the taint analysis accepts with the registers `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true

/-- The arguments public in the prologue, and the registers public in the loop. -/
abbrev inRegs : List Reg := [.r3, .r4, .r5, .r6, .r8, .r9, .r10]
abbrev lpRegs : List Reg := [.r20, .r21, .r23, .r24, .r25]

/-- The taint checks of the pieces of `pbkdf2` between the calls of HMAC's
functions and of `iterate`. -/
structure Checks (F : Fns) : Prop where
  pro : Ck inRegs (.block F.prologue)
  li : Ck lpRegs (.block F.loopInit)
  b1 : Ck lpRegs (.block (F.copyW ++ F.saltArgs))
  upd : Ck (lpRegs ++ [.r3, .r4, .r5, .r6, .r7]) F.H.callUpd
  b3 : Ck lpRegs (.block F.updArgs)
  b5 : Ck lpRegs (.block F.finArgs)
  b7 : Ck lpRegs (.block (F.copyT ++ F.iterArgs))
  tail : Ck lpRegs (.seq F.outLen (.seq F.outLoop (.block F.advance)))
  restore : Ck [.r21] (.block (Hash.restoreAt 0))

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  r4 : s₀.gpr .r4 = s₀'.gpr .r4
  r5 : s₀.gpr .r5 = s₀'.gpr .r5
  r6 : s₀.gpr .r6 = s₀'.gpr .r6
  r7 : (s₀.gpr .r7).setWidth 32 = (s₀'.gpr .r7).setWidth 32
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  r9 : s₀.gpr .r9 = s₀'.gpr .r9
  r10 : s₀.gpr .r10 = s₀'.gpr .r10
  sp : s₀.sp = s₀'.sp

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.sA (o : Nat) : sA s₀' o = sA s₀ o := by simp only [PPC64LE.sA, scr, hq.r10]
theorem PubEq.ol : ol s₀' = ol s₀ := by simp only [PPC64LE.ol, hq.r9]
theorem PubEq.out : out s₀' = out s₀ := by simp only [PPC64LE.out, hq.r8]
theorem PubEq.nbk : nbk s₀' (F := F) = nbk s₀ (F := F) := by simp only [PPC64LE.nbk, hq.ol]
theorem PubEq.dn (k : Nat) : dn s₀' (F := F) k = dn s₀ (F := F) k := by simp only [PPC64LE.dn, hq.ol]

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
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F hF.X s₀) (hp' : Pre F hF.X s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

omit hp hp' in
/-- The registers public in the loop agree in two runs after the same
number of blocks. -/
theorem ag_lp {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (h' : Inv hF s₀' k s') :
    s.sp = s'.sp ∧ ∀ r ∈ lpRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.kr.sp, h'.kr.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.kr.r20, h'.kr.r20, hq.r6]
  · rw [h.kr.r21, h'.kr.r21, scr, scr, hq.r10]
  · rw [h.r23, h'.r23, hq.out, hq.dn]
  · rw [h.r24, h'.r24, hq.ol, hq.dn]
  · rw [h.kr.r25, h'.kr.r25, salt, salt, hq.r5]

end

/-! ## A block -/

section
variable (hF : FnsOK F) (k : Nat) (t₀ : State)

/-- What holds after each piece of a block, in one run from `t₀`. -/
def G1 (t : State) : Prop :=
  Inv hF t₀ k t ∧ hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad) ∧ t.gpr .r3 = sA t₀ F.stWO ∧
    t.gpr .r4 = BitVec.ofNat 64 F.H.B ∧ t.gpr .r5 = salt t₀ ∧ t.gpr .r6 = t₀.gpr .r6 ∧ t.gpr .r7 = sA t₀ 48
def G2 (t : State) : Prop :=
  Inv hF t₀ k t ∧ hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀)
def G3 (t : State) : Prop :=
  Inv hF t₀ k t ∧ hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀) ∧
    t.gpr .r3 = sA t₀ F.stWO ∧ t.gpr .r4 = BitVec.ofNat 64 (F.H.B + sl t₀) ∧ t.gpr .r5 = sA t₀ F.intO ∧
    t.gpr .r6 = BitVec.ofNat 64 4 ∧ t.gpr .r7 = sA t₀ 48
def G4 (t : State) : Prop :=
  Inv hF t₀ k t ∧
    hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
def G5 (t : State) : Prop :=
  Inv hF t₀ k t ∧
    hF.hH.SH.Repr t.mem (sA t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    t.gpr .r3 = sA t₀ F.stWO ∧ t.gpr .r4 = sA t₀ F.st1O ∧ t.gpr .r5 = BitVec.ofNat 64 (F.H.B + (sl t₀ + 4)) ∧
    t.gpr .r6 = sA t₀ F.uO ∧ t.gpr .r7 = sA t₀ 48
def G6 (t : State) : Prop :=
  Inv hF t₀ k t ∧ bytesAt t.mem (sA t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
def G7 (t : State) : Prop :=
  Inv hF t₀ k t ∧ bytesAt t.mem (sA t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt t.mem (sA t₀ F.tO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    t.gpr .r3 = sA t₀ F.st0O ∧ t.gpr .r4 = sA t₀ F.uO ∧ t.gpr .r5 = t₀.gpr .r7 - 1 ∧
    t.gpr .r6 = sA t₀ F.tO ∧ t.gpr .r7 = sA t₀ 48
def G8 (t : State) : Prop := Inv hF t₀ k t ∧ bytesAt t.mem (sA t₀ F.tO) F.H.D = Tk hF t₀ (k + 1)

end

section
variable {hF : FnsOK F} {k : Nat} {t₀ : State} (hp : Pre F hF.X t₀)
include hp

theorem st1 {s : State} (h : Inv hF t₀ k s) : WP isa (.block (F.copyW ++ F.saltArgs)) s (G1 hF k t₀) :=
  b1_ok hp h
theorem st2 {s : State} (h : G1 hF k t₀ s) : WP isa F.H.callUpd s (G2 hF k t₀) :=
  b2_ok hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
theorem st3 {s : State} (h : G2 hF k t₀ s) : WP isa (.block F.updArgs) s (G3 hF k t₀) :=
  WP.mono (b3_ok hp h.1) fun _ ⟨i, m, a3, a4, a5, a6, a7⟩ => ⟨i, by rw [m]; exact h.2, a3, a4, a5, a6, a7⟩
theorem st4 {s : State} (h : G3 hF k t₀ s) : WP isa F.H.callUpd s (G4 hF k t₀) :=
  b4_ok hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
theorem st5 {s : State} (h : G4 hF k t₀ s) : WP isa (.block F.finArgs) s (G5 hF k t₀) :=
  WP.mono (b5_ok hp h.1) fun _ ⟨i, m, a3, a4, a5, a6, a7⟩ => ⟨i, by rw [m]; exact h.2, a3, a4, a5, a6, a7⟩
theorem st6 {s : State} (h : G5 hF k t₀ s) : WP isa F.callHf s (G6 hF k t₀) :=
  b6_ok hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
theorem st7 {s : State} (h : G6 hF k t₀ s) : WP isa (.block (F.copyT ++ F.iterArgs)) s (G7 hF k t₀) :=
  WP.mono (b7_ok hp h.1) fun _ ⟨i, hu, ht, a3, a4, a5, a6, a7⟩ =>
    ⟨i, by rw [hu]; exact h.2, by rw [ht]; exact h.2, a3, a4, a5, a6, a7⟩
theorem st8 {s : State} (h : G7 hF k t₀ s) : WP isa F.callIt s (G8 hF k t₀) :=
  WP.mono (b8_ok hp h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)
    fun _ ⟨i, t⟩ => ⟨i, by rw [t]; rfl⟩

end

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F hF.X s₀) (hp' : Pre F hF.X s₀') (hq : PubEq s₀ s₀')
  (hc : Checks F)
include hp hp' hq hc

/-- Two runs of a block. -/
theorem block_rel {k : Nat} (hk : k < nbk s₀ (F := F)) :
    RelCT isa (fun s s' => Inv hF s₀ k s ∧ Inv hF s₀' k s') F.block
      fun s s' => Inv hF s₀ (k + 1) s ∧ Inv hF s₀' (k + 1) s' := by
  have hk' : k < nbk s₀' (F := F) := by rw [hq.nbk]; exact hk
  have sl' : sl s₀' = sl s₀ := by simp only [PPC64LE.sl, hq.r6]
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
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.2.2.1, h'.2.2.1, hq.sA]
      · rw [h.2.2.2.1, h'.2.2.2.1]
      · rw [h.2.2.2.2.1, h'.2.2.2.2.1, salt, salt, hq.r5]
      · rw [h.2.2.2.2.2.1, h'.2.2.2.2.2.1, hq.r6]
      · rw [h.2.2.2.2.2.2, h'.2.2.2.2.2.2, hq.sA]) hc.upd
    (fun s h => st2 hp h) (fun s h => st2 hp' h)
  have r3 := rel_agree (fun s s' (h : G2 hF k s₀ s) (h' : G2 hF k s₀' s') => ag_lp hq h.1 h'.1) hc.b3
    (fun s h => st3 hp h) (fun s h => st3 hp' h)
  have r4 := rel_agree (fun s s' (h : G3 hF k s₀ s) (h' : G3 hF k s₀' s') => by
      obtain ⟨e, g⟩ := ag_lp hq h.1 h'.1
      refine ⟨e, fun r hr => ?_⟩
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact g r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.2.2.1, h'.2.2.1, hq.sA]
      · rw [h.2.2.2.1, h'.2.2.2.1, sl']
      · rw [h.2.2.2.2.1, h'.2.2.2.2.1, hq.sA]
      · rw [h.2.2.2.2.2.1, h'.2.2.2.2.2.1]
      · rw [h.2.2.2.2.2.2, h'.2.2.2.2.2.2, hq.sA]) hc.upd
    (fun s h => st4 hp h) (fun s h => st4 hp' h)
  have r5 := rel_agree (fun s s' (h : G4 hF k s₀ s) (h' : G4 hF k s₀' s') => ag_lp hq h.1 h'.1) hc.b5
    (fun s h => st5 hp h) (fun s h => st5 hp' h)
  have r6 : RelCT isa (fun s s' => G5 hF k s₀ s ∧ G5 hF k s₀' s') F.callHf
      fun s s' => G6 hF k s₀ s ∧ G6 hF k s₀' s' :=
    rel_wp (hf_rel hF fun s s' ⟨h, h'⟩ => by
        have a' := b6_args hp' h'.1 h'.2.2.1 h'.2.2.2.1 h'.2.2.2.2.2.1 h'.2.2.2.2.2.2
        rw [hq.sA, hq.sA, hq.sA, hq.sA] at a'
        exact ⟨b6_args hp h.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2, a',
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
          by rw [h.2.2.2.2.2.1, h'.2.2.2.2.2.1, lo32_sub, lo32_sub, hq.r7]⟩)
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
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F hF.X s₀) (hp' : Pre F hF.X s₀') (hq : PubEq s₀ s₀')
  (hc : Checks F)
include hp hp' hq hc

/-- Two runs of the loop over the blocks. -/
theorem loop_rel :
    RelCT isa (fun s s' => Inv hF s₀ 0 s ∧ Inv hF s₀' 0 s')
      (.ite (.zero .d .r24) (.block []) (.loop F.block (.nonzero .d .r24)))
      fun s s' => Inv hF s₀ (nbk s₀ (F := F)) s ∧ Inv hF s₀' (nbk s₀' (F := F)) s' := by
  have ev : ∀ {c : Cond} {r : Reg} {s s' : State}, s.gpr r = s'.gpr r → (c = .zero .d r ∨ c = .nonzero .d r) →
      isa.eval c s = isa.eval c s' := by
    intro c r s s' e hc'
    rcases hc' with rfl | rfl
    · rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, e]
    · rw [VG.PPC64LE.eval_nonzero, VG.PPC64LE.eval_nonzero, e]
  have r24 : ∀ {k : Nat} {s s' : State}, Inv hF s₀ k s → Inv hF s₀' k s' → s.gpr .r24 = s'.gpr .r24 :=
    fun h h' => (ag_lp hq h h').2 _ (by simp)
  refine (RelCT.ite (fun s s' h => ev (r24 h.1 h.2) (.inl rfl)) rel_nil ?_).wp
    (F₁ := Inv hF s₀ (nbk s₀ (F := F))) (F₂ := Inv hF s₀' (nbk s₀' (F := F)))
    (fun s s' h => ⟨loop_ok hp h.1, loop_ok hp' h.2⟩) |>.mono (fun _ _ h => h) fun _ _ h => h.2
  · refine (RelCT.loop (Q := fun _ _ => True)
      (fun n s s' => ∃ k, n = nbk s₀ (F := F) - k ∧ k < nbk s₀ (F := F) ∧ Inv hF s₀ k s ∧ Inv hF s₀' k s')
      (fun n => RelCT.exists_ fun k => ?_) (nbk s₀ (F := F))).mono (fun s s' ⟨⟨h, h'⟩, hz⟩ => ⟨0, rfl, ?_, h, h'⟩)
      fun _ _ _ => trivial
    · by_cases hk : n = nbk s₀ (F := F) - k ∧ k < nbk s₀ (F := F)
      · obtain ⟨rfl, hk⟩ := hk
        refine (block_rel hp hp' hq hc hk).mono (fun s s' h => ⟨h.2.2.1, h.2.2.2⟩) fun t t' ⟨i, i'⟩ =>
          ⟨ev (r24 i i') (.inr rfl), fun _ => trivial, fun ht => ?_⟩
        have e : isa.eval (.nonzero .d .r24) t = some (decide (k + 1 < nbk s₀ (F := F))) := by
          rw [VG.PPC64LE.eval_nonzero, i.r24, left_ne hp (k := k + 1) hk]
        rw [e] at ht
        have h1 := of_decide_eq_true (Option.some.inj ht)
        exact ⟨nbk s₀ (F := F) - (k + 1), by omega, k + 1, rfl, h1, i, i'⟩
      · exact RelCT.of_false fun s s' h => hk ⟨h.1, h.2.1⟩
    · have hD := (sizes hF).D
      have e : isa.eval (.zero .d .r24) s = some (decide (ol s₀ = 0)) := by
        rw [VG.PPC64LE.eval_zero, h.r24, VG.Proof.MdStream.PPC64LE.ofNat_beq_zero
          (by have := ol_lt hp; omega)]
        congr 2; show (ol s₀ - min (0 * F.H.D) (ol s₀) = 0) = _; simp
      rw [e] at hz
      have := of_decide_eq_false (Option.some.inj hz)
      have : nbk s₀ (F := F) ≠ 0 := fun h' => this ((Whole.nb_zero hD.1).1 h')
      omega

end

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F hF.X s₀) (hp' : Pre F hF.X s₀') (hq : PubEq s₀ s₀')
  (hc : Checks F)
include hp hp' hq hc

/-- Two runs of `pbkdf2` in its frame. -/
theorem main_rel : RelCT isa (fun s s' => s = entry s₀ ∧ s' = entry s₀') F.main fun _ _ => True := by
  unfold Fns.main
  have rp := rel_agree (P₁ := fun s => s = entry s₀) (P₂ := fun s => s = entry s₀') (fun s s' h h' => by
      subst h h'
      refine ⟨by show s₀.sp - 48 = s₀'.sp - 48; rw [hq.sp], fun r hr => ?_⟩
      rw [entry_gpr s₀ (by revert r hr; decide), entry_gpr s₀' (by revert r hr; decide)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hq.r3, hq.r4, hq.r5, hq.r6, hq.r8, hq.r9, hq.r10]) hc.pro
    (fun s h => h ▸ prologue_ok hF hp) (fun s h => h ▸ prologue_ok hF hp')
  have rh : RelCT isa (fun s s' => Pro F hF.X s₀ s ∧ Pro F hF.X s₀' s') F.callHi
      fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' :=
    rel_wp (hi_rel hF fun s s' ⟨h, h'⟩ => by
        have a' := hi_args hF hp' h'
        rw [hq.sA, hq.sA, show pw s₀' = pw s₀ by simp only [PPC64LE.pw, hq.r3],
          show pwl s₀' = pwl s₀ by simp only [PPC64LE.pwl, hq.r4]] at a'
        exact ⟨hi_args hF hp h, a', by rw [h.kr.sp, h'.kr.sp, hq.sp]⟩)
      (fun s h => hi_ok hF hp h) (fun s h => hi_ok hF hp' h)
  have ri := rel_agree (fun s s' (h : Keyed hF s₀ s) (h' : Keyed hF s₀' s') => by
      refine ⟨by rw [h.kr.sp, h'.kr.sp, hq.sp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.kr.r20, h'.kr.r20, hq.r6]
      · rw [h.kr.r21, h'.kr.r21, scr, scr, hq.r10]
      · rw [h.r23, h'.r23, hq.out]
      · rw [h.r24, h'.r24, hq.r9]
      · rw [h.kr.r25, h'.kr.r25, salt, salt, hq.r5]) hc.li
    (fun s h => loopInit_ok hp h) (fun s h => loopInit_ok hp' h)
  have rl := loop_rel hp hp' hq hc
  obtain ⟨_, hr⟩ := hc.restore
  have rr : RelCT isa (fun s s' => Inv hF s₀ (nbk s₀ (F := F)) s ∧ Inv hF s₀' (nbk s₀' (F := F)) s')
      (.block (Hash.restoreAt 0)) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r21]) (fun s s' ⟨h, h'⟩ => ⟨by rw [h.kr.sp, h'.kr.sp, hq.sp],
      fun r hr => by
        rw [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr
        rw [h.kr.r21, h'.kr.r21, scr, scr, hq.r10]⟩) hr
  exact rp.seq (rh.seq (ri.seq (rl.seq rr)))

end

/-- A run of `main` from the start of the frame, and the frame's push. -/
theorem rel_pushed {r : Reg} {c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = framed r s₁ ∧ b = framed r s₂) c Q)
    (hw : ∀ s₁ s₂, P s₁ s₂ → (∃ t x, Exec isa c (framed r s₁) t x) ∧ (∃ t x, Exec isa c (framed r s₂) t x)) :
    RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed r s₁ ∧ b = pushed r s₂) c fun _ _ => True := by
  rintro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, rfl, rfl⟩ e₁ e₂
  obtain ⟨⟨u₁, x₁, f₁⟩, ⟨u₂, x₂, f₂⟩⟩ := hw s₁ s₂ hp
  have cov : ∀ s : State, Covers ((framed r s).rd ++ (framed r s).wr) ((pushed r s).rd ++ (pushed r s).wr) :=
    fun s a n ⟨r', hr, hc⟩ => ⟨r', by
      simp only [framed, pushed, List.mem_append, List.mem_cons] at hr ⊢
      rcases hr with h | h
      exacts [.inl h, .inr (.inr h)], hc⟩
  have covw : ∀ s : State, Covers (framed r s).wr (pushed r s).wr :=
    fun s a n ⟨r', hr, hc⟩ => ⟨r', by simp only [framed, pushed, List.mem_cons] at hr ⊢; exact .inr hr, hc⟩
  have w₁ := Exec.widen f₁ (cov s₁) (covw s₁)
  have w₂ := Exec.widen f₂ (cov s₂) (covw s₂)
  have e : ∀ s : State, (framed r s).withRegions (pushed r s).rd (pushed r s).wr = pushed r s := fun _ => rfl
  rw [e] at w₁ w₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ w₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ w₂
  exact ⟨(h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ f₁ f₂).1, trivial⟩

variable (hF : FnsOK F)

/-- `pbkdf2` is constant time, given the taint checks of its pieces. -/
theorem ct (hc : Checks F) :
    ConstantTime isa (pbkG hF.hH.SH F.bytes (hF.X + 144)).pre (pbkG hF.hH.SH F.bytes (hF.X + 144)).pub F.pbkdf2 := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₀ s₀' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_of hF h; have hp' := pre_of hF h'
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩ := hpub
  have hq : PubEq s₀ s₀' := ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = s₀ ∧ y = s₀') = P
  suffices hr : RelCT isa P F.pbkdf2 fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold Fns.pbkdf2
  have m1 : RelCT isa (fun x y => x = s₀ ∧ y = s₀') (.block [.mflr .r0])
      fun x y => x = s₀.write .r0 s₀.lr ∧ y = s₀'.write .r0 s₀'.lr :=
    rel_agree (rs := []) (fun x y hx hy => by subst hx hy; exact ⟨qsp, by simp⟩) ⟨.block [], by decide⟩
      (fun x hx => hx ▸ VG.Proof.MdStream.PPC64LE.WP.cons exec_mflr (WP.block_nil rfl))
      (fun x hx => hx ▸ VG.Proof.MdStream.PPC64LE.WP.cons exec_mflr (WP.block_nil rfl))
  have fr : RelCT isa (fun x y => x = s₀.write .r0 s₀.lr ∧ y = s₀'.write .r0 s₀'.lr)
      (.frame (.push .r0) F.main (.pop .r0)) fun x y => x.sp = y.sp := by
    refine RelCT.frame (R := fun _ _ => True) (fun x y ⟨hx, hy⟩ => by subst hx hy; exact qsp) ?_
    refine rel_pushed (P := fun x y => x = s₀.write .r0 s₀.lr ∧ y = s₀'.write .r0 s₀'.lr)
      ((main_rel hp hp' hq hc).mono (fun x y ⟨_, _, ⟨e₁, e₂⟩, hx, hy⟩ => by subst e₁ e₂ hx hy; exact ⟨rfl, rfl⟩)
        fun _ _ h => h) fun x y ⟨e₁, e₂⟩ => ?_
    subst e₁ e₂
    obtain ⟨t, x, he, -⟩ := main_ok hp (hF := hF)
    obtain ⟨t', x', he', -⟩ := main_ok hp' (hF := hF)
    exact ⟨⟨t, x, he⟩, ⟨t', x', he'⟩⟩
  have m2 : RelCT isa (fun x y : State => x.sp = y.sp) (.block [.mtlr .r0]) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs []) (fun x y h => ⟨h, by simp⟩) (hc := .block []) (by decide)
  exact m1.seq (fr.seq m2)

end VG.Proof.Pbkdf2.Whole.PPC64LE
