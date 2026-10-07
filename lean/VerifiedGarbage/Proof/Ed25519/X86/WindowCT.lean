import VerifiedGarbage.Proof.Ed25519.X86.WindowLoop
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits of the scalars and address the tables by
them, so their traces depend on the scalars: both runs must use the same ones
(in verification, the inputs are public, the same in both runs). The digits
are read through the argument pointers and the counter `esi`, the same in both
runs by correctness; everything else is public by the taint analysis, with
the workspace pointer `edi`. The skipped bytes of `k` are its leading zeros,
the same in both runs.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc at_)

/-- Chains two programs: the first related, each run's state after it by correctness. -/
theorem seq_runs {P₁ P₂ F₁ F₂ : State → Prop} {Q : State → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (fun x y => P₁ x ∧ P₂ y) c₁ (fun _ _ => True))
    (w₁ : ∀ x, P₁ x → WP isa c₁ x F₁) (w₂ : ∀ y, P₂ y → WP isa c₁ y F₂)
    (h₂ : RelCT isa (fun x y => F₁ x ∧ F₂ y) c₂ Q) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y) (.seq c₁ c₂) Q :=
  VG.RelCT.seq ((h₁.wp fun x y h => ⟨w₁ x h.1, w₂ y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) h₂

theorem agree_one {r : Reg} {x y : State} (h : x.gpr r = y.gpr r) :
    VG.X86.Taint.Agree (regsTaint [r]) x y :=
  regsTaint_agree fun r' hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r'; exact h

theorem agree_two {r r' : Reg} {x y : State} (h : x.gpr r = y.gpr r ∧ x.gpr r' = y.gpr r') :
    VG.X86.Taint.Agree (regsTaint [r, r']) x y :=
  regsTaint_agree fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [h.1, h.2]

theorem agree_none {x y : State} : VG.X86.Taint.Agree (regsTaint []) x y :=
  regsTaint_agree (by simp)

theorem VerifyCTFacts.kByte {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) :
    kByte s₀ i = kByte t₀ i :=
  congrArg (·.getD i 0) h.challengeBytes

theorem VerifyCTFacts.sByte {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) :
    sByte s₀ i = sByte t₀ i :=
  congrArg (·.getD i 0) h.scalarBytes

theorem VerifyCTFacts.challengeNat {s t : State} (h : VerifyCTFacts s t) :
    verificationChallenge s = verificationChallenge t :=
  congrArg Spec.Ed25519.decodeLE h.challengeBytes

theorem VerifyCTFacts.scalarNat {s t : State} (h : VerifyCTFacts s t) :
    verificationScalar s = verificationScalar t :=
  congrArg Spec.Ed25519.decodeLE h.scalarBytes

theorem saved_edi {s₀ t₀ x y : State} (h : VerifyCTFacts s₀ t₀) (hx : Saved s₀ (arg s₀ 3) x)
    (hy : Saved t₀ (arg t₀ 3) y) : x.gpr .edi = y.gpr .edi :=
  hx.edi.trans ((h.args 3 (by decide)).trans hy.edi.symm)

theorem saved_esp {s₀ t₀ x y : State} (h : VerifyCTFacts s₀ t₀) (hx : Saved s₀ (arg s₀ 3) x)
    (hy : Saved t₀ (arg t₀ 3) y) : x.gpr .esp = y.gpr .esp :=
  hx.esp.trans (h.pub.1.trans hy.esp.symm)

/-! ## Digits -/

theorem argLoad_ok {s₀ s : State} (hp : ScratchPre s₀ 3 4) (hs : Saved s₀ (arg s₀ 3) s) {a : Nat}
    (ha : a < 4) :
    WP isa (.block [.mov .eax (.mem (at_ .esp (4 + 4 * a)))]) s fun u =>
      u.gpr .eax = arg s₀ a ∧ u.gpr .esi = s.gpr .esi :=
  Wp.wp_ldm hs.esp (by rw [hs.rd, hs.wr]; exact hp.argIn ha) fun u hu =>
    WP.block_nil ⟨by rw [hu.gpr]; exact hp.arg_same hs.frame ha, hu.other .esi (by decide)⟩

/-- A digit's code: the pointer's load by the taint analysis with `esp` public, the byte's by
the taint analysis with the pointer, from correctness, and the counter public. -/
theorem digit_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {P₁ P₂ : State → Prop} {a i : Nat}
    {rest : List Instr} (ha : a < 4)
    (h₁ : ∀ x, P₁ x → Saved s₀ (arg s₀ 3) x ∧ x.gpr .esi = BitVec.ofNat 32 i)
    (h₂ : ∀ y, P₂ y → Saved t₀ (arg t₀ 3) y ∧ y.gpr .esi = BitVec.ofNat 32 i)
    (hfirst : RelCT isa (fun x y => x.gpr .esp = y.gpr .esp)
      (.block [.mov .eax (.mem (at_ .esp (4 + 4 * a)))]) (fun _ _ => True))
    (hrest : RelCT isa (fun x y => x.gpr .eax = y.gpr .eax ∧ x.gpr .esi = y.gpr .esi)
      (.block rest) (fun _ _ => True)) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y)
      (.block (([.mov .eax (.mem (at_ .esp (4 + 4 * a)))] : List Instr) ++ rest)) (fun _ _ => True) := by
  have w₁ (x : State) (hx : P₁ x) : WP isa (.block [.mov .eax (.mem (at_ .esp (4 + 4 * a)))]) x
      fun u => u.gpr .eax = arg s₀ a ∧ u.gpr .esi = BitVec.ofNat 32 i :=
    WP.mono (argLoad_ok (verify_pre h.left).scratch (h₁ x hx).1 ha) fun _ ⟨e1, e2⟩ =>
      ⟨e1, e2.trans (h₁ x hx).2⟩
  have w₂ (y : State) (hy : P₂ y) : WP isa (.block [.mov .eax (.mem (at_ .esp (4 + 4 * a)))]) y
      fun u => u.gpr .eax = arg t₀ a ∧ u.gpr .esi = BitVec.ofNat 32 i :=
    WP.mono (argLoad_ok (verify_pre h.right).scratch (h₂ y hy).1 ha) fun _ ⟨e1, e2⟩ =>
      ⟨e1, e2.trans (h₂ y hy).2⟩
  refine ctBlockAppend (((hfirst.mono (P' := fun x y => P₁ x ∧ P₂ y)
    (fun x y hh => saved_esp h (h₁ x hh.1).1 (h₂ y hh.2).1) (fun _ _ h => h)).wp
    fun x y hh => ⟨w₁ x hh.1, w₂ y hh.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, ex, ey⟩
  exact ⟨ex.1.trans ((h.args a ha).trans ey.1.symm), ex.2.trans ey.2.symm⟩

theorem digitK_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {P₁ P₂ : State → Prop} {i : Nat}
    (h₁ : ∀ x, P₁ x → Saved s₀ (arg s₀ 3) x ∧ x.gpr .esi = BitVec.ofNat 32 i)
    (h₂ : ∀ y, P₂ y → Saved t₀ (arg t₀ 3) y ∧ y.gpr .esi = BitVec.ofNat 32 i) (high : Bool) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y) (.block (if high then digitHigh 12 0 else digitLow 12 0))
      (fun _ _ => True) := by
  have first : RelCT isa (fun x y => x.gpr .esp = y.gpr .esp)
      (.block [.mov .eax (.mem (at_ .esp (4 + 4 * 2)))]) (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint [.esp]) (fun _ _ hh => agree_one hh) (by taint_decide)
  cases high
  · show RelCT isa _ (.block ([.mov .eax (.mem (at_ .esp (4 + 4 * 2)))] ++
      [.alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax 0), .alu .and .eax (.imm 15)])) _
    exact digit_ct h (by decide) h₁ h₂ first
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => agree_two hh) (by taint_decide))
  · show RelCT isa _ (.block ([.mov .eax (.mem (at_ .esp (4 + 4 * 2)))] ++
      [.alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax 0), .shift .shr .eax 4])) _
    exact digit_ct h (by decide) h₁ h₂ first
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => agree_two hh) (by taint_decide))

theorem digitS_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {P₁ P₂ : State → Prop} {i : Nat}
    (h₁ : ∀ x, P₁ x → Saved s₀ (arg s₀ 3) x ∧ x.gpr .esi = BitVec.ofNat 32 i)
    (h₂ : ∀ y, P₂ y → Saved t₀ (arg t₀ 3) y ∧ y.gpr .esi = BitVec.ofNat 32 i) (high : Bool) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y) (.block (if high then digitHigh 8 32 else digitLow 8 32))
      (fun _ _ => True) := by
  have first : RelCT isa (fun x y => x.gpr .esp = y.gpr .esp)
      (.block [.mov .eax (.mem (at_ .esp (4 + 4 * 1)))]) (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint [.esp]) (fun _ _ hh => agree_one hh) (by taint_decide)
  cases high
  · show RelCT isa _ (.block ([.mov .eax (.mem (at_ .esp (4 + 4 * 1)))] ++
      [.alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax 32), .alu .and .eax (.imm 15)])) _
    exact digit_ct h (by decide) h₁ h₂ first
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => agree_two hh) (by taint_decide))
  · show RelCT isa _ (.block ([.mov .eax (.mem (at_ .esp (4 + 4 * 1)))] ++
      [.alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax 32), .shift .shr .eax 4])) _
    exact digit_ct h (by decide) h₁ h₂ first
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => agree_two hh) (by taint_decide))

/-! ## Adding a digit's entry -/

theorem digitTest_ok {s : State} {v : Nat} (hv : v < 16) {B : BitVec 32}
    (hs : s.gpr .eax = BitVec.ofNat 32 v ∧ s.gpr .edi = B) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t =>
      (t.gpr .eax = BitVec.ofNat 32 v ∧ t.gpr .edi = B) ∧ t.zf = some (decide (v = 0)) :=
  Wp.wp_test fun t ht zt => WP.block_nil ⟨⟨by rw [ht.gpr]; exact hs.1, by rw [ht.gpr]; exact hs.2⟩,
    by rw [zt, hs.1, digit_test_fact v hv]⟩

/-- A digit's addition branches on the digit and addresses the table by it, the same in both
runs. -/
theorem addDigit_ct (o : Nat) (ho : o = 1024 ∨ o = 3072) {v : Nat} (hv : v < 16) (B : BitVec 32) :
    RelCT isa (fun x y => (x.gpr .eax = BitVec.ofNat 32 v ∧ x.gpr .edi = B) ∧
      (y.gpr .eax = BitVec.ofNat 32 v ∧ y.gpr .edi = B)) (addDigit o) (fun _ _ => True) := by
  have test : RelCT isa (fun x y => (x.gpr .eax = BitVec.ofNat 32 v ∧ x.gpr .edi = B) ∧
      (y.gpr .eax = BitVec.ofNat 32 v ∧ y.gpr .edi = B)) (.block [.alu .test .eax (.reg .eax)])
      (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide)
  have body : RelCT isa (fun x y => x.gpr .eax = y.gpr .eax ∧ x.gpr .edi = y.gpr .edi)
      (.block (entryAddr o ++ pointFromTableQ ++ pointAdd)) (fun _ _ => True) := by
    rcases ho with rfl | rfl
    all_goals
      exact VG.RelCT.taint (A := taint) (regsTaint [.eax, .edi]) (fun _ _ hh => agree_two hh)
        (by taint_decide)
  rw [addDigit]
  refine VG.RelCT.seq ((test.wp fun x y hh => ⟨digitTest_ok hv hh.1, digitTest_ok hv hh.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y hh
    change x.zf.map Bool.not = y.zf.map Bool.not
    rw [hh.1.2, hh.2.2]
  · exact body.mono (fun x y hh => ⟨hh.1.1.1.1.trans hh.1.2.1.1.symm, hh.1.1.1.2.trans hh.1.2.1.2.symm⟩)
      (fun _ _ h => h)
  · exact VG.RelCT.block_nil fun _ _ _ => trivial

/-! ## Windows -/

/-- A window's start, in one run: the counter at `i`, and the sum representing a point. -/
def WinAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (i : Nat) (x : State) : Prop :=
  WinCtx s₀ Aa R x ∧ x.gpr .esi = BitVec.ofNat 32 i ∧
    ∃ a, Rep (point (env x.mem (arg s₀ 3)) 0 1 2 3) a

theorem doubleWindow_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} :
    RelCT isa (fun x y => WinAt s₀ Aa R i x ∧ WinAt t₀ Aa R i y) doubleWindow (fun _ _ => True) :=
  VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi])
    (fun _ _ hh => agree_two ⟨saved_edi h hh.1.1.saved hh.2.1.saved, hh.1.2.1.trans hh.2.2.1.symm⟩)
    (by taint_decide)

theorem doubleWindow_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64)
    (hx : WinAt s₀ Aa R i x) : WP isa doubleWindow x (WinAt s₀ Aa R i) := by
  obtain ⟨w, e, a, ha⟩ := hx
  exact WP.mono (doubleWindow_ok w.ctx (esi_lt hi e) ha) fun b ⟨kb, eb, rb, hb⟩ =>
    ⟨w.of_ikeep kb (hb 16 (by decide)), eb.trans e, _, rb⟩

/-- After a digit's code, its value in `eax`, the workspace pointer in `edi`, and the window's
start but for `eax`. -/
def DigitAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (i v : Nat) (x : State) : Prop :=
  WinAt s₀ Aa R i x ∧ x.gpr .eax = BitVec.ofNat 32 v ∧ x.gpr .edi = arg s₀ 3

theorem DigitAt.of_keep {s₀ x u : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i v : Nat}
    (hx : WinAt s₀ Aa R i x) (k : EaxKeep x u) (hv : u.gpr .eax = BitVec.ofNat 32 v) :
    DigitAt s₀ Aa R i v u :=
  ⟨⟨hx.1.of_ikeep k.ikeep (by rw [k.mem]), by rw [k.gpr _ (by decide)]; exact hx.2.1,
    by rw [k.mem]; exact hx.2.2⟩, hv, by rw [k.gpr _ (by decide)]; exact hx.1.saved.edi⟩

/-- A digit's code and its addition, from the digit's value in both runs. -/
theorem digitAdd_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i v : Nat} (hv : v < 16) {digit : List Instr} {o : Nat}
    (ho : o = 1024 ∨ o = 3072)
    (hct : RelCT isa (fun x y => WinAt s₀ Aa R i x ∧ WinAt t₀ Aa R i y) (.block digit)
      (fun _ _ => True))
    (w₁ : ∀ x, WinAt s₀ Aa R i x → WP isa (.block digit) x (DigitAt s₀ Aa R i v))
    (w₂ : ∀ y, WinAt t₀ Aa R i y → WP isa (.block digit) y (DigitAt t₀ Aa R i v)) :
    RelCT isa (fun x y => WinAt s₀ Aa R i x ∧ WinAt t₀ Aa R i y) (.seq (.block digit) (addDigit o))
      (fun _ _ => True) :=
  seq_runs hct w₁ w₂ ((addDigit_ct o ho hv (arg s₀ 3)).mono
    (fun _ _ hh => ⟨⟨hh.1.2.1, hh.1.2.2⟩, ⟨hh.2.2.1, hh.2.2.2.trans (h.args 3 (by decide)).symm⟩⟩)
    (fun _ _ h => h))

theorem digitK_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64)
    (high : Bool) (hx : WinAt s₀ Aa R i x) :
    WP isa (.block (if high then digitHigh 12 0 else digitLow 12 0)) x
      (DigitAt s₀ Aa R i (if high then (kByte s₀ i).toNat / 16 else (kByte s₀ i).toNat % 16)) :=
  WP.mono (digitK_ok hi high x hx.1 hx.2.1) fun _ ⟨k, e⟩ => DigitAt.of_keep hx k e

theorem digitS_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32)
    (high : Bool) (hx : WinAt s₀ Aa R i x) :
    WP isa (.block (if high then digitHigh 8 32 else digitLow 8 32)) x
      (DigitAt s₀ Aa R i (if high then (sByte s₀ i).toNat / 16 else (sByte s₀ i).toNat % 16)) :=
  WP.mono (digitS_ok hi high x hx.1 hx.2.1) fun _ ⟨k, e⟩ => DigitAt.of_keep hx k e

theorem windowA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64) (high : Bool) :
    RelCT isa (fun x y => WinAt s₀ Aa R i x ∧ WinAt t₀ Aa R i y)
      (windowA (if high then digitHigh 12 0 else digitLow 12 0)) (fun _ _ => True) := by
  rw [windowA, windowWith]
  refine seq_runs (doubleWindow_ct h) (fun _ hx => doubleWindow_at hi hx) (fun _ hy => doubleWindow_at hi hy) ?_
  refine digitAdd_ct h (nibble_lt (kByte s₀ i) high) (.inl rfl)
    (digitK_ct h (fun _ hx => ⟨hx.1.saved, hx.2.1⟩) (fun _ hy => ⟨hy.1.saved, hy.2.1⟩) high)
    (fun _ hx => digitK_at hi high hx) (fun y hy => ?_)
  rw [h.kByte i]
  exact digitK_at hi high hy

theorem windowA_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64)
    (high : Bool) (hx : WinAt s₀ Aa R i x) :
    WP isa (windowA (if high then digitHigh 12 0 else digitLow 12 0)) x (WinAt s₀ Aa R i) := by
  obtain ⟨w, e, a, ha⟩ := hx
  exact WP.mono (windowA_byte_ok w hi e high ha) fun _ ⟨wt, et, rt⟩ => ⟨wt, et.trans e, _, rt⟩

theorem windowAB_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32) (high : Bool) :
    RelCT isa (fun x y => WinAt s₀ Aa R i x ∧ WinAt t₀ Aa R i y)
      (windowAB (if high then digitHigh 12 0 else digitLow 12 0)
        (if high then digitHigh 8 32 else digitLow 8 32)) (fun _ _ => True) := by
  rw [windowAB]
  refine seq_runs (windowA_ct h (by omega) high) (fun _ hx => windowA_at (by omega) high hx)
    (fun _ hy => windowA_at (by omega) high hy) ?_
  refine digitAdd_ct h (nibble_lt (sByte s₀ i) high) (.inr rfl)
    (digitS_ct h (fun _ hx => ⟨hx.1.saved, hx.2.1⟩) (fun _ hy => ⟨hy.1.saved, hy.2.1⟩) high)
    (fun _ hx => digitS_at hi high hx) (fun y hy => ?_)
  rw [h.sByte i]
  exact digitS_at hi high hy

theorem windowAB_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32)
    (high : Bool) (hx : WinAt s₀ Aa R i x) :
    WP isa (windowAB (if high then digitHigh 12 0 else digitLow 12 0)
      (if high then digitHigh 8 32 else digitLow 8 32)) x (WinAt s₀ Aa R i) := by
  obtain ⟨w, e, a, ha⟩ := hx
  exact WP.mono (windowAB_byte_ok w hi e high ha) fun _ ⟨wt, et, rt⟩ => ⟨wt, et.trans e, _, rt⟩

/-! ## Bytes -/

theorem esiDec_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat}
    (hx : LoopAt s₀ Aa R (i + 1) x) : WP isa (.block [.alu .sub .esi (.imm 1)]) x (WinAt s₀ Aa R i) :=
  WP.mono (esiDec_ok hx.1 hx.2.1) fun _ ⟨w, e, m⟩ => ⟨w, e, _, by rw [m]; exact hx.2.2⟩

theorem byteStepA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64) :
    RelCT isa (fun x y => LoopAt s₀ Aa R (i + 1) x ∧ LoopAt t₀ Aa R (i + 1) y) byteStepA
      (fun _ _ => True) := by
  rw [byteStepA]
  refine seq_runs (VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide))
    (fun _ hx => esiDec_at hx) (fun _ hy => esiDec_at hy) ?_
  refine seq_runs (windowA_ct h hi true) (fun _ hx => windowA_at hi true hx)
    (fun _ hy => windowA_at hi true hy) ?_
  refine seq_runs (F₁ := fun _ => True) (F₂ := fun _ => True) (windowA_ct h hi false)
    (fun _ hx => WP.mono (windowA_at hi false hx) fun _ _ => trivial)
    (fun _ hy => WP.mono (windowA_at hi false hy) fun _ _ => trivial) ?_
  exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide)

theorem byteStepAB_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32) :
    RelCT isa (fun x y => LoopAt s₀ Aa R (i + 1) x ∧ LoopAt t₀ Aa R (i + 1) y) byteStepAB
      (fun _ _ => True) := by
  rw [byteStepAB]
  refine seq_runs (VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide))
    (fun _ hx => esiDec_at hx) (fun _ hy => esiDec_at hy) ?_
  refine seq_runs (windowAB_ct h hi true) (fun _ hx => windowAB_at hi true hx)
    (fun _ hy => windowAB_at hi true hy) ?_
  refine seq_runs (F₁ := fun _ => True) (F₂ := fun _ => True) (windowAB_ct h hi false)
    (fun _ hx => WP.mono (windowAB_at hi false hx) fun _ _ => trivial)
    (fun _ hy => WP.mono (windowAB_at hi false hy) fun _ _ => trivial) ?_
  exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide)

/-! ## Loops -/

theorem loopA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {c : Nat} (hc1 : 32 < c) (hc2 : c ≤ 64) :
    RelCT isa (fun x y => LoopAt s₀ Aa R c x ∧ LoopAt t₀ Aa R c y) (.loop byteStepA .ne)
      (fun x y => LoopAt s₀ Aa R 32 x ∧ LoopAt t₀ Aa R 32 y) := by
  refine (VG.RelCT.loop (I := fun m x y => (LoopAt s₀ Aa R (32 + m) x ∧ LoopAt t₀ Aa R (32 + m) y) ∧
    0 < m ∧ m ≤ 32) ?_ (c - 32)).mono
      (fun x y hh => ⟨by rw [show 32 + (c - 32) = c by omega]; exact hh, by omega, by omega⟩)
      (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ hh => Nat.lt_irrefl 0 hh.2.1
  by_cases hj : j < 32
  · have hw (u x : State) (hx : LoopAt u Aa R (32 + j + 1) x) : WP isa byteStepA x fun t =>
        t.zf.map (!·) = some (!decide (32 + j = 32)) ∧ LoopAt u Aa R (32 + j) t :=
      WP.mono (byteStepA_ok hx.1 (by omega) (by omega) hx.2.1 hx.2.2) fun t ⟨wt, et, zt, rt⟩ =>
        ⟨by rw [zt]; rfl, wt, et, rt⟩
    refine (((byteStepA_ct h (i := 32 + j) (by omega)).mono (fun x y hh => hh.1) (fun _ _ h => h)).wp
      fun x y hh => ⟨hw s₀ x hh.1.1, hw t₀ y hh.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have he' := xz.symm.trans he
      have : j = 0 := by simpa using he'
      subst this
      exact ⟨hx, hy⟩
    · have he' := xz.symm.trans he
      have : j ≠ 0 := by simpa using he'
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ hh => hj (by omega)

theorem loopAB_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} :
    RelCT isa (fun x y => LoopAt s₀ Aa R 32 x ∧ LoopAt t₀ Aa R 32 y) (.loop byteStepAB .ne)
      (fun _ _ => True) := by
  refine (VG.RelCT.loop (I := fun m x y => (LoopAt s₀ Aa R m x ∧ LoopAt t₀ Aa R m y) ∧
    0 < m ∧ m ≤ 32) ?_ 32).mono (fun x y hh => ⟨hh, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ hh => Nat.lt_irrefl 0 hh.2.1
  by_cases hj : j < 32
  · have hw (u x : State) (hx : LoopAt u Aa R (j + 1) x) : WP isa byteStepAB x fun t =>
        t.zf.map (!·) = some (!decide (j = 0)) ∧ LoopAt u Aa R j t :=
      WP.mono (byteStepAB_ok hx.1 hj hx.2.1 hx.2.2) fun t ⟨wt, et, zt, rt⟩ =>
        ⟨by rw [zt]; rfl, wt, et, rt⟩
    refine (((byteStepAB_ct h (i := j) hj).mono (fun x y hh => hh.1) (fun _ _ h => h)).wp
      fun x y hh => ⟨hw s₀ x hh.1.1, hw t₀ y hh.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun _ => trivial, fun he => ?_⟩
    have he' := xz.symm.trans he
    have : j ≠ 0 := by simpa using he'
    exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ hh => hj (by omega)

theorem cmp32_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {c : Nat} (hc : c ≤ 64)
    (hx : LoopAt s₀ Aa R c x) : WP isa (.block [.alu .cmp .esi (.imm 32)]) x fun t =>
      LoopAt s₀ Aa R c t ∧ t.zf = some (decide (c = 32)) :=
  Wp.wp_cmpi fun t ht _ zt => WP.block_nil ⟨⟨hx.1.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr]; exact hx.2.1,
    by rw [ht.mem]; exact hx.2.2⟩,
    by rw [zt, hx.2.1, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega) (by omega)]⟩

theorem windowsA_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {c : Nat} (hc1 : 32 ≤ c) (hc2 : c ≤ 64) :
    RelCT isa (fun x y => LoopAt s₀ Aa R c x ∧ LoopAt t₀ Aa R c y) windowsA
      (fun x y => LoopAt s₀ Aa R 32 x ∧ LoopAt t₀ Aa R 32 y) := by
  rw [windowsA]
  refine VG.RelCT.seq ((VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none)
    (by taint_decide)).wp fun x y hh => ⟨cmp32_at hc2 hh.1, cmp32_at hc2 hh.2⟩)
    (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y hh
    change x.zf.map Bool.not = y.zf.map Bool.not
    rw [hh.2.1.2, hh.2.2.2]
  · by_cases hc : c = 32
    · refine VG.RelCT.of_false fun x y hh => ?_
      have e := hh.2
      change x.zf.map Bool.not = some true at e
      rw [hh.1.2.1.2, hc] at e
      simp at e
    · exact (loopA_ct h (by omega) hc2).mono (fun x y hh => ⟨hh.1.2.1.1, hh.1.2.2.1⟩) (fun _ _ h => h)
  · refine VG.RelCT.block_nil fun x y hh => ?_
    have hc : c = 32 := by
      by_contra hne
      have e := hh.2
      change x.zf.map Bool.not = some false at e
      rw [hh.1.2.1.2, decide_eq_false hne] at e
      simp at e
    subst hc
    exact ⟨hh.1.2.1.1, hh.1.2.2.1⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem skipPrefix_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) {c : Nat}
    (hc : 1 ≤ c) (hesi : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (.block [.mov .edx (.reg .esi), .alu .sub .edx (.imm 1), .mov .eax (.mem (at_ .esp 12))]) s
      fun t => t.gpr .eax = arg s₀ 2 ∧ t.gpr .edx = BitVec.ofNat 32 (c - 1) := by
  refine Wp.wp_mov fun u₁ h₁ => Wp.wp_subi fun u₂ h₂ _ _ => ?_
  have e₂ : u₂.gpr .edx = BitVec.ofNat 32 (c - 1) := by
    rw [h₂.gpr, h₁.gpr, hesi]; exact Wp.ofNat_pred hc
  have hsp : u₂.gpr .esp = s₀.gpr .esp := by
    rw [h₂.other _ (by decide), h₁.other _ (by decide)]; exact hs.esp
  have hr₂ : u₂.rd ++ u₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hs.rd, hs.wr]
  have m₂ : u₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine Wp.wp_ldm hsp (by rw [hr₂]; exact hp.scratch.argIn (i := 2) (by decide)) fun u₃ h₃ =>
    WP.block_nil ⟨?_, by rw [h₃.other .edx (by decide), e₂]⟩
  rw [h₃.gpr, m₂, show (12 : Nat) = 4 + 4 * 2 from rfl]
  exact hp.scratch.arg_same hs.frame (by decide)

theorem skipBody_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {m : Nat} :
    RelCT isa (fun x y => SkipAt s₀ Aa R m x ∧ SkipAt t₀ Aa R m y) skipBody (fun _ _ => True) := by
  have pre (u x : State) (hu : VerifyPre u) (hx : SkipAt u Aa R m x) :=
    skipPrefix_ok hu hx.1.saved (c := 32 + m) (by omega) hx.2.2.2.1
  have load : RelCT isa (fun x y => SkipAt s₀ Aa R m x ∧ SkipAt t₀ Aa R m y) (.block skipLoad)
      (fun _ _ => True) := by
    show RelCT isa _ (.block ([.mov .edx (.reg .esi), .alu .sub .edx (.imm 1),
      .mov .eax (.mem (at_ .esp 12))] ++ [.alu .add .eax (.reg .edx), .movzx8 .eax (at_ .eax 0),
      .alu .test .eax (.reg .eax)])) _
    refine ctBlockAppend (((VG.RelCT.taint (A := taint) (regsTaint [.esi, .esp])
      (fun x y hh => agree_two ⟨hh.1.2.2.2.1.trans hh.2.2.2.2.1.symm,
        saved_esp h hh.1.1.saved hh.2.1.saved⟩) (by taint_decide)).wp
      fun x y hh => ⟨pre s₀ x (verify_pre h.left) hh.1, pre t₀ y (verify_pre h.right) hh.2⟩).mono
        (fun _ _ h => h) fun x y hh => ⟨hh.2.1.1.trans ((h.args 2 (by decide)).trans hh.2.2.1.symm),
          hh.2.1.2.trans hh.2.2.2.symm⟩)
      (VG.RelCT.taint (A := taint) (regsTaint [.eax, .edx]) (fun _ _ hh => agree_two hh) (by taint_decide))
  have lw (u x : State) (hx : SkipAt u Aa R m x) : WP isa (.block skipLoad) x fun t =>
      t.zf = some (decide ((kByte u (32 + m - 1)).toNat = 0)) ∧
        t.gpr .edx = BitVec.ofNat 32 (32 + m - 1) :=
    WP.mono (skipLoad_ok hx.1 (by omega) (by have := hx.2.2.1; omega) hx.2.2.2.1) fun _ ⟨_, _, dt, zt, _⟩ => ⟨zt, dt⟩
  rw [skipBody]
  refine VG.RelCT.seq ((load.wp fun x y hh => ⟨lw s₀ x hh.1, lw t₀ y hh.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y hh
    change x.zf.map Bool.not = y.zf.map Bool.not
    rw [hh.1.1, hh.2.1, h.kByte]
  · exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide)
  · exact VG.RelCT.taint (A := taint) (regsTaint [.edx]) (fun _ _ hh => agree_one (hh.1.1.2.trans hh.1.2.2.symm))
      (by taint_decide)

theorem skipZero_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} :
    RelCT isa (fun x y => SkipAt s₀ Aa R 32 x ∧ SkipAt t₀ Aa R 32 y) skipZero
      (fun x y => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ LoopAt s₀ Aa R c x ∧ LoopAt t₀ Aa R c y) := by
  rw [skipZero]
  refine VG.RelCT.loop (M := isa) (fun m x y => SkipAt s₀ Aa R m x ∧ SkipAt t₀ Aa R m y) ?_ 32
  intro m
  rcases m with _ | m
  · exact VG.RelCT.of_false fun _ _ hh => Nat.lt_irrefl 0 hh.1.2.1
  refine ((skipBody_ct h).wp fun x y hh => ⟨skipBody_ok hh.1, skipBody_ok hh.2⟩).mono
    (fun _ _ h => h) ?_
  intro x y ⟨_, ⟨xz, xf, xt⟩, ⟨yz, yf, yt⟩⟩
  have es : skipOn t₀ (m + 1) = skipOn s₀ (m + 1) := by rw [skipOn, skipOn, h.kByte]
  have ee : skipEnd t₀ (m + 1) = skipEnd s₀ (m + 1) := by rw [skipEnd, skipEnd, h.kByte]
  refine ⟨?_, fun he => ?_, fun he => ?_⟩
  · change x.zf.map (!·) = y.zf.map (!·)
    rw [xz, yz, es]
  · have hs : skipOn s₀ (m + 1) = false := Option.some.inj (xz.symm.trans he)
    obtain ⟨c1, c2, lx⟩ := xf hs
    obtain ⟨_, _, ly⟩ := yf (es.trans hs)
    exact ⟨skipEnd s₀ (m + 1), c1, c2, lx, ee ▸ ly⟩
  · have hs : skipOn s₀ (m + 1) = true := Option.some.inj (xz.symm.trans he)
    exact ⟨m, by omega, xt hs, yt (es.trans hs)⟩

/-! ## The whole multiplication -/

/-- Before the equation's points: the saved state, `A` at byte 7680 and `R` at byte 7808. -/
def EquationCTPre (s₀ : State) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  Saved s₀ (arg s₀ 3) s ∧ tablePoint s.mem (arg s₀ 3) 7680 = a ∧ tablePoint s.mem (arg s₀ 3) 7808 = r

theorem windowMultiply_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {a r : Spec.Ed25519.Point}
    {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun x y => EquationCTPre s₀ a r x ∧ EquationCTPre t₀ a r y) windowMultiply
      (fun _ _ => True) := by
  have prep : RelCT isa (fun x y => EquationCTPre s₀ a r x ∧ EquationCTPre t₀ a r y) windowPrep
      (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint [.edi]) (fun _ _ hh => agree_one (saved_edi h hh.1.1 hh.2.1))
      (by taint_decide)
  have pw (u x : State) (hu : VerifyPre u) (hx : EquationCTPre u a r x) :
      WP isa windowPrep x (SkipAt u Aa r 32) :=
    WP.mono (windowPrep_ok hu hx.1 hA hx.2.1 hx.2.2) fun _ ⟨w, e, rp⟩ =>
      ⟨w, by decide, by decide, e, Nat.div_eq_of_lt (decodeLE_lt64 _ _), rp⟩
  rw [windowMultiply]
  refine seq_runs prep (fun x hx => pw s₀ x (verify_pre h.left) hx)
    (fun y hy => pw t₀ y (verify_pre h.right) hy) ?_
  refine VG.RelCT.seq (skipZero_ct h) ?_
  refine VG.RelCT.exists_ (M := isa)
    (P := fun c x y => 32 ≤ c ∧ c ≤ 64 ∧ LoopAt s₀ Aa r c x ∧ LoopAt t₀ Aa r c y) fun c => ?_
  by_cases hc : 32 ≤ c ∧ c ≤ 64
  · exact VG.RelCT.seq ((windowsA_ct h hc.1 hc.2).mono (fun _ _ hh => hh.2.2) (fun _ _ h => h))
      ((loopAB_ct h).mono (fun _ _ h => h) (fun _ _ _ => trivial))
  · exact VG.RelCT.of_false fun _ _ hh => hc ⟨hh.1, hh.2.1⟩

end VG.Proof.Ed25519.X86
