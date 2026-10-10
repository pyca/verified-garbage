import VerifiedGarbage.Proof.Ed25519.X86.WindowLoop
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.X86.Point32.AddSum

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

theorem VerifyCTFacts.kNib {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (n : Nat) :
    kNib s₀ n = kNib t₀ n :=
  congrArg (nibbleOf · n) h.challengeBytes

theorem VerifyCTFacts.sNib {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (n : Nat) :
    sNib s₀ n = sNib t₀ n :=
  congrArg (nibbleOf · n) h.scalarBytes

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

/-- A nibble's byte: its address from `esp` and the counter, which are public, then its load
at an address the same in both runs by correctness, and the nibble's parity. -/
theorem nibbleByte_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {P₁ P₂ : State → Prop} {a add i : Nat}
    (ha : a < 4) (hi : i < 2 ^ 32)
    (h₁ : ∀ x, P₁ x → Saved s₀ (arg s₀ 3) x ∧ x.gpr .esi = BitVec.ofNat 32 i)
    (h₂ : ∀ y, P₂ y → Saved t₀ (arg t₀ 3) y ∧ y.gpr .esi = BitVec.ofNat 32 i)
    (hfirst : RelCT isa (fun x y => x.gpr .esp = y.gpr .esp ∧ x.gpr .esi = y.gpr .esi)
      (.block [.mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))])
      (fun _ _ => True))
    (hrest : RelCT isa (fun x y => x.gpr .eax = y.gpr .eax ∧ x.gpr .esi = y.gpr .esi)
      (.block [.movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)]) (fun _ _ => True)) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y)
      (.block [.mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.mem (at_ .esp (4 + 4 * a))),
        .movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)]) (fun _ _ => True) := by
  have w₁ (x : State) (hx : P₁ x) : WP isa (.block [.mov .eax (.reg .esi), .shift .shr .eax 1,
      .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))]) x fun u =>
        u.gpr .eax = arg s₀ a + BitVec.ofNat 32 (i / 2) ∧ u.gpr .esi = BitVec.ofNat 32 i :=
    WP.mono (nibbleAddr_ok (verify_pre h.left).scratch (h₁ x hx).1 ha hi (h₁ x hx).2)
      fun _ ⟨k, e⟩ => ⟨e, (k.gpr _ (by decide)).trans (h₁ x hx).2⟩
  have w₂ (y : State) (hy : P₂ y) : WP isa (.block [.mov .eax (.reg .esi), .shift .shr .eax 1,
      .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))]) y fun u =>
        u.gpr .eax = arg t₀ a + BitVec.ofNat 32 (i / 2) ∧ u.gpr .esi = BitVec.ofNat 32 i :=
    WP.mono (nibbleAddr_ok (verify_pre h.right).scratch (h₂ y hy).1 ha hi (h₂ y hy).2)
      fun _ ⟨k, e⟩ => ⟨e, (k.gpr _ (by decide)).trans (h₂ y hy).2⟩
  show RelCT isa _ (.block (([.mov .eax (.reg .esi), .shift .shr .eax 1,
    .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))] : List Instr) ++
    [.movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)])) _
  refine ctBlockAppend (((hfirst.mono (P' := fun x y => P₁ x ∧ P₂ y)
    (fun x y hh => ⟨saved_esp h (h₁ x hh.1).1 (h₂ y hh.2).1, (h₁ x hh.1).2.trans (h₂ y hh.2).2.symm⟩)
    (fun _ _ h => h)).wp fun x y hh => ⟨w₁ x hh.1, w₂ y hh.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, ex, ey⟩
  exact ⟨ex.1.trans ((congrArg (· + BitVec.ofNat 32 (i / 2)) (h.args a ha)).trans ey.1.symm),
    ex.2.trans ey.2.symm⟩

/-- A nibble's code: its byte, then a branch on its parity, the same in both runs by
correctness. -/
theorem digitNibble_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {P₁ P₂ : State → Prop} {a add i : Nat}
    (ha : a < 4) (hi : i < 2 ^ 32)
    (h₁ : ∀ x, P₁ x → Saved s₀ (arg s₀ 3) x ∧ x.gpr .esi = BitVec.ofNat 32 i)
    (h₂ : ∀ y, P₂ y → Saved t₀ (arg t₀ 3) y ∧ y.gpr .esi = BitVec.ofNat 32 i)
    (hfirst : RelCT isa (fun x y => x.gpr .esp = y.gpr .esp ∧ x.gpr .esi = y.gpr .esi)
      (.block [.mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.mem (at_ .esp (4 + 4 * a)))])
      (fun _ _ => True))
    (hrest : RelCT isa (fun x y => x.gpr .eax = y.gpr .eax ∧ x.gpr .esi = y.gpr .esi)
      (.block [.movzx8 .eax (at_ .eax add), .alu .test .esi (.imm 1)]) (fun _ _ => True))
    (z₁ : ∀ x, P₁ x → WP isa (.block [.mov .eax (.reg .esi), .shift .shr .eax 1,
      .alu .add .eax (.mem (at_ .esp (4 + 4 * a))), .movzx8 .eax (at_ .eax add),
      .alu .test .esi (.imm 1)]) x fun u => u.zf = some (decide (i % 2 = 0)))
    (z₂ : ∀ y, P₂ y → WP isa (.block [.mov .eax (.reg .esi), .shift .shr .eax 1,
      .alu .add .eax (.mem (at_ .esp (4 + 4 * a))), .movzx8 .eax (at_ .eax add),
      .alu .test .esi (.imm 1)]) y fun u => u.zf = some (decide (i % 2 = 0))) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y) (digitNibble (4 + 4 * a) add) (fun _ _ => True) := by
  rw [digitNibble]
  refine VG.RelCT.seq (((nibbleByte_ct h ha hi h₁ h₂ hfirst hrest).wp fun x y hh => ⟨z₁ x hh.1, z₂ y hh.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y hh
    change x.zf.map Bool.not = y.zf.map Bool.not
    rw [hh.1, hh.2]
  · exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide)
  · exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide)

/-! ## Adding a digit's entry -/

theorem digitTest_ok {s : State} {v : Nat} (hv : v < 16) {B : BitVec 32}
    (hs : s.gpr .eax = BitVec.ofNat 32 v ∧ s.gpr .edi = B) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t =>
      (t.gpr .eax = BitVec.ofNat 32 v ∧ t.gpr .edi = B) ∧ t.zf = some (decide (v = 0)) :=
  Wp.wp_test fun t ht zt => WP.block_nil ⟨⟨by rw [ht.gpr]; exact hs.1, by rw [ht.gpr]; exact hs.2⟩,
    by rw [zt, hs.1, digit_test_fact v hv]⟩

/-- The digit's test keeps the call's context. -/
theorem digitTest_call {s : State} {v : Nat} (hv : v < 16) {B : BitVec 32}
    (hs : s.gpr .eax = BitVec.ofNat 32 v ∧ s.gpr .edi = B) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t =>
      ((t.gpr .eax = BitVec.ofNat 32 v ∧ t.gpr .edi = B) ∧ t.zf = some (decide (v = 0))) ∧
        t.gpr .edi = s.gpr .edi ∧ t.wr = s.wr ∧ t.gpr .esp = s.gpr .esp :=
  Wp.wp_test fun t ht zt => WP.block_nil ⟨⟨⟨by rw [ht.gpr]; exact hs.1, by rw [ht.gpr]; exact hs.2⟩,
    by rw [zt, hs.1, digit_test_fact v hv]⟩, congrFun ht.gpr _, ht.wr, congrFun ht.gpr _⟩

/-- A digit's addition branches on the digit and addresses the table by it, the same in both
runs; its call of `vg_ed25519_r32_point_add` is analysed with it (`callTaintR`). -/
theorem addDigit_ct (o : Nat) (ho : o = 1024 ∨ o = 3072) {v : Nat} (hv : v < 16) (B : BitVec 32) :
    RelCT isa (fun x y => CallCTPre B x y ∧ (x.gpr .eax = BitVec.ofNat 32 v ∧ x.gpr .edi = B) ∧
      (y.gpr .eax = BitVec.ofNat 32 v ∧ y.gpr .edi = B)) (addDigit o) (fun _ _ => True) := by
  have test : RelCT isa (fun x y => CallCTPre B x y ∧ (x.gpr .eax = BitVec.ofNat 32 v ∧ x.gpr .edi = B) ∧
      (y.gpr .eax = BitVec.ofNat 32 v ∧ y.gpr .edi = B)) (.block [.alu .test .eax (.reg .eax)])
      (fun _ _ => True) :=
    VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide)
  have body : RelCT isa (fun x y => CallCTPre B x y ∧ x.gpr .eax = y.gpr .eax)
      (.seq (.block (entryAddr o ++ pointFromTableQ)) Point32.addCall) (fun _ _ => True) := by
    obtain ⟨_, hc⟩ : ∃ h, (taint.check (callTaintR [.eax])
        (.seq (.block (entryAddr o ++ pointFromTableQ)) Point32.addCall) h).isSome = true := by
      rcases ho with rfl | rfl
      · taint_decide_sum [addSum]
      · taint_decide_sum [addSum]
    exact VG.RelCT.taint (A := taint) (callTaintR [.eax])
      (fun _ _ hh => callTaintR_agree hh.1 fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hh.2) hc
  rw [addDigit]
  refine VG.RelCT.seq (ctWithRuns test fun x y hh => ⟨digitTest_call hv hh.2.1, digitTest_call hv hh.2.2⟩)
    (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y ⟨_, a, b, _, ⟨⟨_, zx⟩, _⟩, ⟨⟨_, zy⟩, _⟩⟩
    change x.zf.map Bool.not = y.zf.map Bool.not
    rw [zx, zy]
  · refine body.mono (fun x y hh => ?_) (fun _ _ h => h)
    obtain ⟨⟨_, a, b, ⟨⟨ca, cb, w, sp⟩, _⟩, ⟨⟨vx, _⟩, ex, wx, px⟩, ⟨⟨vy, _⟩, ey, wy, py⟩⟩, _⟩ := hh
    exact ⟨⟨ca.keep ex wx px, cb.keep ey wy py, by rw [wx, wy, w], by rw [px, py, sp]⟩, vx.1.trans vy.1.symm⟩
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

theorem doubleWindow_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 128)
    (hx : WinAt s₀ Aa R i x) : WP isa doubleWindow x (WinAt s₀ Aa R i) := by
  obtain ⟨w, e, a, ha⟩ := hx
  exact WP.mono (doubleWindow_ok w.ctx (esi_lt (by omega) e) ha) fun b ⟨kb, eb, rb, hb⟩ =>
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

/-- A digit's addition, after its code, from the digit's value in both runs. -/
theorem digitAdd_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {i v : Nat} (hv : v < 16) {o : Nat} (ho : o = 1024 ∨ o = 3072) :
    RelCT isa (fun x y => DigitAt s₀ Aa R i v x ∧ DigitAt t₀ Aa R i v y) (addDigit o) (fun _ _ => True) :=
  (addDigit_ct o ho hv (arg s₀ 3)).mono
    (fun _ _ hh => ⟨h.callPre hh.1.1.1.saved hh.2.1.1.saved, ⟨hh.1.2.1, hh.1.2.2⟩,
      ⟨hh.2.2.1, hh.2.2.2.trans (h.args 3 (by decide)).symm⟩⟩)
    (fun _ _ h => h)

theorem digitK_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128) :
    RelCT isa (fun x y => WinAt s₀ Aa R n x ∧ WinAt t₀ Aa R n y) (digitNibble 12 0) (fun _ _ => True) :=
  digitNibble_ct (a := 2) h (by decide) (by omega) (fun _ hx => ⟨hx.1.saved, hx.2.1⟩)
    (fun _ hy => ⟨hy.1.saved, hy.2.1⟩)
    (VG.RelCT.taint (A := taint) (regsTaint [.esp, .esi]) (fun _ _ hh => agree_two hh) (by taint_decide))
    (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => agree_two hh) (by taint_decide))
    (fun _ hx => WP.mono (nibbleByte_ok (a := 2) hx.1.pre.scratch hx.1.saved (by decide) hx.1.pre.challenge
      (by omega) (by decide) hx.2.1) fun _ h => h.2.2)
    (fun _ hy => WP.mono (nibbleByte_ok (a := 2) hy.1.pre.scratch hy.1.saved (by decide) hy.1.pre.challenge
      (by omega) (by decide) hy.2.1) fun _ h => h.2.2)

theorem digitS_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 64) {P₁ P₂ : State → Prop}
    (h₁ : ∀ x, P₁ x → WinAt s₀ Aa R n x) (h₂ : ∀ y, P₂ y → WinAt t₀ Aa R n y) :
    RelCT isa (fun x y => P₁ x ∧ P₂ y) (digitNibble 8 32) (fun _ _ => True) :=
  digitNibble_ct (a := 1) h (by decide) (by omega) (fun _ hx => ⟨(h₁ _ hx).1.saved, (h₁ _ hx).2.1⟩)
    (fun _ hy => ⟨(h₂ _ hy).1.saved, (h₂ _ hy).2.1⟩)
    (VG.RelCT.taint (A := taint) (regsTaint [.esp, .esi]) (fun _ _ hh => agree_two hh) (by taint_decide))
    (VG.RelCT.taint (A := taint) (regsTaint [.eax, .esi]) (fun _ _ hh => agree_two hh) (by taint_decide))
    (fun _ hx => WP.mono (nibbleByte_ok (a := 1) (h₁ _ hx).1.pre.scratch (h₁ _ hx).1.saved (by decide)
      (h₁ _ hx).1.pre.scalar (by omega) (by decide) (h₁ _ hx).2.1) fun _ h => h.2.2)
    (fun _ hy => WP.mono (nibbleByte_ok (a := 1) (h₂ _ hy).1.pre.scratch (h₂ _ hy).1.saved (by decide)
      (h₂ _ hy).1.pre.scalar (by omega) (by decide) (h₂ _ hy).2.1) fun _ h => h.2.2)

theorem digitK_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128)
    (hx : WinAt s₀ Aa R n x) : WP isa (digitNibble 12 0) x (DigitAt s₀ Aa R n (kNib s₀ n)) :=
  WP.mono (digitK_ok hn x hx.1 hx.2.1) fun _ ⟨k, e⟩ => DigitAt.of_keep hx k e

theorem digitS_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 64)
    (hx : WinAt s₀ Aa R n x) : WP isa (digitNibble 8 32) x (DigitAt s₀ Aa R n (sNib s₀ n)) :=
  WP.mono (digitS_ok hn x hx.1 hx.2.1) fun _ ⟨k, e⟩ => DigitAt.of_keep hx k e

theorem addK_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128) :
    RelCT isa (fun x y => WinAt s₀ Aa R n x ∧ WinAt t₀ Aa R n y) addK (fun _ _ => True) :=
  seq_runs (digitK_ct h hn) (fun _ hx => digitK_at hn hx)
    (fun y hy => by rw [h.kNib n]; exact digitK_at hn hy) (digitAdd_ct h (kNib_lt s₀ n) (.inl rfl))

theorem addK_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128)
    (hx : WinAt s₀ Aa R n x) : WP isa addK x (WinAt s₀ Aa R n) := by
  obtain ⟨w, e, a, ha⟩ := hx
  exact WP.mono (addK_ok w hn e ha) fun _ ⟨wt, et, rt⟩ => ⟨wt, et.trans e, _, rt⟩

theorem cmp64_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128)
    (hx : WinAt s₀ Aa R n x) : WP isa (.block [.alu .cmp .esi (.imm 64)]) x fun t =>
      WinAt s₀ Aa R n t ∧ t.cf = some (decide (n < 64)) :=
  WP.mono (cmp64_ok hx.1 hn hx.2.1) fun _ ⟨w, e, m, c⟩ => ⟨⟨w, e.trans hx.2.1, by rw [m]; exact hx.2.2⟩, c⟩

/-- `S`'s digit, added below its 64 nibbles: the branch is on the counter. -/
theorem addS_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128) :
    RelCT isa (fun x y => WinAt s₀ Aa R n x ∧ WinAt t₀ Aa R n y) addS (fun _ _ => True) := by
  rw [addS]
  refine VG.RelCT.seq (((VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none)
    (by taint_decide)).wp fun x y hh => ⟨cmp64_at hn hh.1, cmp64_at hn hh.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro x y hh
    change x.cf = y.cf
    rw [hh.1.2, hh.2.2]
  · by_cases h64 : n < 64
    · exact (seq_runs (digitS_ct h h64 (fun _ hx => hx) (fun _ hy => hy))
        (fun _ hx => digitS_at h64 hx) (fun _ hy => by rw [h.sNib n]; exact digitS_at h64 hy)
        (digitAdd_ct h (sNib_lt s₀ n) (.inr rfl))).mono (fun _ _ hh => ⟨hh.1.1.1, hh.1.2.1⟩)
        (fun _ _ h => h)
    · refine VG.RelCT.of_false fun x y hh => h64 ?_
      have e : x.cf = some true := hh.2
      rw [hh.1.1.2] at e
      simpa using e
  · exact VG.RelCT.block_nil fun _ _ _ => trivial

theorem addS_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128)
    (hx : WinAt s₀ Aa R n x) : WP isa addS x fun _ => True :=
  WP.mono (addS_ok hx.1 hn hx.2.1 hx.2.2.choose_spec) fun _ _ => trivial

/-! ## Nibbles -/

/-- With `n` nibbles of the scalars left. -/
def NLoopAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (n : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
    Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (nsum s₀ Aa n)

theorem esiDec_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat}
    (hx : NLoopAt s₀ Aa R (i + 1) x) : WP isa (.block [.alu .sub .esi (.imm 1)]) x (WinAt s₀ Aa R i) :=
  WP.mono (esiDec_ok hx.1 hx.2.1) fun _ ⟨w, e, m⟩ => ⟨w, e, _, by rw [m]; exact hx.2.2⟩

theorem nibbleStep_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {n : Nat} (hn : n < 128) :
    RelCT isa (fun x y => NLoopAt s₀ Aa R (n + 1) x ∧ NLoopAt t₀ Aa R (n + 1) y) nibbleStep
      (fun _ _ => True) := by
  rw [nibbleStep]
  refine seq_runs (VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide))
    (fun _ hx => esiDec_at hx) (fun _ hy => esiDec_at hy) ?_
  refine seq_runs (doubleWindow_ct h) (fun _ hx => doubleWindow_at hn hx)
    (fun _ hy => doubleWindow_at hn hy) ?_
  refine seq_runs (addK_ct h hn) (fun _ hx => addK_at hn hx) (fun _ hy => addK_at hn hy) ?_
  refine seq_runs (F₁ := fun _ => True) (F₂ := fun _ => True) (addS_ct h hn) (fun _ hx => addS_at hn hx)
    (fun _ hy => addS_at hn hy) ?_
  exact VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide)

theorem loopN_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {Aa : EPoint dZ}
    {R : Spec.Ed25519.Point} {c : Nat} (hc0 : 0 < c) (hc : c ≤ 128) :
    RelCT isa (fun x y => NLoopAt s₀ Aa R c x ∧ NLoopAt t₀ Aa R c y) (.loop nibbleStep .ne)
      (fun _ _ => True) := by
  refine (VG.RelCT.loop (I := fun m x y => (NLoopAt s₀ Aa R m x ∧ NLoopAt t₀ Aa R m y) ∧
    0 < m ∧ m ≤ 128) ?_ c).mono (fun x y hh => ⟨hh, hc0, hc⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ hh => Nat.lt_irrefl 0 hh.2.1
  by_cases hj : j < 128
  · have hw (u x : State) (hx : NLoopAt u Aa R (j + 1) x) : WP isa nibbleStep x fun t =>
        t.zf.map (!·) = some (!decide (j = 0)) ∧ NLoopAt u Aa R j t :=
      WP.mono (nibbleStep_ok hx.1 hj hx.2.1 hx.2.2) fun t ⟨wt, et, zt, rt⟩ =>
        ⟨by rw [zt]; rfl, wt, et, rt⟩
    refine (((nibbleStep_ct h hj).mono (fun x y hh => hh.1) (fun _ _ h => h)).wp
      fun x y hh => ⟨hw s₀ x hh.1.1, hw t₀ y hh.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun _ => trivial, fun he => ?_⟩
    have he' := xz.symm.trans he
    have : j ≠ 0 := by simpa using he'
    exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ hh => hj (by omega)

theorem nibbles_at {s₀ x : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {c : Nat}
    (hx : LoopAt s₀ Aa R c x) : WP isa (.block [.alu .add .esi (.reg .esi)]) x (NLoopAt s₀ Aa R (2 * c)) :=
  WP.mono (nibbles_ok hx.1 hx.2.1) fun _ ⟨w, e, m⟩ => ⟨w, e, by rw [m, nsum_two_mul]; exact hx.2.2⟩

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
    have ⟨_, hc⟩ : ∃ h, (taint.check callTaint₀ windowPrep h).isSome = true := by
      taint_decide_sum [addSum]
    VG.RelCT.taint (A := taint) callTaint₀ (fun _ _ hh => callTaint₀_agree (h.callPre hh.1.1 hh.2.1)) hc
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
  · exact (seq_runs (VG.RelCT.taint (A := taint) (regsTaint []) (fun _ _ _ => agree_none) (by taint_decide))
      (fun _ hx => nibbles_at hx) (fun _ hy => nibbles_at hy)
      (loopN_ct h (c := 2 * c) (by omega) (by omega))).mono (fun _ _ hh => hh.2.2) (fun _ _ h => h)
  · exact VG.RelCT.of_false fun _ _ hh => hc ⟨hh.1, hh.2.1⟩

end VG.Proof.Ed25519.X86
