module

public import VerifiedGarbage.Proof.Bignum.Arm.R2Public
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Public
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! # `R² mod n` for a public modulus is constant-time

Its branches, its search's trip count and its doublings depend only on the
public modulus `M`, through its top word; every address is the workspace's
or one its header holds.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov wp_cmp op2_imm op2_reg dpVal)

/-! ## Composing stages -/

/-- A relational fact proven from the related states. -/
theorem relCT_of_pre {P Q : State → State → Prop} {c : Prog isa} (h : ∀ s t, P s t → RelCT isa P c Q) :
    RelCT isa P c Q :=
  fun s t tr1 tr2 u w hp e1 e2 => h s t hp s t tr1 tr2 u w hp e1 e2

/-- Two stages, each run's state carried by its own predicate. -/
theorem stage_seq_ct {P1 P2 Q1 Q2 : State → Prop} {a b : Prog isa}
    (first : RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) a (fun _ _ => True))
    (wp1 : ∀ s, P1 s → WP isa a s Q1) (wp2 : ∀ s, P2 s → WP isa a s Q2)
    (second : RelCT isa (fun s t => Q1 s ∧ Q2 t ∧ s.sp = t.sp) b (fun _ _ => True)) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.seq a b) (fun _ _ => True) := by
  have start := (relCT_keep_sp first (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wp1 s h.1, wp2 t h.2.1⟩)
  exact start.seq (second.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

/-- A branch both runs take the same way. -/
theorem stage_ite_ct {P1 P2 : State → Prop} {c : Cond} {a b : Prog isa} {cond : Bool}
    (h1 : ∀ s, P1 s → isa.eval c s = some cond) (h2 : ∀ s, P2 s → isa.eval c s = some cond)
    (ha : cond = true → RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) a (fun _ _ => True))
    (hb : cond = false → RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) b (fun _ _ => True)) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.ite c a b) (fun _ _ => True) := by
  refine RelCT.ite (fun s t h => (h1 s h.1).trans (h2 t h.2.1).symm) ?_ ?_
  · cases cond
    · exact RelCT.of_false fun s t h => by rw [h1 s h.1.1] at h; cases h.2
    · exact (ha rfl).mono (fun _ _ h => h.1) (fun _ _ _ => trivial)
  · cases cond
    · exact (hb rfl).mono (fun _ _ h => h.1) (fun _ _ _ => trivial)
    · exact RelCT.of_false fun s t h => by rw [h1 s h.1.1] at h; cases h.2

/-- A block that touches no memory. -/
theorem regBlock_ct {P : State → State → Prop} {l : List Instr} {hc : Taint.Hint _}
    (h : (taint.check (Taint.ofRegs []) (.block l) hc).isSome = true) :
    RelCT isa P (.block l) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) h

/-! ## The search -/

theorem bitTest_ok (s : State) {v : Nat} (r5 : (s.gpr .r5).toNat = v) :
    WP isa (.block bitTest) s fun t => (t.gpr .r2).toNat = 2 ^ 31 ∧ (t.gpr .r5).toNat = v ∧
      t.z = decide (v < 2 ^ 31) := by
  have hlt : v < 2 ^ 32 := r5 ▸ (s.gpr .r5).isLt
  unfold bitTest
  refine wp_mov (op2_imm (by decide)) fun a ha => ?_
  refine wp_dp (op2_reg _ _) fun b hb => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht z => WP.block_nil ?_
  refine ⟨by rw [ht.gpr, hb.other .r2 (by decide), ha.gpr]; rfl,
    by rw [ht.gpr, hb.other .r5 (by decide), ha.other .r5 (by decide)]; exact r5, ?_⟩
  rw [z, hb.gpr, dpVal, ha.other .r5 (by decide), ha.gpr, and_cmp_zero, r5]
  exact decide_eq_decide.mpr (and_two_pow_eq_zero (k := 31) hlt)

/-- The search's trip count is `v`'s, which both runs share. -/
theorem bitFind_ct {v : Nat} (pos : 0 < v) :
    RelCT isa (fun s t => (s.gpr .r5).toNat = v ∧ (t.gpr .r5).toNat = v ∧ s.sp = t.sp) bitFind
      (fun _ _ => True) := by
  let B := fun (s : State) => (s.gpr .r2).toNat = 2 ^ 31 ∧ (s.gpr .r5).toNat = v ∧ s.z = decide (v < 2 ^ 31)
  have test : RelCT isa (fun s t => (s.gpr .r5).toNat = v ∧ (t.gpr .r5).toNat = v ∧ s.sp = t.sp)
      (.block bitTest) (fun _ _ => True) := regBlock_ct (by taint_decide)
  let I := fun (n : Nat) (s t : State) =>
    ((s.gpr .r2).toNat = 2 ^ n ∧ (s.gpr .r5).toNat = v ∧ v < 2 ^ n) ∧
      ((t.gpr .r2).toNat = 2 ^ n ∧ (t.gpr .r5).toNat = v ∧ v < 2 ^ n) ∧ s.sp = t.sp
  have step (n : Nat) : RelCT isa (I n) (.block bitStep) fun s t => isa.eval .eq s = isa.eval .eq t ∧
      (isa.eval .eq s = some false → True) ∧ (isa.eval .eq s = some true → ∃ m < n, I m s t) := by
    refine relCT_of_pre fun s0 _ h0 => ?_
    have n1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with e | e
      · have := h0.1.2.2; rw [e] at this; omega
      · exact e
    let F := fun (u : State) => (u.gpr .r2).toNat = 2 ^ (n - 1) ∧ u.z = decide (v < 2 ^ (n - 1)) ∧
      (u.gpr .r5).toNat = v
    have ct := (relCT_keep_sp (regBlock_ct (P := I n) (l := bitStep) (by taint_decide))
      (fun _ _ h => h.2.2)).wp (F₁ := F) (F₂ := F)
      (fun s t h => ⟨bitStep_ok s h.1.1 h.1.2.2 h.1.2.1 n1, bitStep_ok t h.2.1.1 h.2.1.2.2 h.2.1.2.1 n1⟩)
    refine ct.mono (fun _ _ h => h) ?_
    rintro s t ⟨sp, fs, ft⟩
    refine ⟨by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, fs.2.1, ft.2.1], fun _ => trivial,
      fun e => ⟨n - 1, by omega, ⟨fs.1, fs.2.2, ?_⟩, ⟨ft.1, ft.2.2, ?_⟩, sp⟩⟩
    · rw [VG.Proof.X25519.Arm.eval_eq, fs.2.1] at e; simpa using e
    · rw [VG.Proof.X25519.Arm.eval_eq, fs.2.1] at e; simpa using e
  have loop : RelCT isa (fun s t => B s ∧ B t ∧ s.sp = t.sp) (.ite .eq (.loop (.block bitStep) .eq) (.block []))
      (fun _ _ => True) :=
    stage_ite_ct (cond := decide (v < 2 ^ 31)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2.2])
      (fun hc => (RelCT.loop I step 31).mono (fun _ _ h => by
          have : v < 2 ^ 31 := of_decide_eq_true hc
          exact ⟨⟨h.1.1, h.1.2.1, this⟩, ⟨h.2.1.1, h.2.1.2.1, this⟩, h.2.2⟩) (fun _ _ _ => trivial))
      (fun _ => RelCT.block_nil (fun _ _ _ => trivial))
  rw [bitFind]
  exact stage_seq_ct test (fun s h => bitTest_ok s h) (fun s h => bitTest_ok s h) loop

/-! ## The store and the half's choice -/

theorem topStore_ct {base : BitVec 32} {len w o : Nat} :
    RelCT isa (fun s t => (ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 o) ∧
      (ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 o) ∧ s.sp = t.sp) (.block topStore)
      (fun _ _ => True) := by
  let P := fun (s : State) => s.gpr .r0 = base ∧ s.gpr .r4 = BitVec.ofNat 32 o ∧
    s.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 4)
  have one (s : State) (h : ArithmeticReady base len w s) (r4 : s.gpr .r4 = BitVec.ofNat 32 o) :
      WP isa (.block [.ldr .r6 .r0 96]) s P := by
    have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
    have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have nowrap := h.workspace.nowrap
    have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    refine wp_ldr (a := off (State.addr base) 96) (by decide) (by rw [h.ptr]; exact addr_add (by omega))
      (h.workspace.read (by omega)) fun t a => WP.block_nil ?_
    exact ⟨(a.other .r0 (by decide)).trans h.ptr, (a.other .r4 (by decide)).trans r4,
      a.gpr.trans (header.array 4 (by decide))⟩
  have first := RelCT.wp (RelCT.taint (A := taint) (c := .block [.ldr .r6 .r0 96]) (Taint.ofRegs [.r0])
    (P := fun s t => (ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 o) ∧
      (ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 o) ∧ s.sp = t.sp)
    (fun s t h => Taint.agree_ofRegs (by simpa using h.1.1.ptr.trans h.2.1.1.ptr.symm)) (by taint_decide))
    (fun s t h => ⟨one s h.1.1 h.1.2, one t h.2.1.1 h.2.1.2⟩)
  show RelCT isa _ (.block ([Instr.ldr .r6 .r0 96] ++ [.dp .add .r6 .r6 (.reg .r4), .str .r2 .r6 0,
    .dp .add .r1 .r1 (.imm 1), .str .r1 .r0 208])) _
  apply RelCT.block_append
  refine first.seq (RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r4, .r6]) ?_ (by taint_decide))
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.2.1.1.trans h.2.2.1.symm
  · exact h.2.1.2.1.trans h.2.2.2.1.symm
  · exact h.2.1.2.2.trans h.2.2.2.2.symm

/-- The half the search runs on, and its 32-bit word in the top word. -/
def topV (w M : Nat) : Nat := if topHigh w M = 0 then topLow w M else topHigh w M
def topIdx (w M : Nat) : Nat := if topHigh w M = 0 then 2 * w - 2 else 2 * w - 1

theorem topV_pos {w M : Nat} (hT : topWordOf w M ≠ 0) : 0 < topV w M := by
  unfold topV topLow topHigh at *
  split
  · rename_i h
    have := Nat.div_add_mod (topWordOf w M) (2 ^ 32)
    rw [h, Nat.mul_zero, Nat.zero_add] at this
    omega
  · omega

/-- The top word's halves read: the state the choice starts from. -/
def TopRead (base : BitVec 32) (len w M : Nat) (s : State) : Prop :=
  ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (8 * w - 8) ∧
    (s.gpr .r3).toNat = topLow w M ∧ (s.gpr .r5).toNat = topHigh w M

/-- The half chosen. -/
def TopChosen (base : BitVec 32) (len w M : Nat) (s : State) : Prop :=
  ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (4 * topIdx w M) ∧ (s.gpr .r5).toNat = topV w M

theorem topHalf_wp (s : State) {base : BitVec 32} {len w M : Nat} (h : TopRead base len w M s) :
    WP isa (.block topHalf) s fun t => (ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
      (t.gpr .r3).toNat = topLow w M ∧ (t.gpr .r5).toNat = topHigh w M) ∧ t.z = decide (topHigh w M = 0) := by
  have hw : 2 ≤ w := h.1.width ▸ h.1.layout.1
  unfold topHalf
  refine wp_dp (op2_imm (by decide)) fun a ha => ?_
  refine wp_cmp (op2_imm (by decide)) fun u hu zu => WP.block_nil ?_
  have rest : Rest [.r4] s u := (ha.rest (by decide)).trans (hu.rest _)
  refine ⟨⟨h.1.of_mem (hu.mem.trans ha.mem) rest ((rest.gpr .r0 (by decide)).trans h.1.ptr), ?_,
    by rw [rest.gpr .r3 (by decide)]; exact h.2.2.1, by rw [rest.gpr .r5 (by decide)]; exact h.2.2.2⟩, ?_⟩
  · rw [hu.gpr, ha.gpr, dpVal, h.2.1]
    change BitVec.ofNat 32 _ + BitVec.ofNat 32 4 = _
    rw [← BitVec.ofNat_add, show 8 * w - 8 + 4 = 8 * w - 4 by omega]
  · rw [zu, ha.other .r5 (by decide), cmp_zero, h.2.2.2]

theorem topChoose_wp (s : State) {base : BitVec 32} {len w M : Nat}
    (h : (ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
      (s.gpr .r3).toNat = topLow w M ∧ (s.gpr .r5).toNat = topHigh w M) ∧ s.z = decide (topHigh w M = 0)) :
    WP isa (.ite .eq (.block lowHalf) (.block [])) s (TopChosen base len w M) := by
  have hw : 2 ≤ w := h.1.1.width ▸ h.1.1.layout.1
  by_cases H0 : topHigh w M = 0
  · refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, h.2, decide_eq_true H0]) (fun _ => ?_) (by simp)
    unfold lowHalf
    refine wp_dp (op2_imm (by decide)) fun b hb => ?_
    refine wp_mov (op2_reg _ _) fun c hc => ?_
    refine wp_dp (op2_imm (by decide)) fun d hd => WP.block_nil ?_
    have rest : Rest [.r1, .r4, .r5] s d :=
      (hb.rest (by decide)).trans ((hc.rest (by decide)).trans (hd.rest (by decide)))
    refine ⟨h.1.1.of_mem (hd.mem.trans (hc.mem.trans hb.mem)) rest ((rest.gpr .r0 (by decide)).trans h.1.1.ptr),
      ?_, ?_⟩
    · rw [hd.other .r4 (by decide), hc.other .r4 (by decide), hb.gpr, dpVal, h.1.2.1]
      change BitVec.ofNat 32 _ - BitVec.ofNat 32 4 = _
      simp only [topIdx, H0, ite_true]
      rw [VG.Offset.ofNat_sub_ofNat (by omega)]
      congr 1; omega
    · simp only [topV, H0, ite_true]
      rw [hd.other .r5 (by decide), hc.gpr, hb.other .r3 (by decide), h.1.2.2.1]
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, h.2, decide_eq_false H0]) (by simp)
      (fun _ => WP.block_nil ?_)
    refine ⟨h.1.1, ?_, ?_⟩
    · simp only [topIdx, H0, ite_false]; rw [h.1.2.1]; congr 1; omega
    · simp only [topV, H0, ite_false]; exact h.1.2.2.2

theorem topFind_wp (s : State) {base : BitVec 32} {len w M : Nat} (h : TopChosen base len w M s)
    (pos : 0 < topV w M) :
    WP isa bitFind s fun t => ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 (4 * topIdx w M) := by
  refine (bitFind_ok s (c := (s.gpr .r1).toNat) h.2.2 pos (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])).mono ?_
  rintro t ⟨_, _, _, mem, rest⟩
  exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.1.ptr), by rw [rest.gpr .r4 (by decide)]; exact h.2.1⟩

theorem topInit_ct {base : BitVec 32} {len w M : Nat} (hT : topWordOf w M ≠ 0) :
    RelCT isa (fun s t => TopRead base len w M s ∧ TopRead base len w M t ∧ s.sp = t.sp) topInit
      (fun _ _ => True) := by
  have low : RelCT isa (fun s t =>
      (((ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
        (s.gpr .r3).toNat = topLow w M ∧ (s.gpr .r5).toNat = topHigh w M) ∧ s.z = decide (topHigh w M = 0)) ∧
      ((ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
        (t.gpr .r3).toNat = topLow w M ∧ (t.gpr .r5).toNat = topHigh w M) ∧ t.z = decide (topHigh w M = 0)) ∧
      s.sp = t.sp)) (.block lowHalf) (fun _ _ => True) := regBlock_ct (by taint_decide)
  have choose : RelCT isa (fun s t =>
      ((ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
        (s.gpr .r3).toNat = topLow w M ∧ (s.gpr .r5).toNat = topHigh w M) ∧ s.z = decide (topHigh w M = 0)) ∧
      ((ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
        (t.gpr .r3).toNat = topLow w M ∧ (t.gpr .r5).toNat = topHigh w M) ∧ t.z = decide (topHigh w M = 0)) ∧
      s.sp = t.sp) (.ite .eq (.block lowHalf) (.block [])) (fun _ _ => True) :=
    stage_ite_ct (cond := decide (topHigh w M = 0)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2]) (fun _ => low)
      (fun _ => RelCT.block_nil (fun _ _ _ => trivial))
  have find : RelCT isa (fun s t => TopChosen base len w M s ∧ TopChosen base len w M t ∧ s.sp = t.sp) bitFind
      (fun _ _ => True) :=
    (bitFind_ct (topV_pos hT)).mono (fun _ _ h => ⟨h.1.2.2, h.2.1.2.2, h.2.2⟩) (fun _ _ _ => trivial)
  rw [topInit]
  exact stage_seq_ct (regBlock_ct (by taint_decide)) (fun s h => topHalf_wp s h) (fun s h => topHalf_wp s h)
    (stage_seq_ct choose (fun s h => topChoose_wp s h) (fun s h => topChoose_wp s h)
      (stage_seq_ct find (fun s h => topFind_wp s h (topV_pos hT)) (fun s h => topFind_wp s h (topV_pos hT))
        topStore_ct))

/-! ## The initialization and `R² mod n` -/

theorem r2PublicInit_ct {base : BitVec 32} {len w M : Nat} :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
      r2PublicInit (fun _ _ => True) := by
  let A := fun (s : State) => ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have small (o : Nat) (v : BitVec 32) (ho : o < 8) (ho0 : o ≠ 0) (encO : encodable (BitVec.ofNat 32 o) = true)
      (encV : encodable v = true) (s : State) (h : A s) : WP isa (smallConst (BitVec.ofNat 32 o) v) s A := by
    have fits : arrAt w 8 ≤ 8 * len := h.1.width ▸ h.1.layout.2.2.1
    exact (smallConst_ok s v h.1 ho ho0 encO encV).mono fun t k =>
      ⟨k.1, (keeps_array_num k.2.2.2.1 fits op0 (Ne.symm ho0)).trans h.2⟩
  have smallCT (o : Nat) (v : BitVec 32) (ho : o < 8) (encO : encodable (BitVec.ofNat 32 o) = true)
      (encV : encodable v = true) :
      RelCT isa (fun s t => A s ∧ A t ∧ s.sp = t.sp) (smallConst (BitVec.ofNat 32 o) v) (fun _ _ => True) :=
    (smallConst_ct v ho encO encV).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  let A3 := fun (s : State) => A s ∧ s.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 0) ∧
    s.gpr .r1 = BitVec.ofNat 32 w
  have wp3 (s : State) (h : A s) : WP isa (.block topPointers) s A3 :=
    (topPointers_ok s h.1).mono fun t k =>
      ⟨⟨h.1.of_mem k.2.2.1 k.2.2.2 ((k.2.2.2.gpr .r0 (by decide)).trans h.1.ptr), by rw [k.2.2.1]; exact h.2⟩,
        k.1, k.2.1⟩
  have ct3 : RelCT isa (fun s t => A s ∧ A t ∧ s.sp = t.sp) (.block topPointers) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r0])
      (fun s t h => Taint.agree_ofRegs (by simpa using h.1.1.ptr.trans h.2.1.1.ptr.symm)) (by taint_decide)
  let A4 := fun (s : State) => TopRead base len w M s ∧ s.z = decide (topWordOf w M = 0)
  have wp4 (s : State) (h : A3 s) : WP isa (.block topWord) s A4 :=
    (topWord_state s h.1.1 h.2.1 h.2.2 h.1.2).mono fun t k =>
      ⟨⟨h.1.1.of_mem k.2.2.2.2.1 k.2.2.2.2.2 ((k.2.2.2.2.2.gpr .r0 (by decide)).trans h.1.1.ptr), k.1, k.2.1,
        k.2.2.1⟩, k.2.2.2.1⟩
  have ct4 : RelCT isa (fun s t => A3 s ∧ A3 t ∧ s.sp = t.sp) (.block topWord) (fun _ _ => True) := by
    refine RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .r6]) ?_ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.1.1.ptr.trans h.2.1.1.1.ptr.symm
    · exact h.1.2.2.trans h.2.1.2.2.symm
    · exact h.1.2.1.trans h.2.1.2.1.symm
  have branch : RelCT isa (fun s t => A4 s ∧ A4 t ∧ s.sp = t.sp) (.ite .eq r2Init topInit) (fun _ _ => True) :=
    stage_ite_ct (cond := decide (topWordOf w M = 0)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun _ => (r2Init_ct (base := base) (len := len) (w := w)).mono
        (fun _ _ h => ⟨h.1.1.1, h.2.1.1.1, h.2.2⟩) (fun _ _ _ => trivial))
      (fun hc => (topInit_ct (of_decide_eq_false hc)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩)
        (fun _ _ _ => trivial))
  rw [r2PublicInit]
  exact stage_seq_ct (smallCT 4 0 (by decide) (by decide) (by decide))
    (fun s h => small 4 0 (by decide) (by decide) (by decide) (by decide) s h)
    (fun s h => small 4 0 (by decide) (by decide) (by decide) (by decide) s h)
    (stage_seq_ct (smallCT 7 2 (by decide) (by decide) (by decide))
      (fun s h => small 7 2 (by decide) (by decide) (by decide) (by decide) s h)
      (fun s h => small 7 2 (by decide) (by decide) (by decide) (by decide) s h)
      (stage_seq_ct ct3 (fun s h => wp3 s h) (fun s h => wp3 s h)
        (stage_seq_ct ct4 (fun s h => wp4 s h) (fun s h => wp4 s h) branch)))

theorem r2Public_ct {base : BitVec 32} {len w M : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
      r2Public (fun _ _ => True) := by
  let P := R2PublicInitialized base len w M
  have initialized := (relCT_keep_sp (r2PublicInit_ct (base := base) (len := len) (w := w) (M := M))
    (fun _ _ h => h.2.2)).wp (fun s t h =>
      ⟨WP.mono (r2PublicInit_ok s h.1.1 h.1.2) (fun _ j => j.1),
       WP.mono (r2PublicInit_ok t h.2.1.1 h.2.1.2) (fun _ j => j.1)⟩)
  have loop : RelCT isa (fun s t => s.sp = t.sp ∧ P s ∧ P t) doubleLoop (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have hw : 2 ≤ w := h.2.1.ready.width ▸ h.2.1.ready.layout.1
    obtain ⟨cpos, cle⟩ := r2PublicCount_le (w := w) (M := M) (by omega)
    exact doubleLoop_ct cpos (by omega) s t tr1 tr2 u v ⟨h.2.1.ready, h.2.2.ready, h.1⟩ e1 e2
  have post (s : State) (h : P s) : WP isa doubleLoop s fun t => ∃ m, R2Sq base len w m w t :=
    WP.mono (r2PublicLoop_ok s h countFits) (fun _ j => ⟨M, j.1⟩)
  have powered := ((relCT_keep_sp loop (fun _ _ h => h.1)).wp
    (fun s t h => ⟨post s h.2.1, post t h.2.2⟩)).mono
    (Q' := R2SqRel base len w w) (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)
  exact initialized.seq (powered.seq r2Squares_ct)

end VG.Proof.Bignum.Arm
