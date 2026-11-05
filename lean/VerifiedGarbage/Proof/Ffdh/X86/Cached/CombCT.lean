module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH key generation from the context on i686: the comb's traces

Runs of the comb with the same public width leak the same traces
(`comb_trace`). The row counters come from the context, so the taint
analysis cannot tell they are public: the runs are related row by row
(`relCT_countLoop`) with the counters' values, and each tooth's bit index,
`esi`, is public in its bit's check (`τAs`) because both runs hold the same
one.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)

/-! ## The taint checks -/

/-- A tooth's bit index. -/
abbrev toothHead (j : Nat) : List Instr :=
  [.mov .esi (.mem (sc iOff)), .alu .sub .esi (.imm 1)] ++ List.replicate j (.alu .add .esi (.mem (sc rowsOff)))

/-- A tooth's bit into the window word. -/
abbrev toothTail (j : Nat) : List Instr :=
  [.alu .and .eax (.imm 1)] ++ List.replicate j (.alu .add .eax (.reg .eax)) ++
    [.alu .or .eax (.mem (sc winOff)), .store (sc winOff) .eax]

theorem tooth_eq (j : Nat) : tooth j = .seq (.block (toothHead j)) (.seq bit (.block (toothTail j))) := rfl

/-- The bit, with its index public. -/
abbrev SCheck (p : Prog isa) : Prop := (VG.Taint.check taint τAs p (VG.Taint.hintOf taint τAs p)).isSome = true

theorem bit_check : SCheck Generate.bit := by dsimp only [SCheck]; taint_decide

theorem toothHead_check : ∀ j < 5, ACheck (.block (toothHead j)) := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    (dsimp only [ACheck]; taint_decide)

theorem toothTail_check : ∀ j < 5, ACheck (.block (toothTail j)) := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    (dsimp only [ACheck]; taint_decide)

theorem zero_check : ACheck (.block [.mov .eax (.imm 0), .store (sc winOff) .eax]) := by
  dsimp only [ACheck]; taint_decide

theorem select_check : ACheck Generate.select := by dsimp only [ACheck]; taint_decide

theorem dec_check : ACheck (.block [.mov .eax (.mem (sc iOff)), .alu .sub .eax (.imm 1), .store (sc iOff) .eax]) := by
  dsimp only [ACheck]; taint_decide

theorem init_check : ACheck (.block [.mov .ecx (.mem (VG.Impl.Bignum.X86.PublicRt.argAt 0 ctxArg)),
    .mov .eax (.mem (at_ .ecx 16)), .store (sc rowsOff) .eax, .store (sc iOff) .eax]) := by
  dsimp only [ACheck]; taint_decide

theorem nil_check : ACheck (.block []) := by dsimp only [ACheck]; taint_decide

/-! ## A tooth and the digit -/

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32} {sp : BitVec 32}

/-- A tooth's bit index: `i − 1 + j R`. -/
theorem toothHead_ok (h : In Ex base bytes len args s) {j i R : Nat} (hj : j < 5) (hi : 1 ≤ i)
    (hI : w32 s.mem base iOff = i) (hR : w32 s.mem base rowsOff = R) (hb : i + 4 * R < 2 ^ 32) :
    WP isa (.block (toothHead j)) s fun u => u.mem = s.mem ∧ Keeps [.esi] s u ∧
      u.gpr .esi = BitVec.ofNat 32 (i - 1 + j * R) := by
  have io : iOff = 68 := rfl
  have ro : rowsOff = 56 := rfl
  have nb : numBase = 3336 := rfl
  simp only [toothHead, List.cons_append, List.nil_append]
  refine wp_movS (readW_ok h (d := iOff) (by omega) hI (by omega)) fun s₁ U₁ _ => wp_subS rfl fun s₂ U₂ _ => ?_
  have K₂ : Keeps [.esi] s s₂ := (U₁.keeps.mono (by decide)).widen U₂.keeps
  have m₂ : s₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  rw [← List.append_nil (List.replicate j (Instr.alu .add .esi (.mem (sc rowsOff))))]
  refine addsMem_ok h (d := rowsOff) (by omega) hR (by omega) j m₂ K₂ fun s₃ K₃ m₃ e₃ => WP.block_nil ⟨m₃, K₃, ?_⟩
  have k3 : i - 1 + j * R < 2 ^ 32 := by have := Nat.mul_le_mul_right R (show j ≤ 4 by omega); omega
  rw [e₃, U₂.gpr, U₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), BitVec.ofNat_add_ofNat]

/-- A tooth's bit into the window word. -/
theorem toothTail_ok (h : In Ex base bytes len args s) (j : Nat) :
    WP isa (.block (toothTail j)) s fun u => In Ex base bytes len args u ∧ Outside base winOff 4 s.mem u.mem ∧
      Keeps [.eax] s u := by
  have wo : winOff = 4 := rfl
  have nb : numBase = 3336 := rfl
  simp only [toothTail, List.cons_append, List.nil_append]
  refine wp_logicS (.inl rfl) rfl fun s₅ U₅ => ?_
  have h₅ := h.regs U₅.keeps U₅.mem
  refine addsSelf_ok j fun s₆ K₆ m₆ _ => ?_
  have h₆ := h₅.regs K₆ m₆
  refine wp_orS (readW_ok h₆ (d := winOff) (v := w32 s₆.mem base winOff) (by omega) rfl (BitVec.isLt _))
    fun s₇ U₇ => ?_
  have h₇ := h₆.regs U₇.keeps U₇.mem
  refine WP.mono (storeW_ok h₇ (d := winOff) (by omega) .eax) fun u ⟨I, O, _, Ku⟩ => ⟨I, ?_, ?_⟩
  · rw [U₇.mem, m₆, U₅.mem] at O; exact O
  · exact ((U₅.keeps.mono (by decide)).trans K₆).trans ((U₇.keeps.mono (by decide)).trans (Ku.mono (by decide)))

/-- A run of the digit's teeth, with the row counters. -/
abbrev DT (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (i R : Nat) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ w32 u.mem base iOff = i ∧ w32 u.mem base rowsOff = R

theorem DT.write {i R : Nat} {u t : State} (D : DT Ex base bytes len args sp i R u) (I : In Ex base bytes len args t)
    (O : Outside base winOff 4 u.mem t.mem) {rs : List Reg} (K : Keeps rs u t) (hsp : .esp ∉ rs := by decide) :
    DT Ex base bytes len args sp i R t := by
  have io : iOff = 68 := rfl
  have ro : rowsOff = 56 := rfl
  have wo : winOff = 4 := rfl
  have bl := D.1.1.bytes_lt
  refine ⟨⟨I, D.1.2.1.keep K hsp, (K.1 _ hsp).trans D.1.2.2⟩, ?_, ?_⟩
  · rw [O.w32 (by omega) (by omega)]; exact D.2.1
  · rw [O.w32 (by omega) (by omega)]; exact D.2.2

theorem tooth_trace {i R j : Nat} (hi : 1 ≤ i) (hb : i + 4 * R < 2 ^ 32) (hj : j < 5) :
    RelCT isa (Both (DT Ex base bytes len args sp i R)) (tooth j) (Both (DT Ex base bytes len args sp i R)) := by
  have k3 : i - 1 + j * R < 2 ^ 32 := by have := Nat.mul_le_mul_right R (show j ≤ 4 by omega); omega
  rw [tooth_eq]
  refine VG.RelCT.seq (taint_both (F := fun u => DT Ex base bytes len args sp i R u ∧
      u.gpr .esi = BitVec.ofNat 32 (i - 1 + j * R)) (fun _ _ D₁ D₂ => D₁.1.agree D₂.1) _ (toothHead_check j hj)
    fun x D => WP.mono (toothHead_ok D.1.1 hj hi D.2.1 D.2.2 hb) fun u ⟨m, K, e⟩ =>
      ⟨⟨⟨D.1.1.regs K m, D.1.2.1.keep K, (K.1 _ (by decide)).trans D.1.2.2⟩, by rw [m]; exact D.2.1,
        by rw [m]; exact D.2.2⟩, e⟩) ?_
  refine VG.RelCT.seq (relCT_both (F := DT Ex base bytes len args sp i R) (VG.RelCT.taint (A := taint) τAs (fun _ _ h => agreeAs h.1.1.1.1 h.2.1.1.1
      h.1.1.1.2.1 h.2.1.1.2.1 (h.1.1.1.2.2.trans h.2.1.1.2.2.symm) (h.1.2.trans h.2.2.symm)) bit_check)
    fun x De => WP.mono (bit_ok De.1.1.1 k3 De.2) fun u ⟨m, K, _⟩ =>
      ⟨⟨De.1.1.1.regs K m, De.1.1.2.1.keep K, (K.1 _ (by decide)).trans De.1.1.2.2⟩, by rw [m]; exact De.1.2.1,
        by rw [m]; exact De.1.2.2⟩) ?_
  exact taint_both (fun _ _ D₁ D₂ => D₁.1.agree D₂.1) _ (toothTail_check j hj) fun x D =>
    WP.mono (toothTail_ok D.1.1 j) fun u ⟨I, O, K⟩ => D.write I O K

theorem digit_trace {i R : Nat} (hi : 1 ≤ i) (hb : i + 4 * R < 2 ^ 32) :
    RelCT isa (Both (DT Ex base bytes len args sp i R)) Generate.digit (Both (DT Ex base bytes len args sp i R)) := by
  have wo : winOff = 4 := rfl
  have nb : numBase = 3336 := rfl
  show RelCT isa _ (.seq (.block [.mov .eax (.imm 0), .store (sc winOff) .eax]) (.seq (tooth 0) (.seq (tooth 1)
    (.seq (tooth 2) (.seq (tooth 3) (.seq (tooth 4) (.block []))))))) _
  refine VG.RelCT.seq (taint_both (fun _ _ D₁ D₂ => D₁.1.agree D₂.1) _ zero_check fun x D =>
    wp_movS rfl fun u U _ => WP.mono (storeW_ok (D.1.1.regs U.keeps U.mem) (d := winOff) (by omega) .eax)
      fun t ⟨I, O, _, K⟩ => D.write I (by rw [U.mem] at O; exact O) (U.keeps.trans (K.mono (by decide)))) ?_
  refine VG.RelCT.seq (tooth_trace hi hb (by decide)) (VG.RelCT.seq (tooth_trace hi hb (by decide))
    (VG.RelCT.seq (tooth_trace hi hb (by decide)) (VG.RelCT.seq (tooth_trace hi hb (by decide))
      (VG.RelCT.seq (tooth_trace hi hb (by decide)) ?_))))
  exact taint_both (fun _ _ D₁ D₂ => D₁.1.agree D₂.1) _ nil_check fun _ D => WP.block_nil D

/-- The digit and its entry's selection. -/
theorem digitSelect_trace {i R : Nat} (hi : 1 ≤ i) (hb : i + 4 * R < 2 ^ 32) :
    RelCT isa (Both (DT Ex base bytes len args sp i R)) (.seq Generate.digit Generate.select) fun _ _ => True :=
  VG.RelCT.seq (digit_trace hi hb) (VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.1.agree h.2.1) select_check)

end

/-! ## The rows and the comb -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32} {sp : BitVec 32} {P bits : Nat}

/-- A run at row `i`, from its own start `s₀`, x and g. -/
def CI (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (P bits i : Nat) (u : State) : Prop :=
  ∃ s₀ G x V, In Ex base bytes len args s₀ ∧ CombEnv Ex base bytes len args P G x bits s₀ ∧
    CombSt Ex base bytes len args P bits s₀ V i u ∧ ArgsOk s₀ ∧ s₀.gpr .esp = sp

theorem CI.run {i : Nat} {u : State} (C : CI Ex base bytes len args sp P bits i u) :
    Run Ex base bytes len args sp u :=
  let ⟨_, _, _, _, _, _, S, A, e⟩ := C
  ⟨S.inp, A.keep S.keeps, S.esp.trans e⟩

theorem CI.dt {i : Nat} {u : State} (C : CI Ex base bytes len args sp P bits i u) :
    DT Ex base bytes len args sp i (Spec.Rsa.FixedBaseComb.rows bits) u :=
  let ⟨_, _, _, _, _, _, S, _, _⟩ := C
  ⟨C.run, S.ctr, S.rows⟩

theorem CI.mulIn {i : Nat} {u : State} (C : CI Ex base bytes len args sp P bits i u) :
    MulIn Ex base bytes len args sp .wide 6 u :=
  let ⟨_, _, _, _, _, _, S, _, _⟩ := C
  ⟨⟨P, S.ctx, by rw [S.acc]; exact S.lt⟩, C.run.2.1, C.run.2.2⟩

/-- A run at row `i` with slot 7 below `P`. -/
def CI7 (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (P bits i : Nat) (u : State) : Prop :=
  CI Ex base bytes len args sp P bits i u ∧ sv u.mem base len .wide 7 < P

theorem step_trace {i : Nat} (hi : 1 ≤ i) (hiR : i ≤ Spec.Rsa.FixedBaseComb.rows bits)
    (hR : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639) :
    RelCT isa (Both (CI Ex base bytes len args sp P bits i)) Generate.step
      (Both fun u => CI Ex base bytes len args sp P bits (i - 1) u ∧ u.zf = some (decide (i - 1 = 0))) := by
  have hc := winChecks .wide
  unfold Generate.step
  refine VG.RelCT.seq (mul_both sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.m666
    (F := CI Ex base bytes len args sp P bits i) (fun _ C => C.mulIn) fun _ C => ?_) ?_
  · obtain ⟨s₀, G, x, V, h₀, E, S, A, e⟩ := C
    exact WP.mono (mulStep_ok S (b := 6) (.inl rfl) (by rw [S.acc]; exact S.lt)) fun t ⟨V', _, S'⟩ =>
      ⟨s₀, G, x, V', h₀, E, S', A, e⟩
  refine VG.RelCT.seq (relCT_both (F := CI7 Ex base bytes len args sp P bits i)
    ((digitSelect_trace hi (R := Spec.Rsa.FixedBaseComb.rows bits) (by omega)).mono
      (fun _ _ h => ⟨h.1.dt, h.2.dt⟩) fun _ _ h => h) fun _ C => ?_) ?_
  · obtain ⟨s₀, G, x, V, h₀, E, S, A, e⟩ := C
    have P1 := S.ctx.gt
    exact WP.mono (digitSelect_ok E h₀ S hi hiR) fun t ⟨S', T⟩ => ⟨⟨s₀, G, x, V, h₀, E, S', A, e⟩,
      by rw [T]; exact enc_lt (by omega)⟩
  refine VG.RelCT.seq (mul_both sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.m667
    (F := CI Ex base bytes len args sp P bits i)
    (fun _ C => let ⟨⟨_, _, _, _, _, _, S, _, _⟩, l⟩ := C; ⟨⟨P, S.ctx, l⟩, C.1.run.2.1, C.1.run.2.2⟩)
    fun _ C => ?_) ?_
  · obtain ⟨⟨s₀, G, x, V, h₀, E, S, A, e⟩, l⟩ := C
    exact WP.mono (mulStep_ok S (b := 7) (.inr rfl) l) fun t ⟨V', _, S'⟩ => ⟨s₀, G, x, V', h₀, E, S', A, e⟩
  refine taint_both (fun _ _ C₁ C₂ => C₁.run.agree C₂.run) _ dec_check fun _ C => ?_
  obtain ⟨s₀, G, x, V, h₀, E, S, A, e⟩ := C
  exact WP.mono (decStep_ok S hi (by omega)) fun t ⟨S', z⟩ => ⟨⟨s₀, G, x, V, h₀, E, S', A, e⟩, z⟩

theorem loop_trace (hR0 : 0 < Spec.Rsa.FixedBaseComb.rows bits) (hR : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639) :
    RelCT isa (Both (CI Ex base bytes len args sp P bits (Spec.Rsa.FixedBaseComb.rows bits)))
      (.loop Generate.step .ne) (Both (CI Ex base bytes len args sp P bits 0)) := by
  refine (relCT_countLoop (I := fun j => CI Ex base bytes len args sp P bits (Spec.Rsa.FixedBaseComb.rows bits - j))
    hR0 fun j hj => ?_).mono (fun _ _ h => by simpa only [Nat.sub_zero] using h)
      (fun _ _ h => by simpa only [Nat.sub_self] using h)
  refine (step_trace (i := Spec.Rsa.FixedBaseComb.rows bits - j) (by omega) (by omega) hR).mono (fun _ _ h => h) ?_
  rintro s t ⟨⟨C₁, z₁⟩, ⟨C₂, z₂⟩⟩
  have e : Spec.Rsa.FixedBaseComb.rows bits - j - 1 = Spec.Rsa.FixedBaseComb.rows bits - (j + 1) := by omega
  have d : (Spec.Rsa.FixedBaseComb.rows bits - j - 1 = 0) = (j + 1 = Spec.Rsa.FixedBaseComb.rows bits) :=
    propext (by omega)
  rw [e] at C₁ C₂
  simp only [d] at z₁ z₂
  exact ⟨⟨C₁, z₁⟩, ⟨C₂, z₂⟩⟩

/-- A run the comb starts from. -/
def CS (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (P bits : Nat) (u : State) : Prop :=
  ∃ G x, In Ex base bytes len args u ∧ CombEnv Ex base bytes len args P G x bits u ∧
    safeM (sv u.mem base len .wide 9) = P ∧ w32 u.mem (ctxAddr args) 16 = Spec.Rsa.FixedBaseComb.rows bits ∧
    ArgsOk u ∧ u.gpr .esp = sp

theorem combHead_trace :
    RelCT isa (Both (Run Ex base bytes len args sp)) Generate.combHead fun _ _ => True := by
  have hc := winChecks .wide
  unfold Generate.combHead
  refine VG.RelCT.seq VG.Proof.Ffdh.X86.ctxP_relCT ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m643 (ks' := [3, 4, 6]) (by decide) (by decide) (by decide)) ?_
  exact VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.run.agree h.2.run) init_check

/-- The comb's runs with the same public width `bits` and modulus `P` leak the same traces. -/
theorem comb_trace (hR0 : 0 < Spec.Rsa.FixedBaseComb.rows bits) (hR : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639) :
    RelCT isa (Both (CS Ex base bytes len args sp P bits)) Generate.comb fun _ _ => True := by
  have hc := winChecks .wide
  unfold Generate.comb
  refine VG.RelCT.seq (relCT_both (F := CI Ex base bytes len args sp P bits (Spec.Rsa.FixedBaseComb.rows bits))
    ((combHead_trace (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp)).mono
      (fun _ _ h => ?_) fun _ _ h => h) fun u C => ?_) ?_
  · obtain ⟨⟨_, _, h₁, _, _, _, A₁, e₁⟩, ⟨_, _, h₂, _, _, _, A₂, e₂⟩⟩ := h
    exact ⟨⟨h₁, A₁, e₁⟩, ⟨h₂, A₂, e₂⟩⟩
  · obtain ⟨G, x, h, E, hP, hrows, A, e⟩ := C
    exact WP.mono (combHead_ok h E hP hR0 hrows) fun t S => ⟨u, G, x, _, h, E, S, A, e⟩
  refine VG.RelCT.seq (loop_trace hR0 hR) ?_
  refine (mul_relCT (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) sp (o := 6) (a := 6)
    (b := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc.m663).mono (fun _ _ h => ?_) fun _ _ h => h
  obtain ⟨C₁, C₂⟩ := h
  have R₁ := C₁.run
  have R₂ := C₂.run
  obtain ⟨_, _, _, _, _, _, S₁, _, _⟩ := C₁
  obtain ⟨_, _, _, _, _, _, S₂, _, _⟩ := C₂
  have P1 := S₁.ctx.gt
  have P2 := S₂.ctx.gt
  exact ⟨⟨⟨P, S₁.ctx, by rw [S₁.one]; exact P1⟩, R₁.2.1, R₁.2.2⟩,
    ⟨⟨P, S₂.ctx, by rw [S₂.one]; exact P2⟩, R₂.2.1, R₂.2.2⟩⟩

end

end VG.Proof.Ffdh.X86.Cached
