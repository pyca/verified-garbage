module

public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-! ### `MlDsa.Arm.Pack.HintCT`, which the modules that import this one used -/

section

/-!
# Constant time of code that leaks memory both runs agree on (ARMv7)

The ARMv7 counterpart of the x86-64 `memTaint` of ML-DSA
(`Proof/MlDsa/X86_64/Pack/HintPack.lean`), for `vg_mldsa_hint_bit_pack` and
`vg_mldsa_hint_bit_unpack`, which branch and index memory on their input,
which they load from memory.

The taint analysis (`Proof/Framework/Arm/Taint.lean`) treats loaded memory as
secret. `memTaint` is one for code that runs from states whose permitted
memory both runs agree on (`MemEq`): every load (`ldr`, `ldrb`) it makes is
then public, and a store keeps the agreement if it stores a public value at a
public address.

On ARMv7 these functions run in a frame, which holds the callee-saved
registers of each run, which differ; the analysis would take them for
public. So the code that needs it runs from states narrowed to the regions it
accesses (`RelCT.narrow`): a run with fewer permissions is the actual run
(`Exec.widen` and determinism). What is left of the frame, the instructions
that only access the stack (`spOnly`), leaks only addresses computed from
the stack pointer (`RelCT.spBlock`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm
open VG.Arm.Taint (T pub)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The taint agrees, and the permissions and the memory they permit. -/
def MAgree (τ : T) (s₁ s₂ : State) : Prop :=
  VG.Arm.Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- Loads are public; stores must store public values; the stack and frames
are not analysed. -/
def mstep (τ : T) : Instr → Option T
  | .ldr t n off => (VG.Arm.Taint.stepK τ (.ldr t n off)).map fun τ' => { τ' with regs := τ'.regs.insert t }
  | .ldrb t n off => (VG.Arm.Taint.stepK τ (.ldrb t n off)).map fun τ' => { τ' with regs := τ'.regs.insert t }
  | .str t n off => if pub τ t then VG.Arm.Taint.stepK τ (.str t n off) else none
  | .strb t n off => if pub τ t then VG.Arm.Taint.stepK τ (.strb t n off) else none
  | .ldrSp .. | .push _ | .pop .. => none
  | i => VG.Arm.Taint.stepK τ i

theorem MemEq.read {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) {a : Addr} {n : Nat}
    (hi : InRegions rs a n) (hn : n < 2 ^ 64) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := hi
  exact Mem.read_congr fun i hi' =>
    h _ ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega_using [hn, hi'])]; exact hi')⟩

theorem MemEq.writeW {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) (a : Addr) {w : Nat}
    (v : BitVec w) : MemEq rs (m₁.writeW a v) (m₂.writeW a v) := fun x hx => by
  simp only [Mem.writeW, Mem.write]
  split
  · rfl
  · exact h x hx

/-- A register made public, whose values agree. -/
theorem agree_insert {τ : T} {s₁ s₂ : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂) {d : Reg}
    (hd : s₁.gpr d = s₂.gpr d) : VG.Arm.Taint.Agree { τ with regs := τ.regs.insert d } s₁ s₂ :=
  ⟨⟨fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact hd
      · exact ha.rf.1 r hr, ha.rf.2⟩, ha.wr, ⟨ha.wf₁.lens, ha.wf₁.bases, ha.wf₁.args, ha.wf₁.argBases⟩,
    ⟨ha.wf₂.lens, ha.wf₂.bases, ha.wf₂.args, ha.wf₂.argBases⟩, ha.ok, ha.slots, ha.sp, ha.argMem⟩

/-- The instructions that neither access memory nor change the stack. -/
theorem exec_pure {i : Instr} (hi : ∀ t n off, i ≠ .ldr t n off ∧ i ≠ .ldrb t n off ∧ i ≠ .str t n off ∧
      i ≠ .strb t n off ∧ i ≠ .ldrSp t off) (hd : ∀ t t2 n off, i ≠ .strd t t2 n off)
    {s s' : State} (h : exec i s = some s') : s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | strd t t2 n off => exact absurd rfl (hd t t2 n off)
  | ldr t n off => exact absurd rfl (hi t n off).1
  | ldrb t n off => exact absurd rfl (hi t n off).2.1
  | str t n off => exact absurd rfl (hi t n off).2.2.1
  | strb t n off => exact absurd rfl (hi t n off).2.2.2.1
  | ldrSp t off => exact absurd rfl (hi t t off).2.2.2.2
  | push => simp only [reduceExec, reduceCtorEq] at h
  | pop | alloc | free | blx => simp only [reduceExec, reduceCtorEq] at h
  | addSp d imm =>
    simp only [reduceExec] at h
    split at h <;> cases h
    exact ⟨rfl, rfl, rfl⟩
  | umaal =>
    simp only [reduceExec] at h
    split at h <;> cases h
    exact ⟨rfl, rfl, rfl⟩
  | _ =>
    simp only [reduceExec, Option.map_eq_some_iff, Option.some.injEq] at h
    first
    | (obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩)
    | (subst h; exact ⟨rfl, rfl, rfl⟩)

theorem mstep_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : MAgree τ s₁ s₂)
    (hs : mstep τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ MAgree τ' s₁' s₂' := by
  obtain ⟨hA, hrd, hwr, hm⟩ := ha
  -- Instructions the base analysis handles, which keep the memory.
  have base : ∀ {j : Instr}, (∀ t n off, j ≠ .ldr t n off ∧ j ≠ .ldrb t n off ∧ j ≠ .str t n off ∧
      j ≠ .strb t n off ∧ j ≠ .ldrSp t off) → (∀ t t2 n off, j ≠ .strd t t2 n off) →
      VG.Arm.Taint.stepK τ j = some τ' → exec j s₁ = some s₁' →
      exec j s₂ = some s₂' → addrs j s₁ = addrs j s₂ ∧ MAgree τ' s₁' s₂' := fun hj hjd hs' e₁ e₂ => by
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound ⟨hA.rf, hA.wr, hA.wf₁, hA.wf₂, hA.ok, hA.slots, hA.sp, hA.argMem⟩
      (VG.Arm.Taint.stepK_eq ▸ hs') e₁ e₂
    obtain ⟨m₁, r₁, w₁⟩ := exec_pure hj hjd e₁
    obtain ⟨m₂, r₂, w₂⟩ := exec_pure hj hjd e₂
    exact ⟨hadd, ht, by rw [r₁, r₂, hrd], by rw [w₁, w₂, hwr], by rw [m₁, m₂, r₁, w₁]; exact hm⟩
  cases i with
  | ldr t n off =>
    simp only [mstep, Option.map_eq_some_iff] at hs
    obtain ⟨τ₀, h₀, rfl⟩ := hs
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ h₀) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load32] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [rename_i hi; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    refine ⟨by simp only [addrs, hadd], agree_insert ht ?_, hrd, hwr, hm⟩
    simp only [State.setReg, ite_true, Mem.readW, ← hadd, hm.read hi (by decide)]
  | ldrb t n off =>
    simp only [mstep, Option.map_eq_some_iff] at hs
    obtain ⟨τ₀, h₀, rfl⟩ := hs
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ h₀) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load8] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [rename_i hi; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    refine ⟨by simp only [addrs, hadd], agree_insert ht ?_, hrd, hwr, hm⟩
    simp only [State.setReg, ite_true, ← hadd, hm _ hi]
  | str t n off =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hp; cases hs]
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ hs) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [reduceExec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    refine ⟨by simp only [addrs, hadd], ht, hrd, hwr, ?_⟩
    rw [hadd, hA.reg hp]
    exact hm.writeW _ _
  | strb t n off =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hp; cases hs]
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ hs) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [reduceExec, State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    refine ⟨by simp only [addrs, hadd], ht, hrd, hwr, ?_⟩
    rw [hadd, hA.reg hp]
    exact hm.writeW _ _
  | ldrSp => simp only [mstep, reduceCtorEq] at hs
  | strd => simp only [mstep, VG.Arm.Taint.stepK, reduceCtorEq] at hs
  | push => simp only [mstep, reduceCtorEq] at hs
  | pop => simp only [mstep, reduceCtorEq] at hs
  | mov | mvn => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | dp => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | adds => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | adc => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | subs => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | cmp => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | movw => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | movt => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | adrSym => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | rev => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | mul => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | mla => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | addSp => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | umaal => exact base (fun _ _ _ => by simp) (fun _ _ _ _ => by simp) hs e₁ e₂
  | alloc | free | blx => simp only [reduceExec, reduceCtorEq] at e₁

/-- Taint tracking over memory both runs agree on, for ARMv7. -/
def memTaint : VG.Taint isa where
  T := T
  Agree := MAgree
  step := mstep
  step_sound := mstep_sound
  condPub τ _ := τ.flags
  cond_sound ha hc := VG.Arm.Taint.cond_sound ha.1 hc
  meet := VG.Arm.Taint.meet
  meet_left h := ⟨VG.Arm.Taint.meet_left h.1, h.2⟩
  meet_right h := ⟨VG.Arm.Taint.meet_right h.1, h.2⟩
  le := VG.Arm.Taint.leK
  le_sound hle h := ⟨VG.Arm.Taint.le_sound (VG.Arm.Taint.leK_eq ▸ hle) h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

/-! ## Narrowing the permissions -/

/-- Two runs of `c` leak the same trace if its runs from the states narrowed
to the regions `rd`, `wr` do, and exist. -/
theorem RelCT.narrow {c : Prog isa} {P : State → State → Prop} (rd wr : State → List Region)
    (hc : ∀ a b, P a b → Covers (rd a ++ wr a) (a.rd ++ a.wr) ∧ Covers (wr a) a.wr ∧
      Covers (rd b ++ wr b) (b.rd ++ b.wr) ∧ Covers (wr b) b.wr)
    (hrun : ∀ a b, P a b → (∃ t s', Exec isa c (a.withRegions (rd a) (wr a)) t s') ∧
      ∃ t s', Exec isa c (b.withRegions (rd b) (wr b)) t s')
    (hct : RelCT isa (fun a' b' => ∃ a b, P a b ∧ a' = a.withRegions (rd a) (wr a) ∧
      b' = b.withRegions (rd b) (wr b)) c fun _ _ => True) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨c₁, w₁, c₂, w₂⟩ := hc _ _ hp
  obtain ⟨⟨u₁, n₁, f₁⟩, ⟨u₂, n₂, f₂⟩⟩ := hrun _ _ hp
  have g₁ := Exec.widen f₁ (rd := s₁.rd) (wr := s₁.wr) (by simpa using c₁) (by simpa using w₁)
  have g₂ := Exec.widen f₂ (rd := s₂.rd) (wr := s₂.wr) (by simpa using c₂) (by simpa using w₂)
  simp only [State.withRegions_withRegions, State.withRegions_self] at g₁ g₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ g₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ g₂
  exact ⟨(hct _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ f₁ f₂).1, trivial⟩

/-! ## Instructions that only access the stack -/

/-- The instructions whose addresses depend only on the stack pointer. -/
def spOnly : Instr → Bool
  | .ldr .. | .str .. | .ldrb .. | .strb .. | .strd .. | .push _ | .pop .. => false
  | _ => true

theorem addrs_spOnly {i : Instr} (hi : spOnly i = true) {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp) :
    addrs i s₁ = addrs i s₂ := by
  cases i <;> simp_all [spOnly, addrs]

theorem execBlock_spOnly {is : List Instr} (h : is.all spOnly = true) {s₁ s₂ s₁' s₂' : State}
    {t₁ t₂ : List Leak} (hsp : s₁.sp = s₂.sp) (e₁ : execBlock isa is s₁ = some (s₁', t₁))
    (e₂ : execBlock isa is s₂ = some (s₂', t₂)) : t₁ = t₂ := by
  induction is generalizing s₁ s₂ t₁ t₂ with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> [cases e₁; skip]
    split at e₂ <;> [cases e₂; skip]
    rename_i a₁ x₁ _ a₂ x₂
    simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at e₁ e₂
    obtain ⟨_, u₁, f₁, rfl, rfl⟩ := e₁
    obtain ⟨_, u₂, f₂, rfl, rfl⟩ := e₂
    have ha : addrs i s₁ = addrs i s₂ := addrs_spOnly h.1 hsp
    rw [ha, ih h.2 (by rw [exec_sp x₁, exec_sp x₂, hsp]) f₁ f₂]

/-- A block of instructions that only access the stack leaks the same trace
from states with the same stack pointer. -/
theorem RelCT.spBlock {is : List Instr} (h : is.all spOnly = true) {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | block e₁ =>
    cases e₂ with
    | block e₂ => exact ⟨execBlock_spOnly h (hsp _ _ hp) e₁ e₂, trivial⟩

/-! ## Helpers -/

theorem relct_wp {c : Prog isa} {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa P c fun _ _ => True) (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa P c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.MlDsa.Arm.Pack.Hint

end

end

/-!
# ML-DSA on 32-bit ARM: what the proofs of `HintBitPack` and `HintBitUnpack` share

The comparisons of small numbers (`ltBit`), pointers that do not wrap around,
the parameters, and the frames: the words a push stores, which the body and
the pop reload.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm
open VG.Spec.MlDsa

/-! ## Numbers -/

theorem mem_hintParams {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ 55 ≤ ω ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega_using [h]

/-- The sign bit of `x - y`, for `x` and `y` less than `2³¹`: whether `x < y`. -/
theorem ltBit_val {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    (x - y) >>> 31 = if x.toNat < y.toNat then 1 else 0 := by
  split <;> bv_omega

/-- `Z` after `ltBit`: set iff `x ≥ y`. -/
theorem ltBit_z {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    ((x - y) >>> 31 - 0 == 0) = decide (y.toNat ≤ x.toNat) := by
  rw [ltBit_val hx hy]
  split
  · rw [decide_eq_false (by omega_arith)]; rfl
  · rw [decide_eq_true (by omega_arith)]; rfl

theorem sub_zero32 (x : BitVec 32) : x - 0 = x := BitVec.sub_zero x

theorem toNat_ofNat32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_succ32 (x : Nat) : BitVec.ofNat 32 x + 1 = BitVec.ofNat 32 (x + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]

theorem ptr_add (p : BitVec 32) (a b : Nat) : p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- `Z` after comparing a counter with a constant. -/
theorem cmp_const {j c : Nat} (hj : j < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 j - BitVec.ofNat 32 c == 0) = decide (j = c) := by
  rw [VG.Proof.MlKem.Arm.cmp_z _ _ hc, toNat_ofNat32 hj]

/-- The byte `strb` stores of a small number. -/
theorem setWidth8_ofNat (x : Nat) : (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

/-- A byte, as `ldrb` loads it. -/
theorem byte_toNat32 (b : Byte) : (b.setWidth 32).toNat = b.toNat := VG.Proof.MlKem.Arm.setWidth32_toNat b

/-! ## Addresses -/

theorem addr_ofNat (p : BitVec 32) {a : Nat} (h : p.toNat + a < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 a) = State.addr p + BitVec.ofNat 64 a := addr_add h

theorem addr_sub' {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  have := a.isLt
  simp only [State.addr]; bv_omega

/-! ## Frames -/

/-- Word `i` a push stored. -/
theorem storeWords_readW (m : Mem) (a : BitVec 32) (vs : List (BitVec 32)) (h : a.toNat + 4 * vs.length ≤ 2 ^ 32)
    {i : Nat} (hi : i < vs.length) :
    (storeWords m a vs).readW (State.addr (a + BitVec.ofNat 32 (4 * i))) 32 = vs[i] := by
  induction vs generalizing m a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons v vs ih =>
    simp only [List.length_cons] at h hi
    simp only [storeWords]
    cases i with
    | zero =>
      have hf := storeWords_frame (m.writeW (State.addr a) v) (a + 4) vs (by bv_omega)
      rw [show a + BitVec.ofNat 32 (4 * 0) = a by simp, hf.readW (r := ⟨State.addr a, 4⟩)
        (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          by_cases hv : vs.length = 0
          · intro x _ h2; simp only [Region.Contains, hv] at h2; omega_using [h2]
          rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, addr_ofNat a (by omega_using [h, hv])]
          exact Offset.base_disjoint _ (Nat.le_refl 4) (by have := addr_toNat' a; omega_using [h])) (by decide),
        Mem.readW_writeW_self32]
      rfl
    | succ j =>
      rw [show a + BitVec.ofNat 32 (4 * (j + 1)) = a + 4 + BitVec.ofNat 32 (4 * j) by
        rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add]; congr 2; omega_using []]
      exact ih _ _ (by bv_omega) (by omega_using [hi])

/-- The region of the frame of `rs`. -/
abbrev frameR (s : State) (rs : List Reg) : Region :=
  ⟨State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length)), 4 * rs.length⟩

/-- A push changes memory only in its frame. -/
theorem pushed_frame (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) :
    Frame [frameR s rs] s.mem (pushed rs s).mem := by
  have := storeWords_frame s.mem (s.sp - BitVec.ofNat 32 (4 * rs.length)) (rs.map s.gpr) (by
    rw [List.length_map]; have := s.sp.isLt; bv_omega)
  rwa [List.length_map] at this

/-- The word of register `rs[i]` in the frame. -/
theorem pushed_word (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {i : Nat}
    (hi : i < rs.length) :
    (pushed rs s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length) + BitVec.ofNat 32 (4 * i))) 32 =
      s.gpr rs[i] := by
  have := storeWords_readW s.mem (s.sp - BitVec.ofNat 32 (4 * rs.length)) (rs.map s.gpr) (by
    rw [List.length_map]; have := s.sp.isLt; bv_omega) (i := i) (by rw [List.length_map]; exact hi)
  rw [List.getElem_map] at this
  exact this

/-- The frame of `rs` is the bytes below `sp`. -/
theorem frameR_eq (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) :
    frameR s rs = ⟨State.addr s.sp - BitVec.ofNat 64 (4 * rs.length), 4 * rs.length⟩ := by
  rw [frameR, addr_sub' h]

theorem frameR_contains (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {i : Nat}
    (hi : i < rs.length) :
    (frameR s rs).Contains (State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length) + BitVec.ofNat 32 (4 * i))) 4 := by
  have := s.sp.isLt
  have e : (s.sp - BitVec.ofNat 32 (4 * rs.length)).toNat = s.sp.toNat - 4 * rs.length := by bv_omega
  rw [addr_ofNat _ (by omega_using [h, hi, e])]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [h, hi])

/-- Word `i` of the frame, after the body changed memory only outside it. -/
theorem frame_saved (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {m : Mem} {R : List Region}
    (hf : Frame R (pushed rs s).mem m) (hd : ∀ r ∈ R, (frameR s rs).Disjoint r) {i : Nat} (hi : i < rs.length) :
    m.readW (State.addr ((pushed rs s).sp + BitVec.ofNat 32 (4 * i))) 32 = s.gpr rs[i] := by
  rw [pushed_sp, hf.readW (frameR_contains rs h hi) hd (by decide), pushed_word rs h hi]

/-- The load of the stack argument into `r12`. -/
theorem entry_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldrSp .r12 0]) s fun s' =>
      s' = s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 0)) 32) := by
  run_block [ia]

/-- No instruction of `c` writes `r`, by evaluating `Code.allInstrs`. -/
theorem noWrite {c : Prog isa} {r : Reg} (h : c.allInstrs (fun i => !clobbers i r) = true) :
    ∀ i ∈ instrs c, clobbers i r = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa using h i hi

end VG.Proof.MlDsa.Arm.Pack.Hint
