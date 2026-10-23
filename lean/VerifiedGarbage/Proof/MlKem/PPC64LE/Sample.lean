module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Sample
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Covers

/-!
# ML-KEM on PPC64LE: `vg_mlkem_sample_ntt`, correctness

As on 32-bit ARM (`Proof/MlKem/Arm/Sample.lean`). The phases of the
function, each proved from the state the previous one leaves: the registers
saved and the Keccak state zeroed (`setup_ok`), the seed absorbed, the
padding, 840 bytes squeezed (`absorb_phase`, `pad_phase`, `squeeze_phase`,
calls of the sponge functions verified against `Proof.Sha3.absorbPPC64LE`, …,
by `call_ok`), then the loop of Algorithm 7 over the 280 chunks (`body_ok`,
with the invariant `Inv`: the coefficients sampled from the first `t`
chunks, `sampleAfter`), and the result. What every phase keeps is `SEnv`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Sample

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (Repr stateAt squeezeFrom)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- Runs a short block: the doubleword loads and stores at an offset, and the
register writes, read through. -/
macro "prun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec_mflr, exec_mtlr, exec_ld, exec_std,
    exec_addi', exec_li, exec_lsl, exec_lsr_d, exec_add, exec_sub, exec_subi', exec_logic,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, RegUpd.lr_write, ne_eq, reduceCtorEq, not_false_eq_true, BitVec.add_zero,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reducePow, and_self, Option.some.injEq,
    exists_eq_left', $ls,*]))

section
variable (s₀ : State)

abbrev SEED : Addr := s₀.gpr .r3
abbrev A : Addr := s₀.gpr .r4
abbrev S : Addr := s₀.gpr .r5
/-- The seed. -/
abbrev B : List Byte := Spec.Sha3.bytesAt s₀.mem (SEED s₀) 34
/-- The stack the sponge functions use. -/
abbrev STK : Region := below s₀.sp 48

end

structure Pre (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  rd : s₀.rd = [⟨SEED s₀, 34⟩]
  wr : s₀.wr = [polyRegion (A s₀), ⟨S s₀, 2048⟩]
  seed_a : (⟨SEED s₀, 34⟩ : Region).Disjoint (polyRegion (A s₀))
  seed_s : (⟨SEED s₀, 34⟩ : Region).Disjoint ⟨S s₀, 2048⟩
  a_s : (polyRegion (A s₀)).Disjoint ⟨S s₀, 2048⟩
  b_seed : (STK s₀).Disjoint ⟨SEED s₀, 34⟩
  b_a : (STK s₀).Disjoint (polyRegion (A s₀))
  b_s : (STK s₀).Disjoint ⟨S s₀, 2048⟩
  fseed : (SEED s₀).toNat + 34 ≤ 2 ^ 64
  fa : (A s₀).toNat + 1024 ≤ 2 ^ 64
  fs : (S s₀).toNat + 2048 ≤ 2 ^ 64

/-- What every phase after the setup keeps: the pointers in `r29`–`r31`,
our caller's registers and our return address in `scratch`, and the seed. -/
structure SEnv (s₀ : State) (s : State) : Prop where
  r29 : s.gpr .r29 = SEED s₀
  r30 : s.gpr .r30 = A s₀
  r31 : s.gpr .r31 = S s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s29 : s.mem.readW (S s₀ + BitVec.ofNat 64 1680) 64 = s₀.gpr .r29
  s30 : s.mem.readW (S s₀ + BitVec.ofNat 64 1688) 64 = s₀.gpr .r30
  s31 : s.mem.readW (S s₀ + BitVec.ofNat 64 1696) 64 = s₀.gpr .r31
  slr : s.mem.readW (S s₀ + BitVec.ofNat 64 1704) 64 = s₀.lr
  seed : Spec.Sha3.bytesAt s.mem (SEED s₀) 34 = B s₀

/-! ## Addresses in `scratch` -/

/-- A part of `scratch`. -/
theorem s_sub {s₀ : State} {o n : Nat} (h : o + n ≤ 2048) :
    Region.Sub ⟨S s₀ + BitVec.ofNat 64 o, n⟩ ⟨S s₀, 2048⟩ :=
  Offset.sub_base _ h

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- Two parts of `scratch`, apart. -/
theorem s_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁ : o₁ + n₁ ≤ 2048) (h₂ : o₂ + n₂ ≤ 2048) :
    Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨S s₀ + BitVec.ofNat 64 o₂, n₂⟩ := by
  have := hp.fs
  exact Offset.disjoint _ h (by omega) (by omega)

/-- A part of `scratch` is writable. -/
theorem s_in {o n : Nat} (h : o + n ≤ 2048) : InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) n :=
  ⟨⟨S s₀, 2048⟩, by rw [hp.wr]; simp, Offset.contains_base _ h (by have := hp.fs; omega)⟩

end

/-- A part of `scratch` below the saved registers, or the stack below the
stack pointer. -/
def Low (s₀ : State) (r : Region) : Prop :=
  (∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩) ∨ r = STK s₀

/-- `SEnv` through writes below the saved registers, and below the stack pointer. -/
theorem SEnv.frame {s₀ s s' : State} (hp : Pre s₀) (h : SEnv s₀ s) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, Low s₀ r)
    (g29 : s'.gpr .r29 = s.gpr .r29) (g30 : s'.gpr .r30 = s.gpr .r30) (g31 : s'.gpr .r31 = s.gpr .r31)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : SEnv s₀ s' := by
  have fs := hp.fs
  have hsv : ∀ r ∈ rs, (⟨S s₀ + BitVec.ofNat 64 1680, 32⟩ : Region).Disjoint r := by
    intro r hr
    rcases hrs r hr with ⟨o, n, ho, rfl⟩ | rfl
    · exact s_disj hp (by omega) (by omega) (by omega)
    · exact (hp.b_s.sub_right (s_sub (by decide))).symm
  have hsd : ∀ r ∈ rs, (⟨SEED s₀, 34⟩ : Region).Disjoint r := by
    intro r hr
    rcases hrs r hr with ⟨o, n, ho, rfl⟩ | rfl
    · exact hp.seed_s.sub_right (s_sub (by omega))
    · exact hp.b_seed.symm
  have k : ∀ d, 1680 ≤ d → d + 8 ≤ 1712 →
      s'.mem.readW (S s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (S s₀ + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Offset.contains _ h₁ (by omega) (by omega)) hsv (by decide)
  refine ⟨g29.trans h.r29, g30.trans h.r30, g31.trans h.r31, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    (k 1680 (by omega) (by omega)).trans h.s29, (k 1688 (by omega) (by omega)).trans h.s30,
    (k 1696 (by omega) (by omega)).trans h.s31, (k 1704 (by omega) (by omega)).trans h.slr, ?_⟩
  rw [bytesAt_frame hf hsd (by decide)]; exact h.seed

/-! ## The setup -/

/-- After zeroing the first `k` lanes of the state at `b`. -/
structure ZInv (b : Reg) (s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  lr : s.lr = s₁.lr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp
  frame : Frame [⟨s₁.gpr b, 200⟩] s₁.mem s.mem
  zero : ∀ j < k, s.mem.readW (s₁.gpr b + BitVec.ofNat 64 (8 * j)) 64 = 0

theorem zeroLanes_ok (b : Reg) (hb : b ≠ .r0) {s₁ : State} (h0 : s₁.gpr .r0 = 0)
    (hwr : ∀ k < 25, InRegions s₁.wr (s₁.gpr b + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block ((List.range 25).flatMap fun k => [.store .d .r0 b (8 * k)])) s₁ (ZInv b s₁ 25) := by
  refine wp_range_flatMap (M := isa) (ZInv b s₁) (fun k s hk h => ?_) 25 (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  apply WP.of_runBlock
  rw [runBlock_cons, exec_store_d hb ⟨by omega, by omega⟩ (by rw [h.gpr, h.wr]; exact hwr k hk), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, h.gpr, h.lr, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
  · rw [h.gpr]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ _ = _
    rw [h.gpr, h0]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.zero j (by omega)

theorem stateAt_zero {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Spec.Sha3.zero, Vector.getElem_replicate]
  exact h i hi

/-- The arguments moved and the registers saved. -/
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block [.mflr .r0, .store .d .r29 .r5 1680, .store .d .r30 .r5 1688, .store .d .r31 .r5 1696,
      .store .d .r0 .r5 1704, mov .r29 .r3, mov .r30 .r4, mov .r31 .r5, .li .r0 0]) s₀ fun s =>
        s.gpr .r29 = SEED s₀ ∧ s.gpr .r30 = A s₀ ∧ s.gpr .r31 = S s₀ ∧ s.gpr .r0 = 0 ∧
        s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
        s.mem = (((s₀.mem.writeW (S s₀ + BitVec.ofNat 64 1680) (s₀.gpr .r29)).writeW
          (S s₀ + BitVec.ofNat 64 1688) (s₀.gpr .r30)).writeW (S s₀ + BitVec.ofNat 64 1696) (s₀.gpr .r31)).writeW
          (S s₀ + BitVec.ofNat 64 1704) s₀.lr := by
  have w1680 := s_in hp (o := 1680) (n := 8) (by decide)
  have w1688 := s_in hp (o := 1688) (n := 8) (by decide)
  have w1696 := s_in hp (o := 1696) (n := 8) (by decide)
  have w1704 := s_in hp (o := 1704) (n := 8) (by decide)
  prun [w1680, w1688, w1696, w1704]
  exact ⟨trivial, trivial, trivial, rfl, trivial⟩

/-- Reading a doubleword past a write of another. -/
theorem readW_writeW_off (B : Addr) (m : Mem) {x y : Nat} (v : BitVec 64) (h : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x + 8 ≤ 2 ^ 64) (hy : y + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 64 = m.readW (B + BitVec.ofNat 64 x) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hx hy) (by decide)

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block sampleSetup) s₀ fun s => SEnv s₀ s ∧ stateAt s.mem (S s₀) = Spec.Sha3.zero := by
  have fs := hp.fs
  rw [show sampleSetup = ([.mflr .r0, .store .d .r29 .r5 1680, .store .d .r30 .r5 1688, .store .d .r31 .r5 1696,
      .store .d .r0 .r5 1704, mov .r29 .r3, mov .r30 .r4, mov .r31 .r5, .li .r0 0] : List Instr) ++
      (List.range 25).flatMap fun k => [.store .d .r0 .r31 (8 * k)] from rfl, WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨g29, g30, g31, g0, rd, wr, sp, lr, m⟩ => ?_
  refine WP.mono (zeroLanes_ok .r31 (by decide) g0 fun k hk => by
    rw [g31, wr]; exact s_in hp (by omega)) fun s h => ?_
  have hf := h.frame
  have hz := h.zero
  rw [g31] at hf hz
  have d200 : ∀ r ∈ [(⟨S s₀, 200⟩ : Region)], (⟨S s₀ + BitVec.ofNat 64 1680, 32⟩ : Region).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr
    have := s_disj hp (o₁ := 1680) (n₁ := 32) (o₂ := 0) (n₂ := 200) (by omega) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have k : ∀ d, 1680 ≤ d → d + 8 ≤ 1712 →
      s.mem.readW (S s₀ + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S s₀ + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Offset.contains _ h₁ (by omega) (by omega)) d200 (by decide)
  have fr : Frame [⟨S s₀, 2048⟩] s₀.mem s.mem := by
    refine Frame.trans (m₂ := s₁.mem) ?_ (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩)
    rw [m]
    refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_ <;>
      exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨by rw [h.gpr]; exact g29, by rw [h.gpr]; exact g30, by rw [h.gpr]; exact g31, h.rd.trans rd,
    h.wr.trans wr, h.sp.trans sp, ?_, ?_, ?_, ?_, ?_⟩, stateAt_zero hz⟩
  all_goals first
    | (rw [k _ (by omega) (by omega), m]
       simp (disch := decide) only [readW_writeW_off, Mem.readW_writeW_self64])
    | exact bytesAt_frame fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.seed_s)
        (by decide)

/-! ## Calls -/

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- A call of verified code using at most 48 bytes of stack, reading at
most the seed and writing parts of `scratch` below the saved registers:
afterwards `SEnv` holds again, memory changed only within what it writes and
the stack below the stack pointer, and the callee's postcondition holds. -/
theorem call_ok {s₀ s : State} (hp : Pre s₀) (h : SEnv s₀ s) {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : sdepth c ≤ 48) {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hrd : ∀ r ∈ rd, r = ⟨SEED s₀, 34⟩)
    (hwr : ∀ r ∈ wr, ∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩) {Q : State → Prop}
    (hQ : ∀ s', SEnv s₀ s' → Frame (wr ++ [STK s₀]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) s Q := by
  have hsc : ∀ r ∈ wr, ∃ off, r.base = S s₀ + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048 := fun r hr => by
    obtain ⟨o, n, ho, rfl⟩ := hwr r hr; exact ⟨o, rfl, by simp only; omega⟩
  have hw : Covers wr s.wr := Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := hsc r hr
    exact ⟨⟨S s₀, 2048⟩, by rw [h.wr, hp.wr]; simp, off, hb, hl⟩
  have hc : Covers (rd ++ wr) (s.rd ++ s.wr) := Covers.of_sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · rw [hrd r hr]
      exact ⟨⟨SEED s₀, 34⟩, by rw [h.rd, hp.rd]; simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · obtain ⟨off, hb, hl⟩ := hsc r hr
      exact ⟨⟨S s₀, 2048⟩, by rw [h.wr, hp.wr]; simp, off, hb, hl⟩
  refine WP.callAny hv hpre hc hw (fun s' hrd' hwr' hsp' hf hcs hpost => ?_) (by omega)
  have hsp48 := hp.sp48
  have hf' : Frame (wr ++ [STK s₀]) s.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [h.sp]
      exact below_sub hd (by omega)
  refine hQ s' (h.frame hp hf' (fun r hr => ?_) (hcs _ (by decide)) (hcs _ (by decide)) (hcs _ (by decide))
    hrd' hwr' hsp') hf' hcs hpost
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl (hwr r hr)
  · rw [List.mem_singleton] at hr; exact .inr hr

theorem absorb_sdepth : sdepth Impl.Sha3.PPC64LE.Stream.absorb ≤ 48 := by lit_decide
theorem pad_sdepth : sdepth Impl.Sha3.PPC64LE.Stream.pad ≤ 48 := by lit_decide
theorem squeeze_sdepth : sdepth Impl.Sha3.PPC64LE.Stream.squeeze ≤ 48 := by lit_decide

/-- `SEnv` through a block that writes only registers other than `r29`–`r31`. -/
theorem SEnv.regs {s₀ s t : State} (hp : Pre s₀) (h : SEnv s₀ s) (hm : t.mem = s.mem)
    (g29 : t.gpr .r29 = s.gpr .r29) (g30 : t.gpr .r30 = s.gpr .r30) (g31 : t.gpr .r31 = s.gpr .r31)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : SEnv s₀ t :=
  h.frame hp (rs := []) (by rw [hm]; exact Frame.refl _ _) (fun _ hr => absurd hr List.not_mem_nil) g29 g30 g31
    rd wr sp

/-- The state and the sponge's working space, at the start of `scratch`. -/
theorem wrS {s₀ : State} {r : Region} (hr : r ∈ [(⟨S s₀, 200⟩ : Region), ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) :
    ∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, 200, by decide, by rw [BitVec.add_zero]⟩
  · exact ⟨200, 640, by decide, rfl⟩

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_st : (STK s₀).Disjoint ⟨S s₀, 200⟩ := hp.b_s.sub_right (Region.sub_prefix (by decide))

theorem stk_off {o n : Nat} (h : o + n ≤ 2048) : (STK s₀).Disjoint ⟨S s₀ + BitVec.ofNat 64 o, n⟩ :=
  hp.b_s.sub_right (s_sub h)

theorem st_off {o n : Nat} (h₁ : 200 ≤ o) (h : o + n ≤ 2048) :
    Region.Disjoint ⟨S s₀, 200⟩ ⟨S s₀ + BitVec.ofNat 64 o, n⟩ := by
  have := s_disj hp (o₁ := 0) (n₁ := 200) (o₂ := o) (n₂ := n) (by omega) (by omega) h
  rwa [BitVec.add_zero] at this

theorem absorbArgs_ok {s : State} (h : SEnv s₀ s) :
    WP isa (.block absorbSeedArgs) s fun t => SEnv s₀ t ∧ t.mem = s.mem ∧ t.gpr .r3 = S s₀ ∧
      t.gpr .r4 = BitVec.ofNat 64 168 ∧ t.gpr .r5 = BitVec.ofNat 64 0 ∧ t.gpr .r6 = SEED s₀ ∧
      t.gpr .r7 = BitVec.ofNat 64 34 ∧ t.gpr .r8 = S s₀ + BitVec.ofNat 64 200 := by
  prun [absorbSeedArgs, h.r29, h.r31]
  exact ⟨h.regs hp rfl rfl rfl rfl rfl rfl rfl, trivial⟩

theorem absorb_phase {s : State} (h : SEnv s₀ s) (hz : stateAt s.mem (S s₀) = Spec.Sha3.zero) :
    WP isa (.seq (.block absorbSeedArgs) (.call "vg_keccak_absorb_scratch" Impl.Sha3.PPC64LE.Stream.absorb)) s
      fun s' => SEnv s₀ s' ∧ Repr s'.mem (S s₀) 168 (B s₀) ∧ (s'.gpr .r3).toNat = 34 := by
  refine WP.seq (WP.mono (absorbArgs_ok hp h) fun t ⟨ht, hm, g3, g4, g5, g6, g7, g8⟩ => ?_)
  have hsp48 := hp.sp48
  refine call_ok hp ht (k := Proof.Sha3.absorbPPC64LE) Proof.Sha3.PPC64LE.Stream.absorb_correct absorb_sdepth
    (rd := [⟨SEED s₀, 34⟩]) (wr := [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) ?_
    (fun r hr => by rw [List.mem_singleton] at hr; exact hr) (fun r hr => wrS hr)
    fun s' hs' _ _ hpost => ⟨hs', ?_, ?_⟩
  · simp only [Proof.Sha3.absorbPPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs),
      g3, g4, g5, g6, g7, g8, ht.sp, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact ⟨trivial, trivial, st_off hp (by decide) (by decide), hp.seed_s.sub_right (Region.sub_prefix (by decide)),
      hp.seed_s.sub_right (s_sub (by decide)), hsp48, stk_st hp, hp.b_seed, stk_off hp (by decide), by decide,
      by decide⟩
  · simp only [Proof.Sha3.absorbPPC64LE, State.withRegions_mem, State.callEntry_mem,
      gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), g3, g4, g5, g6, g7, hm, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod] at hpost
    have := hpost.1 [] (VG.Proof.MlKem.repr_nil hz) (by decide)
    rwa [List.nil_append, ← hm, ht.seed] at this
  · simp only [Proof.Sha3.absorbPPC64LE, State.withRegions_gpr, gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), g4, g5, g7,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd] at hpost
    exact hpost.2

end

theorem shakeSuffix64 : (BitVec.ofNat 64 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix := by decide

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem padArgs_ok {s : State} (h : SEnv s₀ s) (h3 : (s.gpr .r3).toNat = 34) :
    WP isa (.block padArgs) s fun t => SEnv s₀ t ∧ t.mem = s.mem ∧ t.gpr .r3 = S s₀ ∧
      t.gpr .r4 = BitVec.ofNat 64 168 ∧ t.gpr .r5 = BitVec.ofNat 64 34 ∧ t.gpr .r6 = BitVec.ofNat 64 0x1f ∧
      t.gpr .r7 = S s₀ + BitVec.ofNat 64 200 := by
  have e3 : s.gpr .r3 = BitVec.ofNat 64 34 := BitVec.eq_of_toNat_eq (by rw [h3]; rfl)
  prun [padArgs, e3, h.r31]
  exact ⟨h.regs hp rfl rfl rfl rfl rfl rfl rfl, trivial⟩

theorem pad_phase {s : State} (h : SEnv s₀ s) (hr : Repr s.mem (S s₀) 168 (B s₀)) (h3 : (s.gpr .r3).toNat = 34) :
    WP isa (.seq (.block padArgs) (.call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad)) s
      fun s' => SEnv s₀ s' ∧ stateAt s'.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀) := by
  refine WP.seq (WP.mono (padArgs_ok hp h h3) fun t ⟨ht, hm, g3, g4, g5, g6, g7⟩ => ?_)
  have hsp48 := hp.sp48
  refine call_ok hp ht (k := Proof.Sha3.padPPC64LE) Proof.Sha3.PPC64LE.Stream.pad_correct pad_sdepth
    (rd := []) (wr := [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) ?_
    (fun r hr => absurd hr List.not_mem_nil) (fun r hr => wrS hr)
    fun s' hs' _ _ hpost => ⟨hs', ?_⟩
  · simp only [Proof.Sha3.padPPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs),
      g3, g4, g5, g7, ht.sp, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact ⟨trivial, trivial, st_off hp (by decide) (by decide), hsp48, stk_st hp, stk_off hp (by decide),
      by decide, by decide⟩
  · simp only [Proof.Sha3.padPPC64LE, State.withRegions_mem, State.callEntry_mem,
      gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
      g3, g4, g5, g6, hm, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, shakeSuffix64] at hpost
    exact hpost (B s₀) hr (by simp [B, VG.Proof.MlKem.bytesAt_length])

theorem squeezeArgs_ok {s : State} (h : SEnv s₀ s) :
    WP isa (.block squeezeArgs) s fun t => SEnv s₀ t ∧ t.mem = s.mem ∧ t.gpr .r3 = S s₀ ∧
      t.gpr .r4 = BitVec.ofNat 64 168 ∧ t.gpr .r5 = BitVec.ofNat 64 0 ∧
      t.gpr .r6 = S s₀ + BitVec.ofNat 64 840 ∧ t.gpr .r7 = BitVec.ofNat 64 840 ∧
      t.gpr .r8 = S s₀ + BitVec.ofNat 64 200 := by
  prun [squeezeArgs, h.r31]
  exact ⟨h.regs hp rfl rfl rfl rfl rfl rfl rfl, trivial⟩

theorem squeeze_phase {s : State} (h : SEnv s₀ s)
    (hst : stateAt s.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀)) :
    WP isa (.seq (.block squeezeArgs) (.call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze)) s
      fun s' => SEnv s₀ s' ∧ Spec.Sha3.bytesAt s'.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840 := by
  refine WP.seq (WP.mono (squeezeArgs_ok hp h) fun t ⟨ht, hm, g3, g4, g5, g6, g7, g8⟩ => ?_)
  have hsp48 := hp.sp48
  refine call_ok hp ht (k := Proof.Sha3.squeezePPC64LE) Proof.Sha3.PPC64LE.Stream.squeeze_correct squeeze_sdepth
    (rd := []) (wr := [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 840, 840⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) ?_
    (fun r hr => absurd hr List.not_mem_nil) (fun r hr => ?_)
    fun s' hs' _ _ hpost => ⟨hs', ?_⟩
  · simp only [Proof.Sha3.squeezePPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs),
      g3, g4, g5, g6, g7, g8, ht.sp, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact ⟨trivial, trivial, st_off hp (by decide) (by decide), st_off hp (by decide) (by decide),
      s_disj hp (by decide) (by decide) (by decide), hsp48, stk_st hp, stk_off hp (by decide),
      stk_off hp (by decide), by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, 200, by decide, by rw [BitVec.add_zero]⟩
    · exact ⟨840, 840, by decide, rfl⟩
    · exact ⟨200, 640, by decide, rfl⟩
  · simp only [Proof.Sha3.squeezePPC64LE, State.withRegions_mem, State.callEntry_mem,
      gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), g3, g4, g5, g6, g7, hm, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at hpost
    rw [hpost.1, hst, VG.Proof.MlKem.xof_eq]

end

end VG.Proof.MlKem.PPC64LE.Sample
