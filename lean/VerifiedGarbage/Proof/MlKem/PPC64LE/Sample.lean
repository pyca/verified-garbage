module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Sample
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
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

/-- A register other than the callee-saved ones keeps them. -/
theorem gpr_write_pres {s : State} {r d : Reg} {v : BitVec 64} (hr : r ∈ preserved) (hd : d ∉ preserved) :
    (s.write d v).gpr r = s.gpr r :=
  RegUpd.gpr_write_of_ne _ _ fun e => hd (e ▸ hr)

/-- The callee-saved registers through the writes of a block that writes
none of them. -/
macro "pres_tac" : tactic => `(tactic| (
  intro r hr
  simp (disch := decide) only [gpr_write_pres hr]))

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
  cs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
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
    (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : SEnv s₀ s' := by
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
  refine ⟨(gp _ (by decide)).trans h.r29, (gp _ (by decide)).trans h.r30, (gp _ (by decide)).trans h.r31,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr a b c => (gp r hr).trans (h.cs r hr a b c),
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
        (∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r) ∧
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
  refine ⟨fun r hr a b c => ?_, by repeat' constructor⟩
  have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
  simp only [RegUpd.gpr_write, a, b, c, h0, ite_false]

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
  refine WP.mono (save_ok hp) fun s₁ ⟨gcs, g29, g30, g31, g0, rd, wr, sp, lr, m⟩ => ?_
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
    h.wr.trans wr, h.sp.trans sp, fun r hr a b c => by rw [h.gpr]; exact gcs r hr a b c, ?_, ?_, ?_, ?_, ?_⟩,
    stateAt_zero hz⟩
  all_goals first
    | (rw [k _ (by omega) (by omega), m]
       simp (disch := decide) only [readW_writeW_off, Mem.readW_writeW_self64])
    | exact bytesAt_frame fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.seed_s)
        (by decide)

/-! ## Calls -/

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- What a call reads and writes is ours: at most the seed, and parts of `scratch`. -/
theorem call_covers {s₀ s : State} (hp : Pre s₀) (h : SEnv s₀ s) {rd wr : List Region}
    (hrd : ∀ r ∈ rd, r = ⟨SEED s₀, 34⟩)
    (hwr : ∀ r ∈ wr, ∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩) :
    Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr := by
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
  exact ⟨hc, hw⟩

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
  obtain ⟨hc, hw⟩ := call_covers hp h hrd hwr
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
  refine hQ s' (h.frame hp hf' (fun r hr => ?_) hcs hrd' hwr' hsp') hf' hcs hpost
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl (hwr r hr)
  · rw [List.mem_singleton] at hr; exact .inr hr

theorem absorb_sdepth : sdepth Impl.Sha3.PPC64LE.Stream.absorb ≤ 48 := by lit_decide
theorem pad_sdepth : sdepth Impl.Sha3.PPC64LE.Stream.pad ≤ 48 := by lit_decide
theorem squeeze_sdepth : sdepth Impl.Sha3.PPC64LE.Stream.squeeze ≤ 48 := by lit_decide

/-- `SEnv` through a block that writes only registers other than `r29`–`r31`. -/
theorem SEnv.regs {s₀ s t : State} (hp : Pre s₀) (h : SEnv s₀ s) (hm : t.mem = s.mem)
    (gp : ∀ r ∈ preserved, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) :
    SEnv s₀ t :=
  h.frame hp (rs := []) (by rw [hm]; exact Frame.refl _ _) (fun _ hr => absurd hr List.not_mem_nil) gp rd wr sp

/-- The state and the sponge's working space, at the start of `scratch`. -/
theorem wrS {s₀ : State} {r : Region} (hr : r ∈ [(⟨S s₀, 200⟩ : Region), ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) :
    ∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, 200, by decide, by rw [BitVec.add_zero]⟩
  · exact ⟨200, 640, by decide, rfl⟩

/-- The state, the output and the sponge's working space, in `scratch`. -/
theorem wrSq {s₀ : State} {r : Region} (hr : r ∈ [(⟨S s₀, 200⟩ : Region), ⟨S s₀ + BitVec.ofNat 64 840, 840⟩,
    ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) :
    ∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨0, 200, by decide, by rw [BitVec.add_zero]⟩
  · exact ⟨840, 840, by decide, rfl⟩
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
  exact ⟨h.regs hp rfl (by pres_tac) rfl rfl rfl, trivial⟩

theorem absorb_pre {t : State} (ht : SEnv s₀ t) (g3 : t.gpr .r3 = S s₀) (g4 : t.gpr .r4 = BitVec.ofNat 64 168) (g5 : t.gpr .r5 = BitVec.ofNat 64 0)
    (g6 : t.gpr .r6 = SEED s₀) (g7 : t.gpr .r7 = BitVec.ofNat 64 34) (g8 : t.gpr .r8 = S s₀ + BitVec.ofNat 64 200) :
    Proof.Sha3.absorbPPC64LE.pre (t.callEntry.withRegions [⟨SEED s₀, 34⟩] [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) := by
  have hsp48 := hp.sp48
  simp only [Proof.Sha3.absorbPPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs),
    g3, g4, g5, g6, g7, g8, ht.sp, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, st_off hp (by decide) (by decide), hp.seed_s.sub_right (Region.sub_prefix (by decide)),
    hp.seed_s.sub_right (s_sub (by decide)), hsp48, stk_st hp, hp.b_seed, stk_off hp (by decide), by decide,
    by decide⟩

theorem absorb_phase {s : State} (h : SEnv s₀ s) (hz : stateAt s.mem (S s₀) = Spec.Sha3.zero) :
    WP isa (.seq (.block absorbSeedArgs) (.call "vg_keccak_absorb_scratch" Impl.Sha3.PPC64LE.Stream.absorb)) s
      fun s' => SEnv s₀ s' ∧ Repr s'.mem (S s₀) 168 (B s₀) ∧ (s'.gpr .r3).toNat = 34 := by
  refine WP.seq (WP.mono (absorbArgs_ok hp h) fun t ⟨ht, hm, g3, g4, g5, g6, g7, g8⟩ => ?_)
  have hsp48 := hp.sp48
  refine call_ok hp ht (k := Proof.Sha3.absorbPPC64LE) Proof.Sha3.PPC64LE.Stream.absorb_correct absorb_sdepth
    (rd := [⟨SEED s₀, 34⟩]) (wr := [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) ?_
    (fun r hr => by rw [List.mem_singleton] at hr; exact hr) (fun r hr => wrS hr)
    fun s' hs' _ _ hpost => ⟨hs', ?_, ?_⟩
  · exact absorb_pre hp ht g3 g4 g5 g6 g7 g8
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
  exact ⟨h.regs hp rfl (by pres_tac) rfl rfl rfl, trivial⟩

theorem pad_pre {t : State} (ht : SEnv s₀ t) (g3 : t.gpr .r3 = S s₀) (g4 : t.gpr .r4 = BitVec.ofNat 64 168) (g5 : t.gpr .r5 = BitVec.ofNat 64 34)
    (g7 : t.gpr .r7 = S s₀ + BitVec.ofNat 64 200) :
    Proof.Sha3.padPPC64LE.pre (t.callEntry.withRegions [] [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) := by
  have hsp48 := hp.sp48
  simp only [Proof.Sha3.padPPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    g3, g4, g5, g7, ht.sp, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, st_off hp (by decide) (by decide), hsp48, stk_st hp, stk_off hp (by decide),
    by decide, by decide⟩

theorem pad_phase {s : State} (h : SEnv s₀ s) (hr : Repr s.mem (S s₀) 168 (B s₀)) (h3 : (s.gpr .r3).toNat = 34) :
    WP isa (.seq (.block padArgs) (.call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad)) s
      fun s' => SEnv s₀ s' ∧ stateAt s'.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀) := by
  refine WP.seq (WP.mono (padArgs_ok hp h h3) fun t ⟨ht, hm, g3, g4, g5, g6, g7⟩ => ?_)
  have hsp48 := hp.sp48
  refine call_ok hp ht (k := Proof.Sha3.padPPC64LE) Proof.Sha3.PPC64LE.Stream.pad_correct pad_sdepth
    (rd := []) (wr := [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) ?_
    (fun r hr => absurd hr List.not_mem_nil) (fun r hr => wrS hr)
    fun s' hs' _ _ hpost => ⟨hs', ?_⟩
  · exact pad_pre hp ht g3 g4 g5 g7
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
  exact ⟨h.regs hp rfl (by pres_tac) rfl rfl rfl, trivial⟩

theorem squeeze_pre {t : State} (ht : SEnv s₀ t) (g3 : t.gpr .r3 = S s₀) (g4 : t.gpr .r4 = BitVec.ofNat 64 168) (g5 : t.gpr .r5 = BitVec.ofNat 64 0)
    (g6 : t.gpr .r6 = S s₀ + BitVec.ofNat 64 840) (g7 : t.gpr .r7 = BitVec.ofNat 64 840)
    (g8 : t.gpr .r8 = S s₀ + BitVec.ofNat 64 200) :
    Proof.Sha3.squeezePPC64LE.pre (t.callEntry.withRegions [] [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 840, 840⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) := by
  have hsp48 := hp.sp48
  simp only [Proof.Sha3.squeezePPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs),
    g3, g4, g5, g6, g7, g8, ht.sp, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact ⟨trivial, trivial, st_off hp (by decide) (by decide), st_off hp (by decide) (by decide),
    s_disj hp (by decide) (by decide) (by decide), hsp48, stk_st hp, stk_off hp (by decide),
    stk_off hp (by decide), by decide, by decide⟩

theorem squeeze_phase {s : State} (h : SEnv s₀ s)
    (hst : stateAt s.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀)) :
    WP isa (.seq (.block squeezeArgs) (.call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze)) s
      fun s' => SEnv s₀ s' ∧ Spec.Sha3.bytesAt s'.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840 := by
  refine WP.seq (WP.mono (squeezeArgs_ok hp h) fun t ⟨ht, hm, g3, g4, g5, g6, g7, g8⟩ => ?_)
  have hsp48 := hp.sp48
  refine call_ok hp ht (k := Proof.Sha3.squeezePPC64LE) Proof.Sha3.PPC64LE.Stream.squeeze_correct squeeze_sdepth
    (rd := []) (wr := [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 840, 840⟩, ⟨S s₀ + BitVec.ofNat 64 200, 640⟩]) ?_
    (fun r hr => absurd hr List.not_mem_nil) (fun r hr => wrSq hr)
    fun s' hs' _ _ hpost => ⟨hs', ?_⟩
  · exact squeeze_pre hp ht g3 g4 g5 g6 g7 g8
  · simp only [Proof.Sha3.squeezePPC64LE, State.withRegions_mem, State.callEntry_mem,
      gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
      gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), g3, g4, g5, g6, g7, hm, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at hpost
    rw [hpost.1, hst, VG.Proof.MlKem.xof_eq]

end

/-! ## The loop of Algorithm 7 -/

/-- A candidate `d` accepted into `a` if `d < q` and there are fewer than
256 coefficients. -/
def accD (a : List Zq) (d : Nat) : List Zq := if d < q ∧ a.length < 256 then a ++ [ofNat d] else a

theorem stepCap_eq {a : List Zq} (ha : a.length ≤ 256) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ =
      accD (accD a (c₀.toNat + 256 * (c₁.toNat % 16))) (c₁.toNat / 16 + 16 * c₂.toNat) := by
  unfold sampleStepCap sampleStep
  rw [n_eq]
  by_cases h : a.length = 256
  · rw [ite_eq_left h]
    have e : ∀ d, accD a d = a := fun d => by unfold accD; rw [ite_eq_right (by omega)]
    rw [e, e]
  · rw [ite_eq_right h]
    have hl : a.length < 256 := by omega
    have e1 : accD a (c₀.toNat + 256 * (c₁.toNat % 16)) = (if c₀.toNat + 256 * (c₁.toNat % 16) < q then
        a ++ [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else a) := by
      unfold accD; simp only [hl, and_true]
    rw [e1]; rfl

/-- The loop's state, with the coefficients `L` sampled so far. -/
structure LS (s₀ : State) (L : List Zq) (s : State) : Prop where
  env : SEnv s₀ s
  buf : Spec.Sha3.bytesAt s.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840
  r4 : s.gpr .r4 = A s₀ + BitVec.ofNat 64 (4 * L.length)
  r5 : s.gpr .r5 = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  coeff : ∀ k < L.length, coeffAt s.mem (A s₀) k = BitVec.ofNat 32 (L.getD k 0).val

/-- What a block of the loop keeps. -/
structure Keep (s s' : State) : Prop where
  gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem LS.keep {s₀ s s' : State} (hp : Pre s₀) {L : List Zq} (h : LS s₀ L s) (hk : Keep s s')
    (h4 : s'.gpr .r4 = s.gpr .r4) (h5 : s'.gpr .r5 = s.gpr .r5) : LS s₀ L s' :=
  ⟨h.env.regs hp hk.mem hk.gp hk.rd hk.wr hk.sp, hk.mem ▸ h.buf, h4.trans h.r4, h5.trans h.r5,
    h.len, fun k hk' => hk.mem ▸ h.coeff k hk'⟩

theorem Keep.env' {s₀ s s' : State} (hk : Keep s s') (hp : Pre s₀) (h : SEnv s₀ s) : SEnv s₀ s' :=
  h.regs hp hk.mem hk.gp hk.rd hk.wr hk.sp

/-- The first candidate of a chunk. -/
def cand1 (b₀ b₁ : Byte) : BitVec 64 := b₀.setWidth 64 + (b₁.setWidth 64 <<< 60) >>> 52

/-- The second candidate of a chunk. -/
def cand2 (b₁ b₂ : Byte) : BitVec 64 := b₁.setWidth 64 >>> 4 + b₂.setWidth 64 <<< 4

/-- Nonzero exactly when the candidate `d` is accepted, with `j` coefficients. -/
def accR (d j : BitVec 64) : BitVec 64 := (d - BitVec.ofNat 64 3329) >>> 63 &&& (j - BitVec.ofNat 64 256) >>> 63

theorem accR_eq {d j : BitVec 64} (hd : d.toNat < 4096) (hj : j.toNat ≤ 256) :
    (accR d j == 0) = !decide (d.toNat < 3329 ∧ j.toNat < 256) := by
  unfold accR
  by_cases h1 : d.toNat < 3329 <;> by_cases h2 : j.toNat < 256
  · have e1 : (d - BitVec.ofNat 64 3329) >>> 63 = 1 := by bv_omega
    have e2 : (j - BitVec.ofNat 64 256) >>> 63 = 1 := by bv_omega
    rw [e1, e2]; simp [h1, h2]
  · have e2 : (j - BitVec.ofNat 64 256) >>> 63 = 0 := by bv_omega
    rw [e2]; simp [h1, h2]
  · have e1 : (d - BitVec.ofNat 64 3329) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]
  · have e1 : (d - BitVec.ofNat 64 3329) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]

theorem toNat_setWidth8 (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem cand1_toNat (b₀ b₁ : Byte) : (cand1 b₀ b₁).toNat = b₀.toNat + 256 * (b₁.toNat % 16) := by
  have := b₀.isLt; have := b₁.isLt
  unfold cand1
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toNat_setWidth8, toNat_setWidth8,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem cand2_toNat (b₁ b₂ : Byte) : (cand2 b₁ b₂).toNat = b₁.toNat / 16 + 16 * b₂.toNat := by
  have := b₁.isLt; have := b₂.isLt
  unfold cand2
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toNat_setWidth8, toNat_setWidth8,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

section
variable {s : State} {x j d : BitVec 64}

theorem blk1_ok (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = j)
    (i0 : InRegions (s.rd ++ s.wr) x 1) (i1 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 1) 1)
    (i2 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 2) 1) :
    WP isa (.block (candidates ++ acceptTest .r10)) s fun t =>
      t.gpr .r10 = cand1 (s.mem x) (s.mem (x + BitVec.ofNat 64 1)) ∧
      t.gpr .r11 = cand2 (s.mem (x + BitVec.ofNat 64 1)) (s.mem (x + BitVec.ofNat 64 2)) ∧
      t.gpr .r12 = accR (cand1 (s.mem x) (s.mem (x + BitVec.ofNat 64 1))) j ∧
      t.gpr .r3 = x ∧ t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = j ∧ t.gpr .r6 = s.gpr .r6 ∧ Keep s t := by
  prun [candidates, acceptTest, List.cons_append, List.nil_append, exec_lbz, read_one, h3, h5, i0, i1, i2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> first | exact trivial | rfl | pres_tac

theorem blk2_ok (h5 : s.gpr .r5 = j) (h11 : s.gpr .r11 = d) :
    WP isa (.block (acceptTest .r11)) s fun t =>
      t.gpr .r12 = accR d j ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = j ∧
      t.gpr .r6 = s.gpr .r6 ∧ t.gpr .r11 = d ∧ Keep s t := by
  prun [acceptTest, h5, h11]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> first | exact trivial | rfl | pres_tac

end

/-! ## Accepting a candidate -/

/-- `SEnv` through writes in `a`. -/
theorem SEnv.frameA {s₀ s s' : State} (hp : Pre s₀) (h : SEnv s₀ s) (hf : Frame [polyRegion (A s₀)] s.mem s'.mem)
    (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) :
    SEnv s₀ s' := by
  have fs := hp.fs
  have hsv : ∀ r ∈ [polyRegion (A s₀)], (⟨S s₀ + BitVec.ofNat 64 1680, 32⟩ : Region).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr
    exact (hp.a_s.sub_right (s_sub (by decide))).symm
  have k : ∀ d, 1680 ≤ d → d + 8 ≤ 1712 →
      s'.mem.readW (S s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (S s₀ + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Offset.contains _ h₁ (by omega) (by omega)) hsv (by decide)
  refine ⟨(gp _ (by decide)).trans h.r29, (gp _ (by decide)).trans h.r30, (gp _ (by decide)).trans h.r31,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr a b c => (gp r hr).trans (h.cs r hr a b c),
    (k 1680 (by omega) (by omega)).trans h.s29, (k 1688 (by omega) (by omega)).trans h.s30,
    (k 1696 (by omega) (by omega)).trans h.s31, (k 1704 (by omega) (by omega)).trans h.slr, ?_⟩
  rw [bytesAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.seed_a) (by decide)]
  exact h.seed

theorem getD_append_single {L : List Zq} {x : Zq} {k : Nat} (hk : k < L.length + 1) :
    (L ++ [x]).getD k 0 = if k < L.length then L.getD k 0 else x := by
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), show k - L.length = 0 by omega]; rfl

theorem accept_ok {s₀ s : State} (hp : Pre s₀) {L : List Zq} (h : LS s₀ L s) {d : Reg}
    {v : BitVec 64} (hv : s.gpr d = v) (hv4 : v.toNat < 4096) (hz : s.gpr .r12 = accR v (s.gpr .r5)) :
    WP isa (accept d) s fun t => LS s₀ (accD L v.toNat) t ∧ ∀ r, r ≠ .r4 → r ≠ .r5 → t.gpr r = s.gpr r := by
  have hl := h.len
  have hj : (s.gpr .r5).toNat = L.length := by
    rw [h.r5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hz' := accR_eq hv4 (j := s.gpr .r5) (by omega)
  rw [← hz, hj] at hz'
  refine WP.ite (s.gpr .r12 == 0) (eval_zero _ _) (fun e => ?_) (fun e => ?_)
  · -- rejected
    have hn : ¬ (v.toNat < 3329 ∧ L.length < 256) := by
      rw [e] at hz'; intro hc; simp [hc] at hz'
    have ea : accD L v.toNat = L := by
      unfold accD; rw [ite_eq_right (show ¬ (v.toNat < q ∧ L.length < 256) from hn)]
    rw [ea]
    exact wp_nil ⟨h, fun _ _ _ => rfl⟩
  · -- accepted
    have hy : v.toNat < 3329 ∧ L.length < 256 := by
      rw [e] at hz'; simpa using hz'
    have ea : accD L v.toNat = L ++ [ofNat v.toNat] := by
      unfold accD; rw [ite_eq_left (show v.toNat < q ∧ L.length < 256 from hy)]
    rw [ea]
    have cA := coeff_contains (A s₀) (i := L.length) (by rw [n_eq]; omega)
    have iA : InRegions s.wr (A s₀ + BitVec.ofNat 64 (4 * L.length)) 4 :=
      ⟨polyRegion (A s₀), by rw [h.env.wr, hp.wr]; simp, cA⟩
    have hblk : WP isa (.block [.store .w d .r4 0, .addi .r4 .r4 4, .addi .r5 .r5 1]) s fun t =>
        t.mem = s.mem.writeW (A s₀ + BitVec.ofNat 64 (4 * L.length)) (v.setWidth 32) ∧
        t.gpr .r4 = A s₀ + BitVec.ofNat 64 (4 * L.length) + BitVec.ofNat 64 4 ∧
        t.gpr .r5 = BitVec.ofNat 64 L.length + BitVec.ofNat 64 1 ∧
        (∀ r, r ≠ .r4 → r ≠ .r5 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [exec_store_w, h.r4, h.r5, hv, iA]
      refine ⟨by trivial, by trivial, by trivial, fun r h4 h5 => ?_, by trivial⟩
      simp only [RegUpd.gpr_write, h4, h5, ite_false]
    refine WP.mono hblk fun t ⟨m, r4, r5, rr, rd, wr, sp⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rr⟩
    · refine h.env.frameA hp (by rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cA)
        (fun r hr => rr r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr))
        rd wr sp
    · rw [m, bytesAt_writeW_sep _ _ _ (fun x h₁ h₂ => ?_) (by decide)]
      · exact h.buf
      · exact hp.a_s _ (cA.byte h₂) (s_sub (s₀ := s₀) (o := 840) (n := 840) (by decide) _
          (by simp only [Region.Contains]; omega))
    · rw [r4, List.length_append, List.length_singleton]; exact ptr_succ _ 4 _
    · rw [r5, List.length_append, List.length_singleton, BitVec.ofNat_add]
    · simp only [List.length_append, List.length_singleton]; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      rw [m, show A s₀ + BitVec.ofNat 64 (4 * L.length) = coeffAddr (A s₀) L.length from rfl,
        coeffAt_writeW _ _ (by rw [n_eq]; omega) (by rw [n_eq]; omega), getD_append_single hk]
      by_cases e' : L.length = k
      · subst e'
        rw [ite_eq_left rfl, ite_eq_right (Nat.lt_irrefl _)]
        exact BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, ofNat_of_lt (show v.toNat < q from hy.1)])
      · rw [ite_eq_right e', ite_eq_left (by omega)]
        exact h.coeff k (by omega)

/-! ## An iteration -/

/-- The coefficients sampled from the first `t` chunks. -/
abbrev Ls (s₀ : State) (t : Nat) : List Zq := sampleAfter [] (VG.Proof.MlKem.xofByte (B s₀)) t

/-- After `t` iterations. -/
structure Inv (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : LS s₀ (Ls s₀ t) s
  r3 : s.gpr .r3 = S s₀ + BitVec.ofNat 64 (840 + 3 * t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (280 - t)

theorem buf_byte {s₀ s : State} (hp : Pre s₀) {L : List Zq} (h : LS s₀ L s) {t k : Nat} (ht : t < 280) (hk : k < 3) :
    InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 (840 + 3 * t) + BitVec.ofNat 64 k) 1 ∧
    s.mem (S s₀ + BitVec.ofNat 64 (840 + 3 * t) + BitVec.ofNat 64 k) =
      VG.Proof.MlKem.xofByte (B s₀) (3 * t + k) := by
  have fs := hp.fs
  refine ⟨?_, ?_⟩
  · rw [ptr_add, h.env.rd, h.env.wr]
    exact ⟨⟨S s₀, 2048⟩, List.mem_append_right _ (by rw [hp.wr]; simp),
      Offset.contains_base _ (by omega) (by omega)⟩
  · rw [show S s₀ + BitVec.ofNat 64 (840 + 3 * t) + BitVec.ofNat 64 k =
        S s₀ + BitVec.ofNat 64 840 + BitVec.ofNat 64 (3 * t + k) by rw [ptr_add, ptr_add, Nat.add_assoc],
      ← bytesAt_getD s.mem (S s₀ + BitVec.ofNat 64 840) (show 3 * t + k < 840 by omega), h.buf,
      VG.Proof.MlKem.xof_getD _ (by omega)]

theorem cand1_lt (b₀ b₁ : Byte) : (cand1 b₀ b₁).toNat < 4096 := by
  rw [cand1_toNat]; have := b₀.isLt; have := b₁.isLt; omega

theorem cand2_lt (b₁ b₂ : Byte) : (cand2 b₁ b₂).toNat < 4096 := by
  rw [cand2_toNat]; have := b₁.isLt; have := b₂.isLt; omega

theorem Ls_succ (s₀ : State) (t : Nat) (hl : (Ls s₀ t).length ≤ 256) :
    Ls s₀ (t + 1) = accD (accD (Ls s₀ t)
      (cand1 (VG.Proof.MlKem.xofByte (B s₀) (3 * t)) (VG.Proof.MlKem.xofByte (B s₀) (3 * t + 1))).toNat)
      (cand2 (VG.Proof.MlKem.xofByte (B s₀) (3 * t + 1)) (VG.Proof.MlKem.xofByte (B s₀) (3 * t + 2))).toNat := by
  rw [Ls, sampleAfter_succ, stepCap_eq hl, cand1_toNat, cand2_toNat]

/-- The candidates of chunk `t`. -/
abbrev D1 (s₀ : State) (t : Nat) : BitVec 64 :=
  cand1 (VG.Proof.MlKem.xofByte (B s₀) (3 * t)) (VG.Proof.MlKem.xofByte (B s₀) (3 * t + 1))
abbrev D2 (s₀ : State) (t : Nat) : BitVec 64 :=
  cand2 (VG.Proof.MlKem.xofByte (B s₀) (3 * t + 1)) (VG.Proof.MlKem.xofByte (B s₀) (3 * t + 2))

/-- After the candidates of chunk `t` and the test of the first. -/
structure P1 (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : LS s₀ (Ls s₀ t) s
  r3 : s.gpr .r3 = S s₀ + BitVec.ofNat 64 (840 + 3 * t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (280 - t)
  r10 : s.gpr .r10 = D1 s₀ t
  r11 : s.gpr .r11 = D2 s₀ t
  r12 : s.gpr .r12 = accR (D1 s₀ t) (BitVec.ofNat 64 (Ls s₀ t).length)

/-- After the first candidate. -/
structure P2 (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : LS s₀ (accD (Ls s₀ t) (D1 s₀ t).toNat) s
  r3 : s.gpr .r3 = S s₀ + BitVec.ofNat 64 (840 + 3 * t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (280 - t)
  r11 : s.gpr .r11 = D2 s₀ t

/-- After the test of the second candidate. -/
structure P3 (s₀ : State) (t : Nat) (s : State) : Prop where
  p2 : P2 s₀ t s
  r12 : s.gpr .r12 = accR (D2 s₀ t) (BitVec.ofNat 64 (accD (Ls s₀ t) (D1 s₀ t).toNat).length)

/-- After the second candidate. -/
structure P4 (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : LS s₀ (Ls s₀ (t + 1)) s
  r3 : s.gpr .r3 = S s₀ + BitVec.ofNat 64 (840 + 3 * t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (280 - t)

theorem piece1 {s₀ s : State} (hp : Pre s₀) {t : Nat} (ht : t < 280) (h : Inv s₀ t s) :
    WP isa (.block (candidates ++ acceptTest .r10)) s (P1 s₀ t) := by
  obtain ⟨i0, v0⟩ := buf_byte hp h.ls ht (k := 0) (by decide)
  obtain ⟨i1, v1⟩ := buf_byte hp h.ls ht (k := 1) (by decide)
  obtain ⟨i2, v2⟩ := buf_byte hp h.ls ht (k := 2) (by decide)
  rw [BitVec.add_zero] at i0 v0
  refine WP.mono (blk1_ok h.r3 h.ls.r5 i0 i1 i2) fun s₁ ⟨r10, r11, r12, r3, r4, r5, r6, k₁⟩ => ?_
  simp only [v0, v1, v2] at r10 r11 r12
  exact ⟨h.ls.keep hp k₁ r4 (r5.trans h.ls.r5.symm), r3, r6.trans h.r6, r10, r11, r12⟩

theorem piece2 {s₀ s : State} (hp : Pre s₀) {t : Nat} (h : P1 s₀ t s) :
    WP isa (accept .r10) s (P2 s₀ t) :=
  WP.mono (accept_ok hp h.ls (d := .r10) h.r10 (cand1_lt _ _) (by rw [h.r12, h.ls.r5]))
    fun _ ⟨ls, rr⟩ => ⟨ls, (rr .r3 (by decide) (by decide)).trans h.r3, (rr .r6 (by decide) (by decide)).trans h.r6,
      (rr .r11 (by decide) (by decide)).trans h.r11⟩

theorem piece3 {s₀ s : State} (hp : Pre s₀) {t : Nat} (h : P2 s₀ t s) :
    WP isa (.block (acceptTest .r11)) s (P3 s₀ t) :=
  WP.mono (blk2_ok h.ls.r5 h.r11) fun _ ⟨r12, r3, r4, r5, r6, r11, k⟩ =>
    ⟨⟨h.ls.keep hp k r4 (r5.trans h.ls.r5.symm), r3.trans h.r3, r6.trans h.r6, r11⟩, r12⟩

theorem piece4 {s₀ s : State} (hp : Pre s₀) {t : Nat} (h : P3 s₀ t s) :
    WP isa (accept .r11) s (P4 s₀ t) :=
  WP.mono (accept_ok hp h.p2.ls (d := .r11) h.p2.r11 (cand2_lt _ _) (by rw [h.r12, h.p2.ls.r5]))
    fun _ ⟨ls, rr⟩ => ⟨by rw [Ls_succ s₀ t (sampleAfter_length_le (by simp) _ t)]; exact ls,
      (rr .r3 (by decide) (by decide)).trans h.p2.r3, (rr .r6 (by decide) (by decide)).trans h.p2.r6⟩

theorem piece5 {s₀ s : State} (hp : Pre s₀) {t : Nat} (ht : t < 280) (h : P4 s₀ t s) :
    WP isa (.block [.addi .r3 .r3 3, .subi .r6 .r6 1]) s
      fun s' => Inv s₀ (t + 1) s' ∧ (s'.gpr .r6 != 0) = decide (t + 1 ≠ 280) := by
  have hk : WP isa (.block [.addi .r3 .r3 3, .subi .r6 .r6 1]) s fun s' =>
      s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 3 ∧ s'.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r5 = s.gpr .r5 ∧ Keep s s' := by
    prun []
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> first | exact trivial | rfl | pres_tac
  refine WP.mono hk fun s' ⟨r3, r6, r4, r5, k⟩ => ⟨⟨h.ls.keep hp k r4 r5, ?_, ?_⟩, ?_⟩
  · rw [r3, h.r3, ptr_add, show 840 + 3 * t + 3 = 840 + 3 * (t + 1) by omega]
  · rw [r6, h.r6]; exact count_sub ht
  · rw [r6, h.r6, count_sub ht]; exact count_nz ht (by decide)

theorem body_ok {s₀ s : State} (hp : Pre s₀) {t : Nat} (ht : t < 280) (h : Inv s₀ t s) :
    WP isa rejBody s fun s' => Inv s₀ (t + 1) s' ∧ (s'.gpr .r6 != 0) = decide (t + 1 ≠ 280) :=
  WP.seq (WP.mono (piece1 hp ht h) fun _ h₁ => WP.seq (WP.mono (piece2 hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (piece3 hp h₂) fun _ h₃ => WP.seq (WP.mono (piece4 hp h₃) fun _ h₄ => piece5 hp ht h₄))))

/-! ## The whole function -/

theorem init_ok {s₀ s : State} (hp : Pre s₀) (h : SEnv s₀ s)
    (hb : Spec.Sha3.bytesAt s.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840) :
    WP isa (.block [.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 280]) s (Inv s₀ 0) := by
  have hk : WP isa (.block [.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 280]) s fun s' =>
      s'.gpr .r3 = S s₀ + BitVec.ofNat 64 840 ∧ s'.gpr .r4 = A s₀ ∧ s'.gpr .r5 = BitVec.ofNat 64 0 ∧
        s'.gpr .r6 = BitVec.ofNat 64 280 ∧ Keep s s' := by
    prun [h.r30, h.r31]
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> first | exact trivial | rfl | pres_tac
  refine WP.mono hk fun s' ⟨r3, r4, r5, r6, k⟩ =>
    ⟨⟨k.env' hp h, k.mem ▸ hb, ?_, ?_, by simp [Ls, sampleAfter], fun _ h => ?_⟩, r3, r6⟩
  · rw [r4]; simp [Ls, sampleAfter]
  · rw [r5]; simp [Ls, sampleAfter]
  · simp [Ls, sampleAfter] at h

theorem ret_val {n : Nat} (h : n ≤ 256) :
    BitVec.ofNat 64 n >>> 8 = if n = 256 then 1 else 0 := by
  have : n < 2 ^ 64 := by omega
  split
  · subst n; decide
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this, Nat.shiftRight_eq_div_pow]
    show n / 256 = 0
    omega

/-- What the function leaves. -/
structure Done (s₀ s : State) : Prop where
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  r3 : s.gpr .r3 = (if (Ls s₀ 280).length = 256 then 1 else 0)
  coeff : ∀ k < (Ls s₀ 280).length, coeffAt s.mem (A s₀) k = BitVec.ofNat 32 ((Ls s₀ 280).getD k 0).val

theorem end_ok {s₀ s : State} (hp : Pre s₀) (h : Inv s₀ 280 s) : WP isa (.block sampleEnd) s (Done s₀) := by
  have e := h.ls.env
  have i1680 : InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 1680) 8 :=
    ⟨⟨S s₀, 2048⟩, List.mem_append_right _ (by rw [e.wr, hp.wr]; simp),
      Offset.contains_base _ (by decide) (by have := hp.fs; omega)⟩
  have i1688 : InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 1688) 8 :=
    ⟨⟨S s₀, 2048⟩, List.mem_append_right _ (by rw [e.wr, hp.wr]; simp),
      Offset.contains_base _ (by decide) (by have := hp.fs; omega)⟩
  have i1696 : InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 1696) 8 :=
    ⟨⟨S s₀, 2048⟩, List.mem_append_right _ (by rw [e.wr, hp.wr]; simp),
      Offset.contains_base _ (by decide) (by have := hp.fs; omega)⟩
  have i1704 : InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 1704) 8 :=
    ⟨⟨S s₀, 2048⟩, List.mem_append_right _ (by rw [e.wr, hp.wr]; simp),
      Offset.contains_base _ (by decide) (by have := hp.fs; omega)⟩
  have hk : WP isa (.block sampleEnd) s fun s' =>
      s'.gpr .r3 = s.gpr .r5 >>> 8 ∧ s'.lr = s₀.lr ∧ s'.gpr .r29 = s₀.gpr .r29 ∧ s'.gpr .r30 = s₀.gpr .r30 ∧
      s'.gpr .r31 = s₀.gpr .r31 ∧ (∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp := by
    prun [sampleEnd, e.r31, i1680, i1688, i1696, i1704, e.s29, e.s30, e.s31, e.slr]
    refine ⟨by trivial, by trivial, by trivial, by trivial, by trivial, fun r hr a b c => ?_, by trivial⟩
    have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
    have h3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    simp only [RegUpd.gpr_write, a, b, c, h0, h3, ite_false]
  refine WP.mono hk fun s' ⟨r3, lr, r29, r30, r31, cs, m, sp⟩ => ⟨fun r hr => ?_, sp.trans e.sp, lr, ?_, ?_⟩
  · by_cases a : r = .r29
    · subst a; exact r29
    by_cases b : r = .r30
    · subst b; exact r30
    by_cases c : r = .r31
    · subst c; exact r31
    exact (cs r hr a b c).trans (e.cs r hr a b c)
  · rw [r3, h.ls.r5, ret_val h.ls.len]
  · intro k hk; rw [m]; exact h.ls.coeff k hk

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa sampleNTT s₀ (Done s₀) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨h₁, hz⟩ => WP.seq ?_)
  refine WP.mono (absorb_phase hp h₁ hz) fun s₂ ⟨h₂, hr, h3⟩ => WP.seq ?_
  refine WP.mono (pad_phase hp h₂ hr h3) fun s₃ ⟨h₃, hst⟩ => WP.seq ?_
  refine WP.mono (squeeze_phase hp h₃ hst) fun s₄ ⟨h₄, hb⟩ => WP.seq ?_
  refine WP.mono (init_ok hp h₄ hb) fun s₅ h₅ => WP.seq ?_
  exact wp_loop_nz (Inv s₀) (N := 280) (by decide) (fun t ht s h => body_ok hp ht h)
    (fun s h => end_ok hp h) h₅

end VG.Proof.MlKem.PPC64LE.Sample
