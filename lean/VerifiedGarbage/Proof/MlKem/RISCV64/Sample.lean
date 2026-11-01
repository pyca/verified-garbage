module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Sample
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Covers
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run

/-!
# ML-KEM on RISC-V: `vg_mlkem_sample_ntt`, correctness

As on PPC64LE (`Proof/MlKem/PPC64LE/Sample.lean`). The phases of the
function, each proved from the state the previous one leaves: the registers
saved and the Keccak state zeroed (`setup_ok`), the seed absorbed, the
padding, 840 bytes squeezed (`absorb_phase`, `pad_phase`, `squeeze_phase`,
calls of the sponge functions by `absorb_call`, `pad_call` and
`squeeze_call`, `Proof/Sha3/RISCV64/Stream/Calls.lean`), then the loop of
Algorithm 7 over the 280 chunks (`body_ok`, with the invariant `Inv`: the
coefficients sampled from the first `t` chunks, `sampleAfter`), and the
result. What every phase keeps is `SEnv`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Sample

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (Repr stateAt squeezeFrom)
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Proof.Sha3.RISCV64.Stream (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call)

section
variable (s₀ : State)

abbrev SEED : Addr := s₀.gpr .a0
abbrev A : Addr := s₀.gpr .a1
abbrev S : Addr := s₀.gpr .a2
/-- The seed. -/
abbrev B : List Byte := Spec.Sha3.bytesAt s₀.mem (SEED s₀) 34
/-- The stack the sponge functions use. -/
abbrev STK : Region := below s₀.sp 1168

end

structure Pre (s₀ : State) : Prop where
  al : s₀.sp.toNat % 16 = 0
  sp1168 : 1168 ≤ s₀.sp.toNat
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
  alA : (A s₀).toNat % 4 = 0
  alS : (S s₀).toNat % 8 = 0

/-- What every phase after the setup keeps: the pointers in `s7`–`s9`,
our caller's registers and our return address in `scratch`, and the seed. -/
structure SEnv (s₀ : State) (s : State) : Prop where
  g7 : s.gpr .s7 = SEED s₀
  g8 : s.gpr .s8 = A s₀
  g9 : s.gpr .s9 = S s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → s.gpr r = s₀.gpr r
  v7 : s.mem.readW (S s₀ + BitVec.ofNat 64 1680) 64 = s₀.gpr .s7
  v8 : s.mem.readW (S s₀ + BitVec.ofNat 64 1688) 64 = s₀.gpr .s8
  v9 : s.mem.readW (S s₀ + BitVec.ofNat 64 1696) 64 = s₀.gpr .s9
  vra : s.mem.readW (S s₀ + BitVec.ofNat 64 1704) 64 = s₀.gpr .ra
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

/-- A doubleword of `scratch` is aligned. -/
theorem s_al {o : Nat} (h : o % 8 = 0) : (S s₀ + BitVec.ofNat 64 o).toNat % 8 = 0 := by
  have := hp.alS
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

end

/-- A part of `scratch` below the saved registers, or the stack below the
stack pointer. -/
def Low (s₀ : State) (r : Region) : Prop :=
  (∃ o n, o + n ≤ 1680 ∧ r = ⟨S s₀ + BitVec.ofNat 64 o, n⟩) ∨ r = STK s₀

/-- `SEnv` through writes below the saved registers, and below the stack pointer. -/
theorem SEnv.frame {s₀ s s' : State} (hp : Pre s₀) (h : SEnv s₀ s) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, Low s₀ r)
    (gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) :
    SEnv s₀ s' := by
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
  refine ⟨(gp _ (by decide)).trans h.g7, (gp _ (by decide)).trans h.g8, (gp _ (by decide)).trans h.g9,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr a b c => (gp r hr).trans (h.cs r hr a b c),
    (k 1680 (by omega) (by omega)).trans h.v7, (k 1688 (by omega) (by omega)).trans h.v8,
    (k 1696 (by omega) (by omega)).trans h.v9, (k 1704 (by omega) (by omega)).trans h.vra, ?_⟩
  rw [bytesAt_frame hf hsd (by decide)]; exact h.seed

/-- `SEnv` through a block that writes only registers other than `s7`–`s9`. -/
theorem SEnv.regs {s₀ s t : State} (hp : Pre s₀) (h : SEnv s₀ s) (hm : t.mem = s.mem)
    (gp : ∀ r ∈ preserved, t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) :
    SEnv s₀ t :=
  h.frame hp (rs := []) (by rw [hm]; exact Frame.refl _ _) (fun _ hr => absurd hr List.not_mem_nil) gp rd wr sp

/-! ## The setup -/

/-- After zeroing the first `k` lanes of the state at `b`. -/
structure ZInv (b : Reg) (s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp
  frame : Frame [⟨s₁.gpr b, 200⟩] s₁.mem s.mem
  zero : ∀ j < k, s.mem.readW (s₁.gpr b + BitVec.ofNat 64 (8 * j)) 64 = 0

theorem zeroLanes_ok (b : Reg) {s₁ : State} (h0 : s₁.gpr .t0 = 0)
    (hwr : ∀ k < 25, InRegions s₁.wr (s₁.gpr b + BitVec.ofNat 64 (8 * k)) 8)
    (hal : ∀ k < 25, (s₁.gpr b + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) :
    WP isa (.block ((List.range 25).flatMap fun k => [.store .d .t0 b (8 * k)])) s₁ (ZInv b s₁ 25) := by
  refine wp_range_flatMap (M := isa) (ZInv b s₁) (fun k s hk h => ?_) 25 (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  refine Wp.WP.cons (exec_store_d (by omega) (by rw [h.gpr]; exact hal k hk)
    (by rw [h.gpr, h.wr]; exact hwr k hk)) (WP.block_nil ?_)
  refine ⟨h.gpr, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
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
    WP isa (.block [.store .d .s7 .a2 1680, .store .d .s8 .a2 1688, .store .d .s9 .a2 1696,
      .store .d .ra .a2 1704, mov .s7 .a0, mov .s8 .a1, mov .s9 .a2, .li .t0 0]) s₀ fun s =>
        (∀ r ∈ preserved, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → s.gpr r = s₀.gpr r) ∧
        s.gpr .s7 = SEED s₀ ∧ s.gpr .s8 = A s₀ ∧ s.gpr .s9 = S s₀ ∧ s.gpr .t0 = 0 ∧
        s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
        s.mem = (((s₀.mem.writeW (S s₀ + BitVec.ofNat 64 1680) (s₀.gpr .s7)).writeW
          (S s₀ + BitVec.ofNat 64 1688) (s₀.gpr .s8)).writeW (S s₀ + BitVec.ofNat 64 1696) (s₀.gpr .s9)).writeW
          (S s₀ + BitVec.ofNat 64 1704) (s₀.gpr .ra) := by
  have w1680 := s_in hp (o := 1680) (n := 8) (by decide)
  have w1688 := s_in hp (o := 1688) (n := 8) (by decide)
  have w1696 := s_in hp (o := 1696) (n := 8) (by decide)
  have w1704 := s_in hp (o := 1704) (n := 8) (by decide)
  have a1680 := s_al hp (o := 1680) (by decide)
  have a1688 := s_al hp (o := 1688) (by decide)
  have a1696 := s_al hp (o := 1696) (by decide)
  have a1704 := s_al hp (o := 1704) (by decide)
  crun [mov, w1680, w1688, w1696, w1704, a1680, a1688, a1696, a1704]
  refine ⟨fun r hr a b c => ?_, rfl⟩
  have h0 : r ≠ .t0 := by rintro rfl; simp [preserved] at hr
  simp [a, b, c, h0]

/-- Reading a doubleword past a write of another. -/
theorem readW_writeW_off (B : Addr) (m : Mem) {x y : Nat} (v : BitVec 64) (h : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x + 8 ≤ 2 ^ 64) (hy : y + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 64 = m.readW (B + BitVec.ofNat 64 x) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hx hy) (by decide)

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block sampleSetup) s₀ fun s => SEnv s₀ s ∧ stateAt s.mem (S s₀) = Spec.Sha3.zero := by
  have fs := hp.fs
  rw [show sampleSetup = ([.store .d .s7 .a2 1680, .store .d .s8 .a2 1688, .store .d .s9 .a2 1696,
      .store .d .ra .a2 1704, mov .s7 .a0, mov .s8 .a1, mov .s9 .a2, .li .t0 0] : List Instr) ++
      (List.range 25).flatMap fun k => [.store .d .t0 .s9 (8 * k)] from rfl, WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨gcs, g7, g8, g9, g0, rd, wr, sp, m⟩ => ?_
  refine WP.mono (zeroLanes_ok .s9 g0 (fun k hk => by rw [g9, wr]; exact s_in hp (by omega))
    (fun k hk => by rw [g9]; exact s_al hp (by omega))) fun s h => ?_
  have hf := h.frame
  have hz := h.zero
  rw [g9] at hf hz
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
  refine ⟨⟨by rw [h.gpr]; exact g7, by rw [h.gpr]; exact g8, by rw [h.gpr]; exact g9, h.rd.trans rd,
    h.wr.trans wr, h.sp.trans sp, fun r hr a b c => by rw [h.gpr]; exact gcs r hr a b c, ?_, ?_, ?_, ?_, ?_⟩,
    stateAt_zero hz⟩
  all_goals first
    | (rw [k _ (by omega) (by omega), m]
       simp (disch := decide) only [readW_writeW_off, Mem.readW_writeW_self64])
    | exact bytesAt_frame fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.seed_s)
        (by decide)

/-! ## Calls -/

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

/-- The state, at the start of `scratch`. -/
theorem lowS {s₀ : State} : ∃ o n, o + n ≤ 1680 ∧ (⟨S s₀, 200⟩ : Region) = ⟨S s₀ + BitVec.ofNat 64 o, n⟩ :=
  ⟨0, 200, by decide, by rw [BitVec.add_zero]⟩

/-- The state, at the start of `scratch`, and the stack, from a state with our stack pointer. -/
theorem low_st {s₀ s : State} (h : s.sp = s₀.sp) :
    ∀ r ∈ [(⟨S s₀, 200⟩ : Region), below s.sp 1168], Low s₀ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl lowS
  · exact .inr (by rw [h])

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
    WP isa (.block absorbSeedArgs) s fun t => SEnv s₀ t ∧ t.mem = s.mem ∧
      AbsorbArgs t (S s₀) (SEED s₀) 168 0 34 := by
  have hk : WP isa (.block absorbSeedArgs) s fun t => t.mem = s.mem ∧ t.gpr .a0 = S s₀ ∧
      t.gpr .a1 = BitVec.ofNat 64 168 ∧ t.gpr .a2 = BitVec.ofNat 64 0 ∧ t.gpr .a3 = SEED s₀ ∧
      t.gpr .a4 = BitVec.ofNat 64 34 ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
    crun [absorbSeedArgs, mov, h.g7, h.g9, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  refine WP.mono hk fun t ⟨m, a0, a1, a2, a3, a4, gp, rd, wr, sp⟩ => ⟨h.regs hp m gp rd wr sp, m, ?_⟩
  have := hp.sp1168
  refine ⟨a0, a1, a2, a3, a4, by decide, by decide, by decide, by rw [sp, h.sp]; exact hp.al,
    by rw [sp, h.sp]; exact this, hp.seed_s.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [sp, h.sp]; exact stk_st hp
  · rw [sp, h.sp]; exact hp.b_seed

theorem absorb_phase {s : State} (h : SEnv s₀ s) (hz : stateAt s.mem (S s₀) = Spec.Sha3.zero) :
    WP isa (.seq (.block absorbSeedArgs) (.call Spec.Sha3.absorbApi.name Impl.Sha3.RISCV64.Stream.absorb)) s
      fun s' => SEnv s₀ s' ∧ Repr s'.mem (S s₀) 168 (B s₀) ∧ (s'.gpr .a0).toNat = 34 := by
  refine WP.seq (WP.mono (absorbArgs_ok hp h) fun t ⟨ht, hm, ha⟩ => ?_)
  obtain ⟨hc, hw⟩ := call_covers hp ht (rd := [⟨SEED s₀, 34⟩]) (wr := [⟨S s₀, 200⟩])
    (fun r hr => by rw [List.mem_singleton] at hr; exact hr)
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact lowS)
  refine absorb_call ha hc hw fun s' rd wr sp gp hf hrep h0 => ⟨ht.frame hp hf (low_st ht.sp) gp rd wr sp, ?_, ?_⟩
  · have := hrep [] (VG.Proof.MlKem.repr_nil (by rw [hm]; exact hz)) (by decide)
    rwa [List.nil_append, hm, h.seed] at this
  · rw [h0]

end

theorem shakeSuffix64 : (BitVec.ofNat 64 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix := by decide

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem padArgs_ok {s : State} (h : SEnv s₀ s) (h0 : (s.gpr .a0).toNat = 34) :
    WP isa (.block padArgs) s fun t => SEnv s₀ t ∧ t.mem = s.mem ∧ PadArgs t (S s₀) 168 34 ∧
      t.gpr .a3 = BitVec.ofNat 64 0x1f := by
  have e0 : s.gpr .a0 = BitVec.ofNat 64 34 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  have hk : WP isa (.block padArgs) s fun t => t.mem = s.mem ∧ t.gpr .a0 = S s₀ ∧
      t.gpr .a1 = BitVec.ofNat 64 168 ∧ t.gpr .a2 = BitVec.ofNat 64 34 ∧ t.gpr .a3 = BitVec.ofNat 64 0x1f ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    crun [padArgs, mov, e0, h.g9, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  refine WP.mono hk fun t ⟨m, a0, a1, a2, a3, gp, rd, wr, sp⟩ => ⟨h.regs hp m gp rd wr sp, m, ?_, a3⟩
  have := hp.sp1168
  refine ⟨a0, a1, a2, by decide, by decide, by rw [sp, h.sp]; exact hp.al, by rw [sp, h.sp]; exact this, ?_⟩
  rw [sp, h.sp]; exact stk_st hp

theorem pad_phase {s : State} (h : SEnv s₀ s) (hr : Repr s.mem (S s₀) 168 (B s₀)) (h0 : (s.gpr .a0).toNat = 34) :
    WP isa (.seq (.block padArgs) (.call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad)) s
      fun s' => SEnv s₀ s' ∧ stateAt s'.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀) := by
  refine WP.seq (WP.mono (padArgs_ok hp h h0) fun t ⟨ht, hm, ha, a3⟩ => ?_)
  obtain ⟨hc, hw⟩ := call_covers hp ht (rd := []) (wr := [⟨S s₀, 200⟩])
    (fun r hr => absurd hr List.not_mem_nil)
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact lowS)
  refine pad_call ha hc hw fun s' rd wr sp gp hf hst => ⟨ht.frame hp hf (low_st ht.sp) gp rd wr sp, ?_⟩
  rw [hst (B s₀) (by rw [hm]; exact hr) (by simp [B, VG.Proof.MlKem.bytesAt_length]), a3, shakeSuffix64]

theorem squeezeArgs_ok {s : State} (h : SEnv s₀ s) :
    WP isa (.block squeezeArgs) s fun t => SEnv s₀ t ∧ t.mem = s.mem ∧
      SqueezeArgs t (S s₀) (S s₀ + BitVec.ofNat 64 840) 168 0 840 := by
  have hk : WP isa (.block squeezeArgs) s fun t => t.mem = s.mem ∧ t.gpr .a0 = S s₀ ∧
      t.gpr .a1 = BitVec.ofNat 64 168 ∧ t.gpr .a2 = BitVec.ofNat 64 0 ∧
      t.gpr .a3 = S s₀ + BitVec.ofNat 64 840 ∧ t.gpr .a4 = BitVec.ofNat 64 840 ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    crun [squeezeArgs, mov, h.g9, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  refine WP.mono hk fun t ⟨m, a0, a1, a2, a3, a4, gp, rd, wr, sp⟩ => ⟨h.regs hp m gp rd wr sp, m, ?_⟩
  have := hp.sp1168
  refine ⟨a0, a1, a2, a3, a4, by decide, by decide, by decide, by rw [sp, h.sp]; exact hp.al,
    by rw [sp, h.sp]; exact this, st_off hp (by decide) (by decide), ?_, ?_⟩
  · rw [sp, h.sp]; exact stk_st hp
  · rw [sp, h.sp]; exact stk_off hp (by decide)

theorem squeeze_phase {s : State} (h : SEnv s₀ s)
    (hst : stateAt s.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀)) :
    WP isa (.seq (.block squeezeArgs) (.call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze)) s
      fun s' => SEnv s₀ s' ∧ Spec.Sha3.bytesAt s'.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840 := by
  refine WP.seq (WP.mono (squeezeArgs_ok hp h) fun t ⟨ht, hm, ha⟩ => ?_)
  obtain ⟨hc, hw⟩ := call_covers hp ht (rd := []) (wr := [⟨S s₀, 200⟩, ⟨S s₀ + BitVec.ofNat 64 840, 840⟩])
    (fun r hr => absurd hr List.not_mem_nil)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact lowS
      · exact ⟨840, 840, by decide, rfl⟩)
  refine squeeze_call ha hc hw fun s' rd wr sp gp hf hb _ _ => ⟨ht.frame hp hf (fun r hr => ?_) gp rd wr sp, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl lowS
    · exact .inl ⟨840, 840, by decide, rfl⟩
    · exact .inr (by rw [ht.sp])
  · rw [hb, hm, hst, VG.Proof.MlKem.xof_eq]

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
  a1 : s.gpr .a1 = A s₀ + BitVec.ofNat 64 (4 * L.length)
  a2 : s.gpr .a2 = BitVec.ofNat 64 L.length
  t3 : s.gpr .t3 = 3329
  len : L.length ≤ 256
  coeff : ∀ k < L.length, coeffAt s.mem (A s₀) k = BitVec.ofNat 32 (L.getD k 0).val

/-- What a block of the loop keeps. -/
def Keep (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .t3 = s.gpr .t3 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
    s'.wr = s.wr ∧ s'.sp = s.sp

theorem Keep.gp {s s' : State} (h : Keep s s') : ∀ r ∈ preserved, s'.gpr r = s.gpr r := h.1
theorem Keep.t3 {s s' : State} (h : Keep s s') : s'.gpr .t3 = s.gpr .t3 := h.2.1
theorem Keep.mem {s s' : State} (h : Keep s s') : s'.mem = s.mem := h.2.2.1
theorem Keep.rd {s s' : State} (h : Keep s s') : s'.rd = s.rd := h.2.2.2.1
theorem Keep.wr {s s' : State} (h : Keep s s') : s'.wr = s.wr := h.2.2.2.2.1
theorem Keep.sp {s s' : State} (h : Keep s s') : s'.sp = s.sp := h.2.2.2.2.2

theorem LS.keep {s₀ s s' : State} (hp : Pre s₀) {L : List Zq} (h : LS s₀ L s) (hk : Keep s s')
    (h4 : s'.gpr .a1 = s.gpr .a1) (h5 : s'.gpr .a2 = s.gpr .a2) : LS s₀ L s' :=
  ⟨h.env.regs hp hk.mem hk.gp hk.rd hk.wr hk.sp, hk.mem ▸ h.buf, h4.trans h.a1, h5.trans h.a2,
    hk.t3.trans h.t3, h.len, fun k hk' => hk.mem ▸ h.coeff k hk'⟩

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

section
variable {s : State} {x j d : BitVec 64}

theorem blk1_ok (h3 : s.gpr .a0 = x) (h5 : s.gpr .a2 = j) (h13 : s.gpr .t3 = 3329)
    (i0 : InRegions (s.rd ++ s.wr) x 1) (i1 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 1) 1)
    (i2 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 2) 1) :
    WP isa (.block (candidates ++ acceptTest .a7)) s fun t =>
      t.gpr .a7 = cand1 (s.mem x) (s.mem (x + BitVec.ofNat 64 1)) ∧
      t.gpr .t1 = cand2 (s.mem (x + BitVec.ofNat 64 1)) (s.mem (x + BitVec.ofNat 64 2)) ∧
      t.gpr .t2 = accR (cand1 (s.mem x) (s.mem (x + BitVec.ofNat 64 1))) j ∧
      t.gpr .a0 = x ∧ t.gpr .a1 = s.gpr .a1 ∧ t.gpr .a2 = j ∧ t.gpr .a3 = s.gpr .a3 ∧ Keep s t := by
  crun [candidates, acceptTest, cand1, cand2, accR, Keep, h3, h5, h13, i0, i1, i2, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  all_goals simp [setWidth_zero_append]

theorem blk2_ok (h5 : s.gpr .a2 = j) (h11 : s.gpr .t1 = d) (h13 : s.gpr .t3 = 3329) :
    WP isa (.block (acceptTest .t1)) s fun t =>
      t.gpr .t2 = accR d j ∧ t.gpr .a0 = s.gpr .a0 ∧ t.gpr .a1 = s.gpr .a1 ∧ t.gpr .a2 = j ∧
      t.gpr .a3 = s.gpr .a3 ∧ t.gpr .t1 = d ∧ Keep s t := by
  crun [acceptTest, accR, Keep, h5, h11, h13, preserved, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff]

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
  refine ⟨(gp _ (by decide)).trans h.g7, (gp _ (by decide)).trans h.g8, (gp _ (by decide)).trans h.g9,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr a b c => (gp r hr).trans (h.cs r hr a b c),
    (k 1680 (by omega) (by omega)).trans h.v7, (k 1688 (by omega) (by omega)).trans h.v8,
    (k 1696 (by omega) (by omega)).trans h.v9, (k 1704 (by omega) (by omega)).trans h.vra, ?_⟩
  rw [bytesAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.seed_a) (by decide)]
  exact h.seed

theorem getD_append_single {L : List Zq} {x : Zq} {k : Nat} (hk : k < L.length + 1) :
    (L ++ [x]).getD k 0 = if k < L.length then L.getD k 0 else x := by
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), show k - L.length = 0 by omega]; rfl

theorem accept_ok {s₀ s : State} (hp : Pre s₀) {L : List Zq} (h : LS s₀ L s) {d : Reg} (_hd : d ≠ .a1 ∧ d ≠ .a2)
    {v : BitVec 64} (hv : s.gpr d = v) (hv4 : v.toNat < 4096) (hz : s.gpr .t2 = accR v (s.gpr .a2)) :
    WP isa (accept d) s fun t => LS s₀ (accD L v.toNat) t ∧ ∀ r, r ≠ .a1 → r ≠ .a2 → t.gpr r = s.gpr r := by
  have hl := h.len
  have hj : (s.gpr .a2).toNat = L.length := by
    rw [h.a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hz' := accR_eq hv4 (j := s.gpr .a2) (by omega)
  rw [← hz, hj] at hz'
  refine WP.ite (s.gpr .t2 == 0) rfl (fun e => ?_) (fun e => ?_)
  · -- rejected
    have hn : ¬ (v.toNat < 3329 ∧ L.length < 256) := by
      rw [e] at hz'; intro hc; simp [hc] at hz'
    have ea : accD L v.toNat = L := by
      unfold accD; rw [ite_eq_right (show ¬ (v.toNat < q ∧ L.length < 256) from hn)]
    rw [ea]
    exact WP.block_nil ⟨h, fun _ _ _ => rfl⟩
  · -- accepted
    have hy : v.toNat < 3329 ∧ L.length < 256 := by
      rw [e] at hz'; simpa using hz'
    have ea : accD L v.toNat = L ++ [ofNat v.toNat] := by
      unfold accD; rw [ite_eq_left (show v.toNat < q ∧ L.length < 256 from hy)]
    rw [ea]
    have cA := coeff_contains (A s₀) (i := L.length) (by rw [n_eq]; omega)
    have iA : InRegions s.wr (A s₀ + BitVec.ofNat 64 (4 * L.length)) 4 :=
      ⟨polyRegion (A s₀), by rw [h.env.wr, hp.wr]; simp, cA⟩
    have aA : (A s₀ + BitVec.ofNat 64 (4 * L.length)).toNat % 4 = 0 := align4_add hp.alA _
    have hblk : WP isa (.block [.store .w d .a1 0, .addi .a1 .a1 4, .addi .a2 .a2 1]) s fun t =>
        t.mem = s.mem.writeW (A s₀ + BitVec.ofNat 64 (4 * L.length)) (v.setWidth 32) ∧
        t.gpr .a1 = A s₀ + BitVec.ofNat 64 (4 * L.length) + BitVec.ofNat 64 4 ∧
        t.gpr .a2 = BitVec.ofNat 64 L.length + BitVec.ofNat 64 1 ∧
        (∀ r, r ≠ .a1 → r ≠ .a2 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      have h4 := h.a1
      have h5 := h.a2
      crun [h4, h5, hv, iA, aA]
      exact ⟨rfl, fun r r1 r2 => by simp [r1, r2]⟩
    refine WP.mono hblk fun t ⟨m, r4, r5, rr, rd, wr, sp⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rr⟩
    · refine h.env.frameA hp (by rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cA)
        (fun r hr => rr r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr))
        rd wr sp
    · rw [m, bytesAt_writeW_sep _ _ _ (fun x h₁ h₂ => ?_) (by decide)]
      · exact h.buf
      · exact hp.a_s _ (cA.byte h₂) (s_sub (s₀ := s₀) (o := 840) (n := 840) (by decide) _
          (by simp only [Region.Contains]; omega))
    · rw [r4, List.length_append, List.length_singleton]; exact ptr_succ _ 4 _
    · rw [r5, List.length_append, List.length_singleton, BitVec.ofNat_add]
    · rw [rr .t3 (by decide) (by decide)]; exact h.t3
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
  a0 : s.gpr .a0 = S s₀ + BitVec.ofNat 64 (840 + 3 * t)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (280 - t)

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
  a0 : s.gpr .a0 = S s₀ + BitVec.ofNat 64 (840 + 3 * t)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (280 - t)
  a7 : s.gpr .a7 = D1 s₀ t
  t1 : s.gpr .t1 = D2 s₀ t
  t2 : s.gpr .t2 = accR (D1 s₀ t) (BitVec.ofNat 64 (Ls s₀ t).length)

/-- After the first candidate. -/
structure P2 (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : LS s₀ (accD (Ls s₀ t) (D1 s₀ t).toNat) s
  a0 : s.gpr .a0 = S s₀ + BitVec.ofNat 64 (840 + 3 * t)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (280 - t)
  t1 : s.gpr .t1 = D2 s₀ t

/-- After the test of the second candidate. -/
structure P3 (s₀ : State) (t : Nat) (s : State) : Prop where
  p2 : P2 s₀ t s
  t2 : s.gpr .t2 = accR (D2 s₀ t) (BitVec.ofNat 64 (accD (Ls s₀ t) (D1 s₀ t).toNat).length)

/-- After the second candidate. -/
structure P4 (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : LS s₀ (Ls s₀ (t + 1)) s
  a0 : s.gpr .a0 = S s₀ + BitVec.ofNat 64 (840 + 3 * t)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (280 - t)

theorem piece1 {s₀ s : State} (hp : Pre s₀) {t : Nat} (ht : t < 280) (h : Inv s₀ t s) :
    WP isa (.block (candidates ++ acceptTest .a7)) s (P1 s₀ t) := by
  obtain ⟨i0, v0⟩ := buf_byte hp h.ls ht (k := 0) (by decide)
  obtain ⟨i1, v1⟩ := buf_byte hp h.ls ht (k := 1) (by decide)
  obtain ⟨i2, v2⟩ := buf_byte hp h.ls ht (k := 2) (by decide)
  rw [BitVec.add_zero] at i0 v0
  refine WP.mono (blk1_ok h.a0 h.ls.a2 h.ls.t3 i0 i1 i2) fun s₁ ⟨r10, r11, r12, r3, r4, r5, r6, k₁⟩ => ?_
  simp only [v0, v1, v2] at r10 r11 r12
  exact ⟨h.ls.keep hp k₁ r4 (r5.trans h.ls.a2.symm), r3, r6.trans h.a3, r10, r11, r12⟩

theorem piece2 {s₀ s : State} (hp : Pre s₀) {t : Nat} (h : P1 s₀ t s) :
    WP isa (accept .a7) s (P2 s₀ t) :=
  WP.mono (accept_ok hp h.ls (d := .a7) (by decide) h.a7 (cand1_lt _ _) (by rw [h.t2, h.ls.a2]))
    fun _ ⟨ls, rr⟩ => ⟨ls, (rr .a0 (by decide) (by decide)).trans h.a0, (rr .a3 (by decide) (by decide)).trans h.a3,
      (rr .t1 (by decide) (by decide)).trans h.t1⟩

theorem piece3 {s₀ s : State} (hp : Pre s₀) {t : Nat} (h : P2 s₀ t s) :
    WP isa (.block (acceptTest .t1)) s (P3 s₀ t) :=
  WP.mono (blk2_ok h.ls.a2 h.t1 h.ls.t3) fun _ ⟨r12, r3, r4, r5, r6, r11, k⟩ =>
    ⟨⟨h.ls.keep hp k r4 (r5.trans h.ls.a2.symm), r3.trans h.a0, r6.trans h.a3, r11⟩, r12⟩

theorem piece4 {s₀ s : State} (hp : Pre s₀) {t : Nat} (h : P3 s₀ t s) :
    WP isa (accept .t1) s (P4 s₀ t) :=
  WP.mono (accept_ok hp h.p2.ls (d := .t1) (by decide) h.p2.t1 (cand2_lt _ _) (by rw [h.t2, h.p2.ls.a2]))
    fun _ ⟨ls, rr⟩ => ⟨by rw [Ls_succ s₀ t (sampleAfter_length_le (by simp) _ t)]; exact ls,
      (rr .a0 (by decide) (by decide)).trans h.p2.a0, (rr .a3 (by decide) (by decide)).trans h.p2.a3⟩

theorem piece5 {s₀ s : State} (hp : Pre s₀) {t : Nat} (ht : t < 280) (h : P4 s₀ t s) :
    WP isa (.block [.addi .a0 .a0 3, .addi .a3 .a3 (-1)]) s
      fun s' => Inv s₀ (t + 1) s' ∧ (s'.gpr .a3 != 0) = decide (t + 1 ≠ 280) := by
  have hk : WP isa (.block [.addi .a0 .a0 3, .addi .a3 .a3 (-1)]) s fun s' =>
      s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 3 ∧ s'.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a2 = s.gpr .a2 ∧ Keep s s' := by
    crun [Keep, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  refine WP.mono hk fun s' ⟨r3, r6, r4, r5, k⟩ => ⟨⟨h.ls.keep hp k r4 r5, ?_, ?_⟩, ?_⟩
  · rw [r3, h.a0, ptr_add, show 840 + 3 * t + 3 = 840 + 3 * (t + 1) by omega]
  · rw [r6, h.a3]; exact count_sub ht
  · rw [r6, h.a3, count_sub ht]; exact count_nz ht (by decide)

theorem body_ok {s₀ s : State} (hp : Pre s₀) {t : Nat} (ht : t < 280) (h : Inv s₀ t s) :
    WP isa rejBody s fun s' => Inv s₀ (t + 1) s' ∧ (s'.gpr .a3 != 0) = decide (t + 1 ≠ 280) :=
  WP.seq (WP.mono (piece1 hp ht h) fun _ h₁ => WP.seq (WP.mono (piece2 hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (piece3 hp h₂) fun _ h₃ => WP.seq (WP.mono (piece4 hp h₃) fun _ h₄ => piece5 hp ht h₄))))

/-! ## The whole function -/

theorem init_ok {s₀ s : State} (hp : Pre s₀) (h : SEnv s₀ s)
    (hb : Spec.Sha3.bytesAt s.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840) :
    WP isa (.block ([.addi .a0 .s9 840, mov .a1 .s8, .li .a2 0, .li .a3 280] ++ liq .t3 3329)) s (Inv s₀ 0) := by
  have hk : WP isa (.block ([.addi .a0 .s9 840, mov .a1 .s8, .li .a2 0, .li .a3 280] ++ liq .t3 3329)) s
      fun s' => s'.gpr .a0 = S s₀ + BitVec.ofNat 64 840 ∧ s'.gpr .a1 = A s₀ ∧ s'.gpr .a2 = BitVec.ofNat 64 0 ∧
        s'.gpr .a3 = BitVec.ofNat 64 280 ∧ s'.gpr .t3 = 3329 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    have g8 := h.g8
    have g9 := h.g9
    simp only [liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
      Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
    crun [mov, g8, g9, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
    all_goals decide
  refine WP.mono hk fun s' ⟨r3, r4, r5, r6, t3, gp, m, rd, wr, sp⟩ =>
    ⟨⟨h.regs hp m gp rd wr sp, m ▸ hb, ?_, ?_, t3, by simp [Ls, sampleAfter], fun _ h => ?_⟩, r3, r6⟩
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
  ra : s.gpr .ra = s₀.gpr .ra
  a0 : s.gpr .a0 = (if (Ls s₀ 280).length = 256 then 1 else 0)
  coeff : ∀ k < (Ls s₀ 280).length, coeffAt s.mem (A s₀) k = BitVec.ofNat 32 ((Ls s₀ 280).getD k 0).val

theorem end_ok {s₀ s : State} (hp : Pre s₀) (h : Inv s₀ 280 s) : WP isa (.block sampleEnd) s (Done s₀) := by
  have e := h.ls.env
  have rS : ∀ {o : Nat}, o + 8 ≤ 2048 → InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 o) 8 := fun ho =>
    ⟨⟨S s₀, 2048⟩, List.mem_append_right _ (by rw [e.wr, hp.wr]; simp),
      Offset.contains_base _ ho (by have := hp.fs; omega)⟩
  have i1680 := rS (o := 1680) (by decide)
  have i1688 := rS (o := 1688) (by decide)
  have i1696 := rS (o := 1696) (by decide)
  have i1704 := rS (o := 1704) (by decide)
  have a1680 := s_al hp (o := 1680) (by decide)
  have a1688 := s_al hp (o := 1688) (by decide)
  have a1696 := s_al hp (o := 1696) (by decide)
  have a1704 := s_al hp (o := 1704) (by decide)
  have g9 := e.g9
  have v7 := e.v7
  have v8 := e.v8
  have v9 := e.v9
  have vra := e.vra
  have hk : WP isa (.block sampleEnd) s fun s' =>
      s'.gpr .a0 = s.gpr .a2 >>> 8 ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.gpr .s7 = s₀.gpr .s7 ∧
      s'.gpr .s8 = s₀.gpr .s8 ∧ s'.gpr .s9 = s₀.gpr .s9 ∧
      (∀ r ∈ preserved, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp := by
    crun [sampleEnd, g9, i1680, i1688, i1696, i1704, a1680, a1688, a1696, a1704]
    refine ⟨?_, ?_, ?_, ?_, fun r hr a b c => ?_⟩
    · rw [← vra]; simp [Mem.readW, Mem.read]
    · rw [← v7]; simp [Mem.readW, Mem.read]
    · rw [← v8]; simp [Mem.readW, Mem.read]
    · rw [← v9]; simp [Mem.readW, Mem.read]
    have h0 : r ≠ .a0 := by rintro rfl; simp [preserved] at hr
    have h3 : r ≠ .ra := by rintro rfl; simp [preserved] at hr
    simp [a, b, c, h0, h3]
  refine WP.mono hk fun s' ⟨r3, ra, r29, r30, r31, cs, m, sp⟩ => ⟨fun r hr => ?_, sp.trans e.sp, ra, ?_, ?_⟩
  · by_cases a : r = .s7
    · subst a; exact r29
    by_cases b : r = .s8
    · subst b; exact r30
    by_cases c : r = .s9
    · subst c; exact r31
    exact (cs r hr a b c).trans (e.cs r hr a b c)
  · rw [r3, h.ls.a2, ret_val h.ls.len]
  · intro k hk; rw [m]; exact h.ls.coeff k hk

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa sampleNTT s₀ (Done s₀) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨h₁, hz⟩ => WP.seq ?_)
  refine WP.mono (absorb_phase hp h₁ hz) fun s₂ ⟨h₂, hr, h3⟩ => WP.seq ?_
  refine WP.mono (pad_phase hp h₂ hr h3) fun s₃ ⟨h₃, hst⟩ => WP.seq ?_
  refine WP.mono (squeeze_phase hp h₃ hst) fun s₄ ⟨h₄, hb⟩ => WP.seq ?_
  refine WP.mono (init_ok hp h₄ hb) fun s₅ h₅ => WP.seq ?_
  exact wp_loop_nz (Inv s₀) (N := 280) (by decide) (fun t ht s h => body_ok hp ht h)
    (fun s h => end_ok hp h) h₅

end VG.Proof.MlKem.RISCV64.Sample
