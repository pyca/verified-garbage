import VerifiedGarbage.Proof.MlKem.Arm.Mul
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Sample`. -/
section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_sample_ntt`, correctness

The phases of the function, each proved from the state the previous one
leaves: the registers saved and the Keccak state zeroed (`setup_ok`), the seed
absorbed, the padding, 840 bytes squeezed (`absorb_phase`, `pad_phase`,
`squeeze_phase`, from `absorb_ok`, … of `Keccak.lean`), then the loop of
Algorithm 7 over the 280 chunks (`body_ok`, with the invariant `Inv`: the
coefficients sampled from the first `t` chunks, `sampleAfter`), and the
result. What every phase keeps is `SEnv`.
-/

namespace VG.Proof.MlKem.Arm.Sample

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (Repr stateAt squeezeFrom)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

section
variable (s₀ : State)

abbrev pseed : BitVec 32 := s₀.gpr .r0
abbrev pa : BitVec 32 := s₀.gpr .r1
abbrev pscr : BitVec 32 := s₀.gpr .r2
abbrev SEED : Addr := State.addr (VG.Proof.MlKem.Arm.Sample.pseed s₀)
abbrev A : Addr := State.addr (VG.Proof.MlKem.Arm.Sample.pa s₀)
abbrev S : Addr := State.addr (VG.Proof.MlKem.Arm.Sample.pscr s₀)
/-- The seed. -/
abbrev B : List Byte := Spec.Sha3.bytesAt s₀.mem (VG.Proof.MlKem.Arm.Sample.SEED s₀) 34

end

structure Pre (s₀ : State) : Prop where
  sp8 : 8 ≤ s₀.sp.toNat
  rd : s₀.rd = [⟨VG.Proof.MlKem.Arm.Sample.SEED s₀, 34⟩]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.Arm.Sample.A s₀), ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩]
  seed_a : (⟨VG.Proof.MlKem.Arm.Sample.SEED s₀, 34⟩ : Region).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Sample.A s₀))
  seed_s : (⟨VG.Proof.MlKem.Arm.Sample.SEED s₀, 34⟩ : Region).Disjoint ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩
  a_s : (polyRegion (VG.Proof.MlKem.Arm.Sample.A s₀)).Disjoint ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩
  b_seed : (below s₀ 8).Disjoint ⟨VG.Proof.MlKem.Arm.Sample.SEED s₀, 34⟩
  b_a : (below s₀ 8).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Sample.A s₀))
  b_s : (below s₀ 8).Disjoint ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩
  fseed : (VG.Proof.MlKem.Arm.Sample.pseed s₀).toNat + 34 ≤ 2 ^ 32
  fa : (VG.Proof.MlKem.Arm.Sample.pa s₀).toNat + 1024 ≤ 2 ^ 32
  fs : (VG.Proof.MlKem.Arm.Sample.pscr s₀).toNat + 2048 ≤ 2 ^ 32

/-- What every phase after the setup keeps: the pointers in `r4`–`r6`, our
caller's registers in `scratch`, and the seed. -/
structure SEnv (s₀ : State) (s : State) : Prop where
  r4 : s.gpr .r4 = VG.Proof.MlKem.Arm.Sample.pseed s₀
  r5 : s.gpr .r5 = VG.Proof.MlKem.Arm.Sample.pa s₀
  r6 : s.gpr .r6 = VG.Proof.MlKem.Arm.Sample.pscr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sav : VG.Proof.MlKem.Arm.Saved s.mem (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680) s₀.gpr
  savlr : s.mem.readW (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1712) 32 = s₀.gpr .lr
  seed : Spec.Sha3.bytesAt s.mem (VG.Proof.MlKem.Arm.Sample.SEED s₀) 34 = VG.Proof.MlKem.Arm.Sample.B s₀

/-! ## Addresses in `scratch` -/

theorem hS {s₀ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {k : Nat} (hk : k < 2048) :
    State.addr (VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 k) = VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 k :=
  addr_add (by have := hp.fs; omega)

theorem sfit {s₀ : State} (_hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) : (VG.Proof.MlKem.Arm.Sample.S s₀).toNat + 2048 ≤ 2 ^ 64 := addr_fit _ (by decide)

/-- A part of `scratch`. -/
theorem s_sub {s₀ : State} {o n : Nat} (h : o + n ≤ 2048) :
    Region.Sub ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 o, n⟩ ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩ := region_sub_off h

/-- Two parts of `scratch`, apart. -/
theorem s_disj {s₀ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁ : o₁ + n₁ ≤ 2048) (h₂ : o₂ + n₂ ≤ 2048) :
    Region.Disjoint ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  region_disj_off h h₁ h₂ (VG.Proof.MlKem.Arm.Sample.sfit hp)

theorem s_in {s₀ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {o n : Nat} (h : o + n ≤ 2048) :
    Covers [⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 o, n⟩] s₀.wr := fun x m ⟨r, hr, hc⟩ => by
  rw [List.mem_singleton] at hr; subst hr
  refine ⟨⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩, by rw [hp.wr]; simp, ?_⟩
  simp only [Region.Contains] at hc ⊢
  bv_omega

theorem covers_cons {r : Region} {rs ws : List Region} (h₁ : Covers [r] ws) (h₂ : Covers rs ws) :
    Covers (r :: rs) ws := fun x n ⟨q, hq, hc⟩ => by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h₁ x n ⟨q, List.mem_singleton_self _, hc⟩
  · exact h₂ x n ⟨q, hq, hc⟩

theorem covers_nil {ws : List Region} : Covers [] ws := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

/-! ## `SEnv` through writes in `scratch` below the saved registers, and below the stack pointer -/

theorem SEnv.frame {s₀ s s' : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s) {rs : List Region}
    (hf : Frame rs s.mem s'.mem)
    (hrs : ∀ r ∈ rs, (∃ o n, o + n ≤ 1680 ∧ r = ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 o, n⟩) ∨ r = below s₀ 8)
    (g4 : s'.gpr .r4 = s.gpr .r4) (g5 : s'.gpr .r5 = s.gpr .r5) (g6 : s'.gpr .r6 = s.gpr .r6)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' := by
  have hsv : ∀ r ∈ rs, (⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩ : Region).Disjoint r := by
    intro r hr
    rcases hrs r hr with ⟨o, n, ho, rfl⟩ | rfl
    · exact VG.Proof.MlKem.Arm.Sample.s_disj hp (by omega) (by omega) (by omega)
    · exact (hp.b_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))).symm
  have hsd : ∀ r ∈ rs, (⟨VG.Proof.MlKem.Arm.Sample.SEED s₀, 34⟩ : Region).Disjoint r := by
    intro r hr
    rcases hrs r hr with ⟨o, n, ho, rfl⟩ | rfl
    · exact hp.seed_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by omega))
    · exact hp.b_seed.symm
  refine ⟨g4.trans h.r4, g5.trans h.r5, g6.trans h.r6, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    fun i hi => ?_, ?_, ?_⟩
  · rw [hf.readW (r := ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩) ?_ hsv (by decide)]
    · exact h.sav i hi
    · simp only [Region.Contains]; bv_omega
  · rw [hf.readW (r := ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩) ?_ hsv (by decide)]
    · exact h.savlr
    · simp only [Region.Contains]; bv_omega
  · rw [bytesAt_frame hf hsd (by decide)]; exact h.seed

/-! ## The setup -/

/-- After zeroing the first `k` words of the state at `b`. -/
structure ZInv (b : Reg) (s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp
  frame : Frame [⟨State.addr (s₁.gpr b), 200⟩] s₁.mem s.mem
  zero : ∀ j < k, s.mem.readW (State.addr (s₁.gpr b) + BitVec.ofNat 64 (4 * j)) 32 = 0

theorem zeroWords_ok (b : Reg) {s₁ : State} (h12 : s₁.gpr .r12 = 0) (hfit : (s₁.gpr b).toNat + 200 ≤ 2 ^ 32)
    (hwr : ∀ k < 50, InRegions s₁.wr (State.addr (s₁.gpr b) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block ((List.range 50).flatMap fun k => [.str .r12 b (4 * k)])) s₁ (VG.Proof.MlKem.Arm.Sample.ZInv b s₁ 50) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.MlKem.Arm.Sample.ZInv b s₁) (fun k s hk h => ?_) 50 (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s.gpr b + BitVec.ofNat 32 (4 * k)) = State.addr (s₁.gpr b) + BitVec.ofNat 64 (4 * k) := by
    rw [h.gpr, addr_add (by omega)]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_str (by omega) (by rw [ea, h.wr]; exact hwr k hk), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.gpr, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
  · rw [ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ _ = _
    rw [ea, h.gpr, h12]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)]
      exact h.zero j (by omega)

theorem stateAt_zero {m : Mem} {p : Addr} (h : ∀ j < 50, m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Spec.Sha3.zero, Vector.getElem_replicate]
  rw [VG.Proof.Sha512.Arm.readW64, show p + BitVec.ofNat 64 (8 * i) + 4 = p + BitVec.ofNat 64 (4 * (2 * i + 1)) by
      rw [BitVec.add_assoc]; congr 1; bv_omega,
    show p + BitVec.ofNat 64 (8 * i) = p + BitVec.ofNat 64 (4 * (2 * i)) by congr 2; omega,
    h _ (by omega), h _ (by omega)]
  rfl

theorem setup_ok {s₀ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) :
    WP isa (.block sampleSetup) s₀ fun s => VG.Proof.MlKem.Arm.Sample.SEnv s₀ s ∧ stateAt s.mem (VG.Proof.MlKem.Arm.Sample.S s₀) = Spec.Sha3.zero := by
  have fs := hp.fs
  have hS' : (VG.Proof.MlKem.Arm.Sample.S s₀).toNat + 2048 ≤ 2 ^ 64 := VG.Proof.MlKem.Arm.Sample.sfit hp
  have wS : ∀ {o n : Nat}, o + n ≤ 2048 → InRegions s₀.wr (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 o) n := fun h =>
    VG.Proof.MlKem.Arm.Sample.s_in hp h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [sampleSetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r2 (off := 1680) (by decide) (fit_le (by decide) fs) fun i hi => by
    rw [add_ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  have g2 : s₁.gpr .r2 = VG.Proof.MlKem.Arm.Sample.pscr s₀ := by rw [h₁.gpr]
  have e1712 : State.addr (s₁.gpr .r2 + BitVec.ofNat 32 1712) = VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1712 := by
    rw [g2]; exact VG.Proof.MlKem.Arm.Sample.hS hp (by decide)
  have i1712 : InRegions s₁.wr (State.addr (s₁.gpr .r2 + BitVec.ofNat 32 1712)) 4 := by
    rw [e1712, h₁.wr]; exact wS (by decide)
  have ho : 1712 < 4096 := by decide
  have hm2 : ∀ (s : State), WP isa (.block [.str .lr .r2 1712, .mov .r4 (.reg .r0), .mov .r5 (.reg .r1),
      .mov .r6 (.reg .r2)]) s₁ fun s₂ => s₂.gpr = (((s₁.setReg .r4 (s₁.gpr .r0)).setReg .r5 (s₁.gpr .r1)).setReg .r6
        (s₁.gpr .r2)).gpr ∧ s₂.mem = s₁.mem.writeW (State.addr (s₁.gpr .r2 + BitVec.ofNat 32 1712)) (s₁.gpr .lr) ∧
        s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.sp = s₁.sp := fun _ => by
    run_block [i1712, ho]
  refine WP.mono (hm2 s₁) fun s₂ ⟨g, m, rd, wr, sp⟩ => ?_
  rw [zeroState, ← List.singleton_append, WP.block_append_iff]
  have e6 : s₂.gpr .r6 = VG.Proof.MlKem.Arm.Sample.pscr s₀ := by rw [g]; simp [State.setReg, g2]
  have hmov : WP isa (.block [.mov .r12 (.imm 0)]) s₂ fun s₃ => s₃.gpr = (s₂.setReg .r12 0).gpr ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.sp = s₂.sp := by
    run_block []
  refine WP.mono hmov fun s₃ ⟨g3, m3, rd3, wr3, sp3⟩ => ?_
  have e36 : s₃.gpr .r6 = VG.Proof.MlKem.Arm.Sample.pscr s₀ := by rw [g3]; simp [State.setReg, e6]
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.zeroWords_ok .r6 (s₁ := s₃) (by rw [g3]; simp [State.setReg])
    (by rw [e36]; exact fit_le (by decide) fs)
    fun k hk => by rw [e36, wr3, wr, h₁.wr]; exact wS (by omega)) fun s₄ h₄ => ?_
  have hf4 := h₄.frame
  have hz4 := h₄.zero
  rw [e36] at hf4 hz4
  have hsave : ∀ r ∈ [(⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 32⟩ : Region)], Region.Sub r ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩ := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlKem.Arm.Sample.s_sub (by decide)
  have fr : Frame [⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩] s₀.mem s₄.mem := by
    refine (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, hsave r hr⟩).trans ?_
    refine Frame.trans (m₂ := s₂.mem) ?_ ?_
    · rw [m, e1712]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))
    · rw [← m3]
      refine hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
      rw [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by decide)
  have hz : ∀ r ∈ [(⟨VG.Proof.MlKem.Arm.Sample.S s₀, 200⟩ : Region)], (⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩ : Region).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr
    have := VG.Proof.MlKem.Arm.Sample.s_disj hp (o₁ := 1680) (n₁ := 36) (o₂ := 0) (n₂ := 200) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  refine ⟨⟨?_, ?_, ?_, rd3.trans (rd.trans h₁.rd) ▸ h₄.rd, wr3.trans (wr.trans h₁.wr) ▸ h₄.wr,
    sp3.trans (sp.trans h₁.sp) ▸ h₄.sp, fun i hi => ?_, ?_, ?_⟩, VG.Proof.MlKem.Arm.Sample.stateAt_zero hz4⟩
  · rw [h₄.gpr, g3]; simp [State.setReg, g, h₁.gpr]
  · rw [h₄.gpr, g3]; simp [State.setReg, g, h₁.gpr]
  · rw [h₄.gpr, g3]; simp [State.setReg, g, h₁.gpr]
  · rw [hf4.readW (r := ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩) (by simp only [Region.Contains]; bv_omega)
      hz (by decide), m3, m, e1712, Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)]
    exact h₁.saved i hi
  · rw [hf4.readW (r := ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩) (by simp only [Region.Contains]; bv_omega)
      hz (by decide), m3, m, e1712, Mem.readW_writeW_self32, h₁.gpr]
  · exact bytesAt_frame fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.seed_s)
      (by decide)

/-! ## The sponge -/

theorem SEnv.kept {s₀ s s' : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s) {rs : List Region} (hk : Kept rs s s')
    (hrs : ∀ r ∈ rs, (∃ o n, o + n ≤ 1680 ∧ r = ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 o, n⟩) ∨ r = below s₀ 8) :
    VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' :=
  h.frame hp hk.frame hrs (hk.cs .r4 (by decide) (by decide)) (hk.cs .r5 (by decide) (by decide))
    (hk.cs .r6 (by decide) (by decide)) hk.rd hk.wr hk.sp

theorem regA_S {s₀ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {k : Nat} (hk : k < 2048) (n : Nat) :
    regA (VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 k) n = ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 k, n⟩ := by
  simp only [regA, VG.Proof.MlKem.Arm.Sample.hS hp hk]

theorem regA_S0 (s₀ : State) (n : Nat) : regA (VG.Proof.MlKem.Arm.Sample.pscr s₀) n = ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 0, n⟩ := by
  simp only [regA, add_ofNat_zero]

theorem fit_add {p : BitVec 32} {k n : Nat} (h : p.toNat + (k + n) ≤ 2 ^ 32) (hk : k < 2 ^ 32) (hn : 0 < n) :
    (p + BitVec.ofNat 32 k).toNat + n ≤ 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]; omega

theorem below_eq {s₀ s : State} (h : s.sp = s₀.sp) : below s 8 = below s₀ 8 := by simp only [below, h]

/-- A block that writes none of `r4`–`r11`, and no memory. -/
structure Regs (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Regs.env {s₀ s s' : State} (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s) (hr : VG.Proof.MlKem.Arm.Sample.Regs s s') : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' := by
  refine ⟨(hr.cs .r4 (by decide) (by decide)).trans h.r4, (hr.cs .r5 (by decide) (by decide)).trans h.r5,
    (hr.cs .r6 (by decide) (by decide)).trans h.r6, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp, ?_, ?_, ?_⟩
  · rw [hr.mem]; exact h.sav
  · rw [hr.mem]; exact h.savlr
  · rw [hr.mem]; exact h.seed

/-- `Regs` of a state that only changes registers other than `r4`–`r11`. -/
theorem regs_cs {s : State} (g : Reg → BitVec 32)
    (h : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], g r = s.gpr r) :
    VG.Proof.MlKem.Arm.Sample.Regs s { s with
                    gpr := g } :=
  ⟨fun r hr hl => by
    have : r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h | h | h | h <;> simp_all
    exact h r this, rfl, rfl, rfl, rfl⟩

section
variable {s : State} {x4 x6 x0 : BitVec 32}

theorem absorbSeedArgs_ok (h4 : s.gpr .r4 = x4) (h6 : s.gpr .r6 = x6) :
    WP isa (.block absorbSeedArgs) s fun s' => VG.Proof.MlKem.Arm.Sample.Regs s s' ∧ s'.gpr .r0 = x6 ∧ s'.gpr .r1 = BitVec.ofNat 32 168 ∧
      s'.gpr .r2 = BitVec.ofNat 32 0 ∧ s'.gpr .r3 = x4 ∧ s'.gpr .r12 = BitVec.ofNat 32 34 ∧
      s'.gpr .lr = x6 + BitVec.ofNat 32 200 := by
  run_block [absorbSeedArgs, h4, h6, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_self, and_true]
  refine ⟨VG.Proof.MlKem.Arm.Sample.regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

theorem absorb_args {s₀ s₁ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h₁ : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s₁) (g0 : s₁.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀)
    (g1 : s₁.gpr .r1 = BitVec.ofNat 32 168) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 0) (g3 : s₁.gpr .r3 = VG.Proof.MlKem.Arm.Sample.pseed s₀)
    (g12 : s₁.gpr .r12 = BitVec.ofNat 32 34) (glr : s₁.gpr .lr = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200) :
    AbsorbArgs s₁ (VG.Proof.MlKem.Arm.Sample.pscr s₀) (VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200) (VG.Proof.MlKem.Arm.Sample.pseed s₀) 168 0 34 := by
  have fs := hp.fs
  have eb := VG.Proof.MlKem.Arm.Sample.below_eq (s := s₁) h₁.sp
  have hsp8 : 8 ≤ s₁.sp.toNat := by rw [h₁.sp]; exact hp.sp8
  exact {
    r0 := g0, r1 := g1, r2 := g2, r3 := g3, r12 := g12, lr := glr
    hrate := by decide, hpos := by decide, hlen := by decide, sp := hsp8
    fst := fit_le (by decide) fs, fdata := hp.fseed, fscr := VG.Proof.MlKem.Arm.Sample.fit_add (fit_le (by decide) fs) (by decide) (by decide)
    d_st_scr := by
      rw [VG.Proof.MlKem.Arm.Sample.regA_S0, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact VG.Proof.MlKem.Arm.Sample.s_disj hp (by omega) (by omega) (by omega)
    d_data_st := by rw [VG.Proof.MlKem.Arm.Sample.regA_S0]; exact hp.seed_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    d_data_scr := by rw [VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact hp.seed_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    b_st := by rw [eb, VG.Proof.MlKem.Arm.Sample.regA_S0]; exact hp.b_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    b_scr := by rw [eb, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact hp.b_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    b_data := by rw [eb]; exact hp.b_seed
    cw := by
      rw [VG.Proof.MlKem.Arm.Sample.regA_S0, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide), h₁.wr]
      exact VG.Proof.MlKem.Arm.Sample.covers_cons (VG.Proof.MlKem.Arm.Sample.s_in hp (by decide)) (VG.Proof.MlKem.Arm.Sample.covers_cons (VG.Proof.MlKem.Arm.Sample.s_in hp (by decide)) VG.Proof.MlKem.Arm.Sample.covers_nil)
    cr := fun x n ⟨r, hr, hc⟩ => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, by rw [h₁.rd, hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _), hc⟩ }

theorem absorb_phase {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s) (hz : stateAt s.mem (VG.Proof.MlKem.Arm.Sample.S s₀) = Spec.Sha3.zero) :
    WP isa (.seq (.block absorbSeedArgs) absorbCall) s fun s' =>
      VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' ∧ Repr s'.mem (VG.Proof.MlKem.Arm.Sample.S s₀) 168 (VG.Proof.MlKem.Arm.Sample.B s₀) ∧ (s'.gpr .r0).toNat = 34 := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Sample.absorbSeedArgs_ok h.r4 h.r6) fun s₁ ⟨hr, g0, g1, g2, g3, g12, glr⟩ => ?_)
  have h₁ := hr.env h
  refine absorb_ok (VG.Proof.MlKem.Arm.Sample.absorb_args hp h₁ g0 g1 g2 g3 g12 glr) fun s' hk hrep hr0 => ⟨?_, ?_, ?_⟩
  · refine h₁.kept hp hk fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨0, 200, by decide, VG.Proof.MlKem.Arm.Sample.regA_S0 _ _⟩
    · exact .inl ⟨200, 640, by decide, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide) _⟩
    · exact .inr (VG.Proof.MlKem.Arm.Sample.below_eq h₁.sp)
  · have := hrep [] (VG.Proof.MlKem.repr_nil (by rw [hr.mem]; exact hz)) (by decide)
    rwa [List.nil_append, show Spec.Sha3.bytesAt _ _ 34 = VG.Proof.MlKem.Arm.Sample.B s₀ from h₁.seed] at this
  · rw [hr0]

section
variable {s : State} {x6 x0 : BitVec 32}

theorem padArgs_ok (h0 : s.gpr .r0 = x0) (h6 : s.gpr .r6 = x6) :
    WP isa (.block padArgs) s fun s' => VG.Proof.MlKem.Arm.Sample.Regs s s' ∧ s'.gpr .r0 = x6 ∧ s'.gpr .r1 = BitVec.ofNat 32 168 ∧
      s'.gpr .r2 = x0 ∧ s'.gpr .r3 = BitVec.ofNat 32 0x1f ∧ s'.gpr .lr = x6 + BitVec.ofNat 32 200 := by
  run_block [padArgs, h0, h6, and_self, and_true]
  refine ⟨VG.Proof.MlKem.Arm.Sample.regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem squeezeArgs_ok (h6 : s.gpr .r6 = x6) :
    WP isa (.block squeezeArgs) s fun s' => VG.Proof.MlKem.Arm.Sample.Regs s s' ∧ s'.gpr .r0 = x6 ∧ s'.gpr .r1 = BitVec.ofNat 32 168 ∧
      s'.gpr .r2 = BitVec.ofNat 32 0 ∧ s'.gpr .r3 = x6 + BitVec.ofNat 32 840 ∧
      s'.gpr .r12 = BitVec.ofNat 32 840 ∧ s'.gpr .lr = x6 + BitVec.ofNat 32 200 := by
  run_block [squeezeArgs, h6, and_self, and_true]
  refine ⟨VG.Proof.MlKem.Arm.Sample.regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

theorem pad_args {s₀ s₁ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h₁ : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s₁) (g0 : s₁.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀)
    (g1 : s₁.gpr .r1 = BitVec.ofNat 32 168) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 34)
    (g3 : s₁.gpr .r3 = BitVec.ofNat 32 0x1f) (glr : s₁.gpr .lr = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200) :
    PadArgs s₁ (VG.Proof.MlKem.Arm.Sample.pscr s₀) (VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200) 168 34 (BitVec.ofNat 32 0x1f) := by
  have fs := hp.fs
  have eb := VG.Proof.MlKem.Arm.Sample.below_eq (s := s₁) h₁.sp
  have hsp8 : 8 ≤ s₁.sp.toNat := by rw [h₁.sp]; exact hp.sp8
  exact {
    r0 := g0, r1 := g1, r2 := g2, r3 := g3, lr := glr
    hrate := by decide, hpos := by decide, sp := hsp8
    fst := fit_le (by decide) fs, fscr := VG.Proof.MlKem.Arm.Sample.fit_add (fit_le (by decide) fs) (by decide) (by decide)
    d_st_scr := by
      rw [VG.Proof.MlKem.Arm.Sample.regA_S0, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact VG.Proof.MlKem.Arm.Sample.s_disj hp (by omega) (by omega) (by omega)
    b_st := by rw [eb, VG.Proof.MlKem.Arm.Sample.regA_S0]; exact hp.b_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    b_scr := by rw [eb, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact hp.b_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    cw := by
      rw [VG.Proof.MlKem.Arm.Sample.regA_S0, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide), h₁.wr]
      exact VG.Proof.MlKem.Arm.Sample.covers_cons (VG.Proof.MlKem.Arm.Sample.s_in hp (by decide)) (VG.Proof.MlKem.Arm.Sample.covers_cons (VG.Proof.MlKem.Arm.Sample.s_in hp (by decide)) VG.Proof.MlKem.Arm.Sample.covers_nil) }

theorem pad_phase {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s) (hr : Repr s.mem (VG.Proof.MlKem.Arm.Sample.S s₀) 168 (VG.Proof.MlKem.Arm.Sample.B s₀))
    (h0 : (s.gpr .r0).toNat = 34) :
    WP isa (.seq (.block padArgs) padCall) s fun s' =>
      VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' ∧ stateAt s'.mem (VG.Proof.MlKem.Arm.Sample.S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (VG.Proof.MlKem.Arm.Sample.B s₀) := by
  have e0 : s.gpr .r0 = BitVec.ofNat 32 34 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Sample.padArgs_ok e0 h.r6) fun s₁ ⟨hR, g0, g1, g2, g3, glr⟩ => ?_)
  have h₁ := hR.env h
  refine pad_ok (VG.Proof.MlKem.Arm.Sample.pad_args hp h₁ g0 g1 g2 g3 glr) fun s' hk hpad => ⟨?_, ?_⟩
  · refine h₁.kept hp hk fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨0, 200, by decide, VG.Proof.MlKem.Arm.Sample.regA_S0 _ _⟩
    · exact .inl ⟨200, 640, by decide, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide) _⟩
    · exact .inr (VG.Proof.MlKem.Arm.Sample.below_eq h₁.sp)
  · have := hpad (VG.Proof.MlKem.Arm.Sample.B s₀) (by rw [hR.mem]; exact hr) (by simp [VG.Proof.MlKem.Arm.Sample.B, bytesAt_length])
    rw [this]
    exact congrArg (fun x => Spec.Sha3.absorb 168 (Spec.Sha3.pad 168 x (VG.Proof.MlKem.Arm.Sample.B s₀))) VG.Proof.MlKem.shakeSuffix32

theorem squeeze_args {s₀ s₁ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h₁ : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s₁) (g0 : s₁.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀)
    (g1 : s₁.gpr .r1 = BitVec.ofNat 32 168) (g2 : s₁.gpr .r2 = BitVec.ofNat 32 0)
    (g3 : s₁.gpr .r3 = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 840) (g12 : s₁.gpr .r12 = BitVec.ofNat 32 840)
    (glr : s₁.gpr .lr = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200) :
    SqueezeArgs s₁ (VG.Proof.MlKem.Arm.Sample.pscr s₀) (VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200) (VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 840) 168 0 840 := by
  have fs := hp.fs
  have eb := VG.Proof.MlKem.Arm.Sample.below_eq (s := s₁) h₁.sp
  have hsp8 : 8 ≤ s₁.sp.toNat := by rw [h₁.sp]; exact hp.sp8
  exact {
    r0 := g0, r1 := g1, r2 := g2, r3 := g3, r12 := g12, lr := glr
    hrate := by decide, hpos := by decide, hlen := by decide, sp := hsp8
    fst := fit_le (by decide) fs, fscr := VG.Proof.MlKem.Arm.Sample.fit_add (fit_le (by decide) fs) (by decide) (by decide)
    fout := VG.Proof.MlKem.Arm.Sample.fit_add (fit_le (by decide) fs) (by decide) (by decide)
    d_st_out := by
      rw [VG.Proof.MlKem.Arm.Sample.regA_S0, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact VG.Proof.MlKem.Arm.Sample.s_disj hp (by omega) (by omega) (by omega)
    d_st_scr := by
      rw [VG.Proof.MlKem.Arm.Sample.regA_S0, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact VG.Proof.MlKem.Arm.Sample.s_disj hp (by omega) (by omega) (by omega)
    d_out_scr := by
      rw [VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide), VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact VG.Proof.MlKem.Arm.Sample.s_disj hp (by omega) (by omega) (by omega)
    b_st := by rw [eb, VG.Proof.MlKem.Arm.Sample.regA_S0]; exact hp.b_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    b_out := by rw [eb, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact hp.b_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    b_scr := by rw [eb, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide)]; exact hp.b_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))
    cw := by
      rw [VG.Proof.MlKem.Arm.Sample.regA_S0, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide), VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide), h₁.wr]
      exact VG.Proof.MlKem.Arm.Sample.covers_cons (VG.Proof.MlKem.Arm.Sample.s_in hp (by decide)) (VG.Proof.MlKem.Arm.Sample.covers_cons (VG.Proof.MlKem.Arm.Sample.s_in hp (by decide))
        (VG.Proof.MlKem.Arm.Sample.covers_cons (VG.Proof.MlKem.Arm.Sample.s_in hp (by decide)) VG.Proof.MlKem.Arm.Sample.covers_nil)) }

theorem squeeze_phase {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s)
    (hst : stateAt s.mem (VG.Proof.MlKem.Arm.Sample.S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (VG.Proof.MlKem.Arm.Sample.B s₀)) :
    WP isa (.seq (.block squeezeArgs) squeezeCall) s fun s' =>
      VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' ∧ Spec.Sha3.bytesAt s'.mem (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 840) 840 = xof (VG.Proof.MlKem.Arm.Sample.B s₀) 840 := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Sample.squeezeArgs_ok h.r6) fun s₁ ⟨hR, g0, g1, g2, g3, g12, glr⟩ => ?_)
  have h₁ := hR.env h
  refine squeeze_ok (VG.Proof.MlKem.Arm.Sample.squeeze_args hp h₁ g0 g1 g2 g3 g12 glr) fun s' hk hout _ _ => ⟨?_, ?_⟩
  · refine h₁.kept hp hk fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨0, 200, by decide, VG.Proof.MlKem.Arm.Sample.regA_S0 _ _⟩
    · exact .inl ⟨840, 840, by decide, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide) _⟩
    · exact .inl ⟨200, 640, by decide, VG.Proof.MlKem.Arm.Sample.regA_S hp (by decide) _⟩
    · exact .inr (VG.Proof.MlKem.Arm.Sample.below_eq h₁.sp)
  · rw [← VG.Proof.MlKem.Arm.Sample.hS hp (by decide), hout, hR.mem, show State.addr (VG.Proof.MlKem.Arm.Sample.pscr s₀) = VG.Proof.MlKem.Arm.Sample.S s₀ from rfl, hst,
      VG.Proof.MlKem.xof_eq]

/-! ## The loop of Algorithm 7 -/

/-- A candidate `d` accepted into `a` if `d < q` and there are fewer than
256 coefficients. -/
def accD (a : List Zq) (d : Nat) : List Zq := if d < VG.Spec.MlKem.q ∧ a.length < 256 then a ++ [ofNat d] else a

theorem accD_length_le {a : List Zq} (h : a.length ≤ 256) (d : Nat) : (VG.Proof.MlKem.Arm.Sample.accD a d).length ≤ 256 := by
  unfold VG.Proof.MlKem.Arm.Sample.accD; split
  · rename_i h'; simp only [List.length_append, List.length_singleton]; omega
  · exact h

theorem stepCap_eq {a : List Zq} (ha : a.length ≤ 256) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ =
      VG.Proof.MlKem.Arm.Sample.accD (VG.Proof.MlKem.Arm.Sample.accD a (c₀.toNat + 256 * (c₁.toNat % 16))) (c₁.toNat / 16 + 16 * c₂.toNat) := by
  unfold sampleStepCap sampleStep
  rw [n_eq]
  by_cases h : a.length = 256
  · rw [ite_eq_left h]
    have e : ∀ d, VG.Proof.MlKem.Arm.Sample.accD a d = a := fun d => by unfold VG.Proof.MlKem.Arm.Sample.accD; rw [ite_eq_right (by omega)]
    rw [e, e]
  · rw [ite_eq_right h]
    have hl : a.length < 256 := by omega
    have e1 : VG.Proof.MlKem.Arm.Sample.accD a (c₀.toNat + 256 * (c₁.toNat % 16)) = (if c₀.toNat + 256 * (c₁.toNat % 16) < VG.Spec.MlKem.q then
        a ++ [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else a) := by
      unfold VG.Proof.MlKem.Arm.Sample.accD; simp only [hl, and_true]
    rw [e1]; rfl

/-- The loop's state, with the coefficients `L` sampled so far. -/
structure LS (s₀ : State) (L : List Zq) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s
  buf : Spec.Sha3.bytesAt s.mem (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 840) 840 = xof (VG.Proof.MlKem.Arm.Sample.B s₀) 840
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Sample.pa s₀ + BitVec.ofNat 32 (4 * L.length)
  r2 : s.gpr .r2 = BitVec.ofNat 32 L.length
  len : L.length ≤ 256
  coeff : ∀ k < L.length, coeffAt s.mem (VG.Proof.MlKem.Arm.Sample.A s₀) k = BitVec.ofNat 32 (L.getD k 0).val

/-- `Z` of the test of a candidate `d`, with `j` coefficients. -/
def accZ (d j : BitVec 32) : Bool := ((d - 3328 - 1) >>> 31 &&& (j - 256) >>> 31) - 0 == 0

theorem accZ_eq {d j : BitVec 32} (hd : d.toNat < 4096) (hj : j.toNat ≤ 256) :
    VG.Proof.MlKem.Arm.Sample.accZ d j = !decide (d.toNat < 3329 ∧ j.toNat < 256) := by
  unfold VG.Proof.MlKem.Arm.Sample.accZ
  by_cases h1 : d.toNat < 3329 <;> by_cases h2 : j.toNat < 256
  · have e1 : (d - 3328 - 1) >>> 31 = 1 := by bv_omega
    have e2 : (j - 256) >>> 31 = 1 := by bv_omega
    rw [e1, e2]; simp [h1, h2]
  · have e2 : (j - 256) >>> 31 = 0 := by bv_omega
    rw [e2]; simp [h1, h2]
  · have e1 : (d - 3328 - 1) >>> 31 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]
  · have e1 : (d - 3328 - 1) >>> 31 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]

/-- What a block of the loop keeps. -/
structure Keep (s s' : State) : Prop where
  r4 : s'.gpr .r4 = s.gpr .r4
  r5 : s'.gpr .r5 = s.gpr .r5
  r6 : s'.gpr .r6 = s.gpr .r6
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem keep_iff {s s' : State} : VG.Proof.MlKem.Arm.Sample.Keep s s' ↔ s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r5 = s.gpr .r5 ∧
    s'.gpr .r6 = s.gpr .r6 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨fun h => ⟨h.r4, h.r5, h.r6, h.mem, h.rd, h.wr, h.sp⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩⟩

theorem Keep.env {s₀ s s' : State} (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s) (hk : VG.Proof.MlKem.Arm.Sample.Keep s s') : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' := by
  refine ⟨hk.r4.trans h.r4, hk.r5.trans h.r5, hk.r6.trans h.r6, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, ?_, ?_, ?_⟩
  · rw [hk.mem]; exact h.sav
  · rw [hk.mem]; exact h.savlr
  · rw [hk.mem]; exact h.seed

theorem LS.keep {s₀ s s' : State} {L : List Zq} (h : VG.Proof.MlKem.Arm.Sample.LS s₀ L s) (hk : VG.Proof.MlKem.Arm.Sample.Keep s s') (h1 : s'.gpr .r1 = s.gpr .r1)
    (h2 : s'.gpr .r2 = s.gpr .r2) : VG.Proof.MlKem.Arm.Sample.LS s₀ L s' :=
  ⟨hk.env h.env, hk.mem ▸ h.buf, h1.trans h.r1, h2.trans h.r2, h.len, fun k hk' => hk.mem ▸ h.coeff k hk'⟩

/-- The first candidate of a chunk. -/
def cand1 (b₀ b₁ : Byte) : BitVec 32 := b₀.setWidth 32 + (b₁.setWidth 32 <<< 28) >>> 20

/-- The second candidate of a chunk. -/
def cand2 (b₁ b₂ : Byte) : BitVec 32 := b₁.setWidth 32 >>> 4 + b₂.setWidth 32 <<< 4

theorem cand1_toNat (b₀ b₁ : Byte) : (VG.Proof.MlKem.Arm.Sample.cand1 b₀ b₁).toNat = b₀.toNat + 256 * (b₁.toNat % 16) := by
  have := b₀.isLt; have := b₁.isLt
  unfold VG.Proof.MlKem.Arm.Sample.cand1
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat, setWidth32_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem cand2_toNat (b₁ b₂ : Byte) : (VG.Proof.MlKem.Arm.Sample.cand2 b₁ b₂).toNat = b₁.toNat / 16 + 16 * b₂.toNat := by
  have := b₁.isLt; have := b₂.isLt
  unfold VG.Proof.MlKem.Arm.Sample.cand2
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat, setWidth32_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

section
variable {s : State} {x j c d : BitVec 32}

theorem blk1_ok (h0 : s.gpr .r0 = x) (h2 : s.gpr .r2 = j)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 1)) 1)
    (i2 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 2)) 1) :
    WP isa (.block (candidates ++ acceptTest .r10)) s fun s' =>
      s'.gpr .r10 = VG.Proof.MlKem.Arm.Sample.cand1 (s.mem (State.addr (x + BitVec.ofNat 32 0))) (s.mem (State.addr (x + BitVec.ofNat 32 1))) ∧
      s'.gpr .r11 = VG.Proof.MlKem.Arm.Sample.cand2 (s.mem (State.addr (x + BitVec.ofNat 32 1))) (s.mem (State.addr (x + BitVec.ofNat 32 2))) ∧
      s'.z = VG.Proof.MlKem.Arm.Sample.accZ (VG.Proof.MlKem.Arm.Sample.cand1 (s.mem (State.addr (x + BitVec.ofNat 32 0))) (s.mem (State.addr (x + BitVec.ofNat 32 1)))) j ∧
      s'.gpr .r0 = x ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r2 = j ∧ s'.gpr .r3 = s.gpr .r3 ∧ VG.Proof.MlKem.Arm.Sample.Keep s s' := by
  run_block [candidates, acceptTest, VG.Proof.MlKem.Arm.Sample.cand1, VG.Proof.MlKem.Arm.Sample.cand2, VG.Proof.MlKem.Arm.Sample.accZ, h0, h2, i0, i1, i2, VG.Proof.MlKem.Arm.Sample.keep_iff, and_self, and_true]

theorem blk2_ok (h2 : s.gpr .r2 = j) (h11 : s.gpr .r11 = d) :
    WP isa (.block (acceptTest .r11)) s fun s' =>
      s'.z = VG.Proof.MlKem.Arm.Sample.accZ d j ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r2 = j ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r11 = d ∧ VG.Proof.MlKem.Arm.Sample.Keep s s' := by
  run_block [acceptTest, VG.Proof.MlKem.Arm.Sample.accZ, h2, h11, VG.Proof.MlKem.Arm.Sample.keep_iff, and_self, and_true]

theorem tail_ok (h0 : s.gpr .r0 = x) (h3 : s.gpr .r3 = c) :
    WP isa (.block [.dp .add .r0 .r0 (.imm 3), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      s'.gpr .r0 = x + 3 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.gpr .r2 = s.gpr .r2 ∧ VG.Proof.MlKem.Arm.Sample.Keep s s' := by
  run_block [h0, h3, VG.Proof.MlKem.Arm.Sample.keep_iff, and_self, and_true]

end

/-! ## Accepting a candidate -/

theorem SEnv.frameA {s₀ s s' : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s) (hf : Frame [polyRegion (VG.Proof.MlKem.Arm.Sample.A s₀)] s.mem s'.mem)
    (g4 : s'.gpr .r4 = s.gpr .r4) (g5 : s'.gpr .r5 = s.gpr .r5) (g6 : s'.gpr .r6 = s.gpr .r6)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' := by
  have hsv : ∀ r ∈ [polyRegion (VG.Proof.MlKem.Arm.Sample.A s₀)], (⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩ : Region).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr
    exact (hp.a_s.sub_right (VG.Proof.MlKem.Arm.Sample.s_sub (by decide))).symm
  refine ⟨g4.trans h.r4, g5.trans h.r5, g6.trans h.r6, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    fun i hi => ?_, ?_, ?_⟩
  · rw [hf.readW (r := ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩) ?_ hsv (by decide)]
    · exact h.sav i hi
    · simp only [Region.Contains]; bv_omega
  · rw [hf.readW (r := ⟨VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680, 36⟩) ?_ hsv (by decide)]
    · exact h.savlr
    · simp only [Region.Contains]; bv_omega
  · rw [bytesAt_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.seed_a)
      (by decide)]
    exact h.seed

theorem getD_append_single {L : List Zq} {x : Zq} {k : Nat} (hk : k < L.length + 1) :
    (L ++ [x]).getD k 0 = if k < L.length then L.getD k 0 else x := by
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), show k - L.length = 0 by omega]; rfl

theorem accept_ok {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {L : List Zq} (h : VG.Proof.MlKem.Arm.Sample.LS s₀ L s) {d : Reg} {v : BitVec 32} (hv : s.gpr d = v) (hv4 : v.toNat < 4096) (hz : s.z = VG.Proof.MlKem.Arm.Sample.accZ v (s.gpr .r2)) :
    WP isa (accept d) s fun s' => VG.Proof.MlKem.Arm.Sample.LS s₀ (VG.Proof.MlKem.Arm.Sample.accD L v.toNat) s' ∧ ∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r := by
  have hl := h.len
  have hj : (s.gpr .r2).toNat = L.length := by rw [h.r2]; exact toNat_ofNat32 (by omega)
  rw [VG.Proof.MlKem.Arm.Sample.accZ_eq hv4 (by omega), hj] at hz
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · -- rejected
    have hn : ¬ (v.toNat < 3329 ∧ L.length < 256) := by
      rw [e] at hz; intro hc; simp [hc] at hz
    have ea : VG.Proof.MlKem.Arm.Sample.accD L v.toNat = L := by unfold VG.Proof.MlKem.Arm.Sample.accD; rw [ite_eq_right (show ¬ (v.toNat < VG.Spec.MlKem.q ∧ L.length < 256) from hn)]
    rw [ea]
    exact WP.block_nil ⟨h, fun _ _ _ => rfl⟩
  · -- accepted
    have hy : v.toNat < 3329 ∧ L.length < 256 := by
      rw [e] at hz; simpa using hz
    have ea : VG.Proof.MlKem.Arm.Sample.accD L v.toNat = L ++ [ofNat v.toNat] := by
      unfold VG.Proof.MlKem.Arm.Sample.accD; rw [ite_eq_left (show v.toNat < VG.Spec.MlKem.q ∧ L.length < 256 from hy)]
    rw [ea]
    have fa := hp.fa
    have eA : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlKem.Arm.Sample.A s₀) L.length := by
      rw [h.r1]; exact addr_coeff fa (by omega) (by omega)
    have cA := coeff_contains (VG.Proof.MlKem.Arm.Sample.A s₀) (i := L.length) (by rw [n_eq]; omega)
    have iA : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 0)) 4 := by
      rw [eA, h.env.wr, hp.wr]; exact inRegions_of (by simp) cA
    have ho : (0 : Nat) < 4096 := by decide
    have hblk : WP isa (.block [.str d .r1 0, .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 1)]) s
        fun s' => s'.mem = s.mem.writeW (State.addr (s.gpr .r1 + BitVec.ofNat 32 0)) v ∧
          s'.gpr .r1 = s.gpr .r1 + 4 ∧ s'.gpr .r2 = s.gpr .r2 + 1 ∧
          (∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
      run_block [iA, ho, hv, and_self, and_true]
      exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2]⟩
    refine WP.mono hblk fun s' ⟨m, r1, r2, rr, rd, wr, sp⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rr⟩
    · refine h.env.frameA hp (by rw [m, eA]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cA)
        (rr _ (by decide) (by decide)) (rr _ (by decide) (by decide)) (rr _ (by decide) (by decide)) rd wr sp
    · rw [m, eA, bytesAt_writeW_sep _ _ _ (fun x h₁ h₂ => ?_) (by decide)]
      · exact h.buf
      · exact hp.a_s _ (cA.byte h₂) (VG.Proof.MlKem.Arm.Sample.s_sub (s₀ := s₀) (o := 840) (n := 840) (by decide) _
          (by simp only [Region.Contains]; omega))
    · rw [r1, h.r1, List.length_append, List.length_singleton]; exact ptr_succ _ 4 _
    · rw [r2, h.r2, List.length_append, List.length_singleton, BitVec.ofNat_add]; rfl
    · simp only [List.length_append, List.length_singleton]; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      rw [m, eA, coeffAt_writeW _ _ (by rw [n_eq]; omega) (by rw [n_eq]; omega), VG.Proof.MlKem.Arm.Sample.getD_append_single hk]
      by_cases e' : L.length = k
      · subst e'
        rw [ite_eq_left rfl, ite_eq_right (Nat.lt_irrefl _)]
        exact BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_ofNat, ofNat_of_lt (show v.toNat < VG.Spec.MlKem.q from hy.1), Nat.mod_eq_of_lt v.isLt])
      · rw [ite_eq_right e', ite_eq_left (by omega)]
        exact h.coeff k (by omega)

/-! ## An iteration -/

/-- The coefficients sampled from the first `t` chunks. -/
abbrev Ls (s₀ : State) (t : Nat) : List Zq := sampleAfter [] (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀)) t

/-- After `t` iterations. -/
structure Inv (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : VG.Proof.MlKem.Arm.Sample.LS s₀ (VG.Proof.MlKem.Arm.Sample.Ls s₀ t) s
  r0 : s.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 (840 + 3 * t)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (280 - t))

theorem buf_byte {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {L : List Zq} (h : VG.Proof.MlKem.Arm.Sample.LS s₀ L s) {t k : Nat} (ht : t < 280) (hk : k < 3) :
    State.addr (VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 (840 + 3 * t) + BitVec.ofNat 32 k) =
      VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 840 + BitVec.ofNat 64 (3 * t + k) ∧
    InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 840 + BitVec.ofNat 64 (3 * t + k)) 1 ∧
    s.mem (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 840 + BitVec.ofNat 64 (3 * t + k)) =
      VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t + k) := by
  have fs := hp.fs
  refine ⟨?_, ?_, ?_⟩
  · rw [ptr_add_add32, VG.Proof.MlKem.Arm.Sample.hS hp (by omega), add_ofNat_add, Nat.add_assoc]
  · rw [h.env.rd, h.env.wr, add_ofNat_add]
    exact inRegions_of (R := ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩) (List.mem_append_right _ (by rw [hp.wr]; simp))
      (contains_off (by omega) (by omega))
  · rw [← bytesAt_getD s.mem (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 840) (show 3 * t + k < 840 by omega), h.buf,
      VG.Proof.MlKem.xof_getD _ (by omega)]

theorem cand1_lt (b₀ b₁ : Byte) : (VG.Proof.MlKem.Arm.Sample.cand1 b₀ b₁).toNat < 4096 := by
  rw [VG.Proof.MlKem.Arm.Sample.cand1_toNat]; have := b₀.isLt; have := b₁.isLt; omega

theorem cand2_lt (b₁ b₂ : Byte) : (VG.Proof.MlKem.Arm.Sample.cand2 b₁ b₂).toNat < 4096 := by
  rw [VG.Proof.MlKem.Arm.Sample.cand2_toNat]; have := b₁.isLt; have := b₂.isLt; omega

theorem Ls_succ (s₀ : State) (t : Nat) (hl : (VG.Proof.MlKem.Arm.Sample.Ls s₀ t).length ≤ 256) :
    VG.Proof.MlKem.Arm.Sample.Ls s₀ (t + 1) = VG.Proof.MlKem.Arm.Sample.accD (VG.Proof.MlKem.Arm.Sample.accD (VG.Proof.MlKem.Arm.Sample.Ls s₀ t)
      (VG.Proof.MlKem.Arm.Sample.cand1 (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t)) (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t + 1))).toNat)
      (VG.Proof.MlKem.Arm.Sample.cand2 (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t + 1)) (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t + 2))).toNat := by
  rw [VG.Proof.MlKem.Arm.Sample.Ls, sampleAfter_succ, VG.Proof.MlKem.Arm.Sample.stepCap_eq hl, VG.Proof.MlKem.Arm.Sample.cand1_toNat, VG.Proof.MlKem.Arm.Sample.cand2_toNat]

/-- The candidates of chunk `t`. -/
abbrev D1 (s₀ : State) (t : Nat) : BitVec 32 :=
  VG.Proof.MlKem.Arm.Sample.cand1 (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t)) (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t + 1))
abbrev D2 (s₀ : State) (t : Nat) : BitVec 32 :=
  VG.Proof.MlKem.Arm.Sample.cand2 (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t + 1)) (VG.Proof.MlKem.xofByte (VG.Proof.MlKem.Arm.Sample.B s₀) (3 * t + 2))

/-- After the candidates of chunk `t` and the test of the first. -/
structure P1 (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : VG.Proof.MlKem.Arm.Sample.LS s₀ (VG.Proof.MlKem.Arm.Sample.Ls s₀ t) s
  r0 : s.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 (840 + 3 * t)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (280 - t))
  r10 : s.gpr .r10 = VG.Proof.MlKem.Arm.Sample.D1 s₀ t
  r11 : s.gpr .r11 = VG.Proof.MlKem.Arm.Sample.D2 s₀ t
  z : s.z = VG.Proof.MlKem.Arm.Sample.accZ (VG.Proof.MlKem.Arm.Sample.D1 s₀ t) (BitVec.ofNat 32 (VG.Proof.MlKem.Arm.Sample.Ls s₀ t).length)

/-- After the first candidate. -/
structure P2 (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : VG.Proof.MlKem.Arm.Sample.LS s₀ (VG.Proof.MlKem.Arm.Sample.accD (VG.Proof.MlKem.Arm.Sample.Ls s₀ t) (VG.Proof.MlKem.Arm.Sample.D1 s₀ t).toNat) s
  r0 : s.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 (840 + 3 * t)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (280 - t))
  r11 : s.gpr .r11 = VG.Proof.MlKem.Arm.Sample.D2 s₀ t

/-- After the test of the second candidate. -/
structure P3 (s₀ : State) (t : Nat) (s : State) : Prop where
  p2 : VG.Proof.MlKem.Arm.Sample.P2 s₀ t s
  z : s.z = VG.Proof.MlKem.Arm.Sample.accZ (VG.Proof.MlKem.Arm.Sample.D2 s₀ t) (BitVec.ofNat 32 (VG.Proof.MlKem.Arm.Sample.accD (VG.Proof.MlKem.Arm.Sample.Ls s₀ t) (VG.Proof.MlKem.Arm.Sample.D1 s₀ t).toNat).length)

/-- After the second candidate. -/
structure P4 (s₀ : State) (t : Nat) (s : State) : Prop where
  ls : VG.Proof.MlKem.Arm.Sample.LS s₀ (VG.Proof.MlKem.Arm.Sample.Ls s₀ (t + 1)) s
  r0 : s.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 (840 + 3 * t)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (280 - t))

theorem piece1 {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {t : Nat} (ht : t < 280) (h : VG.Proof.MlKem.Arm.Sample.Inv s₀ t s) :
    WP isa (.block (candidates ++ acceptTest .r10)) s (VG.Proof.MlKem.Arm.Sample.P1 s₀ t) := by
  obtain ⟨e0, i0, v0⟩ := VG.Proof.MlKem.Arm.Sample.buf_byte hp h.ls ht (k := 0) (by decide)
  obtain ⟨e1, i1, v1⟩ := VG.Proof.MlKem.Arm.Sample.buf_byte hp h.ls ht (k := 1) (by decide)
  obtain ⟨e2, i2, v2⟩ := VG.Proof.MlKem.Arm.Sample.buf_byte hp h.ls ht (k := 2) (by decide)
  rw [Nat.add_zero] at v0 e0
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.blk1_ok h.r0 h.ls.r2 (by rw [e0]; exact i0) (by rw [e1]; exact i1)
    (by rw [e2]; exact i2)) fun s₁ ⟨r10, r11, z1, r0, r1, r2, r3, k1⟩ => ?_
  simp only [e0, e1, e2, v0, v1, v2] at r10 r11 z1
  exact ⟨h.ls.keep k1 r1 (r2.trans h.ls.r2.symm), r0, r3.trans h.r3, r10, r11, z1⟩

theorem piece2 {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {t : Nat} (h : VG.Proof.MlKem.Arm.Sample.P1 s₀ t s) :
    WP isa (accept .r10) s (VG.Proof.MlKem.Arm.Sample.P2 s₀ t) :=
  WP.mono (VG.Proof.MlKem.Arm.Sample.accept_ok hp h.ls (d := .r10) h.r10 (VG.Proof.MlKem.Arm.Sample.cand1_lt _ _) (by rw [h.z, h.ls.r2]))
    fun _ ⟨ls, rr⟩ => ⟨ls, (rr .r0 (by decide) (by decide)).trans h.r0, (rr .r3 (by decide) (by decide)).trans h.r3,
      (rr .r11 (by decide) (by decide)).trans h.r11⟩

theorem piece3 {s₀ s : State} {t : Nat} (h : VG.Proof.MlKem.Arm.Sample.P2 s₀ t s) :
    WP isa (.block (acceptTest .r11)) s (VG.Proof.MlKem.Arm.Sample.P3 s₀ t) :=
  WP.mono (VG.Proof.MlKem.Arm.Sample.blk2_ok h.ls.r2 h.r11) fun _ ⟨z, r0, r1, r2, r3, r11, k⟩ =>
    ⟨⟨h.ls.keep k r1 (r2.trans h.ls.r2.symm), r0.trans h.r0, r3.trans h.r3, r11⟩, z⟩

theorem piece4 {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {t : Nat} (h : VG.Proof.MlKem.Arm.Sample.P3 s₀ t s) :
    WP isa (accept .r11) s (VG.Proof.MlKem.Arm.Sample.P4 s₀ t) :=
  WP.mono (VG.Proof.MlKem.Arm.Sample.accept_ok hp h.p2.ls (d := .r11) h.p2.r11 (VG.Proof.MlKem.Arm.Sample.cand2_lt _ _) (by rw [h.z, h.p2.ls.r2]))
    fun _ ⟨ls, rr⟩ => ⟨by rw [VG.Proof.MlKem.Arm.Sample.Ls_succ s₀ t (sampleAfter_length_le (by simp) _ t)]; exact ls,
      (rr .r0 (by decide) (by decide)).trans h.p2.r0, (rr .r3 (by decide) (by decide)).trans h.p2.r3⟩

theorem piece5 {s₀ s : State} {t : Nat} (ht : t < 280) (h : VG.Proof.MlKem.Arm.Sample.P4 s₀ t s) :
    WP isa (.block [.dp .add .r0 .r0 (.imm 3), .subs .r3 .r3 (.imm 1)]) s
      fun s' => VG.Proof.MlKem.Arm.Sample.Inv s₀ (t + 1) s' ∧ s'.z = decide (t + 1 = 280) :=
  WP.mono (VG.Proof.MlKem.Arm.Sample.tail_ok h.r0 h.r3) fun _ ⟨r0, r3, z, r1, r2, k⟩ =>
    ⟨⟨h.ls.keep k r1 r2, by
      rw [r0]; exact (ptr_add_add32 _ _ 3).trans (by rw [show 840 + 3 * t + 3 = 840 + 3 * (t + 1) by omega]),
      by rw [r3]; exact count_sub (k := 1) ht⟩, by rw [z]; exact count_z (k := 1) ht (by decide) (by decide)⟩

theorem body_ok {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) {t : Nat} (ht : t < 280) (h : VG.Proof.MlKem.Arm.Sample.Inv s₀ t s) :
    WP isa rejBody s fun s' => VG.Proof.MlKem.Arm.Sample.Inv s₀ (t + 1) s' ∧ s'.z = decide (t + 1 = 280) :=
  WP.seq (WP.mono (VG.Proof.MlKem.Arm.Sample.piece1 hp ht h) fun _ h₁ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.Sample.piece2 hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (VG.Proof.MlKem.Arm.Sample.piece3 h₂) fun _ h₃ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.Sample.piece4 hp h₃) fun _ h₄ => VG.Proof.MlKem.Arm.Sample.piece5 ht h₄))))

/-! ## The whole function -/

theorem init_ok {s₀ s : State} (h : VG.Proof.MlKem.Arm.Sample.SEnv s₀ s)
    (hb : Spec.Sha3.bytesAt s.mem (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 840) 840 = xof (VG.Proof.MlKem.Arm.Sample.B s₀) 840) :
    WP isa (.block [.dp .add .r0 .r6 (.imm 840), .mov .r1 (.reg .r5), .mov .r2 (.imm 0), .mov .r3 (.imm 280)]) s
      (VG.Proof.MlKem.Arm.Sample.Inv s₀ 0) := by
  have e5 := h.r5
  have e6 := h.r6
  have hk : WP isa (.block [.dp .add .r0 .r6 (.imm 840), .mov .r1 (.reg .r5), .mov .r2 (.imm 0),
      .mov .r3 (.imm 280)]) s fun s' => s'.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀ + 840 ∧ s'.gpr .r1 = VG.Proof.MlKem.Arm.Sample.pa s₀ ∧ s'.gpr .r2 = 0 ∧
        s'.gpr .r3 = 280 ∧ VG.Proof.MlKem.Arm.Sample.Keep s s' := by
    run_block [e5, e6, VG.Proof.MlKem.Arm.Sample.keep_iff, and_self, and_true]
  refine WP.mono hk fun s' ⟨r0, r1, r2, r3, k⟩ =>
    ⟨⟨k.env h, k.mem ▸ hb, ?_, ?_, by simp [VG.Proof.MlKem.Arm.Sample.Ls, sampleAfter], fun _ h => ?_⟩, ?_, ?_⟩
  · rw [r1]; simp [VG.Proof.MlKem.Arm.Sample.Ls, sampleAfter]
  · rw [r2]; simp [VG.Proof.MlKem.Arm.Sample.Ls, sampleAfter]
  · simp [VG.Proof.MlKem.Arm.Sample.Ls, sampleAfter] at h
  · rw [r0]; rfl
  · rw [r3]; rfl

theorem ret_val {n : Nat} (h : n ≤ 256) :
    BitVec.ofNat 32 n >>> 8 = if n = 256 then 1 else 0 := by
  have : n < 2 ^ 32 := by omega
  split
  · subst n; decide
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this, Nat.shiftRight_eq_div_pow]
    show n / 256 = 0
    omega

theorem end_ok {s₀ s : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) (h : VG.Proof.MlKem.Arm.Sample.Inv s₀ 280 s) :
    WP isa (.block sampleEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      s'.gpr .r0 = (if (VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).length = 256 then 1 else 0) ∧
      ∀ k < (VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).length, coeffAt s'.mem (VG.Proof.MlKem.Arm.Sample.A s₀) k = BitVec.ofNat 32 ((VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).getD k 0).val := by
  have fs := hp.fs
  have e2 := h.ls.r2
  have e6 := h.ls.env.r6
  rw [sampleEnd, List.append_assoc, WP.block_append_iff]
  have hk : WP isa (.block [.mov .r0 (.shifted .r2 .lsr 8), .mov .r3 (.reg .r6)]) s fun s' =>
      s'.gpr .r0 = BitVec.ofNat 32 (VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).length >>> 8 ∧ s'.gpr .r3 = VG.Proof.MlKem.Arm.Sample.pscr s₀ ∧
      s'.gpr .lr = s.gpr .lr ∧ VG.Proof.MlKem.Arm.Sample.Keep s s' := by
    run_block [e2, e6, VG.Proof.MlKem.Arm.Sample.keep_iff, and_self, and_true]
  refine WP.mono hk fun s₁ ⟨r0, r3, _, k₁⟩ => ?_
  have h₁ := k₁.env h.ls.env
  rw [WP.block_append_iff]
  have e3 : State.addr (s₁.gpr .r3) + BitVec.ofNat 64 1680 = VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 1680 := by rw [r3]
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 1680) (by decide)
    (by rw [r3]; exact fit_le (by decide) fs) (g := s₀.gpr) (by rw [e3]; exact h₁.sav)
    fun i hi => by
      rw [e3, h₁.rd, h₁.wr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩) (List.mem_append_right _ (by simp)) (contains_off (by omega) (by omega)))
    fun s₂ h₂ => ?_
  have g3 : s₂.gpr .r3 = VG.Proof.MlKem.Arm.Sample.pscr s₀ := by rw [h₂.other .r3 (by decide), r3]
  have i12 : InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 1712)) 4 := by
    rw [g3, VG.Proof.MlKem.Arm.Sample.hS hp (by decide), h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.wr]
    exact inRegions_of (R := ⟨VG.Proof.MlKem.Arm.Sample.S s₀, 2048⟩) (List.mem_append_right _ (by simp)) (contains_off (by omega) (by omega))
  have ho : 1712 < 4096 := by decide
  have hl : WP isa (.block [.ldr .lr .r3 1712]) s₂ fun s' =>
      s'.gpr .lr = s₂.mem.readW (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 1712)) 32 ∧
      (∀ r, r ≠ .lr → s'.gpr r = s₂.gpr r) ∧ s'.mem = s₂.mem ∧ s'.sp = s₂.sp := by
    run_block [i12, ho, and_self, and_true]
    exact ⟨trivial, fun r hr => by simp [hr]⟩
  refine WP.mono hl fun s' ⟨lr, rr, m, sp⟩ => ⟨fun r hr => ?_, ?_, ?_, fun k hk => ?_⟩
  · by_cases e : r = .lr
    · subst e
      rw [lr, g3, VG.Proof.MlKem.Arm.Sample.hS hp (by decide), h₂.mem]; exact h₁.savlr
    · have hs : ∀ r ∈ preserved, r ≠ .lr → ∃ i < 8, savedRegs.getD i .r4 = r := by decide
      obtain ⟨i, hi, rfl⟩ := hs r hr e
      rw [rr _ e]; exact h₂.loaded i hi
  · rw [sp, h₂.sp, h₁.sp]
  · rw [rr .r0 (by decide), h₂.other .r0 (by decide), r0, VG.Proof.MlKem.Arm.Sample.ret_val h.ls.len]
  · rw [m, h₂.mem, k₁.mem]; exact h.ls.coeff k hk

theorem correct {s₀ : State} (hp : VG.Proof.MlKem.Arm.Sample.Pre s₀) :
    WP isa sampleNTT s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .r0 = (if (VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).length = 256 then 1 else 0) ∧
      ∀ k < (VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).length, coeffAt s.mem (VG.Proof.MlKem.Arm.Sample.A s₀) k = BitVec.ofNat 32 ((VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).getD k 0).val := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Sample.setup_ok hp) fun s₁ ⟨h₁, hz⟩ => WP.seq ?_)
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.absorb_phase hp h₁ hz) fun s₂ ⟨h₂, hr, h0⟩ => WP.seq ?_
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.pad_phase hp h₂ hr h0) fun s₃ ⟨h₃, hst⟩ => WP.seq ?_
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.squeeze_phase hp h₃ hst) fun s₄ ⟨h₄, hb⟩ => WP.seq ?_
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.init_ok h₄ hb) fun s₅ h₅ => WP.seq ?_
  exact wp_loop_ne (VG.Proof.MlKem.Arm.Sample.Inv s₀) (N := 280) (by decide) (fun t ht s h => VG.Proof.MlKem.Arm.Sample.body_ok hp ht h)
    (fun s h => VG.Proof.MlKem.Arm.Sample.end_ok hp h) h₅

end VG.Proof.MlKem.Arm.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.SampleCT`. -/
section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_sample_ntt`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the stack
pointer and the seed, which the contract lets the function leak) leak the same
trace (`RelCT`), phase by phase: the blocks by the taint analysis, from
registers that hold pointers in both runs (`taint_block`); the calls of the
sponge functions by `absorb_ct`, …, from their arguments, which are the same
in both runs; and the loop of Algorithm 7 iteration by iteration, whose
branches are on the same values in both runs because the XOF output is the
same, being that of the same seed (`body_ct`). What each run is at each point
comes from the correctness proof (`RelCT.wp`).
-/

namespace VG.Proof.MlKem.Arm.Sample

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (stateAt)

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : VG.Proof.MlKem.Arm.Sample.Pre s₁
  hp₂ : VG.Proof.MlKem.Arm.Sample.Pre s₂
  sp : s₁.sp = s₂.sp
  seed : VG.Proof.MlKem.Arm.Sample.pseed s₁ = VG.Proof.MlKem.Arm.Sample.pseed s₂
  a : VG.Proof.MlKem.Arm.Sample.pa s₁ = VG.Proof.MlKem.Arm.Sample.pa s₂
  scr : VG.Proof.MlKem.Arm.Sample.pscr s₁ = VG.Proof.MlKem.Arm.Sample.pscr s₂
  B : VG.Proof.MlKem.Arm.Sample.B s₁ = VG.Proof.MlKem.Arm.Sample.B s₂

theorem taint_block {P : State → State → Prop} {is : List Instr} (rs : List Reg)
    (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hP a b hab)) h

theorem relct_wp {c : Prog isa} {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa P c fun _ _ => True) (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa P c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

section
variable {s₁ s₂ : State} (h : VG.Proof.MlKem.Arm.Sample.Two s₁ s₂)
include h

theorem Ls_eq (t : Nat) : VG.Proof.MlKem.Arm.Sample.Ls s₁ t = VG.Proof.MlKem.Arm.Sample.Ls s₂ t := by simp only [VG.Proof.MlKem.Arm.Sample.Ls, h.B]

theorem D1_eq (t : Nat) : VG.Proof.MlKem.Arm.Sample.D1 s₁ t = VG.Proof.MlKem.Arm.Sample.D1 s₂ t := by simp only [VG.Proof.MlKem.Arm.Sample.D1, h.B]

theorem D2_eq (t : Nat) : VG.Proof.MlKem.Arm.Sample.D2 s₁ t = VG.Proof.MlKem.Arm.Sample.D2 s₂ t := by simp only [VG.Proof.MlKem.Arm.Sample.D2, h.B]

/-! ## The loop -/

omit h in
/-- A candidate accepted or not, in both runs alike. -/
theorem accept_ct {d : Reg} (hd : d = .r10 ∨ d = .r11) {P : State → State → Prop} (hz : ∀ a b, P a b → a.z = b.z)
    (h1 : ∀ a b, P a b → a.gpr .r1 = b.gpr .r1) : RelCT isa P (accept d) fun _ _ => True := by
  refine RelCT.ite (fun a b hab => by show some a.z = some b.z; rw [hz a b hab]) ?_ ?_
  · exact VG.Proof.MlKem.Arm.Sample.taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
  · rcases hd with rfl | rfl
    · exact VG.Proof.MlKem.Arm.Sample.taint_block [.r1] (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact h1 a b hab.1) (by taint_decide)
    · exact VG.Proof.MlKem.Arm.Sample.taint_block [.r1] (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact h1 a b hab.1) (by taint_decide)

theorem body_ct {t : Nat} (ht : t < 280) :
    RelCT isa (fun a b => VG.Proof.MlKem.Arm.Sample.Inv s₁ t a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ t b) rejBody fun a b =>
      (VG.Proof.MlKem.Arm.Sample.Inv s₁ (t + 1) a ∧ a.z = decide (t + 1 = 280)) ∧ (VG.Proof.MlKem.Arm.Sample.Inv s₂ (t + 1) b ∧ b.z = decide (t + 1 = 280)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab => ⟨VG.Proof.MlKem.Arm.Sample.body_ok hp₁ ht hab.1, VG.Proof.MlKem.Arm.Sample.body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.P1 s₁ t a ∧ VG.Proof.MlKem.Arm.Sample.P1 s₂ t b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.Sample.piece1 hp₁ ht hab.1, VG.Proof.MlKem.Arm.Sample.piece1 hp₂ ht hab.2⟩) ?_
  · exact VG.Proof.MlKem.Arm.Sample.taint_block [.r0] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.r0, hab.2.r0, h.scr]) (by taint_decide)
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.P2 s₁ t a ∧ VG.Proof.MlKem.Arm.Sample.P2 s₂ t b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.Sample.piece2 hp₁ hab.1, VG.Proof.MlKem.Arm.Sample.piece2 hp₂ hab.2⟩) ?_
  · refine VG.Proof.MlKem.Arm.Sample.accept_ct (.inl rfl) (fun a b hab => by rw [hab.1.z, hab.2.z, VG.Proof.MlKem.Arm.Sample.D1_eq h, VG.Proof.MlKem.Arm.Sample.Ls_eq h]) fun a b hab => ?_
    rw [hab.1.ls.r1, hab.2.ls.r1, h.a, VG.Proof.MlKem.Arm.Sample.Ls_eq h]
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.P3 s₁ t a ∧ VG.Proof.MlKem.Arm.Sample.P3 s₂ t b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.Sample.piece3 hab.1, VG.Proof.MlKem.Arm.Sample.piece3 hab.2⟩) ?_
  · exact VG.Proof.MlKem.Arm.Sample.taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.P4 s₁ t a ∧ VG.Proof.MlKem.Arm.Sample.P4 s₂ t b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.Sample.piece4 hp₁ hab.1, VG.Proof.MlKem.Arm.Sample.piece4 hp₂ hab.2⟩) ?_
  · refine VG.Proof.MlKem.Arm.Sample.accept_ct (.inr rfl) (fun a b hab => by rw [hab.1.z, hab.2.z, VG.Proof.MlKem.Arm.Sample.D1_eq h, VG.Proof.MlKem.Arm.Sample.D2_eq h, VG.Proof.MlKem.Arm.Sample.Ls_eq h])
      fun a b hab => ?_
    rw [hab.1.p2.ls.r1, hab.2.p2.ls.r1, h.a, VG.Proof.MlKem.Arm.Sample.Ls_eq h, VG.Proof.MlKem.Arm.Sample.D1_eq h]
  · exact VG.Proof.MlKem.Arm.Sample.taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)

theorem loop_ct :
    RelCT isa (fun a b => VG.Proof.MlKem.Arm.Sample.Inv s₁ 0 a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ 0 b) (.loop rejBody .ne) fun a b =>
      VG.Proof.MlKem.Arm.Sample.Inv s₁ 280 a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ 280 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rejBody) (c := .ne)
    (Q := fun a b => VG.Proof.MlKem.Arm.Sample.Inv s₁ 280 a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ 280 b)
    (fun n a b => ∃ t, t < 280 ∧ n = 280 - t ∧ VG.Proof.MlKem.Arm.Sample.Inv s₁ t a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ t b) (fun n => ?_) 280)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 280 ∧ n = 280 - t ∧ VG.Proof.MlKem.Arm.Sample.Inv s₁ t a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 280
  · by_cases hn : n = 280 - t
    · refine RelCT.mono (P := fun a b => VG.Proof.MlKem.Arm.Sample.Inv s₁ t a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ t b) (VG.Proof.MlKem.Arm.Sample.body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 280 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 280 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨280 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The sponge -/

theorem absorbPhase_ct :
    RelCT isa (fun a b => (VG.Proof.MlKem.Arm.Sample.SEnv s₁ a ∧ stateAt a.mem (VG.Proof.MlKem.Arm.Sample.S s₁) = Spec.Sha3.zero) ∧
      (VG.Proof.MlKem.Arm.Sample.SEnv s₂ b ∧ stateAt b.mem (VG.Proof.MlKem.Arm.Sample.S s₂) = Spec.Sha3.zero)) (.seq (.block absorbSeedArgs) absorbCall)
      fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' ∧ s'.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧ s'.gpr .r3 = VG.Proof.MlKem.Arm.Sample.pseed s₀ ∧
    s'.gpr .r12 = BitVec.ofNat 32 34 ∧ s'.gpr .lr = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), VG.Proof.MlKem.Arm.Sample.SEnv s₀ s → WP isa (.block absorbSeedArgs) s (F s₀) := fun s₀ s hs =>
    WP.mono (VG.Proof.MlKem.Arm.Sample.absorbSeedArgs_ok hs.r4 hs.r6) fun _ ⟨hr, g0, g1, g2, g3, g12, glr⟩ =>
      ⟨hr.env hs, g0, g1, g2, g3, g12, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1, hw _ _ hab.2.1⟩) (absorb_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, a12, alr⟩, ⟨e₂, b0, b1, b2, b3, b12, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, _, VG.Proof.MlKem.Arm.Sample.absorb_args hp₁ e₁ a0 a1 a2 a3 a12 alr, by
      have := VG.Proof.MlKem.Arm.Sample.absorb_args hp₂ e₂ b0 b1 b2 b3 b12 blr
      rwa [← h.scr, ← h.seed] at this⟩)
  exact VG.Proof.MlKem.Arm.Sample.taint_block [.r4, .r6] (fun a b hab r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hab.1.1.r4, hab.2.1.r4, h.seed]
    · rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

theorem padPhase_ct :
    RelCT isa (fun a b => (VG.Proof.MlKem.Arm.Sample.SEnv s₁ a ∧ Spec.Sha3.Repr a.mem (VG.Proof.MlKem.Arm.Sample.S s₁) 168 (VG.Proof.MlKem.Arm.Sample.B s₁) ∧ (a.gpr .r0).toNat = 34) ∧
      (VG.Proof.MlKem.Arm.Sample.SEnv s₂ b ∧ Spec.Sha3.Repr b.mem (VG.Proof.MlKem.Arm.Sample.S s₂) 168 (VG.Proof.MlKem.Arm.Sample.B s₂) ∧ (b.gpr .r0).toNat = 34))
      (.seq (.block padArgs) padCall) fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' ∧ s'.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 34 ∧ s'.gpr .r3 = BitVec.ofNat 32 0x1f ∧
    s'.gpr .lr = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), VG.Proof.MlKem.Arm.Sample.SEnv s₀ s → (s.gpr .r0).toNat = 34 → WP isa (.block padArgs) s (F s₀) :=
    fun s₀ s hs h0 => WP.mono (VG.Proof.MlKem.Arm.Sample.padArgs_ok (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hs.r6)
      fun _ ⟨hr, g0, g1, g2, g3, glr⟩ => ⟨hr.env hs, g0, g1, g2, g3, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1 hab.1.2.2, hw _ _ hab.2.1 hab.2.2.2⟩) (pad_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, alr⟩, ⟨e₂, b0, b1, b2, b3, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, VG.Proof.MlKem.Arm.Sample.pad_args hp₁ e₁ a0 a1 a2 a3 alr, by
      have := VG.Proof.MlKem.Arm.Sample.pad_args hp₂ e₂ b0 b1 b2 b3 blr
      rwa [← h.scr] at this⟩)
  exact VG.Proof.MlKem.Arm.Sample.taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

theorem squeezePhase_ct :
    RelCT isa (fun a b => (VG.Proof.MlKem.Arm.Sample.SEnv s₁ a ∧ stateAt a.mem (VG.Proof.MlKem.Arm.Sample.S s₁) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (VG.Proof.MlKem.Arm.Sample.B s₁)) ∧
      (VG.Proof.MlKem.Arm.Sample.SEnv s₂ b ∧ stateAt b.mem (VG.Proof.MlKem.Arm.Sample.S s₂) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (VG.Proof.MlKem.Arm.Sample.B s₂)))
      (.seq (.block squeezeArgs) squeezeCall) fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => VG.Proof.MlKem.Arm.Sample.SEnv s₀ s' ∧ s'.gpr .r0 = VG.Proof.MlKem.Arm.Sample.pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
    s'.gpr .r3 = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 840 ∧ s'.gpr .r12 = BitVec.ofNat 32 840 ∧
    s'.gpr .lr = VG.Proof.MlKem.Arm.Sample.pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), VG.Proof.MlKem.Arm.Sample.SEnv s₀ s → WP isa (.block squeezeArgs) s (F s₀) := fun s₀ s hs =>
    WP.mono (VG.Proof.MlKem.Arm.Sample.squeezeArgs_ok hs.r6) fun _ ⟨hr, g0, g1, g2, g3, g12, glr⟩ => ⟨hr.env hs, g0, g1, g2, g3, g12, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1, hw _ _ hab.2.1⟩) (squeeze_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, a12, alr⟩, ⟨e₂, b0, b1, b2, b3, b12, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, _, VG.Proof.MlKem.Arm.Sample.squeeze_args hp₁ e₁ a0 a1 a2 a3 a12 alr, by
      have := VG.Proof.MlKem.Arm.Sample.squeeze_args hp₂ e₂ b0 b1 b2 b3 b12 blr
      rwa [← h.scr] at this⟩)
  exact VG.Proof.MlKem.Arm.Sample.taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

/-! ## The whole function -/

/-- What holds after each phase, in one run. -/
abbrev E1 (s₀ s : State) : Prop := VG.Proof.MlKem.Arm.Sample.SEnv s₀ s ∧ stateAt s.mem (VG.Proof.MlKem.Arm.Sample.S s₀) = Spec.Sha3.zero
abbrev E2 (s₀ s : State) : Prop := VG.Proof.MlKem.Arm.Sample.SEnv s₀ s ∧ Spec.Sha3.Repr s.mem (VG.Proof.MlKem.Arm.Sample.S s₀) 168 (VG.Proof.MlKem.Arm.Sample.B s₀) ∧ (s.gpr .r0).toNat = 34
abbrev E3 (s₀ s : State) : Prop :=
  VG.Proof.MlKem.Arm.Sample.SEnv s₀ s ∧ stateAt s.mem (VG.Proof.MlKem.Arm.Sample.S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (VG.Proof.MlKem.Arm.Sample.B s₀)
abbrev E4 (s₀ s : State) : Prop :=
  VG.Proof.MlKem.Arm.Sample.SEnv s₀ s ∧ Spec.Sha3.bytesAt s.mem (VG.Proof.MlKem.Arm.Sample.S s₀ + BitVec.ofNat 64 840) 840 = xof (VG.Proof.MlKem.Arm.Sample.B s₀) 840

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) sampleNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.E1 s₁ a ∧ VG.Proof.MlKem.Arm.Sample.E1 s₂ b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨by rw [hab.1]; exact VG.Proof.MlKem.Arm.Sample.setup_ok hp₁, by rw [hab.2]; exact VG.Proof.MlKem.Arm.Sample.setup_ok hp₂⟩) ?_
  · exact VG.Proof.MlKem.Arm.Sample.taint_block [.r0, .r1, .r2] (fun a b hab r hr => by
      rw [hab.1, hab.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.seed
      · exact h.a
      · exact h.scr) (by taint_decide)
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.E2 s₁ a ∧ VG.Proof.MlKem.Arm.Sample.E2 s₂ b) (VG.Proof.MlKem.Arm.Sample.relct_wp (VG.Proof.MlKem.Arm.Sample.absorbPhase_ct h) fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.Sample.absorb_phase hp₁ hab.1.1 hab.1.2, VG.Proof.MlKem.Arm.Sample.absorb_phase hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.E3 s₁ a ∧ VG.Proof.MlKem.Arm.Sample.E3 s₂ b) (VG.Proof.MlKem.Arm.Sample.relct_wp (VG.Proof.MlKem.Arm.Sample.padPhase_ct h) fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.Sample.pad_phase hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, VG.Proof.MlKem.Arm.Sample.pad_phase hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.E4 s₁ a ∧ VG.Proof.MlKem.Arm.Sample.E4 s₂ b) (VG.Proof.MlKem.Arm.Sample.relct_wp (VG.Proof.MlKem.Arm.Sample.squeezePhase_ct h) fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.Sample.squeeze_phase hp₁ hab.1.1 hab.1.2, VG.Proof.MlKem.Arm.Sample.squeeze_phase hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.Inv s₁ 0 a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ 0 b) (VG.Proof.MlKem.Arm.Sample.relct_wp ?_ fun a b hab =>
    ⟨VG.Proof.MlKem.Arm.Sample.init_ok hab.1.1 hab.1.2, VG.Proof.MlKem.Arm.Sample.init_ok hab.2.1 hab.2.2⟩) ?_
  · exact VG.Proof.MlKem.Arm.Sample.taint_block [.r5, .r6] (fun a b hab r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1.r5, hab.2.1.r5, h.a]
      · rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)
  refine RelCT.seq (R := fun a b => VG.Proof.MlKem.Arm.Sample.Inv s₁ 280 a ∧ VG.Proof.MlKem.Arm.Sample.Inv s₂ 280 b) (VG.Proof.MlKem.Arm.Sample.loop_ct h) ?_
  exact VG.Proof.MlKem.Arm.Sample.taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.ls.env.r6, hab.2.ls.env.r6, h.scr]) (by taint_decide)

end

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.sampleNTTContract Arm.abi 8).pre s) : VG.Proof.MlKem.Arm.Sample.Pre s := by
  sig_pre [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem polyAt_toPoly {m : Mem} {p : Addr} {L : List Zq} (hl : L.length = n)
    (h : ∀ k < L.length, coeffAt m p k = BitVec.ofNat 32 (L.getD k 0).val) :
    PolyIs m p (VG.Proof.MlKem.toPoly L) := by
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [h i (by rw [hl]; exact hi), getElem!_eq _ hi]
  simp only [VG.Proof.MlKem.toPoly, Vector.getElem_ofFn]

theorem post_of {s₀ s : State}
    (h0 : s.gpr .r0 = (if (VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).length = 256 then 1 else 0))
    (hc : ∀ k < (VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).length, coeffAt s.mem (VG.Proof.MlKem.Arm.Sample.A s₀) k = BitVec.ofNat 32 ((VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).getD k 0).val) :
    (Spec.MlKem.sampleNTTContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  by_cases hl : (VG.Proof.MlKem.Arm.Sample.Ls s₀ 280).length = 256
  · rw [ite_eq_left hl]
    have hpi := VG.Proof.MlKem.Arm.Sample.polyAt_toPoly (by rw [n_eq]; exact hl) hc
    refine ⟨fun _ => hpi.1, VG.Proof.MlKem.outcome_of_min (.inl ⟨rfl, ?_⟩)⟩
    have e2 : polyAt s.mem (BitVec.setWidth 64 (s₀.gpr .r1)) = _ := hpi.2
    rw [e2]
    exact VG.Proof.MlKem.sampleNTT_of_full (Nat.le_refl _) (by rw [n_eq]; exact hl)
  · rw [ite_eq_right hl]
    refine ⟨fun e => absurd e (by decide : (0 : BitVec 32) ≠ 1), VG.Proof.MlKem.outcome_of_min (.inr ⟨rfl, ?_⟩)⟩
    exact VG.Proof.MlKem.sampleNTT_none (by rw [n_eq]; exact hl)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.sampleNTT (Spec.MlKem.sampleNTTContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · have hp := VG.Proof.MlKem.Arm.Sample.pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h0, hc⟩ := VG.Proof.MlKem.Arm.Sample.correct hp
    exact ⟨t, s', he, ⟨hpres, hsp⟩, VG.Proof.MlKem.Arm.Sample.post_of h0 hc⟩
  · have hp₁ := VG.Proof.MlKem.Arm.Sample.pre_of h₁
    have hp₂ := VG.Proof.MlKem.Arm.Sample.pre_of h₂
    sig_pub [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2⟩ := hpub
    have two : VG.Proof.MlKem.Arm.Sample.Two s₁ s₂ := ⟨hp₁, hp₂, hsp, h0, h1, h2,
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩
    exact (VG.Proof.MlKem.Arm.Sample.all_ct two s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlKem.Arm.Sample.satState, ?_⟩
    sig_sat_check [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem.Arm.Sample

end
