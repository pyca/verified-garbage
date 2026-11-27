module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic

/-! ### `MlDsa.Arm.Round.NormLt`, which the modules that import this one used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_norm_lt`

The loop body is symbolically executed once for any state (`body_ok`): a
coefficient `a` is bad when `bound ≤ a` and `bound ≤ q - a` (the carries of
the two comparisons), and `r4` becomes 1 at the first bad one (`acc`); the
result `1 - r4` is 1 exactly when no coefficient is bad, that is when the norm
is less than `bound` (`normRq_lt`, `normZq_lt`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Round.NormLt

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round VG.Proof.MlDsa.Arm.Round
open VG.Spec.MlDsa (q n Poly Zq normRq normZq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced)
open VG.Proof.MlDsa.Arm.Arith (Entry wp_saving ct_of_saving preserved_of_saving Qw loadQ_val)

/-! ## The body -/

/-- 1 if the coefficient `a` is bad for the bound `b`, 0 otherwise. -/
def bad (a b : BitVec 32) : BitVec 32 :=
  (if b.toNat ≤ a.toNat then 1 else 0) &&& (if b.toNat ≤ (Qw - a).toNat then 1 else 0)

section
variable {s : State} {x b c v : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = b) (h2 : s.gpr .r2 = c)
  (h4 : s.gpr .r4 = v) (iF : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h4 iF

theorem body_ok :
    WP isa (.block nlBody) s fun s' =>
      s'.gpr .r4 = v ||| bad (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32) b ∧ s'.gpr .r0 = x + 4 ∧
      s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ s'.mem = s.mem ∧
      (∀ r ∈ [Reg.r1, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [nlBody, bad, loadQ_val, h0, h1, h2, h4, iF, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_self, and_true]
  have z : ∀ y : BitVec 32, (0 : BitVec 32) + 0 + y = y := fun y => by bv_omega
  simp only [decide_eq_true_eq, z]

end

/-- Whether coefficient `a` has `‖a‖∞ < b`. -/
abbrev Ok (a b : BitVec 32) : Prop := a.toNat < b.toNat ∨ q - a.toNat < b.toNat

theorem bad_eq {a : BitVec 32} (ha : a.toNat < q) (b : BitVec 32) :
    bad a b = if Ok a b then 0 else 1 := by
  have e : (Qw - a).toNat = q - a.toNat := by rw [q_eq] at *; bv_omega
  unfold bad Ok
  rw [e]
  by_cases h1 : b.toNat ≤ a.toNat <;> by_cases h2 : b.toNat ≤ q - a.toNat <;>
    simp only [h1, h2, ite_true, ite_false] <;>
    first
    | (rw [ite_eq_right (by omega)]; decide)
    | (rw [ite_eq_left (by omega_arith)]; decide)

/-- The accumulator after the first `i` coefficients of `m` at `F`. -/
def acc (m : Mem) (F : Addr) (b : BitVec 32) (i : Nat) : BitVec 32 :=
  if ∀ k < i, Ok (coeffAt m F k) b then 0 else 1

theorem acc_succ (m : Mem) (F : Addr) (b : BitVec 32) (i : Nat) :
    acc m F b i ||| (if Ok (coeffAt m F i) b then 0 else 1) = acc m F b (i + 1) := by
  have H : (∀ k < i + 1, Ok (coeffAt m F k) b) ↔ (∀ k < i, Ok (coeffAt m F k) b) ∧ Ok (coeffAt m F i) b :=
    ⟨fun h => ⟨fun k hk => h k (by omega_using [hk]), h i (by omega_using [])⟩, fun ⟨h, h'⟩ k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      exacts [h k hk, h']⟩
  unfold acc
  by_cases h : ∀ k < i, Ok (coeffAt m F k) b <;> by_cases h' : Ok (coeffAt m F i) b <;>
    simp only [H, h', and_true, and_false, ite_true, ite_false] <;>
    first | (rw [ite_eq_left h]; decide) | (rw [ite_eq_right h]; decide)

/-! ## The loop -/

/-- The precondition, on entry. -/
structure PreE (s : State) : Prop where
  sp : 4 ≤ s.sp.toNat
  rd : s.rd = [pR (P s .r0)]
  wr : s.wr = []
  s0 : (belowA s.sp 4).Disjoint (pR (P s .r0))
  f0 : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (P s .r0)

theorem pre_of {s : State} (h : (Proof.MlDsa.normLtContract Arm.abi 4).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The registers the loop keeps. -/
abbrev fixedR : List Reg := [.r1, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem loop {s s₁ : State} (hp : PreE s) (hE : Entry 4 s s₁) {s₂ : State} (hg : ∀ r, r ≠ .r4 → s₂.gpr r = s₁.gpr r)
    (h4 : s₂.gpr .r4 = 0) (hm : s₂.mem = s₁.mem) (hrd : s₂.rd = s₁.rd) (_hwr : s₂.wr = s₁.wr) (hsp : s₂.sp = s₁.sp) :
    WP isa (mapLoop .r2 nlBody) s₂ fun s' => (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧
      s'.mem = s₁.mem ∧ s'.gpr .r4 = acc s.mem (P s .r0) (s.gpr .r1) 256 := by
  have g0 : s₂.gpr .r0 = s.gpr .r0 := (hg .r0 (by decide)).trans (congrFun hE.gpr _)
  have e : P s₂ .r0 = P s .r0 := by simp only [P, g0]
  have hL : Layout s₂ [.r0] [] := ⟨fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'; rw [hrd, hE.rd, e, hp.rd]; simp,
    fun _ h => (List.not_mem_nil h).elim, fun _ _ _ h => (List.not_mem_nil h).elim, List.Pairwise.nil,
    fun p hp' => by simp only [List.append_nil, List.mem_singleton] at hp'; subst hp'; rw [g0]; exact hp.f0⟩
  have eT : ∀ k < 256, coeffAt s₂.mem (P s₂ .r0) k = coeffAt s.mem (P s .r0) k := fun k hk => by
    rw [e, hm]
    exact coeffAt_frame hE.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.s0.symm) (by rw [n_eq]; exact hk)
  refine WP.mono (loop_ok (ptrs := [.r0]) (fixed := fixedR) (V := fun _ _ => 0)
    (J := fun i s' => s'.gpr .r4 = acc s.mem (P s .r0) (s.gpr .r1) i) hL (by decide) (by decide)
    (fun s' hs' _ => by
      rw [hs']; simp only [show Reg.r4 ≠ Reg.r2 by decide, ite_false, h4]
      unfold acc; rw [ite_eq_left fun k hk => absurd hk (Nat.not_lt_zero k)])
    fun i hi s' hI => ?_)
    fun s' hI => ⟨fun r hr => (hI.fixed r hr).trans ((hg r (by revert r; decide)).trans (congrFun hE.gpr r)),
      hI.sp.trans hsp, ?_, hI.j⟩
  · have g1 : s'.gpr .r1 = s.gpr .r1 :=
      (hI.fixed .r1 (by decide)).trans ((hg .r1 (by decide)).trans (congrFun hE.gpr _))
    refine WP.mono (body_ok rfl g1 rfl hI.j (hI.inR hL hi (by simp) (by simp)))
      fun s'' ⟨r4, r0, r2, hz, hm', hf, rd, wr, sp⟩ => ⟨by rw [hm']; rfl, ?_, r2, hz, hf, rd, wr, sp, ?_⟩
    · intro p hp'; simp only [List.mem_singleton] at hp'; subst hp'; exact r0
    · show s''.gpr .r4 = _
      rw [r4, hI.read hL hi (by simp) (by simp), eT i hi, bad_eq (hp.red i (by rw [n_eq]; exact hi)), acc_succ]
  · have := hI.frame; simp only [List.map_nil] at this
    funext x; rw [← hm]; exact this x (fun _ h => (List.not_mem_nil h).elim)

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Round.normLt s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.gpr .r0 = if normRq [polyAt s.mem (P s .r0)] < (s.gpr .r1).toNat then 1 else 0 := by
  refine WP.mono (wp_saving [.r4] _ (W := [])
    (fun s₂ => (∀ r ∈ fixedR, s₂.gpr r = s.gpr r) ∧
      s₂.gpr .r0 = if normRq [polyAt s.mem (P s .r0)] < (s.gpr .r1).toNat then 1 else 0)
    s hp.sp (fun _ h => (List.not_mem_nil h).elim) (fun _ _ _ _ q => q) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, h0⟩, _, _, hsp, _, hg⟩ =>
      ⟨preserved_of_saving hg fun r hr hn => hk r (by revert r; decide), hsp, by rw [hg .r0]; exact h0⟩
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine WP.seq (WP.mono (loop hp hE (s₂ := s₁.setReg .r4 0) (fun r hr => by simp [State.setReg, hr])
    (by simp [State.setReg]) rfl rfl rfl rfl) fun s₃ ⟨hf, hsp, hm, h4⟩ => ?_)
  run_block [h4]
  refine ⟨fun x _ => by rw [hm], fun r hr => ?_, ?_⟩
  · have : r ≠ .r0 := by revert r; decide
    rw [ite_eq_right this, ite_eq_right this]; exact hf r hr
  · have hn := normRq_lt (polyAt s.mem (P s .r0)) (s.gpr .r1).toNat
    unfold acc
    by_cases h : ∀ k < 256, Ok (coeffAt s.mem (P s .r0) k) (s.gpr .r1)
    · rw [ite_eq_left h, ite_eq_left (hn.mpr fun i hi => ?_)]
      · rfl
      · rw [normZq_lt, polyAt_val hp.red hi]; exact h i (by rw [n_eq] at hi; exact hi)
    · rw [ite_eq_right h, ite_eq_right fun h' => h fun k hk => ?_]
      · rfl
      · have := (normZq_lt _ _).mp (hn.mp h' k (by rw [n_eq]; exact hk))
        rwa [polyAt_val hp.red (by rw [n_eq]; exact hk)] at this

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Round.normLt (Proof.MlDsa.normLtContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, ct_of_saving [.r4] _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32, h]
    rfl
  · sig_pub [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h0
    · simpa using h1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Round.NormLt

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_sample_in_ball`, constant time but for `c̃`, and `Verified`

Two runs whose `c̃` (the declared leak), `len`, `τ`, pointers and stack
pointer agree (`Two`) leak the same: the prologue by `relct_ldrSp` (the load
of `scratch` from the stack) and the taint analysis, the sponge by
`sponge_ct`, the blocks around the loop by the taint analysis, and the loop,
whose branches and addresses depend on the SHAKE256 output, by relating the
two runs iteration by iteration (`body_ct`): both are at the same iteration
with the same `i`, sign bits and byte `j` (being those of the same output), so
each branch goes the same way, and each piece between the branches is constant
time in registers that hold the same values in both runs.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sample.Ball

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n ofInt toRq)
open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Spec.Sha3 (bytesAt)
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne)

/-! ## Blocks -/

/-- A block in two parts. -/
theorem relct_append {P R Q : State → State → Prop} {l₁ l₂ : List Instr} (h₁ : RelCT isa P (.block l₁) R)
    (h₂ : RelCT isa R (.block l₂) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff, execBlock_append] at e₁ e₂
  obtain ⟨⟨u₁, v₁⟩, a₁, e₁⟩ := Option.bind_eq_some_iff.mp e₁
  obtain ⟨⟨w₁, x₁⟩, b₁, e₁⟩ := Option.map_eq_some_iff.mp e₁
  obtain ⟨⟨u₂, v₂⟩, a₂, e₂⟩ := Option.bind_eq_some_iff.mp e₂
  obtain ⟨⟨w₂, x₂⟩, b₂, e₂⟩ := Option.map_eq_some_iff.mp e₂
  obtain ⟨rfl, r⟩ := h₁ _ _ _ _ _ _ hp (.block a₁) (.block a₂)
  obtain ⟨rfl, q⟩ := h₂ _ _ _ _ _ _ r (.block b₁) (.block b₂)
  cases e₁; cases e₂
  exact ⟨rfl, q⟩

/-- The load of an argument from the stack leaks its address. -/
theorem relct_ldrSp {P : State → State → Prop} {t : Reg} {off : Nat} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block [.ldrSp t off]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  have tr : ∀ {s s' : State} {tr : List Leak}, execBlock isa [.ldrSp t off] s = some (s', tr) →
      tr = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 off))] := fun {s s' tr} e => by
    simp only [execBlock] at e
    split at e
    · cases e
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.2]; rfl
  rw [tr e₁, tr e₂, hsp _ _ hp]
  exact ⟨rfl, trivial⟩

theorem ldrSp_ok (σ : State) (hin : InRegions (σ.rd ++ σ.wr) (stackArgAddr σ 0) 4) :
    WP isa (.block [.ldrSp .r12 0]) σ fun s => s = σ.setReg .r12 (stackArg σ 0) := by
  have hin' : InRegions (σ.rd ++ σ.wr) (State.addr (σ.sp + BitVec.ofNat 32 0)) 4 := hin
  have o0 : (0 : Nat) < 4096 := by decide
  apply WP.of_runBlock
  rw [runBlock_cons]
  simp only [exec, o0, ite_true, State.load32, hin', Option.map_some, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

/-! ## Two runs -/

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : Pre σ₁
  p₂ : Pre σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  scr : stackArg σ₁ 0 = stackArg σ₂ 0
  B : B σ₁ = B σ₂

section
variable {σ₁ σ₂ : State} (two : Two σ₁ σ₂)
include two

theorem Two.P_eq : spOf σ₁ = spOf σ₂ := by simp only [spOf, two.r0, two.r1, two.r2, two.r3, two.scr]
theorem Two.X_eq : X σ₁ = X σ₂ := by simp only [X, two.B]
theorem Two.tau_eq : tau σ₁ = tau σ₂ := by simp only [tau, two.r2]
theorem Two.St_eq (t : Nat) : St σ₁ t = St σ₂ t := by simp only [St, i0, two.X_eq, two.tau_eq]
theorem Two.Xb_eq (t : Nat) : Xb σ₁ t = Xb σ₂ t := by simp only [Xb, two.X_eq]
theorem Two.Wn_eq : Wn σ₁ = Wn σ₂ := by simp only [Wn, two.X_eq]

/-- The sign bits not yet used, in both runs. -/
theorem Two.sg_eq {i : Nat} {a b : State} (ha : Sg σ₁ i a) (hb : Sg σ₂ i b) :
    a.gpr .r1 = b.gpr .r1 ∧ a.gpr .r4 = b.gpr .r4 := by
  have ha' : (a.gpr .r1).toNat + 2 ^ 32 * (a.gpr .r4).toNat = Wn σ₁ / 2 ^ (i - i0 σ₁) := ha
  have hb' : (b.gpr .r1).toNat + 2 ^ 32 * (b.gpr .r4).toNat = Wn σ₂ / 2 ^ (i - i0 σ₂) := hb
  rw [← two.Wn_eq, show i0 σ₂ = i0 σ₁ by simp only [i0, two.tau_eq]] at hb'
  have := (a.gpr .r1).isLt; have := (b.gpr .r1).isLt
  exact ⟨BitVec.eq_of_toNat_eq (by omega_arith), BitVec.eq_of_toNat_eq (by omega_arith)⟩

/-! ## The loop -/

omit two in
theorem pieceA_ct {t : Nat} : RelCT isa (fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) (.block jFull)
    fun a b => M1 σ₁ t a ∧ M1 σ₂ t b :=
  relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by native_taint_decide))
    fun a b h => ⟨pieceA h.1, pieceA h.2⟩

theorem tryA_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => (M1 σ₁ t a ∧ M1 σ₂ t b) ∧ isa.eval .eq a = some false)
      (.block [.ldrb .r8 .r0 0, .dp .sub .r11 .r2 (.reg .r8), .mov .r11 (.shifted .r11 .lsr 31),
        .cmp .r11 (.imm 0)]) fun a b => T1 σ₁ t a ∧ T1 σ₂ t b := by
  refine relW (taintRel [.r0] (fun a b h r hr => ?_) (by native_taint_decide)) fun a b h => ?_
  · rw [List.mem_singleton] at hr; subst hr
    rw [h.1.1.bat.r0, h.1.2.bat.r0, two.scr]
  · have za : a.z = false := Option.some.inj h.2
    have zb : b.z = false := by
      rw [h.1.2.z, ← two.St_eq, ← h.1.1.z]; exact za
    exact ⟨tryA two.p₁.ok ht h.1.1 za, tryA two.p₂.ok ht h.1.2 zb⟩

theorem set_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => (T1 σ₁ t a ∧ T1 σ₂ t b) ∧ isa.eval .eq a = some true) bSet
      fun a b => M2 σ₁ t a ∧ M2 σ₂ t b := by
  refine relW (taintRel [.r1, .r2, .r4, .r5, .r8] (fun a b h r hr => ?_) (by native_taint_decide)) fun a b h => ?_
  · have l₁ := h.1.1.bat
    have l₂ := h.1.2.bat
    have sg := two.sg_eq (two.St_eq t ▸ l₁.sg) l₂.sg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact sg.1
    · rw [l₁.r2, l₂.r2, two.St_eq]
    · exact sg.2
    · rw [l₁.env.r5, l₂.env.r5, two.P_eq]
    · rw [h.1.1.r8, h.1.2.r8, two.Xb_eq]
  · have za : a.z = true := Option.some.inj h.2
    have zb : b.z = true := by
      rw [h.1.2.z, ← two.St_eq, ← two.Xb_eq, ← h.1.1.z]; exact za
    have h1 := two.p₁.tau_le
    have h2 := two.p₂.tau_le
    exact ⟨setOk two.p₁.ok (by omega_arith) ht h.1.1 za, setOk two.p₂.ok (by omega_arith) ht h.1.2 zb⟩

omit two in
theorem nil_ct {P : State → State → Prop} {Q₁ Q₂ : State → Prop} (hq : ∀ a b, P a b → Q₁ a ∧ Q₂ b) :
    RelCT isa P (.block []) fun a b => Q₁ a ∧ Q₂ b :=
  relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by native_taint_decide))
    fun a b h => ⟨WP.block_nil (hq a b h).1, WP.block_nil (hq a b h).2⟩

omit two in
theorem skip_of {σ : State} {t : Nat} (ht : t < 264) {s : State} (h : T1 σ t s) (e : s.z = false) :
    M2 σ t s := by
  have hj : (St σ t).2 < (Xb σ t).toNat := by
    have := h.z; rw [e] at this; exact Nat.lt_of_not_le (of_decide_eq_false this.symm)
  have hst := St_succ σ ht
  rw [bStep, ifT h.lt, ifT hj] at hst
  exact M2.of_same h.bat hst

omit two in
theorem full_of {σ : State} {t : Nat} (ht : t < 264) {s : State} (h : M1 σ t s) (e : s.z = true) :
    M2 σ t s := by
  have hl : (St σ t).2 = 256 := by
    have := h.z; rw [e] at this; simp at this; have := St_le σ t; omega_arith
  exact M2.of_same h.bat (by rw [St_succ σ ht, bStep_full hl])

theorem body_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) bBody fun a b =>
      (BAt σ₁ (t + 1) a ∧ a.z = decide (t + 1 = 264)) ∧ (BAt σ₂ (t + 1) b ∧ b.z = decide (t + 1 = 264)) := by
  refine RelCT.seq pieceA_ct (RelCT.seq (R := fun a b => M2 σ₁ t a ∧ M2 σ₂ t b) ?_ ?_)
  · refine RelCT.ite (fun a b h => by show some a.z = some b.z; rw [h.1.z, h.2.z, two.St_eq]) ?_ ?_
    · exact nil_ct fun a b h => ⟨full_of ht h.1.1 (Option.some.inj h.2), full_of ht h.1.2 (by
        rw [h.1.2.z, ← two.St_eq, ← h.1.1.z]; exact Option.some.inj h.2)⟩
    · refine RelCT.seq (tryA_ct two ht) (RelCT.ite (fun a b h => by
        show some a.z = some b.z; rw [h.1.z, h.2.z, two.St_eq, two.Xb_eq]) (set_ct two ht) ?_)
      exact nil_ct fun a b h => ⟨skip_of ht h.1.1 (Option.some.inj h.2), skip_of ht h.1.2 (by
        rw [h.1.2.z, ← two.St_eq, ← two.Xb_eq, ← h.1.1.z]; exact Option.some.inj h.2)⟩
  · exact relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by native_taint_decide))
      fun a b h => ⟨pieceC ht h.1, pieceC ht h.2⟩

theorem loop_ct : RelCT isa (fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b) (.loop bBody .ne) fun a b =>
    BAt σ₁ 264 a ∧ BAt σ₂ 264 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := bBody) (c := .ne)
    (Q := fun a b => BAt σ₁ 264 a ∧ BAt σ₂ 264 b)
    (fun n a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b) (fun n => ?_) 264)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 264
  · by_cases hn : n = 264 - t
    · refine RelCT.mono (P := fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) (body_ct two ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 264 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 264 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨264 - (t + 1), by omega_arith, t + 1, by omega_arith, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem pro_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂)
    (.block (.ldrSp .r12 0 :: pro .r12 .r3 (.reg .r2) (.reg .r1) .r0))
    fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₂) σ₂ b := by
  refine relW ?_ fun a b h => ⟨by rw [h.1]; exact pro_ball two.p₁.ok rfl (by simp) rfl rfl rfl two.p₁.arg,
    by rw [h.2]; exact pro_ball two.p₂.ok rfl (by simp) rfl rfl rfl two.p₂.arg⟩
  show RelCT isa _ (.block ([.ldrSp .r12 0] ++ pro .r12 .r3 (.reg .r2) (.reg .r1) .r0)) _
  refine relct_append (R := fun a b => a = σ₁.setReg .r12 (stackArg σ₁ 0) ∧ b = σ₂.setReg .r12 (stackArg σ₂ 0))
    (relct_ldrSp (fun a b h => by rw [h.1, h.2, two.sp]) |>.wp (F₁ := fun s => s = σ₁.setReg .r12 (stackArg σ₁ 0))
      (F₂ := fun s => s = σ₂.setReg .r12 (stackArg σ₂ 0))
      (fun a b h => ⟨by rw [h.1]; exact ldrSp_ok σ₁ two.p₁.arg, by rw [h.2]; exact ldrSp_ok σ₂ two.p₂.arg⟩)
      |>.mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine taintRel [.r0, .r1, .r2, .r3, .r12] (fun a b h r hr => ?_) (by native_taint_decide)
  rw [h.1, h.2]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r0
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r1
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r2
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r3
  · rw [gpr_setReg_self, gpr_setReg_self]; exact two.scr

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.sampleInBall fun _ _ => True := by
  have hP := two.P_eq
  have ok₂ : SpOk (spOf σ₁) σ₂ := hP ▸ two.p₂.ok
  refine RelCT.seq (pro_ct two) ?_
  refine RelCT.seq (R := fun a b => J6 136 272 (spOf σ₁) σ₁ a ∧ J6 136 272 (spOf σ₂) σ₂ b)
    ((sponge_ct two.p₁.ok ok₂ two.sp (rate := 136) (outlen := 272) (by decide) (by decide) (by decide) (by decide)
      (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)).mono (fun a b h => ⟨h.1, hP ▸ h.2⟩)
      fun a b h => ⟨h.1, hP ▸ h.2⟩) ?_
  refine RelCT.seq (R := fun a b => ZDone σ₁ a ∧ ZDone σ₂ b) (relW (taintRel [.r5] (fun a b h r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r5, h.2.env.r5, hP]) (by native_taint_decide))
    fun a b h => ⟨zero_ok two.p₁.ok h.1, zero_ok two.p₂.ok h.2⟩) ?_
  have t₁ : tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega_arith
  have t₂ : tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega_arith
  refine RelCT.seq (RelCT.seq (R := fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b) (relW (taintRel [.r6, .r7]
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.env.r6, h.2.env.r6, hP]
        · rw [h.1.r7, h.2.r7, two.r2]) (by native_taint_decide))
    fun a b h => ⟨setup_ok two.p₁.ok t₁ h.1, setup_ok two.p₂.ok t₂ h.2⟩) (loop_ct two)) ?_
  exact taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6, hP]) (by native_taint_decide)

end

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.sampleInBallContract Arm.abi 8).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, -, -, b1, b2, b3, -, f1, f2, f3, hb⟩ := h
  simp only [Proof.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
  exact ⟨⟨by rw [hrd]; exact List.mem_cons.mpr (.inl rfl), hwr, d1, d2, d3, b1, b2, b3, f1, (s.gpr .r1).isLt, f2, f3, h8⟩,
    ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))),
      Region.contains_self _ _⟩, by simp only [tau]; omega_arith, by simp only [tau]; omega_arith⟩

theorem post_of {s₀ s : State}
    (h0 : s.gpr .r0 = (if (ballFold (tau s₀) (X s₀)).2 = 256 then 1 else 0))
    (hc : (ballFold (tau s₀) (X s₀)).2 = 256 →
      PolyIs s.mem (State.addr (s₀.gpr .r3)) (toRq (ballFold (tau s₀) (X s₀)).1)) :
    (Proof.MlDsa.sampleInBallContract Arm.abi 8).post s₀ s := by
  sig_post [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  by_cases hf : (ballFold (tau s₀) (X s₀)).2 = 256
  · rw [ifT hf]
    obtain ⟨hred, hpoly⟩ := hc hf
    exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 272 (B s₀)) =
        some (Proof.MlDsa.polyAt s.mem (State.addr (s₀.gpr .r3)))
      rw [sampleInBall_some _ (by decide) hf]
      exact congrArg some hpoly.symm⟩⟩
  · rw [ifF hf]
    exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 221 (B s₀)) = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) hf]; rfl⟩⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 32 | .r2 => 39 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.Arm.Sample.Ball

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open Ball

theorem sampleInBall_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.sampleInBall (Proof.MlDsa.sampleInBallContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h0, hc, hpres⟩ := correct (pre_of hs)
    exact ⟨t, s', he, hpres, post_of h0 hc⟩
  · sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2, h3, hs⟩ := hpub
    have two : Two s₁ s₂ := ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hs,
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩
    exact (all_ct two s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample
