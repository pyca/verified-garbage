module

public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Hash
import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashMu
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.Arm.Common
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Args

/-! ### `MlDsa.Arm.Message.Rel`, which this module and modules that import it used -/

section

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message_cached`: two runs

Untrusted: everything here is checked by Lean. Blocks whose addresses are
functions of `r7`, which they keep, leak the same in runs that agree on it
(`block_r7_tr`): the moves of a call's arguments are such (`setArgs_r7`).
Two runs with the same layout, each in `Ctx` with inputs related by `I`
(`Two`), and the moves of a call's arguments in them (`setArgs_two`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message

/-! ## Blocks addressed from `r7` -/

/-- An instruction whose addresses are a function of `r7`, which it keeps. -/
def R7Only (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .r7 = s₂.gpr .r7 → isa.addrs i s₁ = isa.addrs i s₂) ∧ clobbers i .r7 = false

theorem execBlock_r7_tr : ∀ {is : List Instr}, (∀ i ∈ is, R7Only i) →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, s₁.gpr .r7 = s₂.gpr .r7 →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, h7, e₁, e₂ => by
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> [cases e₁; skip]
    rename_i a₁ ha₁
    split at e₂ <;> [cases e₂; skip]
    rename_i a₂ ha₂
    obtain ⟨⟨b₁, u₁⟩, eb₁, he₁⟩ := Option.map_eq_some_iff.mp e₁
    obtain ⟨⟨b₂, u₂⟩, eb₂, he₂⟩ := Option.map_eq_some_iff.mp e₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨rfl, rfl⟩ := he₁; obtain ⟨rfl, rfl⟩ := he₂
    have hi := h i (List.mem_cons_self ..)
    have h7' : a₁.gpr .r7 = a₂.gpr .r7 := by rw [exec_gpr hi.2 ha₁, exec_gpr hi.2 ha₂, h7]
    have ht := execBlock_r7_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) h7' eb₁ eb₂
    rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ h7, ht]

theorem block_r7_tr {is : List Instr} (h : ∀ i ∈ is, R7Only i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .r7 = b.gpr .r7) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨execBlock_r7_tr h (hp _ _ hP) e₁ e₂, trivial⟩

theorem arg_r7 (d : Reg) (hd : d ≠ .r7) (a : Arg) : ∀ i ∈ a.mov d, R7Only i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    (try rcases hi with rfl | rfl) <;> (try subst hi) <;>
    exact ⟨fun s₁ s₂ h => by simp [addrs, h], by simpa [clobbers, dstOf] using hd⟩

theorem setArgs_r7 {as : List (Reg × Arg)} (h : argsOk as = true) : ∀ i ∈ setArgs as, R7Only i := by
  induction as with
  | nil => intro i hi; simp [setArgs] at hi
  | cons da as ih =>
    obtain ⟨d, a⟩ := da
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro i hi
    simp only [setArgs, List.flatMap_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact arg_r7 d h.1.1.2 a i hi
    · exact ih h.2 i hi

/-- A relation proved through the final states' facts, from those of each run. -/
theorem RelCT.postDep {P Q : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

/-! ## Runs related through their entry states -/

/-- Two runs whose states are related to entry states `x`, `y` by `A`, with
`P x y`. -/
def Ghost (P A : State → State → Prop) (a b : State) : Prop := ∃ x y, P x y ∧ A x a ∧ A y b

/-- What each run satisfies by correctness, from its entry state, carries over. -/
theorem ghost_step {P A B : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Ghost P A) c fun _ _ => True)
    (hw : ∀ x y a b, P x y → A x a → A y b → WP isa c a (B x) ∧ WP isa c b (B y)) :
    RelCT isa (Ghost P A) c (Ghost P B) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨x, y, hxy, a₁, a₂⟩ := hp
  obtain ⟨⟨_, u₁, x₁, y₁⟩, ⟨_, u₂, x₂, y₂⟩⟩ := hw x y s₁ s₂ hxy a₁ a₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, x, y, hxy, y₁, y₂⟩

/-- Code the taint analysis proves constant time from the registers `rs`
and the first `n` bytes of stack arguments, on which runs related by `R`
agree. -/
theorem argRel {R : State → State → Prop} {c : Prog isa} (rs : List Reg) (n : Nat)
    (hr : ∀ x y, R x y → VG.Arm.Taint.Agree (argTaint rs n) x y) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (argTaint rs n) c hc).isSome = true) : RelCT isa R c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (argTaint rs n) hr h

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRel {R : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, R x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa R c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hr a b hab)) h

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : Lay → Mem → Mem → Prop) (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : Lay → Mem → Mem → Prop}

theorem Two.r7 {Φ : Lay → Mem → State → Prop} {a b : State} (h : Two I Φ a b) :
    a.gpr .r7 = b.gpr .r7 ∧ a.sp = b.sp :=
  let ⟨_, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h
  ⟨c₁.r7.trans c₂.r7.symm, c₁.sp.trans c₂.sp.symm⟩

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two I Φ) c (Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List (Reg × Arg)) (t t1 : State) : Prop :=
  (∀ da ∈ as, t1.gpr da.1 = da.2.val t) ∧ Only (as.map (·.1)) t t1

/-- The moves of a call's arguments in two runs. -/
theorem setArgs_two {Φ : Lay → Mem → State → Prop} {as : List (Reg × Arg)} (hok : argsOk as = true) :
    RelCT isa (Two I Φ) (.block (setArgs as)) fun a1 b1 => ∃ a b, Two I Φ a b ∧ Moved as a a1 ∧ Moved as b b1 :=
  RelCT.postDep (block_r7_tr (setArgs_r7 hok) fun _ _ h => h.r7.1)
    (fun x y ⟨_, _, _, _, _, hL, _, c₁, c₂, _, _⟩ =>
      ⟨setArgs_ok as hok x (c₁.xOk hL), setArgs_ok as hok y (c₂.xOk hL)⟩)
    fun x y _ _ hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩

end

end VG.Proof.MlDsa.Arm.Message

end

end

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message_cached`: two runs of the hashing

Untrusted: everything here is checked by Lean. In two runs with the same
layout (`Two`), zeroing the state and each call of a sponge function leak
the same: their addresses and arguments are functions of the layout alone,
and ML-KEM's lemmas on two runs of the sponge functions' calls need just that
(`zeroSt_tr`, `kabs_tr`, `kpad_tr`, `ksqz_tr`); so does `muHash`
(`muHash_tr`, or `muHash_tr_of` when where `tr` is follows from what the
runs satisfy, as for a cached `tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (AbsorbArgs PadArgs SqueezeArgs absorb_ct pad_ct squeeze_ct regA)
open VG.Spec.MlDsa (Params)

section
variable {I : Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zeroSt_taint : (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.block zeroSt) (.block [])).isSome = true := by
  rfl

theorem zeroSt_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) (.block zeroSt) fun _ _ => True :=
  taintRel [.r7] (fun _ _ h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.r7.1) zeroSt_taint

/-! ## The sponge functions -/

theorem absA_of {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g m₀ t) {src len pos : Arg} (hm : Moved (absArgs src len pos) t t1) {dp : BitVec 32} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 32 n) (hq : pos.val t = BitVec.ofNat 32 q)
    (hql : q < 136) (hnl : n < 2 ^ 32) (hfit : dp.toNat + n ≤ 2 ^ 32)
    (hin : ∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr dp, n⟩ R)
    (dS : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨State.addr dp, n⟩ ⟨L.KS, 640⟩)
    (kD : L.STK.Disjoint ⟨State.addr dp, n⟩) :
    AbsorbArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) dp 136 q n := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.r2, pos) (by simp)
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e3 := hm.1 (.r3, src) (by simp)
  have e4 := hm.1 (.r12, len) (by simp)
  have e5 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, x0'] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  have bs := below_stk hs1
  have hks := ks_eq hL
  have hcw : Covers [regA L.X32 200, regA (L.X32 + BitVec.ofNat 32 200) 640] t1.wr := by
    simp only [regA, hks, hm.2.wr, hc.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_xw0 hL
    · exact hL.covX (e := 200) (by omega_arith)
  exact ⟨e0, e1, e2, e3, e4, e5, by decide, hql, hnl, by rw [hs1]; have := hL.nSP; omega_arith,
    by have := hL.x32_lt; omega_arith, hfit, by rw [x32_toNat hL (by omega_arith)]; have := hL.x32_lt; omega_arith,
    by simp only [regA, hks]; exact st_ks, by simp only [regA]; exact dS,
    by simp only [regA, hks]; exact dK,
    by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hks]; exact (k_ks hL).sub_left bs,
    by simp only [regA]; exact kD.sub_left bs, hcw,
    by simp only [regA, hm.2.rd, hm.2.wr, hc.rd, hc.wr]
       exact covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hin⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both, with where the data are following from `Φ`. -/
theorem kabs_tr_of {Φ : Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : argsOk (absArgs src len pos) = true) (dp : Lay → BitVec 32) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g m (t : State), L.Ok → Ctx L g m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 32 (n L) ∧ pos.val t = BitVec.ofNat 32 (q L))
    (hs : ∀ (L : Lay) m (t : State), L.Ok → Φ L m t → q L < 136 ∧ n L < 2 ^ 32 ∧ (dp L).toNat + n L ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (dp L), n L⟩ R) ∧
      Region.Disjoint ⟨State.addr (dp L), n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr (dp L), n L⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (dp L), n L⟩) :
    RelCT isa (Two I Φ) (kabs src len pos) fun _ _ => True := by
  refine RelCT.seq (setArgs_two hok) (absorb_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, φ₁, φ₂⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, dp L, 136, q L, n L, ?_, ?_⟩)
  · obtain ⟨h1, h2, h3⟩ := hv L g₁ m₁ a hL c₁ φ₁
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hs L m₁ a hL φ₁
    exact absA_of hL c₁ f₁ h1 h2 h3 s1 s2 s3 s4 s5 s6 s7
  · obtain ⟨h1, h2, h3⟩ := hv L g₂ m₂ b hL c₂ φ₂
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hs L m₂ b hL φ₂
    exact absA_of hL c₂ f₂ h1 h2 h3 s1 s2 s3 s4 s5 s6 s7

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr {Φ : Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : argsOk (absArgs src len pos) = true) (dp : Lay → BitVec 32) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g m (t : State), L.Ok → Ctx L g m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 32 (n L) ∧ pos.val t = BitVec.ofNat 32 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 32 ∧ (dp L).toNat + n L ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (dp L), n L⟩ R) ∧
      Region.Disjoint ⟨State.addr (dp L), n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr (dp L), n L⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (dp L), n L⟩) :
    RelCT isa (Two I Φ) (kabs src len pos) fun _ _ => True :=
  kabs_tr_of hok dp n q hv fun L _ _ hL _ => hs L hL

theorem padA_of {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g m₀ t) {pos : Arg} (hm : Moved (padArgs pos) t t1) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 32 q) (hql : q < 136) :
    PadArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) 136 q (BitVec.ofNat 32 0x1f) := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.r2, pos) (by simp)
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e3 := hm.1 (.r3, .imm 0x1f) (by simp)
  have e4 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, x0'] at e0 e1 e3 e4
  rw [hq] at e2
  have bs := below_stk hs1
  have hks := ks_eq hL
  exact ⟨e0, e1, e2, e3, e4, by decide, hql, by rw [hs1]; have := hL.nSP; omega_arith,
    by have := hL.x32_lt; omega_arith, by rw [x32_toNat hL (by omega_arith)]; have := hL.x32_lt; omega_arith,
    by simp only [regA, hks]; exact st_ks,
    by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hks]; exact (k_ks hL).sub_left bs,
    by simp only [regA, hks, hm.2.wr, hc.wr]
       exact covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl
         · exact cov_xw0 hL
         · exact hL.covX (e := 200) (by omega_arith)⟩

theorem kpad_tr {Φ : Lay → Mem → State → Prop} {pos : Arg}
    (hok : argsOk (padArgs pos) = true) (q : Lay → Nat)
    (hv : ∀ (L : Lay) g m (t : State), L.Ok → Ctx L g m t → Φ L m t → pos.val t = BitVec.ofNat 32 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136) :
    RelCT isa (Two I Φ) (kpad pos) fun _ _ => True :=
  RelCT.seq (setArgs_two hok) (pad_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, φ₁, φ₂⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, 136, q L,
      BitVec.ofNat 32 0x1f, padA_of hL c₁ f₁ (hv L g₁ m₁ a hL c₁ φ₁) (hs L hL),
      padA_of hL c₂ f₂ (hv L g₂ m₂ b hL c₂ φ₂) (hs L hL)⟩)

theorem sqzA_of {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g m₀ t) (hm : Moved sqzArgs t t1) :
    SqueezeArgs t1 L.X32 (L.X32 + BitVec.ofNat 32 200) (L.X32 + BitVec.ofNat 32 840) 136 0 64 := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e0 := hm.1 (.r0, .off oST) (by simp)
  have e1 := hm.1 (.r1, .imm 136) (by simp)
  have e2 := hm.1 (.r2, .imm 0) (by simp)
  have e3 := hm.1 (.r3, .off oMU) (by simp)
  have e4 := hm.1 (.r12, .imm 64) (by simp)
  have e5 := hm.1 (.lr, .off oKS) (by simp)
  simp only [Arg.val, hc.r7, oST, oKS, oMU, x0'] at e0 e1 e2 e3 e4 e5
  have bs := below_stk hs1
  have hks := ks_eq hL
  have hmu := mu_eq hL
  exact ⟨e0, e1, e2, e3, e4, e5, by decide, by decide, by decide, by rw [hs1]; have := hL.nSP; omega_arith,
    by have := hL.x32_lt; omega_arith, by rw [x32_toNat hL (by omega_arith)]; have := hL.x32_lt; omega_arith,
    by rw [x32_toNat hL (by omega_arith)]; have := hL.x32_lt; omega_arith,
    by simp only [regA, hmu]; exact st_mu, by simp only [regA, hks]; exact st_ks,
    by simp only [regA, hks, hmu]; exact mu_ks,
    by simp only [regA]; exact (k_st hL).sub_left bs, by simp only [regA, hmu]; exact (k_mu hL).sub_left bs,
    by simp only [regA, hks]; exact (k_ks hL).sub_left bs,
    by simp only [regA, hks, hmu, hm.2.wr, hc.wr]
       exact covers_of_within fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl
         · exact cov_xw0 hL
         · exact hL.covX (e := 840) (by omega_arith)
         · exact hL.covX (e := 200) (by omega_arith)⟩

theorem ksqz_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) ksqz fun _ _ => True :=
  RelCT.seq (setArgs_two (by decide)) (squeeze_ct fun a1 b1 ⟨a, b, ⟨L, g₁, g₂, m₁, m₂, hL, _, c₁, c₂, _, _⟩, f₁, f₂⟩ =>
    ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], L.X32, L.X32 + BitVec.ofNat 32 200, L.X32 + BitVec.ofNat 32 840,
      136, 0, 64, sqzA_of hL c₁ f₁, sqzA_of hL c₂ f₂⟩)

/-! ## `μ` and `tr` -/

/-- The position after the context string. -/
abbrev qCtx (L : Lay) : Nat := (66 + L.ctxLen.toNat) % 136
/-- The position after the message. -/
abbrev qMsg (L : Lay) : Nat := (qCtx L + L.len.toNat) % 136

/-- `muHash`, with where `tr` is following from a property `G` of the layout
that the runs have (a cached `tr` in an argument). -/
theorem muHash_tr_of {Φ : Lay → Mem → State → Prop} {G : Lay → Prop} {tr : Arg}
    (hG : ∀ L m t, Φ L m t → G L) (hok : tr.ok = true) (hret : tr.isRet = false) (trp : Lay → BitVec 32)
    (htr : ∀ (L : Lay) g m (t : State), L.Ok → Ctx L g m t → tr.val t = trp L)
    (hs : ∀ L : Lay, L.Ok → G L → (trp L).toNat + 64 ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (trp L), 64⟩ R) ∧
      Region.Disjoint ⟨State.addr (trp L), 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr (trp L), 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (trp L), 64⟩) :
    RelCT isa (Two I Φ) (muHash tr) fun _ _ => True := by
  -- The relation keeps only the position in `r0`.
  let Ψ : (Lay → Nat) → Lay → Mem → State → Prop := fun q L _ t => (t.gpr .r0).toNat = q L
  have z := two_wp (I := I) (Φ := Φ) (Ψ := fun L _ _ => G L) zeroSt_tr
    fun L g m₀ t hL hc hφ => WP.mono (zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', hG L m₀ t hφ⟩
  have a1 := two_wp (I := I) (Ψ := Ψ fun _ => 64)
    (kabs_tr_of (Φ := fun L _ _ => G L) (absOk hok rfl rfl hret rfl) trp (fun _ => 64)
      (fun _ => 0) (fun L g m t hL hc _ => ⟨htr L g m t hL hc, rfl, rfl⟩)
      fun L _ _ hL hg => ⟨by decide, by decide, (hs L hL hg).1, (hs L hL hg).2.1, (hs L hL hg).2.2.1,
        (hs L hL hg).2.2.2.1, (hs L hL hg).2.2.2.2⟩)
    fun L g m₀ t hL hc hg => by
      obtain ⟨a, b, c, d, e⟩ := hs L hL hg
      exact WP.mono (kabs_ok hL hc (src := tr) (len := .imm 64) (pos := .imm 0) (n := 64) (q := 0)
        (absOk hok rfl rfl hret rfl) (htr L g m₀ t hL hc) rfl rfl (by decide)
        (by decide) a b c d e) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have hdr : ∀ L : Lay, L.Ok → 64 < 136 ∧ 2 < 2 ^ 32 ∧ (L.X32 + BitVec.ofNat 32 944).toNat + 2 ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ R) ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (L.X32 + BitVec.ofNat 32 944), 2⟩ := fun L hL => by
    rw [hL.xo (by decide)]
    exact ⟨by decide, by decide, by rw [x32_toNat hL (by decide)]; have := hL.x32_lt; omega_arith, cov_x hL (by omega_arith),
      by have := Offset.disjoint L.X (d := 944) (n := 2) (e := 0) (k := 200) (by omega_arith) (by omega_arith) (by omega_arith)
         simpa only [x0] using this,
      Offset.disjoint L.X (d := 944) (n := 2) (e := 200) (k := 640) (by omega_arith) (by omega_arith) (by omega_arith),
      hL.stk_x (by omega_arith)⟩
  have a2 := two_wp (I := I) (Φ := Ψ fun _ => 64) (Ψ := Ψ fun _ => 66)
    (kabs_tr (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.X32 + BitVec.ofNat 32 944) (fun _ => 2) (fun _ => 64)
      (fun L g m t _ hc _ => ⟨by rw [hc.off]; rfl, rfl, rfl⟩) hdr)
    fun L g m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := hdr L hL
      exact WP.mono (kabs_ok hL hc (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (n := 2) (q := 64)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.off]; rfl) rfl rfl a b c d e f k)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have ctxS : ∀ L : Lay, L.Ok → 66 < 136 ∧ L.ctxLen.toNat < 2 ^ 32 ∧ L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.ctx, L.ctxLen.toNat⟩ R) ∧
      Region.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.ctx, L.ctxLen.toNat⟩ := fun L hL =>
    ⟨by decide, L.ctxLen.isLt, hL.nCtx, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
      by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xCtx (e := 200) (k := 640) (by decide)).symm, hL.kCtx⟩
  have a3 := two_wp (I := I) (Φ := Ψ fun _ => 66) (Ψ := Ψ qCtx)
    (kabs_tr (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.ctx) (fun L => L.ctxLen.toNat) (fun _ => 66)
      (fun L g m t hL hc _ => ⟨by rw [hc.slotV hL (f := fCtx) (j := 3) rfl (by omega_arith)]; rfl,
        by rw [hc.slotV hL (f := fCtxLen) (j := 4) rfl (by omega_arith), ofNat_toNat32]; rfl, rfl⟩) ctxS)
    fun L g m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := ctxS L hL
      exact WP.mono (kabs_ok hL hc (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (q := 66)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV hL (f := fCtx) (j := 3) rfl (by omega_arith)]; rfl)
        (by rw [hc.slotV hL (f := fCtxLen) (j := 4) rfl (by omega_arith), ofNat_toNat32]; rfl) rfl a b c d e f k)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have msgS : ∀ L : Lay, L.Ok → qCtx L < 136 ∧ L.len.toNat < 2 ^ 32 ∧ L.msg.toNat + L.len.toNat ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.msg, L.len.toNat⟩ R) ∧
      Region.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.msg, L.len.toNat⟩ := fun L hL =>
    ⟨Nat.mod_lt _ (by decide), L.len.isLt, hL.nMsg, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
      by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xMsg (e := 200) (k := 640) (by decide)).symm, hL.kMsg⟩
  have a4 := two_wp (I := I) (Φ := Ψ qCtx) (Ψ := Ψ qMsg)
    (kabs_tr (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.msg) (fun L => L.len.toNat) qCtx
      (fun L g m t hL hc hφ => ⟨by rw [hc.slotV hL (f := fMsg) (j := 1) rfl (by omega_arith)]; rfl,
        by rw [hc.slotV hL (f := fLen) (j := 2) rfl (by omega_arith), ofNat_toNat32]; rfl, ofNat_toNat_eq32 hφ⟩) msgS)
    fun L g m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f, k⟩ := msgS L hL
      exact WP.mono (kabs_ok hL hc (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV hL (f := fMsg) (j := 1) rfl (by omega_arith)]; rfl)
        (by rw [hc.slotV hL (f := fLen) (j := 2) rfl (by omega_arith), ofNat_toNat32]; rfl) (ofNat_toNat_eq32 hφ)
        a b c d e f k) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have pd := kpad_tr (I := I) (Φ := Ψ qMsg) (pos := .ret) (padOk rfl) qMsg
    (fun L g m t _ _ hφ => ofNat_toNat_eq32 hφ) fun L _ => Nat.mod_lt _ (by decide)
  have pd' := two_wp (I := I) (Φ := Ψ qMsg) (Ψ := fun _ _ _ => True) pd
    fun L g m₀ t hL hc hφ => WP.mono (kpad_ok hL hc (pos := .ret) (padOk rfl) (ofNat_toNat_eq32 hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (a2.seq (a3.seq (a4.seq (pd'.seq ksqz_tr)))))

theorem muHash_tr {Φ : Lay → Mem → State → Prop} {tr : Arg}
    (hok : tr.ok = true) (hret : tr.isRet = false) (trp : Lay → BitVec 32)
    (htr : ∀ (L : Lay) g m (t : State), L.Ok → Ctx L g m t → tr.val t = trp L)
    (hs : ∀ L : Lay, L.Ok → (trp L).toNat + 64 ≤ 2 ^ 32 ∧ (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (trp L), 64⟩ R) ∧
      Region.Disjoint ⟨State.addr (trp L), 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr (trp L), 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (trp L), 64⟩) :
    RelCT isa (Two I Φ) (muHash tr) fun _ _ => True :=
  muHash_tr_of (G := fun _ => True) (fun _ _ _ _ => trivial) hok hret trp htr fun L hL _ => hs L hL

end

end VG.Proof.MlDsa.Arm.Message
