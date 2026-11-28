module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
public meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# SLH-DSA (SHAKE) on x86-64: `levels` is constant time

Two runs of `levels` from states of its precondition that agree on its
public data leak the same trace (`levels_ct`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs saveRegs restoreRegs thashArgs)
open VG.Impl.SlhDsa.X86_64.Tree

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun x y hp => Taint.agree_ofRegs (hr x y hp)) h

/-- The sizes of `n`. -/
abbrev Ns (n : Nat) : Prop := n = 16 ∨ n = 24 ∨ n = 32

section
variable {P : State → State → Prop} {n len : Nat} (hn : Ns n)
include hn

theorem ct_scan (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], x.gpr r = y.gpr r) :
    RelCT isa P (.seq (.block scanInit) (.loop (.block (scanBody ⟨n, len⟩)) .ne)) fun _ _ => True := by
  rcases hn with rfl | rfl | rfl
  · exact taintR _ hr (c := .seq (.block scanInit) (.loop (.block (scanBody ⟨16, 0⟩)) .ne)) (by taint_decide)
  · exact taintR _ hr (c := .seq (.block scanInit) (.loop (.block (scanBody ⟨24, 0⟩)) .ne)) (by taint_decide)
  · exact taintR _ hr (c := .seq (.block scanInit) (.loop (.block (scanBody ⟨32, 0⟩)) .ne)) (by taint_decide)

theorem ct_lanes (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r12, .r14, .rbp], x.gpr r = y.gpr r) :
    RelCT isa P (.block (levelLanes ⟨n, len⟩)) fun _ _ => True := by
  rcases hn with rfl | rfl | rfl
  · exact taintR _ hr (c := .block (levelLanes ⟨16, 0⟩)) (by taint_decide)
  · exact taintR _ hr (c := .block (levelLanes ⟨24, 0⟩)) (by taint_decide)
  · exact taintR _ hr (c := .block (levelLanes ⟨32, 0⟩)) (by taint_decide)

theorem ct_out (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r12, .rbp, .r15], x.gpr r = y.gpr r) :
    RelCT isa P (.block (levelOut ⟨n, len⟩)) fun _ _ => True := by
  rcases hn with rfl | rfl | rfl
  · exact taintR _ hr (c := .block (levelOut ⟨16, 0⟩)) (by taint_decide)
  · exact taintR _ hr (c := .block (levelOut ⟨24, 0⟩)) (by taint_decide)
  · exact taintR _ hr (c := .block (levelOut ⟨32, 0⟩)) (by taint_decide)

theorem ct_args (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (thashArgs ⟨n, len⟩ Layout.oA Layout.strideA (3 * n + 32))) fun _ _ => True := by
  rcases hn with rfl | rfl | rfl
  · exact taintR _ hr (c := .block (thashArgs ⟨16, 0⟩ Layout.oA Layout.strideA (3 * 16 + 32))) (by taint_decide)
  · exact taintR _ hr (c := .block (thashArgs ⟨24, 0⟩ Layout.oA Layout.strideA (3 * 24 + 32))) (by taint_decide)
  · exact taintR _ hr (c := .block (thashArgs ⟨32, 0⟩ Layout.oA Layout.strideA (3 * 32 + 32))) (by taint_decide)

theorem ct_next (hr : ∀ x y, P x y → ∀ r ∈ [Reg.r13, .r14, .r15], x.gpr r = y.gpr r) :
    RelCT isa P (.block (nextHeight ⟨n, len⟩)) fun _ _ => True := by
  rcases hn with rfl | rfl | rfl
  · exact taintR _ hr (c := .block (nextHeight ⟨16, 0⟩)) (by taint_decide)
  · exact taintR _ hr (c := .block (nextHeight ⟨24, 0⟩)) (by taint_decide)
  · exact taintR _ hr (c := .block (nextHeight ⟨32, 0⟩)) (by taint_decide)

end

theorem ct_halve {P : State → State → Prop} (hr : ∀ x y, P x y → ∀ r ∈ [Reg.r15], x.gpr r = y.gpr r) :
    RelCT isa P (.block halve) fun _ _ => True :=
  taintR _ hr (by taint_decide)

theorem ct_pro {P : State → State → Prop} (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rdi], x.gpr r = y.gpr r) :
    RelCT isa P (.block pro) fun _ _ => True :=
  taintR _ hr (by taint_decide)

theorem ct_restore {P : State → State → Prop} (hr : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (restoreRegs 4)) fun _ _ => True :=
  taintR _ hr (by taint_decide)

/-! ## Two runs, each with its own invariants -/

/-- `c₁` then `c₂`, from states each satisfying a predicate of its own. -/
theorem relSeq {A₁ A₂ B₁ B₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (hct : RelCT isa (fun a b => A₁ a ∧ A₂ b) c₁ fun _ _ => True)
    (h₁ : ∀ a, A₁ a → WP isa c₁ a B₁) (h₂ : ∀ b, A₂ b → WP isa c₁ b B₂)
    (hr : RelCT isa (fun a b => B₁ a ∧ B₂ b) c₂ Q) : RelCT isa (fun a b => A₁ a ∧ A₂ b) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.mono (RelCT.wp hct fun a b h => ⟨h₁ a h.1, h₂ b h.2⟩) (fun _ _ h => h) fun _ _ h => h.2) hr

/-- A loop whose runs each keep an invariant of their own, at the same
measure, the condition after each pass being a function `cont` of it. -/
theorem relLoop {body : Prog isa} {c : Cond} {I₁ I₂ : Nat → State → Prop} {Q₁ Q₂ : State → Prop}
    (cont : Nat → Bool) (g : Nat → Nat)
    (hct : ∀ m, RelCT isa (fun a b => I₁ m a ∧ I₂ m b) body fun _ _ => True)
    (h₁ : ∀ m s, I₁ m s → WP isa body s fun s' => isa.eval c s' = some (cont m) ∧
      (cont m = false → Q₁ s') ∧ (cont m = true → g m < m ∧ I₁ (g m) s'))
    (h₂ : ∀ m s, I₂ m s → WP isa body s fun s' => isa.eval c s' = some (cont m) ∧
      (cont m = false → Q₂ s') ∧ (cont m = true → g m < m ∧ I₂ (g m) s'))
    (n : Nat) : RelCT isa (fun a b => I₁ n a ∧ I₂ n b) (.loop body c) fun a b => Q₁ a ∧ Q₂ b :=
  RelCT.loop (fun m a b => I₁ m a ∧ I₂ m b) (fun m => RelCT.mono
    (RelCT.wp (hct m) fun a b h => ⟨h₁ m a h.1, h₂ m b h.2⟩) (fun _ _ h => h)
    fun a b ⟨_, ha, hb⟩ => ⟨by rw [ha.1, hb.1], fun hf => by
      rw [ha.1, Option.some.injEq] at hf; exact ⟨ha.2.1 hf, hb.2.1 hf⟩, fun ht => by
      rw [ha.1, Option.some.injEq] at ht; exact ⟨g m, (ha.2.2 ht).1, (ha.2.2 ht).2, (hb.2.2 ht).2⟩⟩) n

/-- The loop of such a run. -/
theorem wpLoop {body : Prog isa} {c : Cond} {I : Nat → State → Prop} {Q : State → Prop}
    (cont : Nat → Bool) (g : Nat → Nat)
    (h : ∀ m s, I m s → WP isa body s fun s' => isa.eval c s' = some (cont m) ∧
      (cont m = false → Q s') ∧ (cont m = true → g m < m ∧ I (g m) s'))
    (n : Nat) {s : State} (hs : I n s) : WP isa (.loop body c) s Q :=
  WP.loop (M := isa) I (fun m s hI => WP.mono (h m s hI) fun s' ⟨he, hq, hi⟩ => by
    cases hc : cont m
    · exact .inl ⟨by rw [he, hc], hq hc⟩
    · exact .inr ⟨by rw [he, hc], g m, (hi hc).1, (hi hc).2⟩) n s hs

/-! ## A call of `thash4` -/

variable {p : Params}

/-- What a call of `thash4` on the lanes `A` needs. -/
structure T4Ok (S : Addr) (stack : Nat) (t : State) : Prop where
  bx : t.gpr .rbx = S
  wr : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩
  rc : RcTable t.mem S

theorem t4_ct (T : Thash4Impl p.n) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (name : String) {stack : Nat}
    (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {S : Addr} {sp : Addr} {A₁ A₂ : State → Prop}
    (h₁ : ∀ a, A₁ a → T4Ok S stack a ∧ a.gpr .rsp = sp) (h₂ : ∀ b, A₂ b → T4Ok S stack b ∧ b.gpr .rsp = sp) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b)
      (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (3 * p.n + 32))
      fun _ _ => True := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  let F : State → Prop := fun u => ∃ t, T4Ok S stack t ∧ t.gpr .rsp = sp ∧ u.gpr .rdi = at' S Layout.oA ∧
    u.gpr .rsi = BitVec.ofNat 64 Layout.strideA ∧ u.gpr .rdx = BitVec.ofNat 64 (3 * p.n + 32) ∧
    u.gpr .rcx = at' S (Layout.oA + (p.n + 32)) ∧ u.gpr .r8 = S ∧
    (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) ∧
    u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr
  have hw : ∀ a, T4Ok S stack a → a.gpr .rsp = sp →
      WP isa (.block (thashArgs ⟨p.n, p.len⟩ Layout.oA Layout.strideA (3 * p.n + 32))) a F := fun a ha hs =>
    args_ok hn32 (by omega) ha.bx fun u e1 e2 e3 e4 e5 eg em er ew => ⟨a, ha, hs, e1, e2, e3, e4, e5, eg, em, er, ew⟩
  unfold Impl.SlhDsa.X86_64.thashCall
  refine relSeq (B₁ := F) (B₂ := F) (ct_args hn fun a b h => ?_) (fun a h => hw a (h₁ a h).1 (h₁ a h).2)
    (fun b h => hw b (h₂ b h).1 (h₂ b h).2) ?_
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [(h₁ a h.1).1.bx, (h₂ b h.2).1.bx]
  refine RelCT.call T.verified.1 T.verified.2.1 [] (callW S) fun a b ⟨⟨t₁, o₁, s₁, a1, a2, a3, a4, a5, ag, am, _, aw⟩,
    ⟨t₂, o₂, s₂, b1, b2, b3, b4, b5, bg, bm, _, bw⟩⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := t4_entry T hn hst hs63 o₁.wr o₁.fit o₁.stk o₁.rc a1 a2 a3 a4 a5 ag am aw
  obtain ⟨p₂, c₂, w₂⟩ := t4_entry T hn hst hs63 o₂.wr o₂.fit o₂.stk o₂.rc b1 b2 b3 b4 b5 bg bm bw
  have hsp : a.gpr .rsp = b.gpr .rsp := by
    rw [ag _ (by decide) (by decide) (by decide) (by decide) (by decide), s₁,
      bg _ (by decide) (by decide) (by decide) (by decide) (by decide), s₂]
  refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂, hsp⟩ <;>
    simp only [State.withRegions_gpr, State.callEntry_rsp]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a1, b1]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a2, b2]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a3, b3]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a4, b4]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a5, b5]
  · rw [hsp]


/-! ## A group of four nodes -/

/-- What a group needs, in one run: `rbx` = `scratch`, the nodes, the
height, the group `j`, the number of nodes, the stack pointer `sp`. -/
structure GPre (p : Params) (S : Addr) (stack no z j P : Nat) (sp : Addr) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r12 : t.gpr .r12 = at' S no
  r14 : t.gpr .r14 = BitVec.ofNat 64 z
  bp : t.gpr .rbp = BitVec.ofNat 64 j
  r15 : t.gpr .r15 = BitVec.ofNat 64 P
  rsp : t.gpr .rsp = sp
  z_lt : z < 14
  j_lt : j < 2 ^ 14
  P_lt : P < 2 ^ 64
  no_lo : 12640 ≤ no
  no_hi : no + 2 * j * p.n + 8 * p.n ≤ 2 ^ 16
  v6 : (t.mem.readW (at' S (Layout.oVar 4 6)) 64).toNat < 2 ^ 32
  wr : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩
  env : ∃ pkSeed a16, Env p t.mem S pkSeed a16 ∧ a16.length = 16

/-- The registers a group keeps that address memory. -/
abbrev RVo (S : Addr) (no j P : Nat) (u : State) : Prop :=
  u.gpr .rbx = S ∧ u.gpr .r12 = at' S no ∧ u.gpr .rbp = BitVec.ofNat 64 j ∧ u.gpr .r15 = BitVec.ofNat 64 P

theorem lanes_t4 (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {stack no z j P : Nat} {sp : Addr} {t : State}
    (g : GPre p S stack no z j P sp t) :
    WP isa (.block (levelLanes ⟨p.n, p.len⟩)) t fun u => (T4Ok S stack u ∧ u.gpr .rsp = sp) ∧ RVo S no j P u := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  obtain ⟨pkSeed, a16, hE, -⟩ := g.env
  refine WP.mono (lanes_ok hn g.bx g.r12 g.r14 g.bp g.z_lt g.j_lt (by have := g.no_lo; omega) g.no_hi rfl rfl rfl
    g.v6 g.wr) fun u l => ?_
  have hk : ∀ r : Reg, r ∈ [Reg.rbx, .r12, .rbp, .r15, .rsp] → u.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact l.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp : u.gpr .rsp = sp := by rw [hk _ (by simp), g.rsp]
  refine ⟨⟨⟨by rw [hk _ (by simp), g.bx], by rw [l.wr]; exact g.wr, g.fit, by rw [hsp]; exact g.stk,
    fun r hr k hk' => ?_⟩, hsp⟩, by rw [hk _ (by simp), g.bx], by rw [hk _ (by simp), g.r12],
    by rw [hk _ (by simp), g.bp], by rw [hk _ (by simp), g.r15]⟩
  rw [← hE.rc r hr k hk']
  refine l.frame.readW (r := ⟨at' S (1600 + 32 * r + 8 * k), 8⟩) (Region.contains_self _ _) (fun R hR => ?_) (by decide)
  simp only [List.mem_map, List.mem_range] at hR
  obtain ⟨k', hk'', rfl⟩ := hR
  exact disj_scr S (.inl (by rw [hLA]; omega)) (by omega) (by rw [hLA]; omega)

theorem group_ct (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {stack : Nat}
    (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {S : Addr} {no z j P : Nat} {sp : Addr}
    {A₁ A₂ : State → Prop} (h₁ : ∀ a, A₁ a → GPre p S stack no z j P sp a)
    (h₂ : ∀ b, A₂ b → GPre p S stack no z j P sp b) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (levelBody ⟨p.n, p.len⟩ name T.code) fun _ _ => True := by
  have hcall : ∀ u, (T4Ok S stack u ∧ u.gpr .rsp = sp) ∧ RVo S no j P u →
      WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (3 * p.n + 32)) u
        (RVo S no j P) := fun u ⟨⟨o, _⟩, b, r12, bp, r15⟩ =>
    WP.mono (t4_ok T name hn hst hs63 o.bx o.wr o.fit o.stk o.rc) fun u' ⟨_, _, cs, _⟩ =>
      ⟨by rw [cs _ (by decide), b], by rw [cs _ (by decide), r12], by rw [cs _ (by decide), bp],
        by rw [cs _ (by decide), r15]⟩
  unfold levelBody
  refine relSeq (ct_lanes hn fun a b h r hr => ?_) (fun a h => lanes_t4 hn (h₁ a h)) (fun b h => lanes_t4 hn (h₂ b h))
    (relSeq (t4_ct T hn name hst hs63 (fun a h => h.1) (fun b h => h.1)) hcall hcall
      (ct_out hn fun a b ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ r hr => ?_))
  · have g₁ := h₁ a h.1
    have g₂ := h₂ b h.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [g₁.bx, g₂.bx]
    · rw [g₁.r12, g₂.r12]
    · rw [g₁.r14, g₂.r14]
    · rw [g₁.bp, g₂.bp]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]
    · rw [a4, b4]


/-! ## The level loop -/

/-- The level loop's invariant in one run, `m` groups' nodes before the end. -/
def LI (p : Params) (S : Addr) (stack no z P : Nat) (sp A13 : Addr) (m : Nat) (s : State) : Prop :=
  ∃ i, m = P - 4 * i ∧ 4 * i < P ∧ GPre p S stack no z (4 * i) P sp s ∧ s.gpr .r13 = A13

/-- What the level loop keeps. -/
abbrev LQ (z P : Nat) (sp A13 : Addr) (s : State) : Prop :=
  s.gpr .r13 = A13 ∧ s.gpr .r14 = BitVec.ofNat 64 z ∧ s.gpr .r15 = BitVec.ofNat 64 P ∧ s.gpr .rsp = sp

theorem level_step (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S : Addr} {no z P : Nat} {sp A13 : Addr} (hP : P ≤ 2 ^ 13) (hcap : no + (2 * P + 8) * p.n ≤ 2 ^ 16) :
    ∀ m s, LI p S stack no z P sp A13 m s → WP isa (levelBody ⟨p.n, p.len⟩ name T.code) s fun s' =>
      isa.eval .b s' = some (decide (P - m + 4 < P)) ∧ (decide (P - m + 4 < P) = false → LQ z P sp A13 s') ∧
      (decide (P - m + 4 < P) = true → m - 4 < m ∧ LI p S stack no z P sp A13 (m - 4) s') := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  intro m s ⟨i, hm, hi, g, h13⟩
  obtain ⟨pk, a, hE, ha⟩ := g.env
  subst hm
  refine WP.mono (group_ok T name hn hf hst hs63 g.bx g.r12 g.r14 g.bp g.r15 g.z_lt g.j_lt g.P_lt g.no_lo g.no_hi
    rfl rfl rfl g.v6 g.wr g.fit (by rw [g.rsp]; exact g.stk) hE ha) fun s' gp => ?_
  have e : P - (P - 4 * i) + 4 = 4 * i + 4 := by omega
  rw [e]
  have hk : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r := gp.keep
  refine ⟨by show s'.cf = _; rw [gp.cf], fun _ => ⟨by rw [hk _ (by simp), h13], by rw [hk _ (by simp), g.r14],
    by rw [hk _ (by simp), g.r15], by rw [hk _ (by simp), g.rsp]⟩, fun hc => ?_⟩
  have hc' : 4 * i + 4 < P := of_decide_eq_true hc
  have hfr := gp.frame
  rw [g.rsp] at hfr
  have hin : (2 * (4 * (i + 1)) + 8) * p.n ≤ (2 * P + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
  have hin' : (4 * i + 4) * p.n ≤ (2 * P + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
  refine ⟨by omega, i + 1, by omega, by omega, ⟨by rw [hk _ (by simp), g.bx], by rw [hk _ (by simp), g.r12],
    by rw [hk _ (by simp), g.r14], by rw [gp.bp]; congr 1, by rw [hk _ (by simp), g.r15],
    by rw [hk _ (by simp), g.rsp], g.z_lt, by omega, g.P_lt, g.no_lo, by grind, ?_, by rw [gp.wr]; exact g.wr, g.fit,
    g.stk, pk, a, gp.env, ha⟩, by rw [hk _ (by simp), h13]⟩
  rw [keep_low hn32 hfr (by have := g.no_lo; omega) (by grind) g.stk (by rw [hv]; omega) (by rw [hv]; omega)]
  exact g.v6

theorem level_ct (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S : Addr} {no z P : Nat} {sp A13 : Addr} (hP : P ≤ 2 ^ 13) (hcap : no + (2 * P + 8) * p.n ≤ 2 ^ 16) :
    RelCT isa (fun a b => LI p S stack no z P sp A13 P a ∧ LI p S stack no z P sp A13 P b)
      (.loop (levelBody ⟨p.n, p.len⟩ name T.code) .b) fun a b => LQ z P sp A13 a ∧ LQ z P sp A13 b := by
  refine relLoop (fun m => decide (P - m + 4 < P)) (fun m => m - 4) (fun m => group_ct (j := P - m) T name hn hst hs63
    (fun a ⟨i, hm, hi, g, _⟩ => by rw [show P - m = 4 * i by omega]; exact g)
    (fun b ⟨i, hm, hi, g, _⟩ => by rw [show P - m = 4 * i by omega]; exact g))
    (level_step T name hn hf hst hs63 hP hcap) (level_step T name hn hf hst hs63 hP hcap) P


/-! ## A height -/

/-- What a height needs, in one run: the `2P` nodes of height `z` at `no`, the path's node at `AP`. -/
structure HPre (p : Params) (S : Addr) (stack no z P : Nat) (sp AP : Addr) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r12 : t.gpr .r12 = at' S no
  r13 : t.gpr .r13 = AP
  r14 : t.gpr .r14 = BitVec.ofNat 64 z
  r15 : t.gpr .r15 = BitVec.ofNat 64 (2 * P)
  rsp : t.gpr .rsp = sp
  z_lt : z < 14
  P_pos : 1 ≤ P
  P_le : P ≤ 2 ^ 13
  no_lo : 12640 ≤ no
  cap : no + (2 * P + 8) * p.n ≤ Layout.oSigTmp
  v0 : (t.mem.readW (at' S (Layout.oVar 4 0)) 64).toNat < 2 ^ 32
  v5 : (t.mem.readW (at' S (Layout.oVar 4 5)) 64).toNat < 2 ^ 32
  v6 : (t.mem.readW (at' S (Layout.oVar 4 6)) 64).toNat < 2 ^ 32
  wr : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩
  env : ∃ pkSeed a16, Env p t.mem S pkSeed a16 ∧ a16.length = 16
  au : ∀ w < p.n / 8, InRegions t.wr (AP + BitVec.ofNat 64 (8 * w)) 8
  ad : Region.Disjoint ⟨AP, p.n⟩ ⟨S, Layout.oSigTmp⟩
  as : Region.Disjoint ⟨AP, p.n⟩ (below sp stack)

/-- `seq (seq a b) c` from `seq a (seq b c)`, for two runs. -/
theorem relAssoc {P Q : State → State → Prop} {a b c : Prog isa} (h : RelCT isa P (.seq (.seq a b) c) Q) :
    RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ r₁ =>
    cases r₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ r₂ =>
        cases r₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          exact ⟨by simpa [List.append_assoc] using ht, hq⟩

/-- After the scan, from a height's start `t`. -/
def Mid (p : Params) (S : Addr) (stack no z P : Nat) (sp AP : Addr) (u : State) : Prop :=
  ∃ t, HPre p S stack no z P sp AP t ∧ (∀ g ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], u.gpr g = t.gpr g) ∧
    u.wr = t.wr ∧ (∃ pkSeed a16, Env p u.mem S pkSeed a16 ∧ a16.length = 16) ∧
    u.mem.readW (at' S (Layout.oVar 4 6)) 64 = t.mem.readW (at' S (Layout.oVar 4 6)) 64

theorem scan_mid (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {stack no z P : Nat} {sp AP : Addr} {t : State}
    (g : HPre p S stack no z P sp AP t) :
    WP isa (.seq (.block scanInit) (.loop (.block (scanBody ⟨p.n, p.len⟩)) .ne)) t
      (Mid p S stack no z P sp AP) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eT : Layout.oSigTmp = 31648 := rfl
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  have hPn : (2 * P) * p.n + 8 * p.n ≤ (2 * P + 8) * p.n := by rw [Nat.add_mul]
  obtain ⟨pk, a, hE, ha⟩ := g.env
  have hd3 : ∀ o l, o + l ≤ Layout.oSigTmp → (o + l ≤ Layout.oVar 4 3 ∨ Layout.oVar 4 3 + 8 ≤ o) →
      ∀ r ∈ [(⟨AP, p.n⟩ : Region), ⟨at' S (Layout.oVar 4 3), 8⟩], Region.Disjoint ⟨at' S o, l⟩ r := fun o l h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (disj_low g.ad h₁).symm
    · exact disj_scr S h₂ (by omega) (by rw [hv]; omega)
  refine scan_ok hn g.bx g.r12 g.r13 g.r14 g.r15 (by have := g.z_lt; omega) (by have := g.P_pos; omega)
    (by have := g.P_le; omega) g.wr (by have := g.no_lo; omega) (by have := g.cap; omega) rfl rfl g.v0 g.v5 g.au g.ad
    fun u g₁ _ wr₁ _ f₁ => ⟨t, g, fun r hr => ?_, wr₁, ⟨pk, a, ?_, ha⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hb : ∀ o l, o + l ≤ 10480 → 3296 ≤ o → bytesAt u.mem (at' S o) l = bytesAt t.mem (at' S o) l :=
      fun o l h₁ h₂ => bytesAt_congr fun i hi =>
        f₁.bytes (R := ⟨at' S o, l⟩) (hd3 o l (by omega) (.inr (by rw [hv]; omega))) (show l ≤ 2 ^ 64 by omega) hi
    have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
    have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
    refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [← hE.rc r hr k hk]
      exact f₁.readW (r := ⟨at' S (1600 + 32 * r + 8 * k), 8⟩) (Region.contains_self _ _)
        (hd3 _ 8 (by omega) (.inl (by rw [hv]; omega))) (by decide)
    · rw [← hE.seedA k hk, hb _ _ (by rw [hLA]; omega) (by rw [hLA]; omega)]
    · rw [← hE.seedB k hk, hb _ _ (by rw [hLB]; omega) (by rw [hLB]; omega)]
    · rw [← hE.adrsA k hk, hb _ _ (by rw [hLA]; omega) (by rw [hLA]; omega)]
    · rw [← hE.adrsB k hk, hb _ _ (by rw [hLB]; omega) (by rw [hLB]; omega)]
  · exact f₁.readW (r := ⟨at' S (Layout.oVar 4 6), 8⟩) (Region.contains_self _ _)
      (hd3 _ 8 (by rw [hv]; omega) (.inr (by rw [hv, hv]; omega))) (by decide)

theorem halve_li (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {stack no z P : Nat} {sp AP : Addr} {u : State}
    (hm : Mid p S stack no z P sp AP u) :
    WP isa (.block halve) u (LI p S stack no z P sp AP P) := by
  obtain ⟨t, g, hk, hwr, ⟨pk, a, hE, ha⟩, h6⟩ := hm
  have hPn : (2 * P + 8) * p.n ≤ Layout.oSigTmp := by have := g.cap; omega
  have eT : Layout.oSigTmp = 31648 := rfl
  refine wp_shr (d := .r15) (by decide) (by decide) fun u₁ v₁ => Proof.Sha3.X86_64.wp_mov32i (d := .rbp)
    fun u₂ v₂ => WP.block_nil ⟨0, by omega, by have := g.P_pos; omega, ⟨?_, ?_, ?_, by rw [v₂.gpr]; rfl, ?_, ?_, g.z_lt,
      by decide, by have := g.P_le; omega, g.no_lo, by have := g.cap; omega, ?_, by rw [v₂.wr, v₁.wr, hwr]; exact g.wr,
      g.fit, g.stk, pk, a, by rw [v₂.mem, v₁.mem]; exact hE, ha⟩, ?_⟩
  · rw [v₂.other _ (by decide), v₁.other _ (by decide), hk _ (by simp), g.bx]
  · rw [v₂.other _ (by decide), v₁.other _ (by decide), hk _ (by simp), g.r12]
  · rw [v₂.other _ (by decide), v₁.other _ (by decide), hk _ (by simp), g.r14]
  · rw [v₂.other _ (by decide), v₁.gpr, hk _ (by simp), g.r15, shr_one P (by have := g.P_le; omega)]
  · rw [v₂.other _ (by decide), v₁.other _ (by decide), hk _ (by simp), g.rsp]
  · rw [v₂.mem, v₁.mem, h6]; exact g.v6
  · rw [v₂.other _ (by decide), v₁.other _ (by decide), hk _ (by simp), g.r13]

theorem height_ct (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S : Addr} {no z P : Nat} {sp AP : Addr} (hP : P ≤ 2 ^ 13) (hcap : no + (2 * P + 8) * p.n ≤ 2 ^ 16) :
    RelCT isa (fun a b => HPre p S stack no z P sp AP a ∧ HPre p S stack no z P sp AP b)
      (heightBody ⟨p.n, p.len⟩ name T.code) fun _ _ => True := by
  have hlv : ∀ u, LI p S stack no z P sp AP P u →
      WP isa (.loop (levelBody ⟨p.n, p.len⟩ name T.code) .b) u (LQ z P sp AP) := fun u h =>
    wpLoop _ _ (level_step T name hn hf hst hs63 hP hcap) P h
  unfold heightBody
  refine relAssoc (relSeq (ct_scan hn fun a b ⟨g₁, g₂⟩ r hr => ?_) (fun a h => scan_mid hn h)
    (fun b h => scan_mid hn h) (relSeq (ct_halve fun a b ⟨⟨t₁, g₁, k₁, _⟩, ⟨t₂, g₂, k₂, _⟩⟩ r hr => ?_)
      (fun a h => halve_li hn h) (fun b h => halve_li hn h)
      (relSeq (RelCT.mono (level_ct T name hn hf hst hs63 hP hcap) (fun _ _ h => h) fun _ _ _ => trivial) hlv hlv
        (ct_next hn fun a b ⟨⟨a1, a2, a3, _⟩, ⟨b1, b2, b3, _⟩⟩ r hr => ?_))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g₁.bx, g₂.bx]
    · rw [g₁.r12, g₂.r12]
    · rw [g₁.r13, g₂.r13]
    · rw [g₁.r14, g₂.r14]
    · rw [g₁.r15, g₂.r15]
    · rw [g₁.rsp, g₂.rsp]
  · simp only [List.mem_singleton] at hr; subst hr
    rw [k₁ _ (by simp), k₂ _ (by simp), g₁.r15, g₂.r15]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]


/-! ## The heights -/

/-- The heights' invariant in one run, `m` heights before the end. -/
def HI (p : Params) (S : Addr) (stack no h z₀ : Nat) (sp AU : Addr) (W : List Region) (m : Nat) (s : State) : Prop :=
  ∃ r, m = h - r ∧ r < h ∧ HPre p S stack no (z₀ + r) (2 ^ (h - r - 1)) sp (AU + BitVec.ofNat 64 (r * p.n)) s ∧
    s.wr = W

theorem heights_step (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S : Addr} {no h z₀ : Nat} {sp AU : Addr} {W : List Region} (hzh : z₀ + h ≤ 14)
    (hcap : no + (2 ^ h + 8) * p.n ≤ Layout.oSigTmp) (hWA : (⟨AU, h * p.n⟩ : Region) ∈ W)
    (hAf : AU.toNat + h * p.n ≤ 2 ^ 64) (hAd : Region.Disjoint ⟨AU, h * p.n⟩ ⟨S, Layout.oSigTmp⟩)
    (hAs : Region.Disjoint ⟨AU, h * p.n⟩ (below sp stack)) :
    ∀ m s, HI p S stack no h z₀ sp AU W m s → WP isa (heightBody ⟨p.n, p.len⟩ name T.code) s fun s' =>
      isa.eval .ne s' = some (decide (m ≠ 1)) ∧ (decide (m ≠ 1) = false → s'.gpr .rbx = S) ∧
      (decide (m ≠ 1) = true → m - 1 < m ∧ HI p S stack no h z₀ sp AU W (m - 1) s') := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  intro m s ⟨r, hm, hr, g, hW⟩
  subst hm
  obtain ⟨pk, a, hE, ha⟩ := g.env
  obtain ⟨k, hk⟩ : ∃ k, h - r - 1 = k := ⟨_, rfl⟩
  rw [hk] at g
  refine WP.mono (height_ok T name hn hf hst hs63 (L := (List.range (2 * 2 ^ k)).map fun i =>
      bytesAt s.mem (at' S (no + i * p.n)) p.n) g.bx g.r12 g.r13 g.r14 g.r15 g.z_lt g.P_pos g.P_le g.no_lo g.cap
    rfl rfl rfl rfl rfl g.v0 g.v5 g.v6 g.wr g.fit (by rw [g.rsp]; exact g.stk) hE ha g.au g.ad
    (by rw [g.rsp]; exact g.as) (by simp) (fun i hi => by simp [List.getD_eq_getElem?_getD, hi])) fun s' hp => ?_
  have hk1 : (2 ^ k = 1) ↔ h - r = 1 := by
    rw [Nat.pow_eq_one]; omega
  refine ⟨by show s'.zf.map (!·) = _; rw [hp.zf]; simp [hk1], fun hc => ?_, fun hc => ?_⟩
  · rw [hp.keep _ (by simp), g.bx]
  · have hc' : h - r ≠ 1 := of_decide_eq_true hc
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hpow : 2 ^ (k' + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
    have hc2 : (2 * 2 ^ k' + 8) * p.n ≤ (2 ^ h + 8) * p.n :=
      Nat.mul_le_mul_right _ (by rw [Nat.pow_succ] at hpow; omega)
    have hr1 : (r + 1) * p.n + p.n ≤ h * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 + 1 ≤ h by omega); rwa [Nat.succ_mul] at this
    have hsub : Region.Sub ⟨AU + BitVec.ofNat 64 ((r + 1) * p.n), p.n⟩ ⟨AU, h * p.n⟩ := Offset.sub_base AU hr1
    have hvr : ∀ i, i ≠ 3 → i < 42 → s'.mem.readW (at' S (Layout.oVar 4 i)) 64 = s.mem.readW (at' S (Layout.oVar 4 i)) 64 :=
      fun i h₁ h₂ => hp.vars _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv, hv]; omega)
    refine ⟨by omega, r + 1, by omega, by omega, ⟨by rw [hp.keep _ (by simp), g.bx], by rw [hp.keep _ (by simp), g.r12],
      by rw [hp.r13, add_add, Nat.add_mul, Nat.one_mul], by rw [hp.r14, Nat.add_assoc],
      by rw [hp.r15, show h - (r + 1) - 1 = k' by omega, Nat.pow_succ, Nat.mul_comm], by rw [hp.keep _ (by simp), g.rsp],
      by omega, Nat.one_le_two_pow, Nat.pow_le_pow_right (by decide) (by omega), g.no_lo,
      by rw [show h - (r + 1) - 1 = k' by omega]; omega, by rw [hvr 0 (by decide) (by decide)]; exact g.v0,
      by rw [hvr 5 (by decide) (by decide)]; exact g.v5, by rw [hvr 6 (by decide) (by decide)]; exact g.v6,
      by rw [hp.wr]; exact g.wr, g.fit, g.stk, ⟨pk, a, hp.env, ha⟩, fun w hw' => ?_, hAd.sub_left hsub, hAs.sub_left hsub⟩,
      by rw [hp.wr, hW]⟩
    refine ⟨_, by rw [hp.wr, hW]; exact hWA, ?_⟩
    rw [add_add]
    exact Offset.contains_base AU (by omega) (by omega)

theorem heights_ct (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S : Addr} {no h z₀ : Nat} {sp AU : Addr} {W : List Region} (hzh : z₀ + h ≤ 14)
    (hcap : no + (2 ^ h + 8) * p.n ≤ Layout.oSigTmp) (hWA : (⟨AU, h * p.n⟩ : Region) ∈ W)
    (hAf : AU.toNat + h * p.n ≤ 2 ^ 64) (hAd : Region.Disjoint ⟨AU, h * p.n⟩ ⟨S, Layout.oSigTmp⟩)
    (hAs : Region.Disjoint ⟨AU, h * p.n⟩ (below sp stack)) :
    RelCT isa (fun a b => HI p S stack no h z₀ sp AU W h a ∧ HI p S stack no h z₀ sp AU W h b)
      (.loop (heightBody ⟨p.n, p.len⟩ name T.code) .ne) fun a b => a.gpr .rbx = S ∧ b.gpr .rbx = S := by
  have eT : Layout.oSigTmp = 31648 := rfl
  refine relLoop (fun m => decide (m ≠ 1)) (fun m => m - 1) (fun m => ?_)
    (heights_step T name hn hf hst hs63 hzh hcap hWA hAf hAd hAs)
    (heights_step T name hn hf hst hs63 hzh hcap hWA hAf hAd hAs) h
  have hb : ∀ s, HI p S stack no h z₀ sp AU W m s →
      HPre p S stack no (z₀ + (h - m)) (2 ^ (h - (h - m) - 1)) sp (AU + BitVec.ofNat 64 ((h - m) * p.n)) s ∧
        m ≤ h ∧ 1 ≤ m := fun s ⟨r, hm, hr, g, _⟩ => by
    rw [show h - m = r by omega]; exact ⟨g, by omega, by omega⟩
  by_cases hmv : 1 ≤ m ∧ m ≤ h
  · have hpm : 2 ^ (h - (h - m) - 1) ≤ 2 ^ 13 := Nat.pow_le_pow_right (by decide) (by omega)
    have hph : 2 * 2 ^ (h - (h - m) - 1) ≤ 2 ^ h := by
      rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by decide) (by omega)
    have hc2 : (2 * 2 ^ (h - (h - m) - 1) + 8) * p.n ≤ (2 ^ h + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
    exact RelCT.mono (height_ct T name hn hf hst hs63 hpm (by omega)) (fun a b ⟨ha, hb'⟩ => ⟨(hb a ha).1, (hb b hb').1⟩)
      fun _ _ h => h
  · exact RelCT.of_false fun a b ⟨ha, _⟩ => hmv ⟨(hb a ha).2.2, (hb a ha).2.1⟩


/-! ## The whole function -/

/-- After the prologue, the heights' invariant at the first height. -/
theorem pro_hi {stack : Nat} {s : State} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hpre : (levelsContract p stack).pre s) {no : Nat} (hno : s.gpr .rsi = at' (s.gpr .rdi) no)
    (hno' : no = Layout.oN ∨ no = Layout.oRoots) :
    WP isa (.block pro) s (HI p (s.gpr .rdi) stack no (heightsOf s) (s.gpr .rcx).toNat (s.gpr .rsp) (s.gpr .r8) s.wr
      (heightsOf s)) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eT : Layout.oSigTmp = 31648 := rfl
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  obtain ⟨hR, ⟨pk₀, a₀, hE₀⟩, _, hh1, hzh, hcnt, hcN, hcR, h9, hv5, hv6, _, _⟩ := hpre
  generalize hSdef : s.gpr .rdi = S at hR hE₀ hcN hcR hv5 hv6 hno
  generalize hhdef : heightsOf s = h at hR hh1 hzh hcnt
  have hcap : no + (2 ^ h + 8) * p.n ≤ Layout.oSigTmp := by
    have eN : Layout.oN = 12640 := rfl
    have eR : Layout.oRoots = 29280 := rfl
    have eNS : Layout.nodeSlots = 520 := rfl
    rcases hno' with rfl | rfl
    · have := hcN hno; rw [hcnt] at this; omega
    · have := hcR hno; rw [hcnt] at this; omega
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr := by rw [hR.wr_eq]; simp [scratchLen]
  have hwA : (⟨s.gpr .r8, h * p.n⟩ : Region) ∈ s.wr := by rw [hR.wr_eq]; simp
  have ha : a₀.length = 16 := by rw [← hE₀.adrsA 0 (by decide)]; simp [bytesAt]
  have hlow : ∀ o l, o + l ≤ 2912 ∨ 2968 ≤ o → o + l ≤ 2 ^ 16 →
      Region.Disjoint ⟨at' S o, l⟩ ⟨at' S (Layout.oSave 4 0), 56⟩ := fun o l h₁ h₂ =>
    disj_scr S (by rw [oSave4]; omega) h₂ (by rw [oSave4]; omega)
  refine WP.mono (pro_ok (by rw [hSdef]; exact hwS)) fun t₀ hp => ?_
  have hpf : Frame [⟨at' S (Layout.oSave 4 0), 56⟩] s.mem t₀.mem := by have := hp.frame; rwa [hSdef] at this
  have hpv0 : t₀.mem.readW (at' S (Layout.oVar 4 0)) 64 = s.gpr .r9 := by have := hp.v0; rwa [hSdef] at this
  have hkeep₀ : ∀ o, (o + 8 ≤ 2912 ∨ 2968 ≤ o) → o + 8 ≤ 2 ^ 16 →
      t₀.mem.readW (at' S o) 64 = s.mem.readW (at' S o) 64 := fun o h₁ h₂ =>
    hpf.readW (r := ⟨at' S o, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hlow o 8 h₁ h₂) (by decide)
  have hE₁ : Env p t₀.mem S pk₀ a₀ := by
    have hb : ∀ o l, 3296 ≤ o → o + l ≤ 10480 → bytesAt t₀.mem (at' S o) l = bytesAt s.mem (at' S o) l :=
      fun o l h₁ h₂ => bytesAt_congr fun i hi => hpf.bytes (R := ⟨at' S o, l⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hlow o l (.inr (by omega)) (by omega))
        (show l ≤ 2 ^ 64 by omega) hi
    have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
    have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
    refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [← hE₀.rc r hr k hk]; exact hkeep₀ _ (.inl (by omega)) (by omega)
    · rw [← hE₀.seedA k hk, hb _ _ (by rw [hLA]; omega) (by rw [hLA]; omega)]
    · rw [← hE₀.seedB k hk, hb _ _ (by rw [hLB]; omega) (by rw [hLB]; omega)]
    · rw [← hE₀.adrsA k hk, hb _ _ (by rw [hLA]; omega) (by rw [hLA]; omega)]
    · rw [← hE₀.adrsB k hk, hb _ _ (by rw [hLB]; omega) (by rw [hLB]; omega)]
  have hpow : 2 * 2 ^ (h - 0 - 1) = 2 ^ h := by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    rw [show k + 1 - 0 - 1 = k by omega, Nat.pow_succ, Nat.mul_comm]
  have hP13 : 2 ^ (h - 0 - 1) ≤ 2 ^ 13 := Nat.pow_le_pow_right (by decide) (by omega)
  have hAd : Region.Disjoint ⟨s.gpr .r8, h * p.n⟩ ⟨S, Layout.oSigTmp⟩ := hR.out_scr
  have hsub : Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 (0 * p.n), p.n⟩ ⟨s.gpr .r8, h * p.n⟩ :=
    Offset.sub_base _ (by have := Nat.mul_le_mul_right p.n hh1; omega)
  refine ⟨0, by omega, by omega, ⟨by rw [hp.bx, hSdef], by rw [hp.r12, hno], by rw [hp.r13]; simp,
    by rw [hp.r14]; simp, by rw [hp.r15, hpow, ← hcnt, ofNat_toNat64], hp.sp, by omega, Nat.one_le_two_pow, hP13,
    by rcases hno' with rfl | rfl <;> decide, by rw [hpow]; exact hcap, by rw [hpv0]; exact h9,
    by rw [hkeep₀ _ (.inr (by rw [hv]; omega)) (by rw [hv]; omega)]; exact hv5,
    by rw [hkeep₀ _ (.inr (by rw [hv]; omega)) (by rw [hv]; omega)]; exact hv6, by rw [hp.wr]; exact hwS, hR.scr_fit,
    hR.stk_scr, ⟨pk₀, a₀, hE₁, ha⟩, fun w hw => ⟨_, by rw [hp.wr]; exact hwA, ?_⟩, hAd.sub_left hsub,
    hR.stk_out.symm.sub_left hsub⟩, hp.wr⟩
  rw [add_add]
  have : 8 * w + 8 ≤ p.n := by omega
  have hf := hR.out_fit
  exact Offset.contains_base _ (by have := Nat.mul_le_mul_right p.n hh1; omega) (by omega)


/-- A state of the precondition with given public data. -/
abbrev LPub (p : Params) (stack : Nat) (S RSI RDX RCX R8 SP : Addr) (s : State) : Prop :=
  (levelsContract p stack).pre s ∧ s.gpr .rdi = S ∧ s.gpr .rsi = RSI ∧ s.gpr .rdx = RDX ∧ s.gpr .rcx = RCX ∧
    s.gpr .r8 = R8 ∧ s.gpr .rsp = SP

theorem levels_ct (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) :
    ConstantTime isa (levelsContract p stack).pre (levelsContract p stack).pub (levels ⟨p.n, p.len⟩ name T.code) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eT : Layout.oSigTmp = 31648 := rfl
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hpub
  -- the public data, from the first run
  have h₁c := h₁
  obtain ⟨hR, _, hrsi, hh1, hzh, hcnt, hcN, hcR, _, _, _, _, _⟩ := h₁c
  obtain ⟨S, eS⟩ : ∃ S, s₁.gpr .rdi = S := ⟨_, rfl⟩
  obtain ⟨h, eh⟩ : ∃ h, heightsOf s₁ = h := ⟨_, rfl⟩
  rw [eS] at hR hrsi hcN hcR
  rw [eh] at hR hh1 hzh hcnt
  obtain ⟨no, hno₁, hno₂⟩ : ∃ no, s₁.gpr .rsi = at' S no ∧ (no = Layout.oN ∨ no = Layout.oRoots) := by
    rcases hrsi with h' | h'
    · exact ⟨_, h', .inl rfl⟩
    · exact ⟨_, h', .inr rfl⟩
  obtain ⟨W, eW⟩ : ∃ W : List Region, W = [⟨S, scratchLen⟩, ⟨s₁.gpr .r8, h * p.n⟩] := ⟨_, rfl⟩
  have hA : ∀ s, LPub p stack S (s₁.gpr .rsi) (s₁.gpr .rdx) (s₁.gpr .rcx) (s₁.gpr .r8) (s₁.gpr .rsp) s →
      WP isa (.block pro) s (HI p S stack no h (s₁.gpr .rcx).toNat (s₁.gpr .rsp) (s₁.gpr .r8) W h) := by
    intro s ⟨hpre, e1, e2, e3, e4, e5, e6⟩
    have ehs : heightsOf s = h := by rw [← eh]; simp only [heightsOf, e3]
    have := pro_hi hn hpre (no := no) (by rw [e2, hno₁, e1]) hno₂
    have hw : s.wr = W := by
      rw [hpre.1.wr_eq, eW, e1, e5, ehs]
    rwa [e1, e6, e4, e5, hw, ehs] at this
  have hcap : no + (2 ^ h + 8) * p.n ≤ Layout.oSigTmp := by
    have eN : Layout.oN = 12640 := rfl
    have eR : Layout.oRoots = 29280 := rfl
    have eNS : Layout.nodeSlots = 520 := rfl
    rcases hno₂ with e | e
    · have := hcN (by rw [hno₁, e]); rw [hcnt] at this; rw [e]; omega
    · have := hcR (by rw [hno₁, e]); rw [hcnt] at this; rw [e]; omega
  have hWA : (⟨s₁.gpr .r8, h * p.n⟩ : Region) ∈ W := by rw [eW]; simp
  have hct : RelCT isa (fun a b =>
      LPub p stack S (s₁.gpr .rsi) (s₁.gpr .rdx) (s₁.gpr .rcx) (s₁.gpr .r8) (s₁.gpr .rsp) a ∧
      LPub p stack S (s₁.gpr .rsi) (s₁.gpr .rdx) (s₁.gpr .rcx) (s₁.gpr .r8) (s₁.gpr .rsp) b)
      (levels ⟨p.n, p.len⟩ name T.code) fun _ _ => True := by
    have hl : ∀ u, HI p S stack no h (s₁.gpr .rcx).toNat (s₁.gpr .rsp) (s₁.gpr .r8) W h u →
        WP isa (.loop (heightBody ⟨p.n, p.len⟩ name T.code) .ne) u fun s' => s'.gpr .rbx = S := fun u hu =>
      wpLoop _ _ (heights_step T name hn hf hst hs63 hzh hcap hWA hR.out_fit hR.out_scr hR.stk_out.symm) h hu
    unfold levels
    refine relSeq (ct_pro fun a b ⟨⟨_, a1, _⟩, ⟨_, b1, _⟩⟩ r hr => ?_) hA hA
      (relSeq (RelCT.mono (heights_ct T name hn hf hst hs63 hzh hcap hWA hR.out_fit hR.out_scr hR.stk_out.symm)
        (fun _ _ h => h) fun _ _ _ => trivial) hl hl
        (ct_restore fun a b ⟨a1, b1⟩ r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; rw [a1, b1]
    · simp only [List.mem_singleton] at hr; subst hr; rw [a1, b1]
  exact (hct _ _ _ _ _ _ ⟨⟨h₁, eS, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, by rw [← hp1, eS], hp2.symm, hp3.symm, hp4.symm, hp5.symm,
    hp6.symm⟩⟩ e₁ e₂).1


/-! ## The stack pointer, the depth of calls, and calls of `levels` -/

theorem nosp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) :=
  fun i hi => (List.mem_append.mp hi).elim (ha i) (hb i)

theorem nosp_block {is : List Instr} (h : is.all (fun i => !Taint.clobbers i .rsp) = true) : NoSp (.block is) :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

/-- `levels` never writes `rsp` itself. -/
theorem levels_nosp (hn : Ns p.n) (name : String) {t4 : Prog isa} (hT : NoSp t4) :
    NoSp (levels ⟨p.n, p.len⟩ name t4) := by
  unfold levels heightBody levelBody Impl.SlhDsa.X86_64.thashCall
  rcases hn with h | h | h <;> rw [h] <;>
  exact nosp_seq (nosp_block (by kernel_rfl))
    (nosp_seq (fun i hi => nosp_seq (nosp_block (by kernel_rfl))
      (nosp_seq (fun i hi => nosp_block (by kernel_rfl) i hi)
        (nosp_seq (nosp_block (by kernel_rfl))
          (nosp_seq (fun i hi => nosp_seq (nosp_block (by kernel_rfl))
              (nosp_seq (nosp_seq (nosp_block (by kernel_rfl)) (fun i hi => hT i hi)) (nosp_block (by kernel_rfl))) i hi)
            (nosp_block (by kernel_rfl))))) i hi)
      (nosp_block (by kernel_rfl)))

theorem levels_depth (L : Layout) (name : String) (t4 : Prog isa) :
    (levels L name t4).depth = t4.depth + 1 := by
  simp [levels, heightBody, levelBody, Impl.SlhDsa.X86_64.thashCall, Code.depth]

/-- `levels`, from its precondition, as `WP.call` needs it. -/
theorem levels_correct (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) :
    ∀ s, (levelsContract p stack).pre s → ∃ t s', Exec isa (levels ⟨p.n, p.len⟩ name T.code) s t s' ∧
      abiPreserved s s' ∧ (levelsContract p stack).post s s' := fun s h => by
  obtain ⟨t, s', e, abi, post⟩ := levels_wp T name hn hf hst hs63 h
  exact ⟨t, s', e, abi, post⟩

/-- A call of `levels`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem levelscall_ok (T : Thash4Impl p.n) (name ln : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {s : State}
    {rd wr : List Region} (hpre : (levelsContract p stack).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (T.code.depth + 2))]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (levelsContract p stack).post (s.callEntry.withRegions rd wr) s₂) →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call ln (levels ⟨p.n, p.len⟩ name T.code)) s Q := by
  have hd := T.depth_le
  exact WP.call_mx (levels_correct T name hn hf hst hs63) (levels_nosp hn name T.nosp)
    (by rw [levels_depth]; omega_using [hd]) hpre hc hw fun s' h₁ h₂ h₃ h₄ _ h₆ h₇ =>
      hQ s' h₁ h₂ h₃ (by rw [levels_depth] at h₄; exact h₄) h₆ h₇


/-! ## A state satisfying the precondition -/

/-- The witness's stack pointer, `2^63`, below which any `stack < 2^63` bytes fit; `scratch` and the
path above it. -/
abbrev lsp : Addr := BitVec.ofNat 64 (2 ^ 63)
abbrev lS : Addr := lsp + BitVec.ofNat 64 0x100000
abbrev lAU : Addr := lsp + BitVec.ofNat 64 0x200000

theorem lS_toNat : lS.toNat = 2 ^ 63 + 0x100000 := by decide

/-- The witness's memory: the round constants at `scratch + 1600`, zeros elsewhere. -/
def lmem (x : Addr) : Byte :=
  if 2 ^ 63 + 0x100000 + 1600 ≤ x.toNat ∧ x.toNat < 2 ^ 63 + 0x100000 + 2368 then
    (Spec.Sha3.RC ((x.toNat - (2 ^ 63 + 0x100000) - 1600) / 32)).extractLsb'
      (8 * ((x.toNat - (2 ^ 63 + 0x100000) - 1600) % 8)) 8
  else 0

/-- A state satisfying the precondition of `levels`: two nodes of height 0 in `nodes`, one height. -/
def lsat (p : Params) : State where
  gpr r := match r with
    | .rdi => lS | .rsi => at' lS Layout.oN | .rdx => 2 | .r8 => lAU | .rsp => lsp | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := lmem
  rd := []
  wr := [⟨lS, scratchLen⟩, ⟨lAU, 1 * p.n⟩]

theorem lmem_at {o : Nat} (h : o < 2 ^ 16) : (at' lS o).toNat = 2 ^ 63 + 0x100000 + o := by
  rw [at', BitVec.toNat_add, lS_toNat, BitVec.toNat_ofNat]; omega

theorem lmem_zero {o : Nat} (h₁ : 2368 ≤ o) (h₂ : o < 2 ^ 16) : lmem (at' lS o) = 0 := by
  simp only [lmem, lmem_at h₂]
  exact ite_eq_right (fun h => absurd h.2 (by omega))

theorem lread_zero {o : Nat} (h₁ : 2368 ≤ o) (h₂ : o + 8 ≤ 2 ^ 16) : Mem.readW lmem (at' lS o) 64 = 0 := by
  simp only [Mem.readW]
  rw [Mem.read_eq_of_bytes (v := 0) fun i hi => by rw [at_add, lmem_zero (by omega) (by omega)]; simp]
  rfl

theorem lbytes_zero {o l : Nat} (h₁ : 2368 ≤ o) (h₂ : o + l ≤ 2 ^ 16) :
    bytesAt lmem (at' lS o) l = List.replicate l 0 :=
  bytesAt_eq (by simp) fun i hi => by rw [at_add, lmem_zero (by omega) (by omega)]; simp [hi]

theorem lsat_rc : RcTable lmem lS := by
  intro r hr k hk
  simp only [Mem.readW]
  rw [Mem.read_eq_of_bytes (v := Spec.Sha3.RC r) fun d hd => ?_]
  · exact BitVec.setWidth_eq _
  rw [show lS + BitVec.ofNat 64 (1600 + 32 * r + 8 * k) + BitVec.ofNat 64 d = at' lS (1600 + 32 * r + 8 * k + d) from
    at_add _ _ _]
  simp only [lmem, lmem_at (show 1600 + 32 * r + 8 * k + d < 2 ^ 16 by omega)]
  rw [ite_eq_left (by omega), show (2 ^ 63 + 0x100000 + (1600 + 32 * r + 8 * k + d) - (2 ^ 63 + 0x100000) - 1600) / 32 = r by
      omega, show (2 ^ 63 + 0x100000 + (1600 + 32 * r + 8 * k + d) - (2 ^ 63 + 0x100000) - 1600) % 8 = d by omega]

theorem lsat_pre (hn : Ns p.n) {stack : Nat} (hs63 : stack < 2 ^ 63) : (levelsContract p stack).pre (lsat p) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hh : heightsOf (lsat p) = 1 := by
    show Nat.log2 (BitVec.toNat (2 : BitVec 64)) = 1
    rw [show BitVec.toNat (2 : BitVec 64) = 2 ^ 1 from rfl, Nat.log2_two_pow]
  have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  have hAs : Region.Disjoint ⟨lAU, p.n⟩ ⟨lS, Layout.oSigTmp⟩ :=
    Offset.disjoint lsp (.inr (by rw [eT]; omega)) (by omega) (by rw [eT]; omega)
  refine ⟨⟨rfl, by rw [hh]; rfl,
    by show lS.toNat + scratchLen ≤ 2 ^ 64; rw [lS_toNat]; decide, ?_, by rw [hh, Nat.one_mul]; exact hAs, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, ?_, ?_, fun _ h => absurd h List.not_mem_nil, ?_, ?_,
    fun _ h => absurd h List.not_mem_nil⟩, ⟨List.replicate p.n 0, List.replicate 16 0, lsat_rc, fun k hk => ?_,
    fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩, .inl rfl, by rw [hh], by rw [hh]; show (0 : BitVec 64).toNat + 1 ≤ 14; decide,
    by rw [hh]; show (2 : BitVec 64).toNat = 2 ^ 1; decide,
    fun _ => by show (2 + 8) * p.n ≤ 32 * Layout.nodeSlots; simp only [Layout.nodeSlots]; omega,
    fun _ => by show (2 + 8) * p.n ≤ 1024; omega, by show (0 : BitVec 64).toNat < 2 ^ 32; decide,
    by simp only [varAt]; rw [show (lsat p).mem = lmem from rfl, show (lsat p).gpr .rdi = lS from rfl,
      lread_zero (by rw [hv]; omega) (by rw [hv]; omega)]; decide,
    by simp only [varAt]; rw [show (lsat p).mem = lmem from rfl, show (lsat p).gpr .rdi = lS from rfl,
      lread_zero (by rw [hv]; omega) (by rw [hv]; omega)]; decide,
    by simp only [varAt]; rw [show (lsat p).mem = lmem from rfl, show (lsat p).gpr .rdi = lS from rfl,
      lread_zero (by rw [hv]; omega) (by rw [hv]; omega)]; decide,
    by simp only [varAt]; rw [show (lsat p).mem = lmem from rfl, show (lsat p).gpr .rdi = lS from rfl,
      lread_zero (by rw [hv]; omega) (by rw [hv]; omega)]; decide⟩
  · rw [hh, Nat.one_mul]; show (lsp + BitVec.ofNat 64 0x200000).toNat + p.n ≤ 2 ^ 64
    have : (lsp + BitVec.ofNat 64 0x200000).toNat = 2 ^ 63 + 0x200000 := by decide
    omega
  · exact (Offset.disjoint_base lsp (k := 8) (by omega) (by rw [show scratchLen = 65536 from rfl]; omega)).symm
  · rw [hh, Nat.one_mul]; exact (Offset.disjoint_base lsp (k := 8) (by omega) (by omega)).symm
  · exact (Offset.disjoint_below lsp (n := stack) (d := 0x100000) (k := scratchLen) (by rw [show scratchLen = 65536 from rfl]; omega)).symm
  · rw [hh, Nat.one_mul]
    exact (Offset.disjoint_below lsp (n := stack) (d := 0x200000) (k := p.n) (by omega)).symm
  · exact (lbytes_zero (by rw [hLA]; omega) (by rw [hLA]; omega))
  · exact (lbytes_zero (by rw [hLB]; omega) (by rw [hLB]; omega))
  · exact (lbytes_zero (by rw [hLA]; omega) (by rw [hLA]; omega))
  · exact (lbytes_zero (by rw [hLB]; omega) (by rw [hLB]; omega))

/-! ## `Verified` -/

theorem levels_verified (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) :
    Verified X86_64.target (levels ⟨p.n, p.len⟩ name T.code) (levelsContract p stack) :=
  ⟨levels_correct T name hn hf hst hs63, levels_ct T name hn hf hst hs63, ⟨lsat p, lsat_pre hn hs63⟩⟩

end VG.Proof.SlhDsa.X86_64.Levels
