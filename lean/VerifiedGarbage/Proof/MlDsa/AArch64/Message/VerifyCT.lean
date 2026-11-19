module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Hash
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Args
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
public import VerifiedGarbage.Spec.MlDsa

/-! ### `MlDsa.AArch64.Message.Rel`, which this module and modules that import it used -/

section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message_cached`: two runs

Untrusted: everything here is checked by Lean. Blocks whose addresses are
functions of `x28` and the stack pointer, which they keep, leak the same in
runs that agree on those (`block_x28_tr`): the moves of a call's arguments
are such (`setArgs_xOnly`). Two runs with the same layout, each in `Ctx`
with inputs related by `I` (`Two`), and a call in them of verified code
whose public data agree (`call_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)

/-! ## Blocks addressed from `x28` -/

/-- An instruction whose addresses are a function of `x28` and the stack
pointer, which it keeps. -/
def XOnly (i : Instr) : Prop :=
  (∀ s₁ s₂ : State, s₁.gpr .x28 = s₂.gpr .x28 → s₁.sp = s₂.sp → isa.addrs i s₁ = isa.addrs i s₂) ∧
    clobbers i .x28 = false

theorem execBlock_x28_tr : ∀ {is : List Instr}, (∀ i ∈ is, XOnly i) →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, s₁.gpr .x28 = s₂.gpr .x28 → s₁.sp = s₂.sp →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, h28, hsp, e₁, e₂ => by
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
    have h28' : a₁.gpr .x28 = a₂.gpr .x28 := by rw [exec_gpr hi.2 ha₁, exec_gpr hi.2 ha₂, h28]
    have hsp' : a₁.sp = a₂.sp := by rw [exec_sp ha₁, exec_sp ha₂, hsp]
    have ht := execBlock_x28_tr (fun j hj => h j (List.mem_cons_of_mem _ hj)) h28' hsp' eb₁ eb₂
    rw [show addrs i s₁ = addrs i s₂ from hi.1 _ _ h28 hsp, ht]

theorem block_x28_tr {is : List Instr} (h : ∀ i ∈ is, XOnly i) {P : State → State → Prop}
    (hp : ∀ a b, P a b → a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨execBlock_x28_tr h (hp _ _ hP).1 (hp _ _ hP).2 e₁ e₂, trivial⟩

theorem arg_xOnly (d : Reg) (hd : d ≠ .x28) (a : Arg) : ∀ i ∈ a.mov d, XOnly i := by
  intro i hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl <;>
    exact ⟨fun s₁ s₂ h _ => by simp [addrs, h], by simpa [clobbers, dstOf] using hd⟩

theorem setArgs_xOnly {as : List (Reg × Arg)} (h : argsOk as = true) : ∀ i ∈ setArgs as, XOnly i := by
  induction as with
  | nil => intro i hi; simp [setArgs] at hi
  | cons da as ih =>
    obtain ⟨d, a⟩ := da
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro i hi
    simp only [setArgs, List.flatMap_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact arg_xOnly d h.1.1.2 a i hi
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

/-! ## Two runs -/

/-- Two runs with the layout `L`, inputs related by `I`, each satisfying `Φ`. -/
def Two (I : Lay → Mem → Mem → Prop) (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ (L : Lay) (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧
    Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b

section
variable {I : Lay → Mem → Mem → Prop}

theorem Two.x28 {Φ : Lay → Mem → State → Prop} {a b : State} (h : Two I Φ a b) :
    a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp :=
  let ⟨_, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := h
  ⟨c₁.x28.trans c₂.x28.symm, c₁.sp.trans c₂.sp.symm⟩

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two I Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g v m₀ (t : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g v m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two I Φ) c (Two I Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ v₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ v₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- What the moves of the arguments `as` leave. -/
abbrev Moved (as : List (Reg × Arg)) (t t1 : State) : Prop :=
  (∀ da ∈ as, t1.gpr da.1 = da.2.val t) ∧ Only (as.map (·.1)) t t1

/-- A call after the moves of its arguments, of verified code whose public
data agree in both runs. -/
theorem call_tr {Φ : Lay → Mem → State → Prop} {as : List (Reg × Arg)} (hok : argsOk as = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g v m₀ (t t1 : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t → Moved as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → Ctx L g₁ v₁ m₁ a →
      Ctx L g₂ v₂ m₂ b → Φ L m₁ a → Φ L m₂ b → Moved as a a1 → Moved as b b1 →
      k.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : Lay) g v m₀ (t : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t →
      (∀ r ∈ rd L, ∃ R ∈ L.rd ++ L.wr, Within r R) ∧ (∀ r ∈ wr L, ∃ R ∈ L.wr, Within r R)) :
    RelCT isa (Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, Two I Φ a b ∧ Moved as a a1 ∧ Moved as b b1)
    (block_x28_tr (setArgs_xOnly hok) fun _ _ h => h.x28)
    (fun x y ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, _, _⟩ =>
      ⟨setArgs_ok as hok x (c₁.xOk hL), setArgs_ok as hok y (c₂.xOk hL)⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  -- The layout, out of the relation, so that the call's regions are fixed.
  refine RelCT.mono (P := fun a1 b1 => ∃ L : Lay, ∃ a b, (∃ (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
      (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧ Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b) ∧
      Moved as a a1 ∧ Moved as b b1)
    (RelCT.exists_ fun L => RelCT.call hv hct (rd L) (wr L) fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_)
    (fun a1 b1 ⟨a, b, ⟨L, hp⟩, f₁, f₂⟩ => ⟨L, a, b, hp, f₁, f₂⟩) fun _ _ h => h
  obtain ⟨g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ v₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g v m₀}, Ctx L g v m₀ t → Moved as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.2.rd, f.2.wr, hc.rd, hc.wr]
    refine ⟨covers_of_within fun r hr' => ?_, covers_of_within fun r hr' => ?_⟩
    · rcases List.mem_append.mp hr' with h' | h'
      · exact hr r h'
      · obtain ⟨R, hR, hW⟩ := hw r h'
        exact ⟨R, by simp [hR], hW⟩
    · exact hw r hr'
  exact ⟨hpre L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2⟩

end

end VG.Proof.MlDsa.AArch64.Message

end

end

/-! ### `MlDsa.AArch64.Message.SignCT`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Message.HashCT`, which this module and modules that import it used -/

section

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message_cached`: two runs of the hashing

Untrusted: everything here is checked by Lean. In two runs with the same
layout (`Two`), zeroing the state and each call of a sponge function leak
the same: their addresses and arguments are functions of the layout alone,
and the sponge functions' public data are those arguments (`zeroSt_tr`,
`kabs_tr`, `kpad_tr`, `ksqz_tr`); so does `muHash`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.Sha3 (rates)

section
variable {I : Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zeroSt_taint : (taint.check (AArch64.Taint.ofRegs [.x28]) (.block zeroSt) (.block [])).isSome = true := by
  rfl

theorem zeroSt_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) (.block zeroSt) fun _ _ => True :=
  AArch64.taintRel [.x28] (fun a b h => ⟨h.x28.2, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.x28.1⟩) zeroSt_taint

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`, in its registers. -/
structure AbsA (s : State) (st dt sc : Addr) (pos len : Nat) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = pos
  h3 : s.gpr .x3 = dt
  h4 : (s.gpr .x4).toNat = len
  h5 : s.gpr .x5 = sc
  hp : pos < 136
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  d₂ : Region.Disjoint ⟨dt, len⟩ ⟨st, 200⟩
  d₃ : Region.Disjoint ⟨dt, len⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₂ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨dt, len⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem AbsA.pre {s : State} {st dt sc : Addr} {pos len : Nat} (h : AbsA s st dt sc pos len) :
    Proof.Sha3.absorbAArch64.pre (s.callEntry.withRegions [⟨dt, len⟩] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, gpr_ce s (r := .x0), gpr_ce s (r := .x1), gpr_ce s (r := .x2),
    gpr_ce s (r := .x3), gpr_ce s (r := .x4), gpr_ce s (r := .x5), h.h0, h.h1, h.h2, h.h3, h.h4, h.h5]
  exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃, h.hsp, h.k₁, h.k₂, h.k₃, by decide, h.hp⟩

theorem absA_of {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g v m₀ t) {src len pos : Arg} (hm : Moved (absArgs src len pos) t t1) {dp : Addr} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n) (hq : pos.val t = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64) (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩)
    (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩) (kD : L.STK.Disjoint ⟨dp, n⟩) : AbsA t1 L.ST dp L.KS q n := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.x2, pos) (by simp)
  have e0 := hm.1 (.x0, .off oST) (by simp)
  have e1 := hm.1 (.x1, .imm 136) (by simp)
  have e3 := hm.1 (.x3, src) (by simp)
  have e4 := hm.1 (.x4, len) (by simp)
  have e5 := hm.1 (.x5, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, x0] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  exact ⟨e0, by rw [e1]; rfl, by rw [e2, BitVec.toNat_ofNat]; omega_using [hql], e3, by rw [e4, BitVec.toNat_ofNat]; omega_using [hnl], e5,
    hql, st_ks, dS, dK, by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL,
    by simp only [Proof.MlKem.AArch64.stk, hs1]; exact kD, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr_of (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : argsOk (absArgs src len pos) = true) (dp : Lay → Addr) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g vv m (t : State), L.Ok → Ctx L g vv m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ (L : Lay) g vv m (t : State), L.Ok → Ctx L g vv m t → Φ L m t →
      q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨dp L, n L⟩) :
    RelCT isa (Two I Φ) (kabs v.callee src len pos) fun _ _ => True := by
  have args : ∀ (L : Lay) g vv m₀ (t t1 : State), L.Ok → Ctx L g vv m₀ t → Φ L m₀ t →
      Moved (absArgs src len pos) t t1 → AbsA t1 L.ST (dp L) L.KS (q L) (n L) :=
    fun L g vv m₀ t t1 hL hc hφ hm => by
      obtain ⟨h1, h2, h3⟩ := hv L g vv m₀ t hL hc hφ
      obtain ⟨s1, s2, _, s4, s5, s6⟩ := hs L g vv m₀ t hL hc hφ
      exact absA_of hL hc hm h1 h2 h3 s1 s2 s4 s5 s6
  refine call_tr hok (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v) (fun L => [⟨dp L, n L⟩]) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc hφ hm => (args L g vv m₀ t t1 hL hc hφ hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L g vv m₀ t hL hc hφ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.absorbAArch64, State.withRegions_sp, State.callEntry_sp,
      gpr_ce a1 (r := .x0), gpr_ce a1 (r := .x1), gpr_ce a1 (r := .x2), gpr_ce a1 (r := .x3),
      gpr_ce a1 (r := .x4), gpr_ce a1 (r := .x5), gpr_ce b1 (r := .x0), gpr_ce b1 (r := .x1),
      gpr_ce b1 (r := .x2), gpr_ce b1 (r := .x3), gpr_ce b1 (r := .x4), gpr_ce b1 (r := .x5),
      x.h0, x.h3, x.h5, y.h0, y.h3, y.h5, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      BitVec.eq_of_toNat_eq (x.h4.trans y.h4.symm), by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · obtain ⟨_, _, hin, _, _, _⟩ := hs L g vv m₀ t hL hc hφ
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hin
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := cov_xw hL (e := 0) (k := 200) (by omega_using []); rwa [x0] at this
      · exact cov_xw hL (e := 200) (by omega_using [])

theorem kabs_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : argsOk (absArgs src len pos) = true) (dp : Lay → Addr) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g vv m (t : State), L.Ok → Ctx L g vv m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨dp L, n L⟩) :
    RelCT isa (Two I Φ) (kabs v.callee src len pos) fun _ _ => True :=
  kabs_tr_of v hok dp n q hv (fun L _ _ _ _ hL _ _ => hs L hL)

/-- The arguments of a call of `vg_keccak_pad`, in its registers. -/
structure PadA (s : State) (st sc : Addr) (pos : Nat) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = pos
  h4 : s.gpr .x4 = sc
  hp : pos < 136
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem PadA.pre {s : State} {st sc : Addr} {pos : Nat} (h : PadA s st sc pos) :
    Proof.Sha3.padAArch64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.padAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, gpr_ce s (r := .x0), gpr_ce s (r := .x1), gpr_ce s (r := .x2),
    gpr_ce s (r := .x4), h.h0, h.h1, h.h2, h.h4]
  exact ⟨trivial, trivial, h.d₁, h.hsp, h.k₁, h.k₃, by decide, h.hp⟩

theorem kpad_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} {pos : Arg}
    (hok : argsOk (padArgs pos) = true) (q : Lay → Nat)
    (hv : ∀ (L : Lay) g vv m (t : State), L.Ok → Ctx L g vv m t → Φ L m t → pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136) :
    RelCT isa (Two I Φ) (kpad v.callee pos) fun _ _ => True := by
  have args : ∀ (L : Lay) g vv m₀ (t t1 : State), L.Ok → Ctx L g vv m₀ t → Φ L m₀ t →
      Moved (padArgs pos) t t1 → PadA t1 L.ST L.KS (q L) :=
    fun L g vv m₀ t t1 hL hc hφ hm => by
      have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
      have e2 := hm.1 (.x2, pos) (by simp)
      have e0 := hm.1 (.x0, .off oST) (by simp)
      have e1 := hm.1 (.x1, .imm 136) (by simp)
      have e4 := hm.1 (.x4, .off oKS) (by simp)
      simp only [Arg.val, hc.x28, oST, oKS, x0] at e0 e1 e4
      rw [hv L g vv m₀ t hL hc hφ] at e2
      have := hs L hL
      exact ⟨e0, by rw [e1]; rfl, by rw [e2, BitVec.toNat_ofNat]; omega_using [this], e4, this, st_ks,
        by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL⟩
  refine call_tr hok (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc hφ hm => (args L g vv m₀ t t1 hL hc hφ hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.padAArch64, State.withRegions_sp, State.callEntry_sp,
      gpr_ce a1 (r := .x0), gpr_ce a1 (r := .x1), gpr_ce a1 (r := .x2), gpr_ce a1 (r := .x4),
      gpr_ce b1 (r := .x0), gpr_ce b1 (r := .x1), gpr_ce b1 (r := .x2), gpr_ce b1 (r := .x4),
      x.h0, x.h4, y.h0, y.h4, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := cov_xw hL (e := 0) (k := 200) (by omega_using []); rwa [x0] at this
    · exact cov_xw hL (e := 200) (by omega_using [])

/-- The arguments of a call of `vg_keccak_squeeze`, in its registers. -/
structure SqzA (s : State) (st out sc : Addr) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = 0
  h3 : s.gpr .x3 = out
  h4 : (s.gpr .x4).toNat = 64
  h5 : s.gpr .x5 = sc
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨out, 64⟩
  d₂ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  d₃ : Region.Disjoint ⟨out, 64⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₂ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨out, 64⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem SqzA.pre {s : State} {st out sc : Addr} (h : SqzA s st out sc) :
    Proof.Sha3.squeezeAArch64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨out, 64⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.squeezeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, gpr_ce s (r := .x0), gpr_ce s (r := .x1), gpr_ce s (r := .x2),
    gpr_ce s (r := .x3), gpr_ce s (r := .x4), gpr_ce s (r := .x5), h.h0, h.h1, h.h2, h.h3, h.h4, h.h5]
  exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃, h.hsp, h.k₁, h.k₂, h.k₃, by decide, by decide⟩

theorem ksqz_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} :
    RelCT isa (Two I Φ) (ksqz v.callee) fun _ _ => True := by
  have args : ∀ (L : Lay) g vv m₀ (t t1 : State), L.Ok → Ctx L g vv m₀ t →
      Moved sqzArgs t t1 → SqzA t1 L.ST L.MU L.KS :=
    fun L g vv m₀ t t1 hL hc hm => by
      have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
      have e0 := hm.1 (.x0, .off oST) (by simp)
      have e1 := hm.1 (.x1, .imm 136) (by simp)
      have e2 := hm.1 (.x2, .imm 0) (by simp)
      have e3 := hm.1 (.x3, .off oMU) (by simp)
      have e4 := hm.1 (.x4, .imm 64) (by simp)
      have e5 := hm.1 (.x5, .off oKS) (by simp)
      simp only [Arg.val, hc.x28, oST, oKS, oMU, x0] at e0 e1 e2 e3 e4 e5
      exact ⟨e0, by rw [e1]; rfl, by rw [e2]; rfl, e3, by rw [e4]; rfl, e5, st_mu, st_ks, mu_ks,
        by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_mu hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL⟩
  refine call_tr (by decide) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v) (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc _ hm => (args L g vv m₀ t t1 hL hc hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ f₂
    simp only [Proof.Sha3.squeezeAArch64, State.withRegions_sp, State.callEntry_sp,
      gpr_ce a1 (r := .x0), gpr_ce a1 (r := .x1), gpr_ce a1 (r := .x2), gpr_ce a1 (r := .x3),
      gpr_ce a1 (r := .x4), gpr_ce a1 (r := .x5), gpr_ce b1 (r := .x0), gpr_ce b1 (r := .x1),
      gpr_ce b1 (r := .x2), gpr_ce b1 (r := .x3), gpr_ce b1 (r := .x4), gpr_ce b1 (r := .x5),
      x.h0, x.h3, x.h5, y.h0, y.h3, y.h5, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      BitVec.eq_of_toNat_eq (x.h4.trans y.h4.symm), by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := cov_xw hL (e := 0) (k := 200) (by omega_using []); rwa [x0] at this
    · exact cov_xw hL (e := 840) (by omega_using [])
    · exact cov_xw hL (e := 200) (by omega_using [])

/-! ## `μ` and `tr` -/

/-- The position after the context string. -/
abbrev qCtx (L : Lay) : Nat := (66 + L.ctxLen.toNat) % 136
/-- The position after the message. -/
abbrev qMsg (L : Lay) : Nat := (qCtx L + L.len.toNat) % 136

/-- Hash with additional layout facts for an external cached digest. -/
theorem muHash_tr_of (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} {G : Lay → Prop} {tr : Arg}
    (hok : tr.ok = true) (hret : tr.isRet = false) (trp : Lay → Addr)
    (htr : ∀ (L : Lay) g vv m (t : State), Ctx L g vv m t → tr.val t = trp L)
    (hs : ∀ L : Lay, L.Ok → G L → (∃ R ∈ L.rd ++ L.wr, Within ⟨trp L, 64⟩ R) ∧
      Region.Disjoint ⟨trp L, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨trp L, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨trp L, 64⟩) :
    RelCT isa (Two I (fun L m t => G L ∧ Φ L m t)) (muHash v.callee tr) fun _ _ => True := by
  -- The relation keeps only the position in `x0`.
  let Ψ : (Lay → Nat) → Lay → Mem → State → Prop := fun q L _ t => (t.gpr .x0).toNat = q L
  have z := two_wp (I := I) (Φ := fun L m t => G L ∧ Φ L m t) (Ψ := fun L _ _ => G L) zeroSt_tr
    fun L g vv m₀ t hL hc hφ => WP.mono (zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', hφ.1⟩
  have a1 := two_wp (I := I) (Ψ := Ψ fun _ => 64)
    (kabs_tr_of v (Φ := fun L _ _ => G L) (absOk hok rfl rfl hret rfl) trp (fun _ => 64)
      (fun _ => 0) (fun L g vv m t _ hc _ => ⟨htr L g vv m t hc, rfl, rfl⟩)
      fun L _ _ _ _ hL _ hG => ⟨by decide, by decide, (hs L hL hG).1, (hs L hL hG).2.1, (hs L hL hG).2.2.1, (hs L hL hG).2.2.2⟩)
    fun L g vv m₀ t hL hc hG => by
      obtain ⟨a, b, c, d⟩ := hs L hL hG
      exact WP.mono (kabs_ok v hL hc (src := tr) (len := .imm 64) (pos := .imm 0) (n := 64) (q := 0)
        (absOk hok rfl rfl hret rfl) (htr L g vv m₀ t hc) rfl rfl (by decide)
        (by decide) a b c d) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have hdr : ∀ L : Lay, L.Ok → 64 < 136 ∧ 2 < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 984, 2⟩ R) ∧
      Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ := fun L hL =>
    ⟨by decide, by decide, cov_x hL (by omega_using []),
      by have := Offset.disjoint L.X (d := 984) (n := 2) (e := 0) (k := 200) (by omega_using []) (by omega_using []) (by omega_using [])
         simpa only [x0] using this,
      Offset.disjoint L.X (d := 984) (n := 2) (e := 200) (k := 640) (by omega_using []) (by omega_using []) (by omega_using []),
      hL.stk_x (by omega_using [])⟩
  have a2 := two_wp (I := I) (Φ := Ψ fun _ => 64) (Ψ := Ψ fun _ => 66)
    (kabs_tr v (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.X + BitVec.ofNat 64 984) (fun _ => 2) (fun _ => 64)
      (fun L g vv m t _ hc _ => ⟨by rw [hc.off]; rfl, rfl, rfl⟩) hdr)
    fun L g vv m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f⟩ := hdr L hL
      exact WP.mono (kabs_ok v hL hc (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (n := 2) (q := 64)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.off]; rfl) rfl rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have ctxS : ∀ L : Lay, L.Ok → 66 < 136 ∧ L.ctxLen.toNat < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.ctx, L.ctxLen.toNat⟩ R) ∧
      Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ := fun L hL =>
    ⟨by decide, L.ctxLen.isLt, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
      by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xCtx (e := 200) (k := 640) (by decide)).symm, hL.kCtx⟩
  have a3 := two_wp (I := I) (Φ := Ψ fun _ => 66) (Ψ := Ψ qCtx)
    (kabs_tr v (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.ctx) (fun L => L.ctxLen.toNat) (fun _ => 66)
      (fun L g vv m t _ hc _ => ⟨by rw [hc.slotV (f := fCtx) (j := 3) rfl (by omega_using [])]; rfl,
        by rw [hc.slotV (f := fCtxLen) (j := 4) rfl (by omega_using []), ofNat_toNat_self]; rfl, rfl⟩) ctxS)
    fun L g vv m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f⟩ := ctxS L hL
      exact WP.mono (kabs_ok v hL hc (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (q := 66)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV (f := fCtx) (j := 3) rfl (by omega_using [])]; rfl)
        (by rw [hc.slotV (f := fCtxLen) (j := 4) rfl (by omega_using []), ofNat_toNat_self]; rfl) rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have msgS : ∀ L : Lay, L.Ok → qCtx L < 136 ∧ L.len.toNat < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.msg, L.len.toNat⟩ R) ∧
      Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.msg, L.len.toNat⟩ := fun L hL =>
    ⟨Nat.mod_lt _ (by decide), L.len.isLt, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
      by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xMsg (e := 200) (k := 640) (by decide)).symm, hL.kMsg⟩
  have a4 := two_wp (I := I) (Φ := Ψ qCtx) (Ψ := Ψ qMsg)
    (kabs_tr v (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.msg) (fun L => L.len.toNat) qCtx
      (fun L g vv m t _ hc hφ => ⟨by rw [hc.slotV (f := fMsg) (j := 1) rfl (by omega_using [])]; rfl,
        by rw [hc.slotV (f := fLen) (j := 2) rfl (by omega_using []), ofNat_toNat_self]; rfl, ofNat_toNat_eq hφ⟩) msgS)
    fun L g vv m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := msgS L hL
      exact WP.mono (kabs_ok v hL hc (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV (f := fMsg) (j := 1) rfl (by omega_using [])]; rfl)
        (by rw [hc.slotV (f := fLen) (j := 2) rfl (by omega_using []), ofNat_toNat_self]; rfl) (ofNat_toNat_eq hφ)
        a b c d e f) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have pd := kpad_tr v (I := I) (Φ := Ψ qMsg) (pos := .ret) (padOk rfl) qMsg
    (fun L g vv m t _ _ hφ => ofNat_toNat_eq hφ) fun L _ => Nat.mod_lt _ (by decide)
  have pd' := two_wp (I := I) (Φ := Ψ qMsg) (Ψ := fun _ _ _ => True) pd
    fun L g vv m₀ t hL hc hφ => WP.mono (kpad_ok v hL hc (pos := .ret) (padOk rfl) (ofNat_toNat_eq hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (a2.seq (a3.seq (a4.seq (pd'.seq (ksqz_tr v))))))

theorem muHash_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} {tr : Arg}
    (hok : tr.ok = true) (hret : tr.isRet = false) (trp : Lay → Addr)
    (htr : ∀ (L : Lay) g vv m (t : State), Ctx L g vv m t → tr.val t = trp L)
    (hs : ∀ L : Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨trp L, 64⟩ R) ∧
      Region.Disjoint ⟨trp L, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨trp L, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨trp L, 64⟩) :
    RelCT isa (Two I Φ) (muHash v.callee tr) fun _ _ => True := by
  apply RelCT.mono (muHash_tr_of v (I := I) (Φ := Φ) (G := fun _ => True) hok hret trp htr
    (fun L hL _ => hs L hL))
  · intro a b h
    obtain ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := h
    exact ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, ⟨trivial, φ₁⟩, ⟨trivial, φ₂⟩⟩
  · intro _ _ _; trivial

end

end VG.Proof.MlDsa.AArch64.Message

end

end

/-!
# ML-DSA on AArch64, `sign_message`: pieces of the constant-time proofs

Untrusted: everything here is checked by Lean. What the contract says two
runs agree on, which includes what `signMessageLeak` says (`signI`), and
that the branch on `ctx_len`, the entry and the exit leak only the pointers
and the lengths (`lsr_taint`, `movz2_taint`, `enterS_taint`,
`leave_taint`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def signI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop :=
  signMessageLeak p (bytesAt m₁ L.key p.skLen) (bytesAt m₁ L.msg L.len.toNat) (bytesAt m₁ L.ctx L.ctxLen.toNat)
      (bytesAt m₁ L.rnd 32) =
    signMessageLeak p (bytesAt m₂ L.key p.skLen) (bytesAt m₂ L.msg L.len.toNat)
      (bytesAt m₂ L.ctx L.ctxLen.toNat) (bytesAt m₂ L.rnd 32)

/-- `μ` at `X + 840`. -/
def MuOk (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- The public data of the contract, spelled out. -/
structure SPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : signMessageLeak p (bytesAt s₁.mem (s₁.gpr .x0) p.skLen) (bytesAt s₁.mem (s₁.gpr .x1) (s₁.gpr .x2).toNat)
      (bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat) (bytesAt s₁.mem (s₁.gpr .x5) 32) =
    signMessageLeak p (bytesAt s₂.mem (s₂.gpr .x0) p.skLen) (bytesAt s₂.mem (s₂.gpr .x1) (s₂.gpr .x2).toNat)
      (bytesAt s₂.mem (s₂.gpr .x3) (s₂.gpr .x4).toNat) (bytesAt s₂.mem (s₂.gpr .x5) 32)
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  x4 : s₁.gpr .x4 = s₂.gpr .x4
  x5 : s₁.gpr .x5 = s₂.gpr .x5
  x6 : s₁.gpr .x6 = s₂.gpr .x6
  x7 : s₁.gpr .x7 = s₂.gpr .x7

/-- After the shift of `ctx_len`. -/
abbrev ALsr (x s1 : State) : Prop :=
  Only [.x9] x s1 ∧ isa.eval (.nonzero .x .x9) s1 = some (decide ¬ (x.gpr .x4).toNat < 256)

theorem lsr_taint :
    (taint.check (AArch64.Taint.ofRegs []) (.block [.lsr .x .x9 .x4 8]) (.block [])).isSome = true := by rfl

theorem movz2_taint :
    (taint.check (AArch64.Taint.ofRegs []) (.block [.movz .x .x0 2 0]) (.block [])).isSome = true := by rfl

theorem leave_taint : (taint.check (AArch64.Taint.ofRegs [.x28]) (.block leave) (.block [])).isSome = true := by
  rfl

theorem enterS_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs [.x7]) (.block (enter .x7 p signSaves)) (.block [])).isSome = true := by
  rfl

end

end VG.Proof.MlDsa.AArch64.Message

end

end

/-!
# ML-DSA on AArch64, `verify_message_cached`: what two runs agree on

Untrusted: everything here is checked by Lean. What the proofs that the
cached message verifier runs in constant time
(`Proof/MlDsa/AArch64/Optimized/CachedVerifyCT.lean`,
`RootedCachedVerifyCT.lean`) share: the public inputs of two runs, `pk`, the
message, the context string and the signature (`verifyI`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : Lay) (m : Mem) : List Byte :=
  bytesAt m L.key p.pkLen ++ bytesAt m L.msg L.len.toNat ++ bytesAt m L.ctx L.ctxLen.toNat ++
    bytesAt m L.sig p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop := leakBytes (vIn p L m₁) = leakBytes (vIn p L m₂)

theorem verifyI_eq {L : Lay} {m₁ m₂ : Mem} (h : verifyI p L m₁ m₂) :
    bytesAt m₁ L.key p.pkLen = bytesAt m₂ L.key p.pkLen ∧
      bytesAt m₁ L.msg L.len.toNat = bytesAt m₂ L.msg L.len.toNat ∧
      bytesAt m₁ L.ctx L.ctxLen.toNat = bytesAt m₂ L.ctx L.ctxLen.toNat ∧
      bytesAt m₁ L.sig p.sigLen = bytesAt m₂ L.sig p.sigLen :=
  leak4 (by simp only [Proof.MlKem.bytesAt_length]) (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length]) h

end

end VG.Proof.MlDsa.AArch64.Message
