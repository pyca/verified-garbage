module

public import VerifiedGarbage.Proof.Ed25519.X86_64.BaseCallee
public import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Hash
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Ed25519.X86_64.BaseCallee
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Hash
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
meta import Mathlib.Tactic.NormNum.Prime
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Spec.Weierstrass

/-! # Ed25519 public-key derivation on x86-64, after its first step -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86_64.PublicKey.Correct`. -/
section
/-!
# Ed25519 public-key derivation on x86-64: correctness

After a first step that leaves the seed's SHA-512 digest at `scratch + 1568`, the
frame's body leaves the public key in `out` (`bodyFrom_ok`).
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem zero_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkZero) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
  apply WP.of_runBlock
  simp only [pkZero, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), rfl⟩

theorem wipe_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkWipe) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem := by
  rw [pkWipe, WP.block_append_iff]
  refine WP.mono (zero_ok hc) fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (stores_ok hu) fun u' ⟨hu', hf, _⟩ => ⟨hu', hm ▸ hf⟩

/-- The public key of `seed` in `out`, after any `hash` that leaves its digest `E` at
`scratch + 1568`. -/
theorem bodyFrom_ok (hL : L.Ok) {hash : Prog isa} {t : State} {E seed : List Byte}
    (hh : WP isa hash t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1568) 64 = E)
    (hE : E = Spec.Sha512.sha512 seed) :
    WP isa (pkBodyFrom hash bs fs) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 = Spec.Ed25519.publicKey seed := by
  subst hE
  refine WP.seq (WP.mono hh fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.mono (baseArgs_ok hc₁) fun t₂ ⟨hc₂, hm₂, ha₂⟩ => ?_)
  refine WP.seq (WP.mono (prune_ok hc₂ ha₂ (hm₂ ▸ hh₁)) fun t₃ ⟨hc₃, _, ha₃, hs⟩ => ?_)
  refine WP.seq (WP.mono (base_ok hL hc₃ ha₃ hs) fun t₃ ⟨hc₃, ho₃⟩ => ?_)
  refine WP.mono (wipe_ok hc₃) fun t₄ ⟨hc₄, hf₄⟩ => ⟨hc₄, ?_⟩
  rw [Spec.Ed25519.publicKey, Spec.Ed25519.expandSecret, ← ho₃]
  simp only [Spec.Ed25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact Frame.bytes (R := L.OUT) hf₄ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_OUT (d := 16) (n := 32) (by omega)).symm) (by show (32 : Nat) ≤ 2 ^ 64; decide)
    (List.mem_range.mp hi)

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * 7) = B + BitVec.ofNat 64 72 := by
  rw [add_add]

end VG.Proof.Ed25519.X86_64.PublicKey
end

/-!
# Ed25519 public-key derivation on x86-64: constant time

Two runs whose pointers agree have the same layout, so between the frame's
push and pop they are related by `Two`: both satisfy `Ctx` with that layout
(and `Φ`, what the next call needs of the registers), whatever their secrets.
The blocks address only the stack and, in `pkPrune`, `scratch`, from registers
that agree (the taint analysis); each call is of constant-time code whose
public data, its pointers, agree (`RelCT.callEx`).
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Two.Env := Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧ Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧ Φ e.1 a ∧ Φ e.1 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      WP isa c t fun t' => Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_block {is : List Instr} {Φ : Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rsp_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {mx₁ mx₂ : BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ mx₁ m₁ t₁) (c₂ : Ctx L g₂ mx₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

theorem covers {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.TBL, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.OUT ∨ Within r L.SCR) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simpa using hR, hw⟩
  · rw [hc.wr]
    rcases hwsub r hr with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call, with the same regions in both runs. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, L.Ok → ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.TBL, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, Within r L.OUT ∨ Within r L.SCR) :
    RelCT isa (Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂, (covers c₁ (hsub L hL) (hwsub L)).1,
      (covers c₁ (hsub L hL) (hwsub L)).2, (covers c₂ (hsub L hL) (hwsub L)).1,
      (covers c₂ (hsub L hL) (hwsub L)).2, rsp_two c₁ c₂⟩

/-- A block, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      WP isa (.block is) t fun t' => Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (two_block rs hrs h) hw

/-- A call of verified code, after which `Ctx` holds again. -/
theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, L.Ok → ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.TBL, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, Within r L.OUT ∨ Within r L.SCR) :
    RelCT isa (Two Φ) (.call n c) (Two fun _ _ => True) :=
  two_wp (two_call hv hct rd wr hpre hpub hsub hwsub) fun L _ _ _ _ hL hc hf =>
    call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (hsub L hL) (hwsub L) fun _ hc' _ _ _ => ⟨hc', trivial⟩

theorem rspOnly {Φ : Lay → State → Prop} : ∀ (L : Lay) (t₁ t₂ : State) g₁ g₂ mx₁ mx₂ m₁ m₂,
    Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact rsp_two c₁ c₂

/-- The frame's body after any `hash` whose runs are related. -/
theorem bodyFrom_ct {Φ : Lay → State → Prop} {hash : Prog isa}
    (hh : RelCT isa (Two Φ) hash (Two fun _ _ => True)) :
    RelCT isa (Two Φ) (pkBodyFrom hash bs fs) fun _ _ => True := by
  -- the scalar and the base point
  have b₁ : RelCT isa (Two fun _ _ => True) (.block pkBaseArgs) (Two BaseArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (baseArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have b₂ : RelCT isa (Two BaseArgs) (.block pkPrune) (Two BaseArgs) := by
    refine two_blk [.rsp, .rdx] (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ r hr => ?_) (by taint_decide)
      fun _ _ _ _ _ _ hc ha => WP.mono (prune_ok hc ha rfl) fun _ ⟨hc', _, ha', _⟩ => ⟨hc', ha'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact rsp_two c₁ c₂
    · exact a₁.2.2.trans a₂.2.2.symm
  have b₃ := two_callP (n := (scalarBaseName fs)) (Φ := BaseArgs)
    (VG.Proof.Ed25519.X86_64.EdBase.ok (bs := bs)) (VG.Proof.Ed25519.X86_64.EdBase.ct (bs := bs))
    base_nosp base_depth baseRd baseWr (fun _ _ _ _ _ hL hc ha => ⟨base_pre hL hc ha, base_clear hL hc⟩)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := base_regs a₁ (baseRd L) (baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := base_regs a₂ (baseRd L) (baseWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm,
        c₁.sym.trans c₂.sym.symm⟩)
    (fun _ _ => base_sub) (fun _ => base_wsub)
  have w : RelCT isa (Two fun _ _ => True) (.block pkWipe) fun _ _ => True :=
    two_block [.rsp] rspOnly (by taint_decide)
  exact hh.seq (b₁.seq (b₂.seq (b₃.seq w)))

end VG.Proof.Ed25519.X86_64.PublicKey
end

/-!
# Ed25519 public-key derivation on x86-64: constant time from the frame's push
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {n : Nat} {key : State → Prop} {post : State → State → Prop} in
/-- Derivation after any `hash` whose runs are related, from the frame's push. -/
theorem bodyFrom_pk_ct (hn : 32 ≤ n) {Φ : Lay → State → Prop} {hash : Prog isa}
    (hh : RelCT isa (Two Φ) hash (Two fun _ _ => True))
    (hΦ : ∀ s, (pkLocalWith n key post).pre s → Φ (lay n s) (pushed pushRs s)) :
    ConstantTime isa (pkLocalWith n key post).pre (pkLocalWith n key post).pub
      (.frame (.push pushRs) (pkBodyFrom hash bs fs) (.pop .rax 7)) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1)
    (RelCT.mono (bodyFrom_ct hh) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx, hsy⟩, rfl, rfl⟩
  have e : lay n s₂ = lay n s₁ := by simp only [lay, hsp, hdi, hsi, hdx, hsy]
  exact ⟨⟨lay n s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, lay_ok h₁ hn, push_ctx h₁,
    e ▸ push_ctx h₂, hΦ _ h₁, e ▸ hΦ _ h₂⟩

end VG.Proof.Ed25519.X86_64.PublicKey
