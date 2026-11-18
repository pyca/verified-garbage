module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# Code that reads a comb's table, on PPC64LE: for every curve

What `<Curve>/Comb.lean` (the signature, here, and the public key,
`Proof/EcKey/PPC64LE/`) needs of a curve, once for every configuration and
table:

* `Tab.withTable`: a contract with a table at the end of its readable
  regions, from the contract without it: on the state without the table's
  region (`stripConsts`), with what the table adds (`ConstsOk`) and the
  table's address public;
* `Tab.implies`: it implies the function's contract under
  `abi.withConsts`, if the contract without the table implies the one under
  `abi` (`pre_consts`, `post_consts`, `pub_consts`, and `post_strip`,
  `pub_strip`: a contract under `abi` does not depend on the readable
  regions but in its precondition);
* `Tab.sign_ok`: `signWith` with a generator that reads the table (the
  comb, `comb_generator_ok`) runs and leaves `SignPost`, from `Pre` without
  the table's region and `ConstsOk`: the table is readable, apart from the
  working space, and unchanged by the stages before the generator.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.Tab

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

/-- A contract with the tables `consts` at the end of the readable regions,
from the contract `K` without them. -/
def withTable (K : Contract isa) (consts : List (String × List (BitVec 64))) (tsym : String) : Contract isa where
  pre s := K.pre (stripConsts consts s) ∧ ConstsOk consts 0 s
  post s s' := K.post (stripConsts consts s) s'
  pub s₁ s₂ := K.pub (stripConsts consts s₁) (stripConsts consts s₂) ∧ s₁.syms tsym = s₂.syms tsym

theorem post_intro {K : Contract isa} {consts : List (String × List (BitVec 64))} {tsym : String} {s s' : State}
    (h : K.post (stripConsts consts s) s') : (withTable K consts tsym).post s s' := h

section
variable {sig : Sig} {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- A postcondition under `abi` does not depend on the readable regions. -/
theorem post_strip {K : List (String × List (BitVec 64))} {s s' : State} :
    (sig.contract abi pre post wa st leak).post (stripConsts K s) s' ↔
      (sig.contract abi pre post wa st leak).post s s' := by
  dsimp only [Sig.contract]
  cases h : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => exact Iff.rfl
  | some vals =>
    dsimp only
    rw [args_stripConsts h]
    exact Iff.rfl

/-- The public data under `abi` do not depend on the readable regions. -/
theorem pub_strip {K : List (String × List (BitVec 64))} {s₁ s₂ : State} :
    (sig.contract abi pre post wa st leak).pub (stripConsts K s₁) (stripConsts K s₂) ↔
      (sig.contract abi pre post wa st leak).pub s₁ s₂ := by
  dsimp only [Sig.contract]
  cases h : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => exact Iff.rfl
  | some vals =>
    dsimp only
    rw [args_stripConsts h, args_stripConsts h]
    exact Iff.rfl

/-- A contract with a table implies the one under `abi.withConsts`, if the
contract without it implies the one under `abi`. -/
theorem implies {K : Contract isa} (h : K.Implies (sig.contract abi pre post wa 0 leak))
    (sat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa 0 leak).pre s) :
    (withTable K (c₀ :: cs) c₀.1).Implies (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa 0 leak) :=
  { pre := fun _ hs => ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (post_strip.mp (h.post (stripConsts (c₀ :: cs) s) s'
      (pre_consts.mp hs).1 hp))
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨h.pub (stripConsts (c₀ :: cs) s₁) (stripConsts (c₀ :: cs) s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_strip.mpr (pub_consts.mp hp).1),
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := sat }

end

variable {c : Cfg}

/-- The table of a state that meets `ConstsOk`: readable, and its words. -/
theorem tableMem {tsym : String} {words : List (BitVec 64)} {s : State}
    (hk : ConstsOk [(tsym, words)] 0 s) : TableMem s (s.syms tsym) words :=
  ⟨hk.fit (List.mem_singleton_self _),
    ⟨_, List.mem_append_left _ (hk.mem_rd (List.mem_singleton_self _)), Region.contains_self _ _⟩,
    fun _ hi => hk.readW (List.mem_singleton_self _) hi⟩

/-- The signature with a generator that reads a table. -/
theorem sign_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hL : VG.Proof.Weierstrass.Law c.C) {tsym : String}
    {words : List (BitVec 64)} {generator : Prog isa}
    (hgen : ∀ {A : Args} {s₀ : State} {base : Addr} {F : BitVec 64} {s : State}, St₁ c A s₀ base F s →
      ∀ {T : Addr}, TableMem s T words → s.syms tsym = T →
      Region.Disjoint ⟨T, 8 * words.length⟩ ⟨base, 8192⟩ →
      WP isa generator s (GeneratorPost c base (kv c A s₀) (G c.C) s))
    {s : State} (hp : Pre c (stripConsts [(tsym, words)] s)) (hk : ConstsOk [(tsym, words)] 0 s) :
    ∃ t s', Exec isa (c.signWith generator) s t s' ∧ abiPreserved s s' ∧
      SignPost c (stripConsts [(tsym, words)] s) s' := by
  have hpre : Pre c s (constRegs [(tsym, words)] s) := by
    refine ⟨?_, hp.wr, hp.out_sc, hp.d_sc, hp.digest_sc, hp.k_sc, hp.out_fit, hp.d_fit, hp.digest_fit, hp.k_fit,
      hp.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - [(tsym, words)].length) s.rd, hk.1]
    exact congrArg (fun rs => rs ++ constRegs [(tsym, words)] s) hp.rd
  have ht := tableMem hk
  have hd : Region.Disjoint ⟨s.syms tsym, 8 * words.length⟩ ⟨s.gpr .r7, 8192⟩ :=
    hk.disjoint_wr (List.mem_singleton_self _) (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := signWith_ok hc h3 hL hpre fun s₁ S₁ sy =>
    hgen S₁ (ht.unch (by rw [S₁.rk.rd, S₁.rk.wr]) S₁.whole (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw; decide) hd) (by rw [sy]) hd
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, hpost⟩

end VG.Proof.Ecdsa.PPC64LE.Tab
