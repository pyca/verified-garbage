module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll

/-!
# The public key by a comb's table, on PPC64LE: for every curve

`Tab.pk_ok`: `publicKeyWith` with a generator that reads a table (the comb,
`comb_generator_ok`) runs and leaves `PkPost`, from `PkPre` without the
table's region and `ConstsOk`, once for every configuration and table, as
`Proof/Ecdsa/PPC64LE/CombAll.lean`'s `Tab.sign_ok` is for the signature;
the contract with the table and what it implies are that module's
(`Tab.withTable`, `Tab.implies`).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.Tab

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

variable {c : Cfg}

/-- The public key with a generator that reads a table. -/
theorem pk_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hL : VG.Proof.Weierstrass.Law c.C) {tsym : String}
    {words : List (BitVec 64)} {generator : Prog isa}
    (hgen : ∀ {A : Args} {s₀ : State} {base : Addr} {F : BitVec 64} {s : State}, St₁ c A s₀ base F s →
      ∀ {T : Addr}, TableMem s T words → s.syms tsym = T →
      Region.Disjoint ⟨T, 8 * words.length⟩ ⟨base, 8192⟩ →
      WP isa generator s (GeneratorPost c base (kv c A s₀) (G c.C) s))
    {s : State} (hp : PkPre c (stripConsts [(tsym, words)] s)) (hk : ConstsOk [(tsym, words)] 0 s) :
    ∃ t s', Exec isa (Impl.EcKey.PPC64LE.Cfg.publicKeyWith c generator) s t s' ∧ abiPreserved s s' ∧
      PkPost c (stripConsts [(tsym, words)] s) s' := by
  have hpre : PkPre c s (constRegs [(tsym, words)] s) := by
    refine ⟨?_, hp.wr, hp.out_sc, hp.d_sc, hp.out_fit, hp.d_fit, hp.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - [(tsym, words)].length) s.rd, hk.1]
    exact congrArg (fun rs => rs ++ constRegs [(tsym, words)] s) hp.rd
  have ht := Proof.Ecdsa.PPC64LE.Tab.tableMem hk
  have hd : Region.Disjoint ⟨s.syms tsym, 8 * words.length⟩ ⟨s.gpr .r5, 8192⟩ :=
    hk.disjoint_wr (List.mem_singleton_self _) (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := publicKeyWith_ok hc h3 hL hpre fun s₁ S₁ sy =>
    hgen S₁ (ht.unch (by rw [S₁.rk.rd, S₁.rk.wr]) S₁.whole (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw; decide) hd) (by rw [sy]) hd
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, hpost⟩

end VG.Proof.EcKey.PPC64LE.Tab
