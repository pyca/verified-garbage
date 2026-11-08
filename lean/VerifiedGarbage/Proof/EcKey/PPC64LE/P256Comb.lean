module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Contract
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Verified
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
import VerifiedGarbage.Proof.P256.PPC64LE.Comb
import VerifiedGarbage.Proof.EcKey.PPC64LE.P256CombLit
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Spec.EcKey.P256
meta import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Verified
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
meta import VerifiedGarbage.Proof.P256.PPC64LE.Comb
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.P256CombLit
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# P-256 public keys by the comb on PPC64LE: `Verified`

`vg_ec_p256_public_key` with `[d]G` by the seven-bit comb, whose table is a
read-only constant (`Abi.withConsts`): `combPk_ok`, from `publicKeyWith_ok`
and the comb as the generator; `combPk_ct`, by `taint_decide` with the
table's address public; and the contract with the table.
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

/-- The public key's contract with the table, as the proof states it. -/
def pkPC : Contract isa where
  pre s := pkPPC.pre (stripConsts p256CombConsts s) ∧ ConstsOk p256CombConsts 0 s
  post := pkPPC.post
  pub s₁ s₂ := pkPPC.pub s₁ s₂ ∧ s₁.syms p256Comb.tsym = s₂.syms p256Comb.tsym

theorem combPk_ok (hL : Weierstrass.Law Spec.P256.curve) (s : State) (hs : pkPC.pre s) :
    ∃ t s', Exec isa Impl.EcKey.PPC64LE.publicKeyP256Comb s t s' ∧ abiPreserved s s' ∧ pkPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  have p := pre_of hp
  have hpre : PkPre p256 s (constRegs p256CombConsts s) := by
    refine ⟨?_, p.wr, p.out_sc, p.d_sc, p.out_fit, p.d_fit, p.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - p256CombConsts.length) s.rd, hk.1]
    exact congrArg (fun rs => rs ++ constRegs p256CombConsts s) p.rd
  have member : (p256Comb.tsym, p256CombWords) ∈ p256CombConsts := List.mem_singleton_self _
  have ht : TableMem s (s.syms p256Comb.tsym) p256CombWords :=
    ⟨hk.fit member, ⟨_, List.mem_append_left _ (hk.mem_rd member), Region.contains_self _ _⟩,
      fun i hi => hk.readW member hi⟩
  have hd : Region.Disjoint ⟨s.syms p256Comb.tsym, 8 * p256CombWords.length⟩ ⟨s.gpr .r5, 8192⟩ :=
    (hk.2.2.1 _ (List.mem_map_of_mem (f := fun c => (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) member)).2.1 _
      (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := publicKeyWith_ok p256_ok (by decide) hL hpre fun s₁ S₁ sy =>
    Proof.P256.PPC64LE.comb_generator_ok hL S₁
      (ht.unch (by rw [S₁.rk.rd, S₁.rk.wr]) S₁.whole (fun w hw => by
        rw [List.mem_singleton] at hw; subst hw; decide) hd) (by rw [sy]) hd
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem combPk_ct : ConstantTime isa pkPC.pre pkPC.pub Impl.EcKey.PPC64LE.publicKeyP256Comb :=
  VG.Taint.constantTime (A := taintSym [p256Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

theorem combConsts_eq : p256CombConsts = [(p256Comb.tsym, p256CombWords)] := rfl

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 p256CombWords

theorem combSatMem_held : ∀ i < p256CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p256CombWords.getD i 0 := by
  unfold combSatMem
  exact constMem_held _ _ (by rw [Proof.P256.PPC64LE.comb_words_length]; omega)

/-- A state satisfying the precondition with the table. -/
def combSatC : State :=
  { satState with mem := combSatMem, rd := [⟨0x2000, 32⟩, ⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem combPk_sat : (Spec.EcKey.P256.inst.publicKeyContract (abi.withConsts p256CombConsts)).pre combSatC := by
  have hl := Proof.P256.PPC64LE.comb_words_length
  have held := combSatMem_held
  rw [combConsts_eq]
  generalize p256CombWords = W at hl held ⊢
  generalize e : combSatC = s
  sig_pre [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
    Spec.P256.curve, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem pkPC_implies : pkPC.Implies (Spec.EcKey.P256.inst.publicKeyContract (abi.withConsts p256CombConsts)) :=
  { pre := fun _ hs => ⟨pkPPC_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (pkPPC_implies.post (stripConsts p256CombConsts s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨pkPPC_implies.pub (stripConsts p256CombConsts s₁) (stripConsts p256CombConsts s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨combSatC, combPk_sat⟩ }

theorem combPk_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified PPC64LE.target Impl.EcKey.PPC64LE.publicKeyP256Comb
      (Spec.EcKey.P256.inst.publicKeyContract (PPC64LE.abi.withConsts p256CombConsts)) :=
  Verified.of_correct (combPk_ok hL) combPk_ct pkPC_implies

end VG.Proof.EcKey.PPC64LE
