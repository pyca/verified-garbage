module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.Contract
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
public import VerifiedGarbage.Proof.P224.PPC64LE.Comb
import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.CombLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.Contract
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
meta import VerifiedGarbage.Proof.P224.PPC64LE.Comb
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.CombLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# P-224 public keys by the comb on PPC64LE: `Verified`

`vg_ec_p224_public_key` with `[d]G` by the seven-bit comb, whose table is a
read-only constant (`Abi.withConsts`): `combPk_ok`, from `publicKeyWith_ok`
and the comb as the generator; `combPk_ct`, by `taint_decide` with the
table's address public; and the contract with the table.
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.P224

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

theorem pre_of {s : State} (h : pkPPC.pre s) : PkPre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem post_of {s s' : State} (h : PkPost p224 s s') : pkPPC.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .r4) with
    | some (.affine x y) => s'.gpr .r3 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 57 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 57 = List.replicate 57 0
  revert h
  generalize hq : pk s.mem (s.gpr .r4) = q
  rw [show Spec.EcKey.publicKey p224.C (dk p224 s) = pk s.mem (s.gpr .r4) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- A state satisfying the precondition (without the table). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 28⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the public key's (without the table). -/
theorem pkPPC_implies : pkPPC.Implies (Spec.EcKey.P224.inst.publicKeyContract PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [pkPPC, pk, Spec.P224.curve] at h
        revert h
        generalize Spec.EcKey.publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

/-- The public key's contract with the table, as the proof states it. -/
def pkPC : Contract isa where
  pre s := pkPPC.pre (stripConsts p224CombConsts s) ∧ ConstsOk p224CombConsts 0 s
  post := pkPPC.post
  pub s₁ s₂ := pkPPC.pub s₁ s₂ ∧ s₁.syms p224Comb.tsym = s₂.syms p224Comb.tsym

theorem combPk_ok (hL : Weierstrass.Law Spec.P224.curve) (s : State) (hs : pkPC.pre s) :
    ∃ t s', Exec isa Impl.EcKey.PPC64LE.publicKeyP224Comb s t s' ∧ abiPreserved s s' ∧ pkPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  have p := pre_of hp
  have hpre : PkPre p224 s (constRegs p224CombConsts s) := by
    refine ⟨?_, p.wr, p.out_sc, p.d_sc, p.out_fit, p.d_fit, p.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - p224CombConsts.length) s.rd, hk.1]
    exact congrArg (fun rs => rs ++ constRegs p224CombConsts s) p.rd
  have member : (p224Comb.tsym, p224CombWords) ∈ p224CombConsts := List.mem_singleton_self _
  have ht : TableMem s (s.syms p224Comb.tsym) p224CombWords :=
    ⟨hk.fit member, ⟨_, List.mem_append_left _ (hk.mem_rd member), Region.contains_self _ _⟩,
      fun i hi => hk.readW member hi⟩
  have hd : Region.Disjoint ⟨s.syms p224Comb.tsym, 8 * p224CombWords.length⟩ ⟨s.gpr .r5, 8192⟩ :=
    (hk.2.2.1 _ (List.mem_map_of_mem (f := fun c => (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) member)).2.1 _
      (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := publicKeyWith_ok p224_ok (by decide) hL hpre fun s₁ S₁ sy =>
    Proof.P224.PPC64LE.comb_generator_ok hL S₁
      (ht.unch (by rw [S₁.rk.rd, S₁.rk.wr]) S₁.whole (fun w hw => by
        rw [List.mem_singleton] at hw; subst hw; decide) hd) (by rw [sy]) hd
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem combPk_ct : ConstantTime isa pkPC.pre pkPC.pub Impl.EcKey.PPC64LE.publicKeyP224Comb :=
  VG.Taint.constantTime (A := taintSym [p224Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

theorem combConsts_eq : p224CombConsts = [(p224Comb.tsym, p224CombWords)] := rfl

/-- A state satisfying the precondition with the table. -/
def combSatC : State :=
  { satState with mem := Proof.P224.PPC64LE.combSatMem, rd := [⟨0x2000, 28⟩, ⟨0x100000, 131072⟩], syms := fun _ => 0x100000 }

theorem combPk_sat : (Spec.EcKey.P224.inst.publicKeyContract (abi.withConsts p224CombConsts)).pre combSatC := by
  have hl := Proof.P224.PPC64LE.comb_words_length
  have held := Proof.P224.PPC64LE.combSatMem_held
  rw [combConsts_eq]
  generalize p224CombWords = W at hl held ⊢
  generalize e : combSatC = s
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
    Spec.P224.curve, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem pkPC_implies : pkPC.Implies (Spec.EcKey.P224.inst.publicKeyContract (abi.withConsts p224CombConsts)) :=
  { pre := fun _ hs => ⟨pkPPC_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (pkPPC_implies.post (stripConsts p224CombConsts s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨pkPPC_implies.pub (stripConsts p224CombConsts s₁) (stripConsts p224CombConsts s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨combSatC, combPk_sat⟩ }

theorem combPk_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified PPC64LE.target Impl.EcKey.PPC64LE.publicKeyP224Comb
      (Spec.EcKey.P224.inst.publicKeyContract (PPC64LE.abi.withConsts p224CombConsts)) :=
  Verified.of_correct (combPk_ok hL) combPk_ct pkPC_implies

end VG.Proof.EcKey.PPC64LE.P224
