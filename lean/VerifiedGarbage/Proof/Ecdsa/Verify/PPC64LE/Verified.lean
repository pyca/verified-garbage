module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Hash
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Hash
meta import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P256Comb
import VerifiedGarbage.Proof.P256.PPC64LE.Comb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Contract
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P256Comb
import VerifiedGarbage.Proof.P256.PPC64LE.Comb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Contract
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Ecdsa.Verify.P256
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Front
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic

/-!
# ECDSA verification over P-256 on PPC64LE: `Verified`

`vg_ecdsa_p256_verify` with `[u]G` by the comb, from its table, a constant
(`abi.withConsts p256CombConsts`): `verify_ppc`, from `verifyWith_ok` and
`combPts_ok`; `verify_ct`: the time depends only on the pointers and the
table's address (`taint_decide` with `vectorTaintSym` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass
open VG.Impl.Weierstrass.PPC64LE (p256Comb p256CombWords p256CombConsts)

theorem pre_of {s : State} (h : verifyPPC.pre s) : VPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨by rw [h1]; rfl, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 65⟩, ⟨0x2000, 32⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x8000, 8192⟩]

/-- `verifyPPC` states `verifyContract`'s facts by name. -/
theorem verifyPPC_implies : verifyPPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst PPC64LE.abi) :=
  { pre := by
      sig_implies_pre [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    post := by
      intro s s' _ h
      sig_post [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
      simp only [verifyPPC, vf, Spec.P256.curve] at h
      revert h
      split <;> rename_i hv <;> simp only [hv, ite_true, ite_false, Bool.false_eq_true] <;>
        exact fun h => by rw [h]; rfl
    pub := by
      sig_implies_pub [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    sat := by
      sig_implies_sat [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
        [satState] using satState }

/-- The verification's contract with the comb's table, as the proof states it. -/
def vPC : Contract isa where
  pre s := verifyPPC.pre (stripConsts p256CombConsts s) ∧ ConstsOk p256CombConsts 0 s
  post := verifyPPC.post
  pub s₁ s₂ := verifyPPC.pub s₁ s₂ ∧ s₁.syms p256Comb.tsym = s₂.syms p256Comb.tsym

theorem verify_ppc (hL : Weierstrass.Law Spec.P256.curve) (s : State) (hs : vPC.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ vPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  have p := pre_of hp
  have hpre : VPre p256 s (constRegs p256CombConsts s) := by
    refine ⟨?_, p.wr, p.pk_sc, p.dg_sc, p.sig_sc, p.pk_fit, p.dg_fit, p.sig_fit, p.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - p256CombConsts.length) s.rd, hk.1]
    have e := p.rd
    simp only [List.append_nil] at e
    exact congrArg (fun rs => rs ++ constRegs p256CombConsts s) e
  have member : (p256Comb.tsym, p256CombWords) ∈ p256CombConsts := List.mem_singleton_self _
  have ht : VG.Proof.Weierstrass.PPC64LE.TComb.TableMem s (s.syms p256Comb.tsym) p256CombWords :=
    ⟨hk.fit member, ⟨_, List.mem_append_left _ (hk.mem_rd member), Region.contains_self _ _⟩,
      fun i hi => hk.readW member hi⟩
  have hd : Region.Disjoint ⟨s.syms p256Comb.tsym, 8 * p256CombWords.length⟩ ⟨s.gpr .r6, 8192⟩ :=
    hk.disjoint_wr member (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := verifyWith_ok p256_ok hL hpre (P256.combPts_ok hL ht rfl hd)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, hpost⟩

theorem verify_ct : ConstantTime isa vPC.pre vPC.pub verifyP256 :=
  VG.Taint.constantTime (A := vectorTaintSym [p256Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def vSatMem : Mem := constMem 0x100000 p256CombWords

theorem vSatMem_held : ∀ i < p256CombWords.length,
    vSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p256CombWords.getD i 0 := by
  unfold vSatMem
  exact constMem_held _ _ (by rw [Proof.P256.PPC64LE.comb_words_length]; omega_using [])

/-- A state satisfying the precondition with the table. -/
def vSatC : State :=
  { satState with mem := vSatMem, rd := satState.rd ++ [⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem combConsts_eq : p256CombConsts = [(p256Comb.tsym, p256CombWords)] := rfl

theorem vSat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (abi.withConsts p256CombConsts)).pre vSatC := by
  have hl := Proof.P256.PPC64LE.comb_words_length
  have held := vSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, p256CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : vSatC = s
  sig_pre [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.P256.curve,
    Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x8000, 8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem vPC_implies :
    vPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (abi.withConsts p256CombConsts)) :=
  { pre := fun _ hs => ⟨verifyPPC_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (verifyPPC_implies.post (stripConsts p256CombConsts s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨verifyPPC_implies.pub (stripConsts p256CombConsts s₁)
        (stripConsts p256CombConsts s₂) (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨vSatC, vSat⟩ }

theorem verify_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified PPC64LE.target verifyP256
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (PPC64LE.abi.withConsts p256CombConsts)) :=
  Verified.of_correct (verify_ppc hL) verify_ct vPC_implies

/-- A state satisfying `verifyHashContract`'s precondition with the table, with an empty hash. -/
def hSatC : State :=
  let h := Hash.hashSatState 32
  { h with mem := vSatMem, rd := h.rd ++ [⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem verifyHash_sat :
    ∃ s, (Spec.Ecdsa.P256.inst.verifyHashContract (PPC64LE.abi.withConsts p256CombConsts) 112).pre s := by
  refine ⟨hSatC, ?_⟩
  have hl := Proof.P256.PPC64LE.comb_words_length
  have held := vSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, p256CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : hSatC = s
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.P256.inst,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_,
    Region.disjoint_of_sep (by decide), by decide, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x8000, 8192⟩] at hr
  obtain rfl := List.mem_singleton.mp hr
  exact Region.disjoint_of_sep (by decide)

/-- `vg_ecdsa_p256_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash
(`Hash.verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified PPC64LE.target
      (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false verifyP256)
      (Spec.Ecdsa.P256.inst.verifyHashContract (PPC64LE.abi.withConsts p256CombConsts) 112) :=
  Proof.Ecdsa.Verify.PPC64LE.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.p256_len (by decide)
    (verify_verified hL) (by taint_decide) verifyHash_sat

end VG.Proof.Ecdsa.Verify.PPC64LE
