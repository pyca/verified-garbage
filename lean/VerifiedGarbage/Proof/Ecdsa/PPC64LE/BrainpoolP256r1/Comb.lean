module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1.Contract
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1
public import VerifiedGarbage.Proof.BrainpoolP256r1.PPC64LE.Comb
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1.Contract
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1
meta import VerifiedGarbage.Proof.BrainpoolP256r1.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over brainpoolP256r1 by the comb on PPC64LE: `Verified`

`vg_ecdsa_brainpoolp256r1_sign` with `[k]G` by the seven-bit comb, whose table is a
read-only constant (`Abi.withConsts`): `combSign_ok`, from `signWith_ok` and
the comb as the generator; `combSign_ct`, by `taint_decide` with the
table's address public; and the contract with the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.BrainpoolP256r1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

theorem pre_of {s : State} (h : signPPC.pre s) : Pre brainpoolp256r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem post_of {s s' : State} (h : SignPost brainpoolp256r1 s s') : signPPC.post s s' := by
  unfold SignPost at h
  show match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 64 = Spec.Ecdsa.encode Spec.BrainpoolP256r1.curve rs
    | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 64 = List.replicate 64 0
  revert h
  generalize hq : sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) = q
  rw [show Spec.Ecdsa.signWith brainpoolp256r1.C (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) brainpoolp256r1.C.len))
      (Spec.Ecdsa.hashToInt brainpoolp256r1.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) brainpoolp256r1.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r6) brainpoolp256r1.C.len)) = sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
    from rfl, hq]
  rcases q with _ | rs <;> exact id

/-- A state satisfying the precondition (without the table). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the signature's (without the table). -/
theorem signPPC_implies : signPPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP256r1.inst PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.BrainpoolP256r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.BrainpoolP256r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
        simp only [signPPC, sig, Spec.BrainpoolP256r1.curve] at h
        revert h
        generalize Spec.Ecdsa.signWith _ _ _ _ = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.BrainpoolP256r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.BrainpoolP256r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }


/-- The signature's contract with the table, as the proof states it. -/
def signPC : Contract isa where
  pre s := signPPC.pre (stripConsts brainpoolp256r1CombConsts s) ∧ ConstsOk brainpoolp256r1CombConsts 0 s
  post := signPPC.post
  pub s₁ s₂ := signPPC.pub s₁ s₂ ∧ s₁.syms brainpoolp256r1Comb.tsym = s₂.syms brainpoolp256r1Comb.tsym

theorem combSign_ok (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (s : State) (hs : signPC.pre s) :
    ∃ t s', Exec isa signBrainpoolP256r1Comb s t s' ∧ abiPreserved s s' ∧ signPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  have p := pre_of hp
  have hpre : Pre brainpoolp256r1 s (constRegs brainpoolp256r1CombConsts s) := by
    refine ⟨?_, p.wr, p.out_sc, p.d_sc, p.digest_sc, p.k_sc, p.out_fit, p.d_fit, p.digest_fit, p.k_fit, p.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - brainpoolp256r1CombConsts.length) s.rd, hk.1]
    exact congrArg (fun rs => rs ++ constRegs brainpoolp256r1CombConsts s) p.rd
  have member : (brainpoolp256r1Comb.tsym, brainpoolp256r1CombWords) ∈ brainpoolp256r1CombConsts := List.mem_singleton_self _
  have ht : TableMem s (s.syms brainpoolp256r1Comb.tsym) brainpoolp256r1CombWords :=
    ⟨hk.fit member, ⟨_, List.mem_append_left _ (hk.mem_rd member), Region.contains_self _ _⟩,
      fun i hi => hk.readW member hi⟩
  have hd : Region.Disjoint ⟨s.syms brainpoolp256r1Comb.tsym, 8 * brainpoolp256r1CombWords.length⟩ ⟨s.gpr .r7, 8192⟩ :=
    (hk.2.2.1 _ (List.mem_map_of_mem (f := fun c => (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) member)).2.1 _
      (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := signWith_ok brainpoolp256r1_ok (by decide) hL hpre fun s₁ S₁ sy =>
    Proof.BrainpoolP256r1.PPC64LE.comb_generator_ok hL S₁
      (ht.unch (by rw [S₁.rk.rd, S₁.rk.wr]) S₁.whole (fun w hw => by
        rw [List.mem_singleton] at hw; subst hw; decide) hd) (by rw [sy]) hd
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem combSign_ct : ConstantTime isa signPC.pre signPC.pub signBrainpoolP256r1Comb :=
  VG.Taint.constantTime (A := taintSym [brainpoolp256r1Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6, h7⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

theorem combConsts_eq : brainpoolp256r1CombConsts = [(brainpoolp256r1Comb.tsym, brainpoolp256r1CombWords)] := rfl

/-- A state satisfying the precondition with the table. -/
def combSatC : State :=
  { satState with
    mem := Proof.BrainpoolP256r1.PPC64LE.combSatMem
    rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x100000, 151552⟩]
    syms := fun _ => 0x100000 }

theorem combSign_sat :
    (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP256r1.inst (abi.withConsts brainpoolp256r1CombConsts)).pre combSatC := by
  have hl := Proof.BrainpoolP256r1.PPC64LE.comb_words_length
  have held := Proof.BrainpoolP256r1.PPC64LE.combSatMem_held
  rw [combConsts_eq]
  generalize brainpoolp256r1CombWords = W at hl held ⊢
  generalize e : combSatC = s
  sig_pre [Spec.Ecdsa.BrainpoolP256r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
    Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem signPC_implies :
    signPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP256r1.inst (abi.withConsts brainpoolp256r1CombConsts)) :=
  { pre := fun _ hs => ⟨signPPC_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (signPPC_implies.post (stripConsts brainpoolp256r1CombConsts s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨signPPC_implies.pub (stripConsts brainpoolp256r1CombConsts s₁)
        (stripConsts brainpoolp256r1CombConsts s₂) (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨combSatC, combSign_sat⟩ }

theorem combSign_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified PPC64LE.target signBrainpoolP256r1Comb
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP256r1.inst (PPC64LE.abi.withConsts brainpoolp256r1CombConsts)) :=
  Verified.of_correct (combSign_ok hL) combSign_ct signPC_implies

end VG.Proof.Ecdsa.PPC64LE.BrainpoolP256r1
