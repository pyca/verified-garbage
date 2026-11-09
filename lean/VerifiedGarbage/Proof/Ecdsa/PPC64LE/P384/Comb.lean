module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Contract
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384
public import VerifiedGarbage.Proof.P384.PPC64LE.Comb
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384
meta import VerifiedGarbage.Proof.P384.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over P-384 by the comb on PPC64LE: `Verified`

`vg_ecdsa_p384_sign` with `[k]G` by the seven-bit comb, whose table is a
read-only constant (`Abi.withConsts`): `combSign_ok`, from `signWith_ok` and
the comb as the generator; `combSign_ct`, by `taint_decide` with the
table's address public; and the contract with the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.P384

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

theorem pre_of {s : State} (h : signPPC.pre s) : Pre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem post_of {s s' : State} (h : SignPost p384 s s') : signPPC.post s s' := by
  unfold SignPost at h
  show match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 96 = Spec.Ecdsa.encode Spec.P384.curve rs
    | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 96 = List.replicate 96 0
  revert h
  generalize hq : sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) = q
  rw [show Spec.Ecdsa.signWith p384.C (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) p384.C.len))
      (Spec.Ecdsa.hashToInt p384.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) p384.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r6) p384.C.len)) = sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
    from rfl, hq]
  rcases q with _ | rs <;> exact id

/-- A state satisfying the precondition (without the table). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 48⟩, ⟨0x4000, 48⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the signature's (without the table). -/
theorem signPPC_implies : signPPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P384.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P384.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
        simp only [signPPC, sig, Spec.P384.curve] at h
        revert h
        generalize Spec.Ecdsa.signWith _ _ _ _ = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P384.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P384.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }


/-- The signature's contract with the table, as the proof states it. -/
def signPC : Contract isa where
  pre s := signPPC.pre (stripConsts p384CombConsts s) ∧ ConstsOk p384CombConsts 0 s
  post := signPPC.post
  pub s₁ s₂ := signPPC.pub s₁ s₂ ∧ s₁.syms p384Comb.tsym = s₂.syms p384Comb.tsym

theorem combSign_ok (hL : Weierstrass.Law Spec.P384.curve) (s : State) (hs : signPC.pre s) :
    ∃ t s', Exec isa signP384Comb s t s' ∧ abiPreserved s s' ∧ signPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  have p := pre_of hp
  have hpre : Pre p384 s (constRegs p384CombConsts s) := by
    refine ⟨?_, p.wr, p.out_sc, p.d_sc, p.digest_sc, p.k_sc, p.out_fit, p.d_fit, p.digest_fit, p.k_fit, p.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - p384CombConsts.length) s.rd, hk.1]
    exact congrArg (fun rs => rs ++ constRegs p384CombConsts s) p.rd
  have member : (p384Comb.tsym, p384CombWords) ∈ p384CombConsts := List.mem_singleton_self _
  have ht : TableMem s (s.syms p384Comb.tsym) p384CombWords :=
    ⟨hk.fit member, ⟨_, List.mem_append_left _ (hk.mem_rd member), Region.contains_self _ _⟩,
      fun i hi => hk.readW member hi⟩
  have hd : Region.Disjoint ⟨s.syms p384Comb.tsym, 8 * p384CombWords.length⟩ ⟨s.gpr .r7, 8192⟩ :=
    (hk.2.2.1 _ (List.mem_map_of_mem (f := fun c => (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) member)).2.1 _
      (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := signWith_ok p384_ok (by decide) hL hpre fun s₁ S₁ sy =>
    Proof.P384.PPC64LE.comb_generator_ok hL S₁
      (ht.unch (by rw [S₁.rk.rd, S₁.rk.wr]) S₁.whole (fun w hw => by
        rw [List.mem_singleton] at hw; subst hw; decide) hd) (by rw [sy]) hd
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem combSign_ct : ConstantTime isa signPC.pre signPC.pub signP384Comb :=
  VG.Taint.constantTime (A := taintSym [p384Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6, h7⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

theorem combConsts_eq : p384CombConsts = [(p384Comb.tsym, p384CombWords)] := rfl

/-- A state satisfying the precondition with the table. -/
def combSatC : State :=
  { satState with
    mem := Proof.P384.PPC64LE.combSatMem
    rd := [⟨0x2000, 48⟩, ⟨0x3000, 48⟩, ⟨0x4000, 48⟩, ⟨0x100000, 337920⟩]
    syms := fun _ => 0x100000 }

theorem combSign_sat :
    (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst (abi.withConsts p384CombConsts)).pre combSatC := by
  have hl := Proof.P384.PPC64LE.comb_words_length
  have held := Proof.P384.PPC64LE.combSatMem_held
  rw [combConsts_eq]
  generalize p384CombWords = W at hl held ⊢
  generalize e : combSatC = s
  sig_pre [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
    Spec.P384.curve, Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 96⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem signPC_implies :
    signPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst (abi.withConsts p384CombConsts)) :=
  { pre := fun _ hs => ⟨signPPC_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (signPPC_implies.post (stripConsts p384CombConsts s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨signPPC_implies.pub (stripConsts p384CombConsts s₁)
        (stripConsts p384CombConsts s₂) (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨combSatC, combSign_sat⟩ }

theorem combSign_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified PPC64LE.target signP384Comb
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst (PPC64LE.abi.withConsts p384CombConsts)) :=
  Verified.of_correct (combSign_ok hL) combSign_ct signPC_implies

end VG.Proof.Ecdsa.PPC64LE.P384
