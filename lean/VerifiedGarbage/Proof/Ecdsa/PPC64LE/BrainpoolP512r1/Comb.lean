module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Contract
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
public import VerifiedGarbage.Proof.BrainpoolP512r1.PPC64LE.Comb
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
meta import VerifiedGarbage.Proof.BrainpoolP512r1.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over brainpoolP512r1 by the comb on PPC64LE: `Verified`

`vg_ecdsa_brainpoolp512r1_sign` with `[k]G` by the seven-bit comb, whose table is a
read-only constant (`Abi.withConsts`): `combSign_ok`, from `signWith_ok` and
the comb as the generator; `combSign_ct`, by `taint_decide` with the
table's address public; and the contract with the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.BrainpoolP512r1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

theorem pre_of {s : State} (h : signPPC.pre s) : Pre brainpoolp512r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem post_of {s s' : State} (h : SignPost brainpoolp512r1 s s') : signPPC.post s s' := by
  unfold SignPost at h
  show match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 128 = Spec.Ecdsa.encode Spec.BrainpoolP512r1.curve rs
    | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 128 = List.replicate 128 0
  revert h
  generalize hq : sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) = q
  rw [show Spec.Ecdsa.signWith brainpoolp512r1.C (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) brainpoolp512r1.C.len))
      (Spec.Ecdsa.hashToInt brainpoolp512r1.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) brainpoolp512r1.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r6) brainpoolp512r1.C.len)) = sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
    from rfl, hq]
  rcases q with _ | rs <;> exact id

/-- A state satisfying the precondition (without the table). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the signature's (without the table). -/
theorem signPPC_implies : signPPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
        simp only [signPPC, sig, Spec.BrainpoolP512r1.curve] at h
        revert h
        generalize Spec.Ecdsa.signWith _ _ _ _ = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }


/-- The signature's contract with the table, as the proof states it. -/
def signPC : Contract isa := Tab.withTable signPPC brainpoolp512r1CombConsts brainpoolp512r1Comb.tsym

theorem combSign_ok (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (s : State) (hs : signPC.pre s) :
    ∃ t s', Exec isa signBrainpoolP512r1Comb s t s' ∧ abiPreserved s s' ∧ signPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := Tab.sign_ok brainpoolp512r1_ok (by decide) hL
    (Proof.BrainpoolP512r1.PPC64LE.comb_generator_ok hL) (pre_of hp) hk
  exact ⟨t, s', he, K, Tab.post_intro (post_of hpost)⟩

theorem combSign_ct : ConstantTime isa signPC.pre signPC.pub signBrainpoolP512r1Comb :=
  VG.Taint.constantTime (A := vectorTaintSym [brainpoolp512r1Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6, h7⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

theorem combConsts_eq : brainpoolp512r1CombConsts = [(brainpoolp512r1Comb.tsym, brainpoolp512r1CombWords)] := rfl

/-- A state satisfying the precondition with the table. -/
def combSatC : State :=
  { satState with
    mem := Proof.BrainpoolP512r1.PPC64LE.combSatMem
    rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 64⟩, ⟨0x100000, 606208⟩]
    syms := fun _ => 0x100000 }

theorem combSign_sat :
    (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst (abi.withConsts brainpoolp512r1CombConsts)).pre combSatC := by
  have hl := Proof.BrainpoolP512r1.PPC64LE.comb_words_length
  have held := Proof.BrainpoolP512r1.PPC64LE.combSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp512r1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : combSatC = s
  sig_pre [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
    Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 128⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem signPC_implies :
    signPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst (abi.withConsts brainpoolp512r1CombConsts)) :=
  Tab.implies signPPC_implies ⟨combSatC, combSign_sat⟩

theorem combSign_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified PPC64LE.target signBrainpoolP512r1Comb
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst (PPC64LE.abi.withConsts brainpoolp512r1CombConsts)) :=
  Verified.of_correct (combSign_ok hL) combSign_ct signPC_implies

end VG.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
