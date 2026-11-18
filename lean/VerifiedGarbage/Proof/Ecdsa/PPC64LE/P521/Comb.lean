module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Contract
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.CombLit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521
public import VerifiedGarbage.Proof.P521.PPC64LE.Comb
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Spec.Ecdsa.P521
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521
meta import VerifiedGarbage.Proof.P521.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over P-521 by the comb on PPC64LE: `Verified`

`vg_ecdsa_p521_sign` with `[k]G` by the seven-bit comb, whose table is a
read-only constant (`Abi.withConsts`): `combSign_ok`, from `signWith_ok` and
the comb as the generator; `combSign_ct`, by `taint_decide` with the
table's address public; and the contract with the table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.P521

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

theorem pre_of {s : State} (h : signPPC.pre s) : Pre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem post_of {s s' : State} (h : SignPost p521 s s') : signPPC.post s s' := by
  unfold SignPost at h
  show match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 132 = Spec.Ecdsa.encode Spec.P521.curve rs
    | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 132 = List.replicate 132 0
  revert h
  generalize hq : sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) = q
  rw [show Spec.Ecdsa.signWith p521.C (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) p521.C.len))
      (Spec.Ecdsa.hashToInt p521.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) p521.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r6) p521.C.len)) = sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
    from rfl, hq]
  rcases q with _ | rs <;> exact id

/-- A state satisfying the precondition (without the table). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 66⟩, ⟨0x3000, 66⟩, ⟨0x4000, 66⟩]
  wr := [⟨0x1000, 132⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the signature's (without the table). -/
theorem signPPC_implies : signPPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P521.inst PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P521.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P521.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P521.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P521.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
        simp only [signPPC, sig, Spec.P521.curve] at h
        revert h
        generalize Spec.Ecdsa.signWith _ _ _ _ = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.P521.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P521.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P521.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P521.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }


/-- The signature's contract with the table, as the proof states it. -/
def signPC : Contract isa := Tab.withTable signPPC p521CombConsts p521Comb.tsym

theorem combSign_ok (hL : Weierstrass.Law Spec.P521.curve) (s : State) (hs : signPC.pre s) :
    ∃ t s', Exec isa signP521Comb s t s' ∧ abiPreserved s s' ∧ signPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := Tab.sign_ok p521_ok (by decide) hL
    (Proof.P521.PPC64LE.comb_generator_ok hL) (pre_of hp) hk
  exact ⟨t, s', he, K, Tab.post_intro (post_of hpost)⟩

theorem combSign_ct : ConstantTime isa signPC.pre signPC.pub signP521Comb :=
  VG.Taint.constantTime (A := vectorTaintSym [p521Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6, h7⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

theorem combConsts_eq : p521CombConsts = [(p521Comb.tsym, p521CombWords)] := rfl

/-- A state satisfying the precondition with the table. -/
def combSatC : State :=
  { satState with
    mem := Proof.P521.PPC64LE.combSatMem
    rd := [⟨0x2000, 66⟩, ⟨0x3000, 66⟩, ⟨0x4000, 66⟩, ⟨0x100000, 764928⟩]
    syms := fun _ => 0x100000 }

theorem combSign_sat :
    (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P521.inst (abi.withConsts p521CombConsts)).pre combSatC := by
  have hl := Proof.P521.PPC64LE.comb_words_length
  have held := Proof.P521.PPC64LE.combSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, p521CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : combSatC = s
  sig_pre [Spec.Ecdsa.P521.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 132⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem signPC_implies :
    signPC.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P521.inst (abi.withConsts p521CombConsts)) :=
  Tab.implies signPPC_implies ⟨combSatC, combSign_sat⟩

theorem combSign_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified PPC64LE.target signP521Comb
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P521.inst (PPC64LE.abi.withConsts p521CombConsts)) :=
  Verified.of_correct (combSign_ok hL) combSign_ct signPC_implies

end VG.Proof.Ecdsa.PPC64LE.P521
