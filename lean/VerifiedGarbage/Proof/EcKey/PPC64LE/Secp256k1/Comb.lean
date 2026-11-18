module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.CombAll
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.EcKey.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1
public import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Comb
import VerifiedGarbage.Proof.EcKey.PPC64LE.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.CombAll
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Spec.EcKey.Secp256k1
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1
meta import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Comb
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Secp256k1.CombLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Secp256k1
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Secp256k1
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `EcKey.PPC64LE.Secp256k1.Contract`, which only this module used -/

section

/-!
# secp256k1 public keys on PPC64LE: the contract the proof is written against

The facts of `Spec.EcKey.Secp256k1.inst.publicKeyContract` for PPC64LE, by name:
`vg_ec_secp256k1_public_key(out, d, scratch)`, with the arguments in `r3`–`r5`
and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.Secp256k1

open VG VG.PPC64LE Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.Secp256k1.curve) :=
  publicKey Spec.Secp256k1.curve (ofBytes (bytesAt m d 32))

def pkPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 65⟩
    let d : Region := ⟨s.gpr .r4, 32⟩
    let scratch : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .r3).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .r4) with
    | some (.affine x y) => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 65 = encodePoint (.affine x y)
    | _ => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 65 = List.replicate 65 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

end VG.Proof.EcKey.PPC64LE.Secp256k1

end

end

/-!
# secp256k1 public keys by the comb on PPC64LE: `Verified`

`vg_ec_secp256k1_public_key` with `[d]G` by the seven-bit comb, whose table is a
read-only constant (`Abi.withConsts`): `combPk_ok`, from `publicKeyWith_ok`
and the comb as the generator; `combPk_ct`, by `taint_decide` with the
table's address public; and the contract with the table.
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.Secp256k1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.TComb

theorem pre_of {s : State} (h : pkPPC.pre s) : PkPre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem post_of {s s' : State} (h : PkPost secp256k1 s s') : pkPPC.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .r4) with
    | some (.affine x y) => s'.gpr .r3 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 65 = List.replicate 65 0
  revert h
  generalize hq : pk s.mem (s.gpr .r4) = q
  rw [show Spec.EcKey.publicKey secp256k1.C (dk secp256k1 s) = pk s.mem (s.gpr .r4) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- A state satisfying the precondition (without the table). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the public key's (without the table). -/
theorem pkPPC_implies : pkPPC.Implies (Spec.EcKey.Secp256k1.inst.publicKeyContract PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [pkPPC, pk, Spec.Secp256k1.curve] at h
        revert h
        generalize Spec.EcKey.publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

/-- The public key's contract with the table, as the proof states it. -/
def pkPC : Contract isa := Tab.withTable pkPPC secp256k1CombConsts secp256k1Comb.tsym

theorem combPk_ok (hL : Weierstrass.Law Spec.Secp256k1.curve) (s : State) (hs : pkPC.pre s) :
    ∃ t s', Exec isa Impl.EcKey.PPC64LE.publicKeySecp256k1Comb s t s' ∧ abiPreserved s s' ∧ pkPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := Tab.pk_ok secp256k1_ok (by decide) hL
    (Proof.Secp256k1.PPC64LE.comb_generator_ok hL) (pre_of hp) hk
  exact ⟨t, s', he, K, Tab.post_intro (post_of hpost)⟩

theorem combPk_ct : ConstantTime isa pkPC.pre pkPC.pub Impl.EcKey.PPC64LE.publicKeySecp256k1Comb :=
  VG.Taint.constantTime (A := vectorTaintSym [secp256k1Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

theorem combConsts_eq : secp256k1CombConsts = [(secp256k1Comb.tsym, secp256k1CombWords)] := rfl

/-- A state satisfying the precondition with the table. -/
def combSatC : State :=
  { satState with mem := Proof.Secp256k1.PPC64LE.combSatMem, rd := [⟨0x2000, 32⟩, ⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem combPk_sat : (Spec.EcKey.Secp256k1.inst.publicKeyContract (abi.withConsts secp256k1CombConsts)).pre combSatC := by
  have hl := Proof.Secp256k1.PPC64LE.comb_words_length
  have held := Proof.Secp256k1.PPC64LE.combSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, secp256k1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : combSatC = s
  sig_pre [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
    Spec.Secp256k1.curve, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem pkPC_implies : pkPC.Implies (Spec.EcKey.Secp256k1.inst.publicKeyContract (abi.withConsts secp256k1CombConsts)) :=
  Tab.implies pkPPC_implies ⟨combSatC, combPk_sat⟩

theorem combPk_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified PPC64LE.target Impl.EcKey.PPC64LE.publicKeySecp256k1Comb
      (Spec.EcKey.Secp256k1.inst.publicKeyContract (PPC64LE.abi.withConsts secp256k1CombConsts)) :=
  Verified.of_correct (combPk_ok hL) combPk_ct pkPC_implies

end VG.Proof.EcKey.PPC64LE.Secp256k1
