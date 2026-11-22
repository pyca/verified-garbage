module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
public import VerifiedGarbage.Proof.EcKey.PPC64LE.CombAll
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
public import VerifiedGarbage.Proof.P224.PPC64LE.Comb
import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.CombLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.CombAll
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
meta import VerifiedGarbage.Proof.P224.PPC64LE.Comb
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.CombLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.P224
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.P224
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `EcKey.PPC64LE.P224.Contract`, which only this module used -/

section

/-!
# P-224 public keys on PPC64LE: the contract the proof is written against

The facts of `Spec.EcKey.P224.inst.publicKeyContract` for PPC64LE, by name:
`vg_ec_p224_public_key(out, d, scratch)`, with the arguments in `r3`–`r5`
and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.P224

open VG VG.PPC64LE Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P224.curve) :=
  publicKey Spec.P224.curve (ofBytes (bytesAt m d 28))

def pkPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 57⟩
    let d : Region := ⟨s.gpr .r4, 28⟩
    let scratch : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .r3).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 28 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .r4) with
    | some (.affine x y) => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 57 = encodePoint (.affine x y)
    | _ => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 57 = List.replicate 57 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

end VG.Proof.EcKey.PPC64LE.P224

end

end

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

/-- The tables of constants the public key reads: the comb's, and the setup's
(`Cfg.constsK`). -/
abbrev pkK : List (String × List (BitVec 64)) := p224CombConsts ++ p224.constsK

theorem pkK_eq : pkK = [(p224Comb.tsym, p224CombWords), (p224.constSym, p224.constTbl)] := rfl

theorem pre_of {s : State} (h : pkPPC.pre (stripConsts pkK s)) (hk : ConstsOk pkK 0 s) :
    PkPre p224 s (constRegs pkK s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨hk.rd_strip h1, h2, h3, h4, h5, h6, h7, fun _ =>
    tbl_of_consts hk (List.mem_append_right _ (List.mem_singleton_self _)) (hk.disjoint_wr
      (List.mem_append_right _ (List.mem_singleton_self _)) (by
        show (⟨s.gpr .r5, size⟩ : Region) ∈ (stripConsts pkK s).wr
        rw [h2]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

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

/-- The public key's contract with its tables, as the proof states it. -/
abbrev pkPC : Contract isa := pkPPC.withTables pkK

theorem combPk_ok (hL : Weierstrass.Law Spec.P224.curve) (s : State) (hs : pkPC.pre s) :
    ∃ t s', Exec isa Impl.EcKey.PPC64LE.publicKeyP224Comb s t s' ∧ abiPreserved s s' ∧ pkPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := Tab.pk_okK p224_ok (by decide) hL
    (Proof.P224.PPC64LE.comb_generator_ok hL) (pre_of hp hk) hk (List.mem_append_left _ (List.mem_singleton_self _))
  exact ⟨t, s', he, K, post_of hpost⟩

theorem combPk_ct : ConstantTime isa pkPC.pre pkPC.pub Impl.EcKey.PPC64LE.publicKeyP224Comb :=
  VG.Taint.constantTime (A := vectorTaintSym [p224Comb.tsym, p224.constSym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl
        · exact sy _ (List.mem_append_left _ (List.mem_singleton_self _))
        · exact sy _ (List.mem_append_right _ (List.mem_singleton_self _))⟩)
    (by taint_decide)

/-- The memory of the witness with the tables: the comb's at `0x100000`,
the setup's at `0x200000` (irreducible: unfolding it in a definitional check
would evaluate the tables). -/
@[irreducible] def pkSatMem2 : Mem := constMem2 0x100000 p224CombWords 0x200000 p224.constTbl

theorem pkSatMem2_held₁ : ∀ i < p224CombWords.length,
    pkSatMem2.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p224CombWords.getD i 0 := by
  unfold pkSatMem2
  exact constMem2_held₁ _ _ _ _ (by rw [Proof.P224.PPC64LE.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem pkSatMem2_held₂ : ∀ i < p224.constTbl.length,
    pkSatMem2.readW (0x200000 + BitVec.ofNat 64 (8 * i)) 64 = p224.constTbl.getD i 0 := by
  unfold pkSatMem2
  exact constMem2_held₂ _ _ _ _ (by rw [constTbl_length]; decide)

/-- The addresses of the witness's tables. -/
def pkSyms (n : String) : Addr := if n = p224.constSym then 0x200000 else 0x100000

/-- A state satisfying the precondition with the tables. -/
def combSatC : State where
  gpr := satState.gpr
  lr := satState.lr
  sp := satState.sp
  mem := pkSatMem2
  rd := satState.rd ++ [⟨0x100000, 8 * 16384⟩, ⟨0x200000, 8 * (17 * 4)⟩]
  wr := satState.wr
  syms := pkSyms

theorem combPk_sat : (Spec.EcKey.P224.inst.publicKeyContract (abi.withConsts pkK)).pre combSatC := by
  have hl₁ := Proof.P224.PPC64LE.comb_words_length
  have hl₂ := constTbl_length p224
  have held₁ := pkSatMem2_held₁
  have held₂ := pkSatMem2_held₂
  rw [pkK_eq]
  obtain ⟨W₁, eW₁⟩ : ∃ W, p224CombWords = W := ⟨_, rfl⟩
  obtain ⟨W₂, eW₂⟩ : ∃ W, p224.constTbl = W := ⟨_, rfl⟩
  rw [eW₁] at hl₁ held₁ ⊢
  rw [eW₂] at hl₂ held₂ ⊢
  generalize e : combSatC = s
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
    Spec.P224.curve, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl₁, hl₂]
  refine ⟨rfl, fun i hi => ?_, fun i hi => ?_, by decide, fun r hr => ?_, by decide, fun r hr => ?_, by decide,
    by decide, ?_⟩
  · show pkSatMem2.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = _
    exact held₁ i (by rw [hl₁]; exact hi)
  · show pkSatMem2.readW (0x200000 + BitVec.ofNat 64 (8 * i)) 64 = _
    exact held₂ i (by rw [hl₂]; exact hi)
  · change r ∈ satState.wr at hr
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · change r ∈ satState.wr at hr
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem pkPC_implies : pkPC.Implies (Spec.EcKey.P224.inst.publicKeyContract (abi.withConsts pkK)) :=
  withTables_implies pkPPC_implies ⟨combSatC, combPk_sat⟩

theorem combPk_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified PPC64LE.target Impl.EcKey.PPC64LE.publicKeyP224Comb
      (Spec.EcKey.P224.inst.publicKeyContract (PPC64LE.abi.withConsts pkK)) :=
  Verified.of_correct (combPk_ok hL) combPk_ct pkPC_implies

end VG.Proof.EcKey.PPC64LE.P224
