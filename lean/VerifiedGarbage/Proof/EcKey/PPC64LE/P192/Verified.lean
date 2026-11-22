module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
public import VerifiedGarbage.Impl.EcKey.P192.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.EcKey.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
meta import VerifiedGarbage.Impl.EcKey.P192.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
meta import VerifiedGarbage.Spec.EcKey.P192
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.P192.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.P192
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.P192
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `EcKey.PPC64LE.P192.Contract`, which only this module used -/

section

/-!
# P-192 public keys on PPC64LE: the contract the proof is written against

The facts of `Spec.EcKey.P192.inst.publicKeyContract` for PPC64LE, by name:
`vg_ec_p192_public_key(out, d, scratch)`, with the arguments in `r3`–`r5`
and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.P192

open VG VG.PPC64LE Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P192.curve) :=
  publicKey Spec.P192.curve (ofBytes (bytesAt m d 24))

def pkPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 49⟩
    let d : Region := ⟨s.gpr .r4, 24⟩
    let scratch : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .r3).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 24 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .r4) with
    | some (.affine x y) => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 49 = encodePoint (.affine x y)
    | _ => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 49 = List.replicate 49 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

end VG.Proof.EcKey.PPC64LE.P192

end

end

/-!
# P-192 public keys on PPC64LE: `Verified`

`pk_ppc`: from `publicKey_ok`, for P-192's configuration; `pk_ct`: the
time depends only on `out`, `d` and `scratch` (`taint_decide` on the code's
literal).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.P192

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

/-- The contract with the table of constants (`Cfg.constsK`), as the proof states it. -/
abbrev pkPC : Contract isa := pkPPC.withTables p192.constsK

theorem pre_of {s : State} (h : pkPPC.pre (stripConsts p192.constsK s)) (hk : ConstsOk p192.constsK 0 s) :
    PkPre p192 s (constRegs p192.constsK s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨hk.rd_strip h1, h2, h3, h4, h5, h6, h7, fun _ =>
    tbl_of_consts hk (List.mem_singleton_self _) (hk.disjoint_wr (List.mem_singleton_self _) (by
      show (⟨s.gpr .r5, size⟩ : Region) ∈ (stripConsts p192.constsK s).wr
      rw [h2]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

theorem post_of {s s' : State} (h : PkPost p192 s s') : pkPPC.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .r4) with
    | some (.affine x y) => s'.gpr .r3 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 49 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 49 = List.replicate 49 0
  revert h
  generalize hq : pk s.mem (s.gpr .r4) = q
  rw [show Spec.EcKey.publicKey p192.C (dk p192 s) = pk s.mem (s.gpr .r4) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_ppc (hL : Weierstrass.Law Spec.P192.curve) (s : State) (hs : pkPC.pre s) :
    ∃ t s', Exec isa Impl.EcKey.PPC64LE.publicKeyP192 s t s' ∧ abiPreserved s s' ∧ pkPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := publicKey_ok p192_ok (by decide) hL (pre_of hp hk)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem pk_ct : ConstantTime isa pkPC.pre pkPC.pub Impl.EcKey.PPC64LE.publicKeyP192 :=
  VG.Taint.constantTime (A := taintSym [p192.constSym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact sy _ (List.mem_singleton_self _)⟩)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 24⟩]
  wr := [⟨0x1000, 49⟩, ⟨0x8000, 8192⟩]

/-- `pkPPC` states `publicKeyContract`'s facts by name. -/
theorem pkPPC_implies : pkPPC.Implies (Spec.EcKey.P192.inst.publicKeyContract PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [pkPPC, pk, Spec.P192.curve] at h
        revert h
        generalize Spec.EcKey.publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

theorem constsK_eq : p192.constsK = [(p192.constSym, p192.constTbl)] := rfl

/-- A state satisfying the precondition with the table. -/
def pkSatC : State where
  gpr := satState.gpr
  lr := satState.lr
  sp := satState.sp
  mem := tblSatMem p192
  rd := satState.rd ++ [⟨0x100000, 8 * (17 * 3)⟩]
  wr := satState.wr
  syms := fun _ => 0x100000

theorem pkSat : (Spec.EcKey.P192.inst.publicKeyContract (abi.withConsts p192.constsK)).pre pkSatC := by
  have hl := constTbl_length p192
  have held := tblSatMem_held p192 (by decide)
  rw [constsK_eq]
  obtain ⟨W, eW⟩ : ∃ W, p192.constTbl = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : pkSatC = s
  sig_pre [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
    Spec.P192.curve, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 49⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem pk_verified (hL : Weierstrass.Law Spec.P192.curve) :
    Verified PPC64LE.target Impl.EcKey.PPC64LE.publicKeyP192
      (Spec.EcKey.P192.inst.publicKeyContract (PPC64LE.abi.withConsts p192.constsK)) :=
  Verified.of_correct (pk_ppc hL) pk_ct (withTables_implies pkPPC_implies ⟨pkSatC, pkSat⟩)

end VG.Proof.EcKey.PPC64LE.P192
