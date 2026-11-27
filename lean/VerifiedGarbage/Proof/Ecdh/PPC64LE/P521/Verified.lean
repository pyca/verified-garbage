module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
public import VerifiedGarbage.Impl.Ecdh.P521.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Window
import VerifiedGarbage.Proof.Ecdh.PPC64LE.VerifiedAll
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
meta import VerifiedGarbage.Impl.Ecdh.P521.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
meta import VerifiedGarbage.Spec.EcKey.P521
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Ecdh
public import VerifiedGarbage.Spec.P521
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Ecdh
meta import VerifiedGarbage.Spec.P521
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdh.PPC64LE.P521.Contract`, which only this module used -/

section

/-!
# ECDH over P-521 on PPC64LE: the contract the proof is written against

The facts of `Spec.Ecdh.Instance.exchangeContract` for P-521 on PPC64LE, by
name: `vg_ecdh_p521(out, d, peer, scratch)`, with the arguments in `r3`–`r6`
and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.P521

open VG VG.PPC64LE Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P521.curve (ofBytes (bytesAt m d 66)) (bytesAt m peer 133)

def ecdhPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 66⟩
    let d : Region := ⟨s.gpr .r4, 66⟩
    let peer : Region := ⟨s.gpr .r5, 133⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .r3).toNat + 66 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 66 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 133 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 66 = z
    | none => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 66 = List.replicate 66 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdh.PPC64LE.P521

end

end

/-!
# ECDH over P-521 on PPC64LE: `Verified`

`win_mulPowOk`: `[d]P` by the three-bit windows
(`Proof/Ecdsa/PPC64LE/P521/Window.lean`), then `Z^(p-2)` by its addition chain, leaves
what ECDH's last stage needs (`LadPost`),
by `Win.mulPowOk` (`Proof/Ecdh/PPC64LE/VerifiedAll.lean`) on the curve's kit.
`ecdh_ppc`: from `exchangeWith_ok`,
for P-521's configuration; `ecdh_ct`: the
time depends only on `out`, `d`, `peer` and `scratch` (`taint_decide` on the
code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.P521

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdh.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

/-- The contract with the table of constants (`Cfg.constsK`), as the proof states it. -/
abbrev ecdhPC : Contract isa := ecdhPPC.withTables p521.constsK

theorem pre_of {s : State} (h : ecdhPPC.pre (stripConsts p521.constsK s)) (hk : ConstsOk p521.constsK 0 s) :
    EPre p521 s (constRegs p521.constsK s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨hk.rd_strip h1, h2, h3, h4, h5, h6, h7, h8, h9, tbl_of_consts hk (List.mem_singleton_self _)
    (hk.disjoint_wr (List.mem_singleton_self _) (by
      show (⟨s.gpr .r6, size⟩ : Region) ∈ (stripConsts p521.constsK s).wr
      rw [h2]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

theorem post_of {s s' : State} (h : EPost p521 s s') : ecdhPPC.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 66 = z
    | none => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 66 = List.replicate 66 0
  revert h
  generalize hq : ex s.mem (s.gpr .r4) (s.gpr .r5) = q
  rw [show Spec.Ecdh.exchange p521.C (dk p521 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) (1 + 2 * p521.C.len)) = ex s.mem (s.gpr .r4) (s.gpr .r5) from rfl, hq]
  rcases q with _ | z <;> exact id

/-- The windows, then the addition chain, meet `MulPowOk`. -/
theorem win_mulPowOk (hL : Weierstrass.Law Spec.P521.curve) (s₀ : State) :
    MulPowOk p521 s₀ (p521.winCall (Window.Cfg.mul3 p521 PX PY BP)) :=
  Win.mulPowOk Proof.Ecdsa.PPC64LE.Window.P521.kit (.inl ⟨rfl, rfl⟩) (by decide) hL s₀

theorem ecdh_ppc (hL : Weierstrass.Law Spec.P521.curve) (s : State) (hs : ecdhPC.pre s) :
    ∃ t s', Exec isa exchangeP521 s t s' ∧ abiPreserved s s' ∧ ecdhPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := exchangeWith_ok p521_ok hL (pre_of hp hk) (win_mulPowOk hL s)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhPC.pre ecdhPC.pub exchangeP521 :=
  VG.Taint.constantTime (A := taintSym [p521.constSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact sy _ (List.mem_singleton_self _)⟩)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 66⟩, ⟨0x3000, 133⟩]
  wr := [⟨0x1000, 66⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the exchange's (without the table). -/
theorem ecdhPPC_implies :
    ecdhPPC.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [ecdhPPC, ex, Spec.P521.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P521.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

/-- A state satisfying the precondition with the table. -/
def satStateC : State where
  gpr := satState.gpr
  lr := satState.lr
  sp := satState.sp
  mem := tblSatMem p521
  rd := satState.rd ++ [⟨0x100000, 8 * (17 * 9)⟩]
  wr := satState.wr
  syms := fun _ => 0x100000

theorem satC_pre :
    (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst (abi.withConsts p521.constsK)).pre satStateC := by
  have hl := constTbl_length p521
  have held := tblSatMem_held p521 (by decide)
  obtain ⟨W, eW⟩ : ∃ W, p521.constTbl = W := ⟨_, rfl⟩
  have hk : p521.constsK = [(p521.constSym, W)] := by rw [← eW]; rfl
  rw [hk]
  rw [eW] at hl held
  generalize e : satStateC = s
  sig_pre [Spec.EcKey.P521.inst, Spec.Ecdh.Instance.exchangeContract, Spec.Ecdh.Instance.exchangeSig,
    Spec.P521.curve, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 66⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem ecdhPC_implies :
    ecdhPC.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst (PPC64LE.abi.withConsts p521.constsK)) :=
  withTables_implies ecdhPPC_implies ⟨satStateC, satC_pre⟩

theorem ecdh_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified PPC64LE.target exchangeP521
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst (PPC64LE.abi.withConsts p521.constsK)) :=
  Verified.of_correct (ecdh_ppc hL) ecdh_ct ecdhPC_implies

end VG.Proof.Ecdh.PPC64LE.P521
