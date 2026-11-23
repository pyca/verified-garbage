module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Window
import VerifiedGarbage.Proof.Ecdh.PPC64LE.VerifiedAll
import VerifiedGarbage.Proof.Weierstrass.BytesLen
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Ecdh
public import VerifiedGarbage.Spec.BrainpoolP512r1
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Ecdh
meta import VerifiedGarbage.Spec.BrainpoolP512r1
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdh.PPC64LE.BrainpoolP512r1.Contract`, which only this module used -/

section

/-!
# ECDH over brainpoolP512r1 on PPC64LE: the contract the proof is written against

The facts of `Spec.Ecdh.Instance.exchangeContract` for brainpoolP512r1 on PPC64LE, by
name: `vg_ecdh_brainpoolp512r1(out, d, peer, scratch)`, with the arguments in `r3`–`r6`
and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.BrainpoolP512r1

open VG VG.PPC64LE Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64)) (bytesAt m peer 129)

def ecdhPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 64⟩
    let d : Region := ⟨s.gpr .r4, 64⟩
    let peer : Region := ⟨s.gpr .r5, 129⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .r3).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 129 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 64 = z
    | none => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdh.PPC64LE.BrainpoolP512r1

end

end

/-!
# ECDH over brainpoolP512r1 on PPC64LE: `Verified`

`win_mulPowOk`: `[d]P` by the three-bit windows for any `a`
(`Proof/Ecdsa/PPC64LE/BrainpoolP512r1/Window.lean`), then `Z^(p-2)` by its addition chain, leaves
what ECDH's last stage needs (`LadPost`),
by `Win.pow_ok` (`Proof/Ecdh/PPC64LE/VerifiedAll.lean`) on the curve's `mul_ok`.
`ecdh_ppc`: from `exchangeWith_ok`,
for brainpoolP512r1's configuration; `ecdh_ct`: the
time depends only on `out`, `d`, `peer` and `scratch` (`taint_decide` on the
code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.BrainpoolP512r1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdh.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

/-- The contract with the table of constants (`Cfg.constsK`), as the proof states it. -/
abbrev ecdhPC : Contract isa := ecdhPPC.withTables brainpoolp512r1.constsK

theorem pre_of {s : State} (h : ecdhPPC.pre (stripConsts brainpoolp512r1.constsK s)) (hk : ConstsOk brainpoolp512r1.constsK 0 s) :
    EPre brainpoolp512r1 s (constRegs brainpoolp512r1.constsK s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨hk.rd_strip h1, h2, h3, h4, h5, h6, h7, h8, h9, tbl_of_consts hk (List.mem_singleton_self _)
    (hk.disjoint_wr (List.mem_singleton_self _) (by
      show (⟨s.gpr .r6, size⟩ : Region) ∈ (stripConsts brainpoolp512r1.constsK s).wr
      rw [h2]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

theorem post_of {s s' : State} (h : EPost brainpoolp512r1 s s') : ecdhPPC.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 64 = z
    | none => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 64 = List.replicate 64 0
  revert h
  generalize hq : ex s.mem (s.gpr .r4) (s.gpr .r5) = q
  rw [show Spec.Ecdh.exchange brainpoolp512r1.C (dk brainpoolp512r1 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) (1 + 2 * brainpoolp512r1.C.len)) = ex s.mem (s.gpr .r4) (s.gpr .r5) from rfl, hq]
  rcases q with _ | z <;> exact id

set_option exponentiation.threshold 1024 in
open VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass
  VG.Proof.Weierstrass.PPC64LE in
/-- The windows, then the addition chain, meet `MulPowOk`. -/
theorem win_mulPowOk (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (s₀ : State) :
    MulPowOk brainpoolp512r1 s₀ (brainpoolp512r1.winCall (WindowA.Cfg.mul3top brainpoolp512r1 PX PY B3P)) := by
  intro base s K hrx hry hrz _ ht₀ _ _ P hP hG hlx hly rest Q h
  have F' := K.fixed
  have hpre : Proof.Ecdsa.PPC64LE.Window.BrainpoolP512r1.MPre base s P (dk brainpoolp512r1 s₀) :=
    ⟨K.ws, ⟨F'.ap, F'.b3p, F'.zero, F'.onep⟩,
      ⟨hG, hlx, hly, lt_of_eq_of_lt F'.onep (Nat.mod_lt _ (by decide))⟩, hP,
      fun t ht => ht₀ t ht, Nat.lt_of_lt_of_le (ofBytes_bytesAt_lt _ _ _) (Nat.le_refl _)⟩
  obtain h7 : brainpoolp512r1.n < 10 := by decide
  exact Win.pow_ok brainpoolp512r1_ok (E := 8) (by decide) K
    (WP.mono (Win.winCall_of h7 K.ws (W := Proof.Ecdsa.PPC64LE.Window.BrainpoolP512r1.mulW)
      (fun w hw => by
        simp only [Proof.Ecdsa.PPC64LE.Window.BrainpoolP512r1.mulW, List.mem_cons, List.not_mem_nil,
          or_false] at hw
        rcases hw with rfl | rfl | rfl <;> rw [sl_eq, show brainpoolp512r1.n = 8 from rfl] <;> omega)
      (P := fun t => Proof.Ecdsa.PPC64LE.Window.BrainpoolP512r1.PtOk base t (Impl.Ecdsa.PPC64LE.Window.Cfg.rPt brainpoolp512r1)
        (Spec.Weierstrass.mul (dk brainpoolp512r1 s₀) P))
      (fun t t' hm R => R.of_eq (by rw [hm]) (by rw [hm]) (by rw [hm]))
      fun t ht hU => by
        obtain k' := Win.KC.saved h7 (bs := B3P) (bK := 3 * brainpoolp512r1.C.b) (by decide) K.ws.nowrap hU
          ⟨hpre.kc.ap, hpre.kc.bp, hpre.kc.zero, hpre.kc.onep⟩
        obtain g' := Win.PtOk.saved h7 K.ws.nowrap hU (Q := P) ⟨hpre.g.rep, hpre.g.x, hpre.g.y, hpre.g.z⟩
        exact Proof.Ecdsa.PPC64LE.Window.BrainpoolP512r1.mul_ok hL ⟨ht, ⟨k'.ap, k'.bp, k'.zero, k'.onep⟩,
          ⟨g'.rep, g'.x, g'.y, g'.z⟩, hpre.on, Win.Bits.saved h7 hU hpre.bits, hpre.lt⟩) fun _ ⟨hk, hu, hr⟩ =>
      ⟨hk, hu, ⟨hr.rep, hr.x, hr.y, hr.z⟩⟩) h

theorem ecdh_ppc (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (s : State) (hs : ecdhPC.pre s) :
    ∃ t s', Exec isa exchangeBrainpoolP512r1 s t s' ∧ abiPreserved s s' ∧ ecdhPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  obtain ⟨t, s', he, K, hpost⟩ := exchangeWith_ok brainpoolp512r1_ok hL (pre_of hp hk) (win_mulPowOk hL s)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhPC.pre ecdhPC.pub exchangeBrainpoolP512r1 :=
  VG.Taint.constantTime (A := taintSym [brainpoolp512r1.constSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
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
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 129⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

/-- The contract as the proof states it implies the exchange's (without the table). -/
theorem ecdhPPC_implies :
    ecdhPPC.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst PPC64LE.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [ecdhPPC, ex, Spec.BrainpoolP512r1.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

/-- A state satisfying the precondition with the table. -/
def satStateC : State where
  gpr := satState.gpr
  lr := satState.lr
  sp := satState.sp
  mem := tblSatMem brainpoolp512r1
  rd := satState.rd ++ [⟨0x100000, 8 * (17 * 8)⟩]
  wr := satState.wr
  syms := fun _ => 0x100000

theorem satC_pre :
    (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst (abi.withConsts brainpoolp512r1.constsK)).pre satStateC := by
  have hl := constTbl_length brainpoolp512r1
  have held := tblSatMem_held brainpoolp512r1 (by decide)
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp512r1.constTbl = W := ⟨_, rfl⟩
  have hk : brainpoolp512r1.constsK = [(brainpoolp512r1.constSym, W)] := by rw [← eW]; rfl
  rw [hk]
  rw [eW] at hl held
  generalize e : satStateC = s
  sig_pre [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract, Spec.Ecdh.Instance.exchangeSig,
    Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem ecdhPC_implies :
    ecdhPC.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst (PPC64LE.abi.withConsts brainpoolp512r1.constsK)) :=
  withTables_implies ecdhPPC_implies ⟨satStateC, satC_pre⟩

theorem ecdh_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified PPC64LE.target exchangeBrainpoolP512r1
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst (PPC64LE.abi.withConsts brainpoolp512r1.constsK)) :=
  Verified.of_correct (ecdh_ppc hL) ecdh_ct ecdhPC_implies

end VG.Proof.Ecdh.PPC64LE.BrainpoolP512r1
