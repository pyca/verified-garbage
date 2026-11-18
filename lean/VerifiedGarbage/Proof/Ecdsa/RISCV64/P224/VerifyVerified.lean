module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.VerifyLit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombVerified
meta import VerifiedGarbage.Spec.Ecdsa.Verify.P224
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.VerifyAll
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.Sign
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Exchange
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P224
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.JointComb
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.VerifyAll
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.Sign
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Exchange
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.P224
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.JointComb
meta import VerifiedGarbage.Spec.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.Verify

/-! ### `Ecdsa.RISCV64.P224.Verify`, which only this module used -/

section

/-!
# ECDSA verification over P-224 on RISC-V: correctness

`vg_ecdsa_p224_verify` meets its contract by register (`verifyRV`, with the comb's table (`verifyRVC`)),
given the group law (`verify_rv`). The proof is the one of every curve, `VerifyAll.Kit.verify_ok`
(`Proof/Ecdsa/RISCV64/VerifyAll.lean`), from what `vkit` says of this one, with `[u]G + [v]Q`
by the comb and windows (`JointComb.jointComb_ok`), with the comb's table, which the code before
it leaves alone.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.P224
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)

/-- Whether the signature at `sig` of `digest` verifies with the key at `pk`,
as the specification answers. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  Spec.Ecdsa.verify W (bytesAt m pk 57) (hashToInt W (bytesAt m digest 28)) (bytesAt m sig 56)

def verifyRV : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 57⟩
    let digest : Region := ⟨s.gpr .a1, 28⟩
    let sig : Region := ⟨s.gpr .a2, 56⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .a0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 28 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 56 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' := s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

/-- `verifyRV` with the comb's table (`abi.withConsts`): `verifyRV` for the
state without it, and what the table adds. -/
def verifyRVC : Contract isa where
  pre s := verifyRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.p224CombConsts 0 s
  post := verifyRV.post
  pub s₁ s₂ := verifyRV.pub s₁ s₂ ∧ s₁.syms Impl.Ecdsa.RISCV64.Comb.p224Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.p224Sym

/-- What the proofs shared by every curve (`VerifyAll.lean`) need of this one: the signature's kit,
and that a number of the signature's bytes is below `2 n`. -/
def vkit : VerifyAll.Kit where
  toSKit := skit
  n2 := by decide

theorem verify_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : verifyRVC.pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.P224.verifyP224 s t s' ∧ abiPreserved s s' ∧ verifyRVC.post s s' := by
  obtain ⟨hs₀, hk⟩ := hs
  obtain ⟨hrd, hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩ := hs₀
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hpd hdd hsd hfp hfd hfg hfs hal
  obtain ⟨t, s', he, h⟩ := vkit.verify_ok hL (s := s) (T := Comb.TabAt (s.gpr .a3))
    (JW := VG.Proof.Ecdsa.RISCV64.P224.JointComb.combW) ⟨by decide, by decide, by decide, by decide⟩
    ⟨stripConsts_rd_mem (by rw [hrd]; exact .head _), stripConsts_rd_mem (by rw [hrd]; exact .tail _ (.head _)),
      stripConsts_rd_mem (by rw [hrd]; exact .tail _ (.tail _ (.head _))), hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩
    (fun s₁ sy₁ rd₁ F₁ =>
      (Comb.tabAt_of_consts hk (by rw [hwr]; simp)).of_frame sy₁ rd₁ F₁ (Comb.tab_wr_of_consts hk))
    (fun hT hw h => JointComb.wp_tab (JointComb.wsCall_noFrames vkit.checkNF) hT hw h)
    (fun hT sy rd hW U => hT.of_unch sy rd hW U)
    (fun J hT => WP.mono (VG.Proof.Ecdsa.RISCV64.P224.JointComb.jointComb_ok hL
        ⟨J.ws, J.tc.ap, J.bp, J.tc.zero, J.tc.onep, J.gx, J.gy, J.qx, J.qy, J.q, J.on⟩ J.s3
        ⟨J.tc.mp, J.tc.mn, J.tc.zero, J.tc.one, J.tc.onep, J.tc.ap, J.tc.b3p, J.tc.expp⟩ hT J.wr J.u J.v)
      fun _ ⟨K₆, U₆, pR₆⟩ => ⟨K₆, U₆, pR₆.rep, pR₆.x, pR₆.y, pR₆.z⟩)
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdsa.RISCV64.P224

end

end

/-!
# ECDSA verification over P-224 on RISC-V: `Verified`

`verify_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, and the comb's table's address public, although the
contract lets every input affect timing), under `abi.withConsts` of the
comb's table (`verifyRVC_implies`, from `verifyRV_implies` without it, as for
signatures).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64.P224

theorem verify_ct : ConstantTime isa verifyRVC.pre verifyRVC.pub verifyP224 :=
  VG.Taint.constantTime (A := taintSym [Impl.Ecdsa.RISCV64.Comb.p224Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2, h3⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- A state satisfying the precondition without the table. -/
def verifySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 28⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verifyRV_implies : verifyRV.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
        have h' : s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0 := h
        rw [h']
        show BitVec.setWidth 32 (if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0) =
          if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
        split <;> rfl
      pub := by
        sig_implies_pub [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs] [verifySat] using verifySat }

/-- A state satisfying the precondition with the table. -/
def verifySatC : State :=
  { verifySat with mem := Comb.combSatMem, rd := verifySat.rd ++ [⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem verify_sat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst
    (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts)).pre verifySatC := by
  have hl := Comb.combWords_length
  have held := Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.Comb.p224CombConsts = [(Impl.Ecdsa.RISCV64.Comb.p224Sym,
    Impl.Ecdsa.RISCV64.Comb.p224CombWords)] from rfl]
  obtain ⟨W', eW⟩ : ∃ W, Impl.Ecdsa.RISCV64.Comb.p224CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : verifySatC = s
  sig_pre [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.P224.curve,
    Spec.Ecdsa.scratchWords, RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x8000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact Region.disjoint_of_sep (by decide)

theorem verifyRVC_implies :
    verifyRVC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts)) :=
  { pre := fun _ hs => ⟨verifyRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (verifyRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨verifyRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨verifySatC, verify_sat⟩ }

theorem verify_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target verifyP224 (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts)) :=
  Verified.of_correct (verify_rv hL) verify_ct verifyRVC_implies


/-- `vg_ecdsa_p224_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target
      (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false Impl.Ecdsa.RISCV64.P224.verifyP224)
      (Spec.Ecdsa.Instance.verifyHashContract Spec.Ecdsa.P224.inst (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts) 80) :=
  Proof.Ecdsa.Verify.RISCV64.verifyHash_verified_cons Proof.Ecdsa.Verify.p224_len (by decide) (verify_verified hL)
    (by taint_decide) (Proof.Ecdsa.Verify.RISCV64.hashSat_cons (by decide) verify_sat (by decide) fun r hr => by
      simp only [verifySatC, verifySat, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end VG.Proof.Ecdsa.RISCV64.P224
