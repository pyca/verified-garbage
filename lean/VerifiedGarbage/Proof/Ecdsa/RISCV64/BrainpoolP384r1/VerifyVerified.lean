module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.RISCV64.Hash
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.VerifyLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.MulFn
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.MulFn
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Sign
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.Sign
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.VerifyAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.Exchange
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.JointJ
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.RISCV64.Ecdsa
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.VerifyAll
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.Exchange
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.JointJ
meta import VerifiedGarbage.Spec.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.RISCV64.Ecdsa

/-! ### `Ecdsa.RISCV64.BrainpoolP384r1.Verify`, which only this module used -/

section

/-!
# ECDSA verification over brainpoolp384r1 on RISC-V: correctness

`vg_ecdsa_brainpoolp384r1_verify` meets its contract by register (`verifyRV`),
given the group law (`verify_rv`). The proof is the one of every curve, `VerifyAll.Kit.verify_ok`
(`Proof/Ecdsa/RISCV64/VerifyAll.lean`), from what `vkit` says of this one, with `[u]G + [v]Q`
by the joint ladder (`JointJ.jointJ_ok`).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.

set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.BrainpoolP384r1
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)

/-- Whether the signature at `sig` of `digest` verifies with the key at `pk`,
as the specification answers. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  Spec.Ecdsa.verify W (bytesAt m pk 97) (hashToInt W (bytesAt m digest 48)) (bytesAt m sig 96)

def verifyRV : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 97⟩
    let digest : Region := ⟨s.gpr .a1, 48⟩
    let sig : Region := ⟨s.gpr .a2, 96⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .a0).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 96 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' := s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

/-- What the proofs shared by every curve (`VerifyAll.lean`) need of this one: the signature's kit,
and that a number of the signature's bytes is below `2 n`. -/
def vkit : VerifyAll.Kit where
  toSKit := skit
  n2 := by decide

theorem verify_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : verifyRV.pre s) :
    ∃ t s', Exec isa verifyBrainpoolP384r1 s t s' ∧ abiPreserved s s' ∧ verifyRV.post s s' := by
  obtain ⟨hrd, hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩ := hs
  obtain ⟨t, s', he, h⟩ := vkit.verify_ok hL (s := s) (T := fun _ => True)
    (JW := VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.JointJ.jointW) ⟨by decide, by decide, by decide, by decide⟩
    ⟨by rw [hrd]; exact .head _, by rw [hrd]; exact .tail _ (.head _), by rw [hrd]; exact .tail _ (.tail _ (.head _)),
      hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩
    (fun _ _ _ _ => trivial) (fun _ _ h => WP.mono h fun _ q => ⟨q, trivial⟩) (fun _ _ _ _ _ => trivial)
    (fun J _ => WP.mono (VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.JointJ.jointJ_ok hL
        ⟨J.ws, J.tc.ap, J.tc.b3p, J.tc.zero, J.tc.onep, J.gx, J.gy, J.qx, J.qy, J.q, J.on⟩)
      fun _ ⟨K₆, U₆, pR₆⟩ => ⟨K₆, U₆, pR₆.rep, pR₆.x, pR₆.y, pR₆.z⟩)
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1

end

end

/-!
# ECDSA verification over brainpoolp384r1 on RISC-V: `Verified`

`verify_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, public, although the contract lets every input
affect timing).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify

theorem verify_ct : ConstantTime isa verifyRV.pre verifyRV.pub verifyBrainpoolP384r1 :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, h3⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩)
    (by taint_decide_sum [VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.pMulSum,
      VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.pAddSum, VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.pSubSum,
      VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.nMulSum, VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.nAddSum,
      VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1.nSubSum])

/-- A state satisfying the precondition. -/
def verifySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verify_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target verifyBrainpoolP384r1 (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst RISCV64.abi) :=
  Verified.of_correct (verify_rv hL) verify_ct
    { pre := by
        sig_implies_pre [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
        have h' : s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0 := h
        rw [h']
        show BitVec.setWidth 32 (if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0) =
          if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
        split <;> rfl
      pub := by
        sig_implies_pub [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
          Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, verifyRV, vf, RISCV64.abi,
          RISCV64.argRegs] [verifySat] using verifySat }


/-- `verifySat` satisfies the precondition. -/
theorem verify_sat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst RISCV64.abi).pre verifySat := by
  sig_pre [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, RISCV64.abi, RISCV64.argRegs, verifySat]
  repeat' (first | exact Region.disjoint_of_sep (by decide) | decide | rfl | constructor)

/-- `vg_ecdsa_brainpoolp384r1_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_nil`). -/
theorem verifyHash_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target
      (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false Impl.Ecdsa.RISCV64.verifyBrainpoolP384r1)
      (Spec.Ecdsa.Instance.verifyHashContract Spec.Ecdsa.BrainpoolP384r1.inst RISCV64.abi 80) :=
  Proof.Ecdsa.Verify.RISCV64.verifyHash_verified_nil Proof.Ecdsa.Verify.brainpoolP384r1_len (by decide) (verify_verified hL)
    (by taint_decide) (Proof.Ecdsa.Verify.RISCV64.hashSat_nil (by decide) verify_sat (by decide) fun r hr => by
      simp only [verifySat, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- `vg_ecdsa_brainpoolp384r1_verify` as emitted, cleanup included
(`Impl.Ecdsa.RISCV64.Fn.verifyBrainpoolP384r1`), meets its contract in constant time and
returns without secret residue. -/
theorem verifyHash_scrubbed (hL : VG.Proof.Weierstrass.Law W) :
    VerifiedScrubbed RISCV64.target Impl.Ecdsa.RISCV64.Fn.verifyBrainpoolP384r1
      (Spec.Ecdsa.Instance.verifyHashContract Spec.Ecdsa.BrainpoolP384r1.inst RISCV64.abi 80) 32 :=
  RISCV64.Scrub.verifiedScrubbed (api := Spec.Ecdsa.BrainpoolP384r1.verifyHashApi) (W := 80)
    { code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false
        Impl.Ecdsa.RISCV64.verifyBrainpoolP384r1
      verified := verifyHash_verified hL }
    (EcKey.RISCV64.Scrub.verifyHashOut _ [] _) (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1
