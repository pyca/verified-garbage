module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.VerifyAll
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Sign
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.Exchange
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.JointComb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.CombVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify

/-!
# ECDSA verification over secp256k1 on RISC-V: correctness

`vg_ecdsa_secp256k1_verify` meets its contract by register (`verifyRV`, with the comb's table (`verifyRVC`)),
given the group law (`verify_rv`). The proof is the one of every curve, `VerifyAll.Kit.verify_ok`
(`Proof/Ecdsa/RISCV64/VerifyAll.lean`), from what `vkit` says of this one, with `[u]G + [v]Q`
by the comb and windows (`JointComb.jointComb_ok`), with the comb's table, which the code before
it leaves alone.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.Secp256k1
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)

/-- Whether the signature at `sig` of `digest` verifies with the key at `pk`,
as the specification answers. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  Spec.Ecdsa.verify W (bytesAt m pk 65) (hashToInt W (bytesAt m digest 32)) (bytesAt m sig 64)

def verifyRV : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 65⟩
    let digest : Region := ⟨s.gpr .a1, 32⟩
    let sig : Region := ⟨s.gpr .a2, 64⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .a0).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' := s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

/-- `verifyRV` with the comb's table (`abi.withConsts`): `verifyRV` for the
state without it, and what the table adds. -/
def verifyRVC : Contract isa where
  pre s := verifyRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts 0 s
  post := verifyRV.post
  pub s₁ s₂ := verifyRV.pub s₁ s₂ ∧
    s₁.syms Impl.Ecdsa.RISCV64.Comb.secp256k1Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.secp256k1Sym

/-- What the proofs shared by every curve (`VerifyAll.lean`) need of this one: the signature's kit,
and that a number of the signature's bytes is below `2 n`. -/
def vkit : VerifyAll.Kit where
  toSKit := skit
  n2 := by decide

theorem verify_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : verifyRVC.pre s) :
    ∃ t s', Exec isa verifySecp256k1 s t s' ∧ abiPreserved s s' ∧ verifyRVC.post s s' := by
  obtain ⟨hs₀, hk⟩ := hs
  obtain ⟨hrd, hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩ := hs₀
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hpd hdd hsd hfp hfd hfg hfs hal
  obtain ⟨t, s', he, h⟩ := vkit.verify_ok hL (s := s) (T := Comb.TabAt (s.gpr .a3))
    (JW := VG.Proof.Ecdsa.RISCV64.Secp256k1.JointComb.combW) ⟨by decide, by decide, by decide, by decide⟩
    ⟨stripConsts_rd_mem (by rw [hrd]; exact .head _), stripConsts_rd_mem (by rw [hrd]; exact .tail _ (.head _)),
      stripConsts_rd_mem (by rw [hrd]; exact .tail _ (.tail _ (.head _))), hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩
    (fun s₁ sy₁ rd₁ F₁ =>
      (Comb.tabAt_of_consts hk (by rw [hwr]; simp)).of_frame sy₁ rd₁ F₁ (Comb.tab_wr_of_consts hk))
    (fun hT hw h => JointComb.wp_tab (JointComb.wsCall_noFrames vkit.checkNF) hT hw h)
    (fun hT sy rd hW U => hT.of_unch sy rd hW U)
    (fun J hT => WP.mono (VG.Proof.Ecdsa.RISCV64.Secp256k1.JointComb.jointComb_ok hL
        ⟨J.ws, J.tc.ap, J.tc.b3p, J.tc.zero, J.tc.onep, J.gx, J.gy, J.qx, J.qy, J.q, J.on⟩ J.s3
        ⟨J.tc.mp, J.tc.mn, J.tc.zero, J.tc.one, J.tc.onep, J.tc.ap, J.tc.b3p, J.tc.expp⟩ hT J.wr J.u J.v)
      fun _ ⟨K₆, U₆, pR₆⟩ => ⟨K₆, U₆, pR₆.rep, pR₆.x, pR₆.y, pR₆.z⟩)
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdsa.RISCV64.Secp256k1
