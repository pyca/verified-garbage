module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.VerifyAll
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Sign
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.Exchange
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P192
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.JointJ
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify

/-!
# ECDSA verification over P-192 on RISC-V: correctness

`vg_ecdsa_p192_verify` meets its contract by register (`verifyRV`),
given the group law (`verify_rv`). The proof is the one of every curve, `VerifyAll.Kit.verify_ok`
(`Proof/Ecdsa/RISCV64/VerifyAll.lean`), from what `vkit` says of this one, with `[u]G + [v]Q`
by the joint ladder (`JointJ.jointJ_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P192

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.P192
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)

/-- Whether the signature at `sig` of `digest` verifies with the key at `pk`,
as the specification answers. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  Spec.Ecdsa.verify W (bytesAt m pk 49) (hashToInt W (bytesAt m digest 24)) (bytesAt m sig 48)

def verifyRV : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 49⟩
    let digest : Region := ⟨s.gpr .a1, 24⟩
    let sig : Region := ⟨s.gpr .a2, 48⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .a0).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 24 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' := s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

/-- What the proofs shared by every curve (`VerifyAll.lean`) need of this one: the signature's kit,
and that a number of the signature's bytes is below `2 n`. -/
def vkit : VerifyAll.Kit where
  toSKit := skit
  n2 := by decide

theorem verify_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : verifyRV.pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.P192.verifyP192 s t s' ∧ abiPreserved s s' ∧ verifyRV.post s s' := by
  obtain ⟨hrd, hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩ := hs
  obtain ⟨t, s', he, h⟩ := vkit.verify_ok hL (s := s) (T := fun _ => True)
    (JW := VG.Proof.Ecdsa.RISCV64.P192.JointJ.jointW) ⟨by decide, by decide, by decide, by decide⟩
    ⟨by rw [hrd]; exact .head _, by rw [hrd]; exact .tail _ (.head _), by rw [hrd]; exact .tail _ (.tail _ (.head _)),
      hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩
    (fun _ _ _ _ => trivial) (fun _ _ h => WP.mono h fun _ q => ⟨q, trivial⟩) (fun _ _ _ _ _ => trivial)
    (fun J _ => WP.mono (VG.Proof.Ecdsa.RISCV64.P192.JointJ.jointJ_ok hL
        ⟨J.ws, J.tc.ap, J.bp, J.tc.zero, J.tc.onep, J.gx, J.gy, J.qx, J.qy, J.q, J.on⟩)
      fun _ ⟨K₆, U₆, pR₆⟩ => ⟨K₆, U₆, pR₆.rep, pR₆.x, pR₆.y, pR₆.z⟩)
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdsa.RISCV64.P192
