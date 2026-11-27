module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.SignAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.Exchange
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P192
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.MulFn
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit

/-!
# ECDSA signatures over P-192 on RISC-V: correctness

`vg_ecdsa_p192_sign` meets its contract by register (`signRV`),
given the group law (`sign_rv`). The proof is the one of every curve, `SignAll.Kit.sign_ok`
(`Proof/Ecdsa/RISCV64/SignAll.lean`), from what `skit` says of this one: ECDH's kit, the functions
modulo `n` (`order_ok`) and the chain of `n - 2` (`chainN_ok`).
Here are also the statements about this curve that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P192

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.Ecdsa.RISCV64.Sign
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.P192
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)
open VG.WriteBytes (writeBytes)

/-- The functions of `n` meet the contracts by register. -/
theorem order_ok : FieldOk p192Order :=
  ⟨P192Field.mul_rv_n, P192Field.add_rv_n, P192Field.sub_rv_n,
    Impl.Ecdsa.RISCV64.p192MulN_noFrames,
    Impl.Ecdsa.RISCV64.p192AddN_noFrames, Impl.Ecdsa.RISCV64.p192SubN_noFrames,
    P192Field.mulA_rv_n, P192Field.addA_rv_n, P192Field.subA_rv_n,
    Impl.Ecdsa.RISCV64.p192MulNA_noFrames,
    Impl.Ecdsa.RISCV64.p192AddNA_noFrames, Impl.Ecdsa.RISCV64.p192SubNA_noFrames⟩

instance : NeZero p192Order.S.m := ⟨by decide⟩

instance : NeZero W.n := ⟨by decide⟩

theorem n_odd : W.n % 2 = 1 := by decide

/-- The chain is `n - 2`'s. -/
theorem chainN_ok : ChainOkR (Cfg.chainN p192) (W.n - 2) := ChainOkR.of_check (by lit_decide)

/-- The signature of `digest` with the private key at `d` and the secret
number at `k`, as the specification computes it. -/
abbrev sg (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith W (ofBytes (bytesAt m d 24)) (hashToInt W (bytesAt m digest 24)) (ofBytes (bytesAt m k 24))

def signRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 48⟩
    let d : Region := ⟨s.gpr .a1, 24⟩
    let digest : Region := ⟨s.gpr .a2, 24⟩
    let k : Region := ⟨s.gpr .a3, 24⟩
    let scratch : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      digest.Disjoint scratch ∧ k.Disjoint scratch ∧ (s.gpr .a0).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + 24 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 24 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 24 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
    | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 48 = Spec.Ecdsa.encode W rs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4

theorem nconsts_lt : ∀ e ∈ Cfg.nConsts p192, e.2 < 2 ^ 256 := by decide

/-- What the proofs shared by every curve (`SignAll.lean`) need of this one: ECDH's kit, and the
functions modulo `n`. -/
def skit : SignAll.Kit where
  toKit := VG.Proof.Ecdh.RISCV64.P192.kit
  FN := p192Order
  order_ok := order_ok
  FNk := rfl
  FNm := rfl
  n_odd := n_odd
  pn := by decide
  nBits := by decide
  chainN_ok := chainN_ok
  nconsts_lt := nconsts_lt

theorem sign_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : signRV.pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.P192.signP192 s t s' ∧ abiPreserved s s' ∧ signRV.post s s' := by
  obtain ⟨hrd, hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk, hfs, hal⟩ := hs
  obtain ⟨t, s', he, h⟩ := skit.signTail_ok hL (s := s)
    ⟨by rw [hrd]; exact .head _, by rw [hrd]; exact .tail _ (.head _), by rw [hrd]; exact .tail _ (.tail _ (.head _)),
      hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk, hfs, hal⟩
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdsa.RISCV64.P192
