module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.SignAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.Exchange
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64.Ecdsa
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Order.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Order.Lit
meta import VerifiedGarbage.Impl.Weierstrass.Layout.Mont
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP512r1Order

/-!
# ECDSA signatures over brainpoolp512r1 on RISC-V: correctness

`vg_ecdsa_brainpoolp512r1_sign` meets its contract by register (`signRV`),
given the group law (`sign_rv`). The proof is the one of every curve, `SignAll.Kit.sign_ok`
(`Proof/Ecdsa/RISCV64/SignAll.lean`), from what `skit` says of this one: ECDH's kit, the functions
modulo `n` (`order_ok`) and the chain of `n - 2` (`chainN_ok`).
Here are also the statements about this curve that other modules use.
-/

@[expose] public section

-- `p`, below `2^512`, is evaluated.

set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.Ecdsa.RISCV64.Sign
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.BrainpoolP512r1
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)
open VG.WriteBytes (writeBytes)

/-- The functions of `n` meet the contracts by register. -/
private theorem n_ok : GenWide.WideOk Impl.Weierstrass.Mont.brainpoolp512r1n := ⟨by decide, by decide, by decide, by decide⟩

theorem order_ok : FieldOk brainpoolp512r1Order :=
  ⟨GenWide.mul_rv n_ok, GenWide.add_rv n_ok, GenWide.sub_rv n_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.addFn_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.subFn_noFrames,
    GenWide.mulA_rv n_ok, GenWide.addA_rv n_ok, GenWide.subA_rv n_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.addFnA_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.subFnA_noFrames⟩

instance : NeZero brainpoolp512r1Order.S.m := ⟨by decide⟩

instance : NeZero W.n := ⟨by decide⟩

theorem n_odd : W.n % 2 = 1 := by decide

/-- The chain is `n - 2`'s. -/
theorem chainN_ok : ChainOkR (Cfg.chainN brainpoolp512r1) (W.n - 2) := ChainOkR.of_check (by lit_decide)

/-- The signature of `digest` with the private key at `d` and the secret
number at `k`, as the specification computes it. -/
abbrev sg (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith W (ofBytes (bytesAt m d 64)) (hashToInt W (bytesAt m digest 64)) (ofBytes (bytesAt m k 64))

def signRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 128⟩
    let d : Region := ⟨s.gpr .a1, 64⟩
    let digest : Region := ⟨s.gpr .a2, 64⟩
    let k : Region := ⟨s.gpr .a3, 64⟩
    let scratch : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      digest.Disjoint scratch ∧ k.Disjoint scratch ∧ (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
    | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 128 = Spec.Ecdsa.encode W rs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 128 = List.replicate 128 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4

theorem nconsts_lt : ∀ e ∈ Cfg.nConsts brainpoolp512r1, e.2 < 2 ^ 512 := by decide

/-- `n` has 512 bits. -/
theorem nBits_eq : Spec.Ecdsa.nBits W = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  obtain h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  obtain h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- What the proofs shared by every curve (`SignAll.lean`) need of this one: ECDH's kit, and the
functions modulo `n`. -/
def skit : SignAll.Kit where
  toKit := VG.Proof.Ecdh.RISCV64.BrainpoolP512r1.kit
  FN := brainpoolp512r1Order
  order_ok := order_ok
  FNk := rfl
  FNm := rfl
  n_odd := n_odd
  pn := by decide
  nBits := nBits_eq
  chainN_ok := chainN_ok
  nconsts_lt := nconsts_lt

theorem sign_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : signRV.pre s) :
    ∃ t s', Exec isa signBrainpoolP512r1 s t s' ∧ abiPreserved s s' ∧ signRV.post s s' := by
  obtain ⟨hrd, hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk, hfs, hal⟩ := hs
  obtain ⟨t, s', he, h⟩ := skit.signTail_ok hL (s := s)
    ⟨by rw [hrd]; exact .head _, by rw [hrd]; exact .tail _ (.head _), by rw [hrd]; exact .tail _ (.tail _ (.head _)),
      hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk, hfs, hal⟩
  exact ⟨t, s', he, h⟩

/-! The constant-time analyses of the calls of the functions of brainpoolP512r1's `n` from their
arguments, each done once for every check of code that calls it (`taint_decide_sum`), which keep
what is public of `s0`–`s11`: the functions write none of them. -/

taint_summary nMulSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.brainpoolp512r1n.fn "mul") Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

taint_summary nAddSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.brainpoolp512r1n.fn "add") Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.addFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

taint_summary nSubSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.brainpoolp512r1n.fn "sub") Impl.Weierstrass.RISCV64.BrainpoolP512r1Order.subFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

end VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1
