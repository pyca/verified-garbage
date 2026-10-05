import VerifiedGarbage.Impl.Ecdsa.Arm
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Layout

/-!
# Deterministic ECDSA on 32-bit ARM: the curve

What the proof needs of the curve (`RfcCurve`), as on x86
(`Proof/Ecdsa/Rfc6979/X86/Curve.lean`): the code of `vg_ecdsa_<curve>_sign`
for curves of `n` 64-bit words (`Impl.Ecdsa.Arm.Cfg`, `n` 4 or 6), the
instance of ECDSA it is, that the order `n` of its base point has exactly
`64 n` bits and `2^(64 n) < 2 n` (so that `bits2octets` is one conditional
subtraction), and what is proven of the code: that it meets the contract the
proof of each curve is written against (`coreK`: P-256's `signArm` and
P-384's at the curve's sizes), in constant time, that it uses no stack, and
the taint check of the block computing `bits2octets`, which holds `n`'s words
as immediates. Each curve's file builds one, so that the heavy algebra of
its proof stays out of the modules generic over the curve and the hash
function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- The taint analysis's start: the registers `rs` public, the flags not. -/
def τr (rs : List Reg) : VG.Arm.Taint.T := { regs := RegSet.ofList rs, flags := false }

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.Arm.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d (8 * E.n))) (hashToInt E.C (bytesAt m digest (8 * E.n)))
    (ofBytes (bytesAt m k (8 * E.n)))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, as each
curve's proof states it (`Proof.Ecdsa.Arm.signArm` for P-256). -/
def coreK (E : Impl.Ecdsa.Arm.Cfg) : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 16 * E.n⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 8 * E.n⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), 8 * E.n⟩
    let k : Region := ⟨State.addr (s.gpr .r3), 8 * E.n⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      (s.gpr .r0).toNat + 16 * E.n ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 * E.n ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8 * E.n ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8 * E.n ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    match coreSigOf E s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) (16 * E.n) = encode E.C rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) (16 * E.n) = List.replicate (16 * E.n) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The code's blocks that depend on neither the hash function nor the
functions it calls, for scalars of `E`. -/
def cfgC (E : Impl.Ecdsa.Arm.Cfg) : Impl.Ecdsa.Rfc6979.Arm.Cfg where
  F := ⟨⟨0, 0, 0, 0, 0, "", .block [], "", .block [], "", .block []⟩, 0, "", .block [], "", .block [], "",
    .block []⟩
  w := 2 * E.n
  n := E.C.n
  tries := 8
  coreN := ""
  coreC := .block []

/-- A curve, for RFC 6979 on 32-bit ARM. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.Arm.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Scalars of 4 or 6 64-bit words. -/
  n46 : E.n = 4 ∨ E.n = 6
  len : E.C.len = 8 * E.n
  /-- `n` has exactly `64 n` bits, and `2^(64 n) < 2 n`. -/
  nBits : nBits E.C = 64 * E.n
  n_lt : E.C.n < 2 ^ (64 * E.n)
  lt_2n : 2 ^ (64 * E.n) < 2 * E.C.n
  /-- `vg_ecdsa_<curve>_sign`, its name, and that it is correct and constant time. -/
  coreN : String
  coreC : Prog isa
  coreX : ∀ s, (coreK E).pre s → ∃ t s', Exec isa coreC s t s' ∧ abiPreserved s s' ∧ (coreK E).post s s'
  coreCT : ConstantTime isa (coreK E).pre (coreK E).pub coreC
  /-- It uses no stack. -/
  coreStack : VG.Arm.FrameStack.armStack coreC = 0
  /-- `bits2octets` and the initial `K` and `V` address memory only from
  the registers that hold the pointers (the taint analysis, of the block for
  `n`'s words). -/
  reduceT : ∃ hc, (VG.Taint.check taint (τr ptrRegs)
    (.block ((cfgC E).reduce ++ Impl.Ecdsa.Rfc6979.Arm.Cfg.initKV)) hc).isSome = true

theorem RfcCurve.n4 (R : RfcCurve) : 4 ≤ R.E.n := by rcases R.n46 with h | h <;> omega

theorem RfcCurve.n6 (R : RfcCurve) : R.E.n ≤ 6 := by rcases R.n46 with h | h <;> omega

end VG.Proof.Ecdsa.Rfc6979.Arm
