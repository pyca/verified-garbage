import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Deterministic ECDSA on x86-64: the curve

What the proof needs of the curve (`RfcCurve`): the code of
`vg_ecdsa_<curve>_sign` for curves of `n` words (`Impl.Ecdsa.X86_64.Cfg`,
`4 ≤ n ≤ 6`), the instance of ECDSA it is, that the order `n` of its base
point has exactly `64 n` bits and `2^(64 n) < 2 n` (so that `bits2octets` is
one conditional subtraction), and what is proven of the code: that it meets
the contract the proof of each curve is written against (`coreK`: P-256's
`signX86_64` and P-384's at the curve's sizes), in constant time, and the
facts of every instruction the proof of the whole function needs. Each
curve's file builds one, so that the heavy algebra of its proof stays out
of the modules generic over the curve and the hash function.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- The signature with `k` of the arguments, on the curve `E`, as the
specification computes it. -/
abbrev coreSigOf (E : Impl.Ecdsa.X86_64.Cfg) (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith E.C (ofBytes (bytesAt m d (8 * E.n))) (hashToInt E.C (bytesAt m digest (8 * E.n)))
    (ofBytes (bytesAt m k (8 * E.n)))

/-- The contract of `vg_ecdsa_<curve>_sign` on the curve `E`, as each
curve's proof states it (`Proof.Ecdsa.X86_64.signX86_64` for P-256). -/
def coreK (E : Impl.Ecdsa.X86_64.Cfg) : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 16 * E.n⟩
    let d : Region := ⟨s.gpr .rsi, 8 * E.n⟩
    let digest : Region := ⟨s.gpr .rdx, 8 * E.n⟩
    let k : Region := ⟨s.gpr .rcx, 8 * E.n⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 16 * E.n ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match coreSigOf E s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) (16 * E.n) = encode E.C rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) (16 * E.n) =
        List.replicate (16 * E.n) 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

/-- A curve, for RFC 6979 on x86-64. -/
structure RfcCurve where
  /-- The curve, as the code of `vg_ecdsa_<curve>_sign` has it. -/
  E : Impl.Ecdsa.X86_64.Cfg
  /-- The instance of ECDSA. -/
  inst : Spec.Ecdsa.Instance
  curve : inst.curve = E.C
  /-- Scalars of 4 to 6 words. -/
  n4 : 4 ≤ E.n
  n6 : E.n ≤ 6
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
  /-- Its instructions: none writes `rsp` (or loads MXCSR), and it calls nothing. -/
  coreNs : coreC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  coreSp : coreC.allInstrs (fun i => !isa.writesSp i) = true
  coreMx : coreC.allInstrs (fun i => !loadsMxcsr i) = true
  coreD : coreC.depth = 0

end VG.Proof.Ecdsa.Rfc6979.X86_64
