import VerifiedGarbage.Proof.Bignum.X86_64.Cmp

namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- The common comparison guarantee used by RSA setup proofs. -/
def CompareCorrect (cmp : Prog isa) : Prop :=
  ∀ {s : State} {B : Addr} {Z w eX eN : Nat}, Scr s B Z →
    s.gpr .rbx=off B eX → s.gpr .r10=off B eN →
    s.gpr .r12=BitVec.ofNat 64 w → s.gpr .rbp=mask false →
    1≤w → w<2^31 → eX+8*w≤Z → eN+8*w≤Z →
    WP isa cmp s fun t => t.gpr .rbp=mask (decide (wv s.mem B eX w < wv s.mem B eN w)) ∧
      t.mem=s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax,.rbp,.r14] s t
end VG.Proof.Bignum.X86_64
