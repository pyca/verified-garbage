module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ProductState

/-! One public tooth index and the table prefix completed before constructing it. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum

structure BasisState (p : Parameters) (b : Nat) (s : State) : Prop where
 tooth : 1≤b ∧ b≤5
 bits : 0<p.N ∧ p.N≤8192
 basis : Basis p (2^((b-1)*Spec.Rsa.FixedBaseComb.rows p.N)) s
 space : ContextSpace p s
 context : word s.mem p.B (8*sCtx)=p.ctx
 index : word s.mem p.B (8*sD)=BitVec.ofNat 64 (2^b)
 rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)
 table : TablePrefix p (2^b) s

end VG.Proof.Ffdh.AArch64.Cached
