module
public import VerifiedGarbage.Proof.Divstep.Alg32Def
/-! # The final sign and scale correction of a batched inverse -/
@[expose] public section
namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep
def corrected (p : Int) (st : W32.IState) (B : Nat) : Int :=
 ((if st.f<0 then -st.a else st.a)*2^(2*B))%p

end VG.Proof.Rsa.Divstep
