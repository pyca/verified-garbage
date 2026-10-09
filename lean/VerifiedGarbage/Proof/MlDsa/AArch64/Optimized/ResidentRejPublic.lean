import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRows
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParsePublic

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)

def Pub (v : Nat) (s t : State) : Prop :=
  seedP s=seedP t ∧ aP s=aP t ∧ scr s=scr t ∧ s.sp=t.sp ∧
    bytesAt s.mem (seedP s) (34*v)=bytesAt t.mem (seedP t) (34*v)

theorem Pub.seed {v k : Nat} {σ τ : State} (h : Pub v σ τ) (hk : k<v) : B σ k=B τ k := by
  change Spec.MlDsa.seed4 σ.mem (seedP σ) k=Spec.MlDsa.seed4 τ.mem (seedP τ) k
  unfold Spec.MlDsa.seed4
  rw [← VG.Proof.MlKem.bytesAt_slice σ.mem (seedP σ) (show 34*k+34≤34*v by omega),
    ← VG.Proof.MlKem.bytesAt_slice τ.mem (seedP τ) (show 34*k+34≤34*v by omega),h.2.2.2.2]

theorem Pub.byte {v k : Nat} {σ τ : State} (h : Pub v σ τ) (hk : k<v) (i : Nat) : F σ k i=F τ k i := by
  unfold F
  exact congrArg (fun xs => (Spec.MlDsa.G xs 1008).getD i 0) (h.seed hk)

theorem Pub.prefix {v k : Nat} {σ τ : State} (h : Pub v σ τ) (hk : k<v) (n : Nat) :
    prefixRow σ k n=prefixRow τ k n := by
  have he : streamBytes σ k 0 n=streamBytes τ k 0 n := by
    unfold streamBytes
    apply List.map_congr_left
    intro i hi
    exact h.byte hk _
  exact congrArg (VG.Proof.MlDsa.Sample.rnFold []) he

theorem Pub.buf {v : Nat} {σ τ : State} (h : Pub v σ τ) (k : Nat) : bufP σ k=bufP τ k := by
  change scr σ+BitVec.ofNat 64 (840+1008*k)=scr τ+BitVec.ofNat 64 (840+1008*k)
  rw [h.2.2.1]

theorem Pub.poly {v : Nat} {σ τ : State} (h : Pub v σ τ) (k : Nat) : polyP σ k=polyP τ k := by
  unfold polyP
  rw [h.2.1]

theorem rows_input_eq {v blocks k off n : Nat} {σ τ s t : State}
    {L R : Nat → List VG.Spec.MlDsa.Zq} (hp : Pub v σ τ)
    (hs : Rows v blocks σ L s) (ht : Rows v blocks τ R t)
    (hk : k<v) (hn : off+3*n≤168*blocks) :
    InputEq s t (bufP σ k+BitVec.ofNat 64 off) n := by
  intro i hi
  rw [Offset.add_add,hs.bytes k hk _ (by omega),hp.buf k,ht.bytes k hk _ (by omega)]
  exact hp.byte hk _

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
