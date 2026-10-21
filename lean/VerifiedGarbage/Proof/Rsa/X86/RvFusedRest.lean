module

public import VerifiedGarbage.Proof.Rsa.X86.RvRest
import VerifiedGarbage.Proof.Rsa.X86.RvFusedSearch
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

/-! Complete fused recovery after the initial validity test. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (recoverPrimes)

 theorem fusedPrepare_ok {g : Geo} {s0 s : State} {A AW : Nat → Nat} {e : Nat}
    (h : KS g s0 A [aN] AW [wM] (fun _ => 0) [] s) (value : AW wM=e) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedPrepare s fun t =>
      KS g s0 A [aN] (fun _ => e) [wR] (fun _ => 0) [sTc,sCnt] t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedPrepare
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_W (o := wR) (a := wM) (by decide) (by decide)
    (by decide) (by decide)) fun u ⟨hu,_⟩ => ?_)
  refine wp_movS rfl fun v U _ => ?_
  have hv := hu.of_rest U.keeps (by decide) U.mem
  refine WP.block_append (WP.mono (hv.storeSlot (d := sTc) (by decide) .eax) fun u1 ⟨h1,_,K⟩ => ?_)
  rw [U.gpr,show (0 : BitVec 32).toNat=0 from rfl] at h1
  refine WP.mono (h1.storeSlot (d := sCnt) (by decide) .eax) fun t ⟨ht,_,_⟩ => ?_
  rw [K.1 _ (by decide),U.gpr,show (0 : BitVec 32).toNat=0 from rfl] at ht
  refine ht.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨by simp_all,?_⟩) (fun d hd => ⟨by simp_all [or_comm],?_⟩)
  · simp only [List.mem_singleton] at hj
    subst j
    rw [upd_self]
    exact value
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl <;> rfl

 theorem fusedRest_ok {g : CallGeometry} {s0 s : State} (inputs : Inputs g s0) (len : Lengths g)
    (h : KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
      (fun _ => 2*(product g s0.mem/2)) [wM] (fun _ => 0) [] s)
    (go : GoOn (product g s0.mem)) (bound : inputValue g s0.mem 0<2^(64*g.n))
    (odd : inputValue g s0.mem 0%2=1) (large : 101<inputValue g s0.mem 0) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedRest s (RestResult g s0) := by
  obtain ⟨ae,ad⟩ := inputArguments inputs
  obtain ⟨count,limit⟩ := inputs.countBounds
  obtain ⟨evenValue,positive,even,fit⟩ := exponent_facts go
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedRest
  simp only [seqs]
  refine WP.seq (WP.mono (fusedPrepare_ok h evenValue) fun u1 h1 => ?_)
  refine WP.seq (WP.mono (mont_ok h1 rfl bound odd (by omega)) fun u2 ⟨h2,mr⟩ => ?_)
  obtain ⟨I,tracked,inverse⟩ := h2.trackInverse mr (by decide)
  refine WP.seq (WP.mono (fusedLoop_ok
    (by simp [AM,upd,mBase,aNg,aO,mXm,mR2])
    (by simp [AM,upd,aN,aNg,aO,mXm,mR2,mBase,aOne,aZ])
    (by simp [AM,upd,aZ,aNg,aO,mXm,mR2,mBase,aOne]) bound
    (by simpa only [upd_self] using inverse) odd (by omega)
    (by simp [AM,upd,aO,aNg]) (by simp [AM,upd]) ae ad positive even fit count limit
    inputs.countWide tracked (by rfl)) fun u3 ⟨j,st,_,hs,zl,zpos,found⟩ => ?_)
  refine WP.mono (fin_ok inputs len hs
    (by simp [AM,upd,mBase,aNg,aO,mXm,mR2])
    (by simp [AM,upd,aN,aNg,aO,mXm,mR2,mBase,aOne,aZ]) bound
    (by simpa [VJ,upd,sInv,sCand,sCnt] using inverse) odd (by omega)
    (by simp [AM,upd,aZ,aNg,aO,mXm,mR2,mBase,aOne])
    (by simp [AM,upd,aOne,aNg,aO,mXm,mR2,mBase]) zl) fun t finished => ?_
  refine ⟨st.1,st.2.2,j+1,finished,zl,zpos,?_⟩
  rw [VG.Proof.Rsa.recoverPrimes_go go]
  simpa only [exponent,product,Spec.Rsa.recoverTries] using found

end VG.Proof.Rsa.X86.Recover
