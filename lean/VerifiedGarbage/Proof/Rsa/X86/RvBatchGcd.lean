module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.RvGcd
public import VerifiedGarbage.Impl.Rsa.X86.GcdDispatch
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Body
import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.FrameBase

/-! # Batched GCD inside the prime-recovery workspace -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)

 theorem batchGcdBody_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {m y : Nat}
    (h : KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s)
    (odd : m%2=1) :
    WP isa (VG.Impl.Rsa.X86.GcdBatch.body g.w) s fun t =>
      KS g s0 (AP m (Nat.gcd (sub32 g.w y 1) m)) [1,aN,aZero] (fun _ => 0) [] V [sMask] t := by
  have vn : val32 s.mem g.B (VG.Impl.Rsa.X86.GcdBatch.offset g.w 8) g.w=m := by
    rw [GcdBatch.offset_arr]
    exact h.arrs aM (by simp [liveG])
  have vu : val32 s.mem g.B (VG.Impl.Rsa.X86.GcdBatch.offset g.w 0) g.w=sub32 g.w y 1 := by
    rw [GcdBatch.offset_arr]
    exact h.arrs 0 (by simp [liveG])
  have hn : 16≤g.w := by have := h.lower; simp only [Geo.w,width]; omega
  have hz : VG.Impl.Rsa.X86.GcdBatch.offset g.w 15≤g.Z := by
    rw [GcdBatch.offset_arr]
    exact (arr_mono (by decide : 15≤nArr)).trans h.ws.fits
  refine WP.mono (GcdBatch.body_ok h.ws.workspace hn h.ws.wle hz (by rw [vn]; exact odd))
    fun t ⟨result,r,k⟩ => ?_
  rw [GcdBatch.offset_arr,vn,vu,Nat.gcd_comm m] at result
  refine h.core k ?_ (by decide) (r.mono (by decide)) ?_ (by decide) (by simp [Arrs])
    (by simp) (h.sl_keep k (by decide)) h.ls_ok
  · intro j hj
    exact h.ws.arr_fit ((by decide : ∀ j ∈ invArrs,j<nArr) j hj)
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact result
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl
      · rw [k.num (by decide) (by decide) (h.ws.fit64 (by decide)),h.arrs aN (by simp [liveG])]
        rfl
      · rw [k.num (by decide) (by decide) (h.ws.fit64 (by decide)),h.arrs aZero (by simp [liveG])]
        rfl

 omit rsaBatchLaw in
 theorem KS.batchWidth {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) :
    g.w=2*Spec.Rsa.modulusWords ((g.args 5).toNat+8) := by
  obtain ⟨a,ha,he,ca⟩ := h.rt.lenArg
  have ce := (h.arg (h.start.2 5 (by decide)).1 (by decide)).readSrc
  have eq : BitVec.ofNat 32 a=g.args 5 := Option.some.inj (ca.readSrc.symm.trans ce)
  have av : (g.args 5).toNat=a := by rw [←eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [av]
  rw [kw_nar] at he
  exact he.symm

 omit rsaBatchLaw in
 theorem batchChoice_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} (len : Nat)
    (h : KS g s0 A live AW liveW V ls s) :
    WP isa (.block (VG.Impl.Rsa.X86.GcdBatch.choice len)) s fun t =>
      KS g s0 A live AW liveW V ls t ∧
      t.zf=some (decide (g.args 5=BitVec.ofNat 32 len)) := by
  unfold VG.Impl.Rsa.X86.GcdBatch.choice
  refine wp_movS (h.arg (h.start.2 5 (by decide)).1 (by decide)).readSrc fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_cmpS rfl fun t T z => WP.block_nil ⟨hu.of_rest (T.keeps []) (by simp) T.mem,?_⟩
  rw [z,U.gpr]
  congr 1
  rw [Bool.eq_iff_iff,beq_iff_eq,decide_eq_true_iff,BitVec.sub_eq_iff_eq_add]
  change g.args 5=(0#32)+BitVec.ofNat 32 len ↔ _
  rw [BitVec.zero_add]

 theorem batchChoose_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {m y len words : Nat}
    {fallback : Prog isa}
    (h : KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s)
    (odd : m%2=1) (small : len<2^32)
    (width : 2*Spec.Rsa.modulusWords (len+8)=words)
    (other : ∀ u, KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] u →
      WP isa fallback u fun t =>
       KS g s0 (AP m (Nat.gcd (sub32 g.w y 1) m)) [1,aN,aZero] (fun _ => 0) [] V [sMask] t) :
    WP isa (VG.Impl.Rsa.X86.GcdBatch.choose len words fallback) s fun t =>
      KS g s0 (AP m (Nat.gcd (sub32 g.w y 1) m)) [1,aN,aZero] (fun _ => 0) [] V [sMask] t := by
  unfold VG.Impl.Rsa.X86.GcdBatch.choose
  refine WP.seq (WP.mono (batchChoice_ok len h) fun u ⟨hu,zu⟩ => ?_)
  refine WP.ite (decide (g.args 5=BitVec.ofNat 32 len)) (by exact zu) ?_ ?_
  · intro yes
    have e := of_decide_eq_true yes
    have w := hu.batchWidth
    rw [e,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,width] at w
    simpa only [←w] using batchGcdBody_ok hu odd
  · intro _
    exact other u hu

 theorem batchGcd_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {m y : Nat}
    (h : KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s)
    (odd : m%2=1) (hm : 1<m) :
    WP isa (VG.Impl.Rsa.X86.GcdBatch.dispatch
      (VG.Impl.Rsa.X86.KeyRt.gcd VG.Impl.Rsa.X86.RecoverRt.nar)) s fun t =>
      KS g s0 (AP m (Nat.gcd (sub32 g.w y 1) m)) [1,aN,aZero] (fun _ => 0) [] V [sMask] t := by
  unfold VG.Impl.Rsa.X86.GcdBatch.dispatch
  exact batchChoose_ok h odd (by decide) (by decide) fun _ hu =>
    batchChoose_ok hu odd (by decide) (by decide) fun _ hv =>
      batchChoose_ok hv odd (by decide) (by decide) fun _ hw => gcd_ok hw odd hm

end VG.Proof.Rsa.X86.Recover
