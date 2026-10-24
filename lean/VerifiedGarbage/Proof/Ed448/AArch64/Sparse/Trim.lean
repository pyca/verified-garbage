module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TrimStep
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointLoop

/-! Leading zero pairs may be omitted: both remaining recoded scalars are zero above the chosen start. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off)

private theorem residual_zero {wide:Bool} {k i:Nat}
    (hr:residual wide k (i+1)=0) (hd:digitAt wide k i=0) : residual wide k i=0:=by
  have h:=WnafWide.residual_step wide k i
  rw [hr,hd] at h
  omega

theorem trim_ok {s:State} {base:Addr} (hs:Scr s base) {S K:Nat}
    (hS:S<VG.Impl.Ed448.WnafWide.scalarLimit) (hK:K<VG.Impl.Ed448.WnafWide.scalarLimit) (hc:s.gpr .x19=BitVec.ofNat 64 464)
    (hsd:∀ i<464,s.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i))
    (hkd:∀ i<464,s.mem (off base (BITS+i))=BitVec.ofInt 8 (digitAt false K i)) :
    WP isa (.loop (.block trimStep) (.zero .x .x9)) s fun t =>
      ∃ i<464,t.gpr .x19=BitVec.ofNat 64 i ∧ residual true S (i+1)=0 ∧ residual false K (i+1)=0 ∧
        Keeps trimClob s t ∧ t.mem=s.mem:=by
  have rS:residual true S 464=0:=WnafWide.residual_end true (k:=S) (by exact hS)
  have rK:residual false K 464=0:=WnafWide.residual_end false (k:=K) (by exact hK)
  let inv:=fun m (t:State) =>
    0<m ∧ m≤464 ∧ t.gpr .x19=BitVec.ofNat 64 m ∧
      residual true S m=0 ∧ residual false K m=0 ∧ Keeps trimClob s t ∧ t.mem=s.mem
  refine WP.loop (M:=isa) (body:=.block trimStep) (c:=.zero .x .x9)
    (Q:=fun t => ∃ i<464,t.gpr .x19=BitVec.ofNat 64 i ∧ residual true S (i+1)=0 ∧
      residual false K (i+1)=0 ∧ Keeps trimClob s t ∧ t.mem=s.mem)
    inv ?_ 464 s ⟨by decide,by decide,hc,rS,rK,Keeps.refl _ _,rfl⟩
  intro m u ⟨hm,hm',u19,rs,rk,ku,um⟩
  obtain ⟨i,rfl⟩:∃ i,m=i+1:=⟨m-1,by omega⟩
  have hi:i<464:=by omega
  refine WP.mono (trimStep_ok (ds:=digitAt true S i) (dk:=digitAt false K i) (hs.of_keeps ku (by decide)) hi u19
    (baseDigit_bound S i) (by have := keyDigit_bound K i;omega)
    (by rw [um];exact hsd i hi) (by rw [um];exact hkd i hi))
    fun t ⟨t19,tz,kt,tm⟩ => ?_
  simp only [eval,State.read,BitVec.setWidth_eq,tz]
  by_cases hz:digitAt true S i=0 ∧ digitAt false K i=0 ∧ i≠0
  · refine Or.inr ⟨?_,i,by omega,?_⟩
    · exact congrArg some (decide_eq_true hz)
    · exact ⟨by omega,by omega,t19,residual_zero rs hz.1,residual_zero rk hz.2.1,
        ku.trans kt,tm.trans um⟩
  · refine Or.inl ⟨?_,i,hi,t19,rs,rk,ku.trans kt,tm.trans um⟩
    exact congrArg some (decide_eq_false hz)

end VG.Proof.Ed448.AArch64.Sparse
