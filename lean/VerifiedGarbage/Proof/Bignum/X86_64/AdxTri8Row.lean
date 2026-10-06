import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Store
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Value

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

private theorem split_arith {A B R T V : Nat} (h : A+R*(B+R*T)=V) :
    (A+R*B)+(R*R)*T=V := by grind

theorem rowStep_ok {s : State} {B : Addr} {Z w I i e : Nat} {mi : BitVec 64}
    {lo hi : Reg} {tail : List Reg}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) (hp : s.gpr .rbp=off B e)
    (he : e+8*(i+(lo::hi::tail).length)≤Z)
    (hout : slot w aAcc+16*I+(16+8*(2*i+2))+8≤Z)
    (hr : (lo::hi::tail).Nodup)
    (hrs : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx ∧ r≠.rdi)
    (hv : value s (lo::hi::tail)<2^(64*((lo::hi::tail).length-1))) :
    let out := slot w aAcc+16*I+(16+8*(2*i+1))
    WP isa (AdxTri8.rowStep i lo hi tail) s fun t =>
      wv t.mem B out 2+2^128*value t (tail++[lo])=
        value s (lo::hi::tail)+(word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) ((lo::hi::tail).length-1) ∧
      t.gpr lo=0 ∧ Outside B out 16 s.mem t.mem ∧ Keep (([.rdx,.rcx,.rax,.rbx,.rsi] : List Reg)++lo::hi::tail) s t := by
  dsimp only
  unfold AdxTri8.rowStep
  have baseSafe : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx :=
    fun r h => let q := hrs r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩
  refine WP.seq (WP.mono (rowCore_ok (lo::hi::tail) hs hp he (by simp) hr baseSafe hv)
    fun a ⟨va,ka⟩ => ?_)
  have da : a.gpr .rdi=B := (ka.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hrs lo (by simp)).2.2.2.2.symm,(hrs hi (by simp)).2.2.2.2.symm,
      fun h => (hrs .rdi (by simp [h])).2.2.2.2 rfl⟩⟩)).trans hd
  have sl := hrs lo (by simp)
  have sh := hrs hi (by simp)
  refine WP.seq (WP.mono (storeHead_ok (hs.congr ka.2.2.2) da (ka.2.1 ▸ hh) hZ (ka.2.1 ▸ hI) hout
    ⟨sl.1.1,sl.1.2.2.2⟩ ⟨sh.1.1,sh.1.2.2.2⟩) fun b ⟨vb,ob,kb⟩ => ?_)
  refine WP.mono (movZero_ok b lo) fun t ⟨zt,_,_,kt⟩ => ?_
  have tailA : value b tail=value a tail := value_congr fun r h =>
    kb.gpr (by have q := hrs r (by simp [h]); simp [q.1.1,q.1.2.2.2])
  have tailT : value t tail=value b tail := value_congr fun r h =>
    kt.gpr (by
      have nd := (List.nodup_cons.mp hr).1
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      intro eq
      subst r
      exact nd (by simp [h]))
  have rot : value t (tail++[lo])=value a tail := by
    rw [value_append]
    simp only [value,zt,show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero]
    exact tailT.trans tailA
  have outT : wv t.mem B (slot w aAcc+16*I+(16+8*(2*i+1))) 2=
      (a.gpr lo).toNat+2^64*(a.gpr hi).toNat := by rw [kt.2.1]; exact vb
  rw [ka.2.1] at ob
  refine ⟨?_,zt,?_,((ka.keep.trans kb).trans kt.keep).mono (by simp; grind only)⟩
  · rw [outT,rot]
    simp only [value] at va
    have mul : (2 : Nat)^128=2^64*2^64 := by rw [← Nat.pow_add]
    rw [mul]
    exact split_arith va
  · rw [kt.2.1]; exact ob

end VG.Proof.Bignum.X86_64.AdxTri8
