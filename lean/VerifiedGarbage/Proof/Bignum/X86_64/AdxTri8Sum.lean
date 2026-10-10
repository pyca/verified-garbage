import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Value
import VerifiedGarbage.Proof.Bignum.Triangular

/-! ## AdxTri8Store -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem headBases_ok {s : State} {B : Addr} {Z w I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (.block AdxTri8.headBases) s fun t =>
      t.gpr .rcx=off B (slot w aAcc+16*I) ∧ t.mem=s.mem ∧ Keep [.rsi,.rcx] s t := by
  have ld : ∀ k<32, InRegions (s.rd++s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  have sh : BitVec.ofNat 64 I <<< (4 : Nat)=BitVec.ofNat 64 (16*I) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 I*BitVec.ofNat 64 16=BitVec.ofNat 64 (16*I)
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  have add : BitVec.ofNat 64 (16*I)+off B (slot w aAcc)=off B (slot w aAcc+16*I) := by
    rw [BitVec.add_comm]; exact off_off ..
  refine WP.mono (WP.keep [.rsi,.rcx] (Q := fun t => t.gpr .rcx=off B (slot w aAcc+16*I) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨p,m⟩,k⟩ => ⟨p,m,k⟩
  unfold AdxTri8.headBases
  xrun [State.ea,hdr,hd,hdrOff,ld (sArr aAcc) (by decide),ld (sFn 12) (by decide),
    hh.harr aAcc (by decide),hI,sh,add]

theorem storeHead_ok {s : State} {B : Addr} {Z w I i : Nat} {lo hi : Reg}
    (hs : Scr s B Z) (hc : s.gpr .rcx=off B (slot w aAcc+16*I))
    (he : slot w aAcc+16*I+(16+8*(2*i+2))+8≤Z) :
    let e := slot w aAcc+16*I+(16+8*(2*i+1))
    WP isa (AdxTri8.storeHead i lo hi) s fun t =>
      wv t.mem B e 2=(s.gpr lo).toNat+2^64*(s.gpr hi).toNat ∧
      Outside B e 16 s.mem t.mem ∧ Keep [] s t := by
  dsimp only
  have nowrap := hs.nowrap
  unfold AdxTri8.storeHead
  refine WP.seq (WP.mono (AdxRotate8.storeAt_ok (p := .rcx) (r := lo) hs hc
    (by omega : slot w aAcc+16*I+(16+8*(2*i+1))+8≤Z)) fun b ⟨vb,ob,kb⟩ => ?_)
  refine WP.mono (AdxRotate8.storeAt_ok (p := .rcx) (r := hi) (hs.congr kb.2.2)
    ((kb.gpr (by simp)).trans hc) he) fun t ⟨vt,ot,kt⟩ => ?_
  have low : word t.mem B (slot w aAcc+16*I+(16+8*(2*i+1)))=s.gpr lo := by
    rw [ot.word (by omega) (by omega),vb]
  have high : word t.mem B (slot w aAcc+16*I+(16+8*(2*i+2)))=s.gpr hi :=
    vt.trans (kb.gpr (by simp))
  refine ⟨?_,(ob.mono (n' := 16) (by omega) (by omega)).trans (ot.mono (by omega) (by omega)),(kb.trans kt).mono (by simp)⟩
  rw [wv,wv,wv]
  simp only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.one_mul,Nat.zero_add,Nat.add_zero]
  rw [low,show slot w aAcc+16*I+(16+8*(2*i+1))+8=slot w aAcc+16*I+(16+8*(2*i+2)) by omega,high]

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Row -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

private theorem split_arith {A B R T V : Nat} (h : A+R*(B+R*T)=V) :
    (A+R*B)+(R*R)*T=V := by grind

theorem rowStep_ok {s : State} {B : Addr} {Z w I i e : Nat}
    {lo hi : Reg} {tail : List Reg}
    (hs : Scr s B Z) (hc : s.gpr .rcx=off B (slot w aAcc+16*I)) (hp : s.gpr .rbp=off B e)
    (he : e+8*(i+(lo::hi::tail).length)≤Z)
    (hout : slot w aAcc+16*I+(16+8*(2*i+2))+8≤Z)
    (hr : (lo::hi::tail).Nodup)
    (hrs : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx ∧ r≠.rdi)
    (hv : value s (lo::hi::tail)<2^(64*((lo::hi::tail).length-1))) :
    let out := slot w aAcc+16*I+(16+8*(2*i+1))
    WP isa (AdxTri8.rowStep i lo hi tail) s fun t =>
      wv t.mem B out 2+2^128*value t (tail++[lo])=
        value s (lo::hi::tail)+(word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) ((lo::hi::tail).length-1) ∧
      t.gpr lo=0 ∧ Outside B out 16 s.mem t.mem ∧ Keep (([.rdx,.rax,.rbx,.rsi] : List Reg)++lo::hi::tail) s t := by
  dsimp only
  unfold AdxTri8.rowStep
  have baseSafe : ∀ r ∈ lo::hi::tail, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx :=
    fun r h => let q := hrs r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩
  refine WP.seq (WP.mono (rowCore_ok (lo::hi::tail) hs hp he (by simp) hr baseSafe hv)
    fun a ⟨va,ka⟩ => ?_)
  have sl := hrs lo (by simp)
  have sh := hrs hi (by simp)
  have ca : a.gpr .rcx=off B (slot w aAcc+16*I) := (ka.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨sl.2.2.2.1.symm,sh.2.2.2.1.symm,
      fun h => (hrs .rcx (by simp [h])).2.2.2.1 rfl⟩⟩)).trans hc
  refine WP.seq (WP.mono (storeHead_ok (hs.congr ka.2.2.2) ca hout)
    fun b ⟨vb,ob,kb⟩ => ?_)
  refine WP.mono (movZero_ok b lo) fun t ⟨zt,_,_,kt⟩ => ?_
  have tailA : value b tail=value a tail := value_congr fun r h =>
    kb.gpr (by simp)
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

end

/-! ## AdxTri8Rotate -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

/-- All triangular accumulators stay in registers untouched by addressing. -/
def Regs (rs : List Reg) : Prop := rs.Nodup ∧
  ∀ r ∈ rs, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx ∧ r≠.rdi

theorem rotate_regs {lo hi : Reg} {tail : List Reg} (h : Regs (lo::hi::tail)) : Regs (tail++[lo]) := by
  refine ⟨?_,?_⟩
  · rw [List.nodup_append]
    refine ⟨h.1.tail.tail,by simp,?_⟩
    intro r hr q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    subst q
    intro eq
    subst r
    exact (List.nodup_cons.mp h.1).1 (by simp [hr])
  · intro r hr
    apply h.2 r
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    rcases hr with hr | rfl
    · exact Or.inr (Or.inr hr)
    · exact Or.inl rfl

theorem rotate_subset {lo hi : Reg} {tail : List Reg} :
    ∀ r ∈ tail++[lo], r∈lo::hi::tail := by
  intro r hr
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
  rcases hr with hr | rfl
  · exact Or.inr (Or.inr hr)
  · exact Or.inl rfl

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Sum -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def rowSum (m : Mem) (B : Addr) (e : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | i, n+1 => (word m B (e+8*i)).toNat*wv m B (e+8*(i+1)) (n+1)+2^128*rowSum m B e (i+1) n

theorem rowSum_congr {m m' : Mem} {B : Addr} {e i n : Nat}
    (h : ∀ j≤n, word m' B (e+8*(i+j))=word m B (e+8*(i+j))) : rowSum m' B e i n=rowSum m B e i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have w : wv m' B (e+8*(i+1)) (n+1)=wv m B (e+8*(i+1)) (n+1) := by
      apply wv_congr
      intro k hk
      rw [show e+8*(i+1)+8*k=e+8*(i+(k+1)) by omega]
      exact h (k+1) (by omega)
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [rowSum,rowSum,h0,w,ih (by
      intro j hj
      rw [show (i+1)+j=i+(j+1) by omega]
      exact h (j+1) (by omega))]

end VG.Proof.Bignum.X86_64.AdxTri8

end
