module

import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Sum
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Row0
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Value

/-! ## AdxTri8Rows -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def output (w I i : Nat) := slot w aAcc+16*I+(16+8*(2*i+1))

private theorem compose_arith {P R T V A S W : Nat}
    (h : P+R*T=V+A) (e : W=T+S) : P+R*W=V+(A+R*S) := by grind

theorem rows_ok (n : Nat) {s : State} {B : Addr} {Z w I i e : Nat} {rs : List Reg}
    (hs : Scr s B Z) (hc : s.gpr .rcx=off B (slot w aAcc+16*I)) (hp : s.gpr .rbp=off B e)
    (he : e+8*(i+n+1)≤Z) (hout : output w I i+16*n≤Z)
    (hsep : e+8*(i+n+1)≤output w I i ∨ output w I i+16*n≤e)
    (hr : Regs rs) (hlen : rs.length=n+1) (hv : value s rs<2^(64*n)) :
    WP isa (AdxTri8.rows n i rs) s fun t =>
      wv t.mem B (output w I i) (2*n)=value s rs+rowSum s.mem B e i n ∧
      Outside B (output w I i) (16*n) s.mem t.mem ∧
      Keep (([.rdx,.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  have nowrap := hs.nowrap
  induction n generalizing s i rs with
  | zero =>
    change WP isa (.block []) s _
    apply WP.block_nil
    have vz : value s rs=0 := by simpa only [Nat.mul_zero,Nat.pow_zero,Nat.lt_one_iff] using hv
    exact ⟨by simp only [wv,rowSum,vz,Nat.zero_add],Outside.refl _ _ _ _,Keep.refl _ _⟩
  | succ n ih =>
    cases rs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons lo rs =>
      cases rs with
      | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
      | cons hi tail =>
        have tl : tail.length=n := by simp only [List.length_cons] at hlen; omega
        change WP isa (.seq (AdxTri8.rowStep i lo hi tail) (AdxTri8.rows n (i+1) (tail++[lo]))) s _
        refine WP.seq (WP.mono (rowStep_ok hs hc hp (by rw [hlen]; omega)
          (by unfold output at hout; omega) hr.1 hr.2 (by rw [hlen]; simpa only [Nat.add_sub_cancel] using hv))
          fun a ⟨va,za,oa,ka⟩ => ?_)
        change Outside B (output w I i) 16 s.mem a.mem at oa
        have sa := hs.congr ka.2.2
        have ca : a.gpr .rcx=off B (slot w aAcc+16*I) := (ka.gpr (by
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨by decide,⟨(hr.2 lo (by simp)).2.2.2.1.symm,(hr.2 hi (by simp)).2.2.2.1.symm,
            fun h => (hr.2 .rcx (by simp [h])).2.2.2.1 rfl⟩⟩)).trans hc
        have pa : a.gpr .rbp=off B e := (ka.gpr (by
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨by decide,⟨(hr.2 lo (by simp)).1.2.1.symm,(hr.2 hi (by simp)).1.2.1.symm,
            fun h => (hr.2 .rbp (by simp [h])).1.2.1 rfl⟩⟩)).trans hp
        have av : value a (tail++[lo])<2^(64*n) := by
          have h := value_zero_top (rs := tail) za
          simpa only [List.length_append,List.length_cons,List.length_nil,tl,Nat.zero_add,Nat.add_sub_cancel] using h
        have outNext : output w I (i+1)=output w I i+16 := by unfold output; omega
        refine WP.mono (ih (i := i+1) sa ca pa (by omega)
          (by rw [outNext]; omega) (by rw [outNext]; omega) (rotate_regs hr)
          (by simp only [List.length_append,List.length_cons,List.length_nil,tl]) av)
          fun t ⟨vt,ot,kt⟩ => ?_
        have input : rowSum a.mem B e (i+1) n=rowSum s.mem B e (i+1) n :=
          rowSum_congr fun j hj => oa.word (by omega) (by omega)
        rw [input] at vt
        have pre : wv t.mem B (output w I i) 2=wv a.mem B (output w I i) 2 :=
          ot.wv (by rw [outNext]; omega) (by omega)
        have frames : Outside B (output w I i) (16*(n+1)) s.mem t.mem :=
          (oa.mono (by omega) (by omega)).trans (ot.mono (by rw [outNext]; omega) (by rw [outNext]; omega))
        refine ⟨?_,frames,(ka.trans kt).mono ?_⟩
        · rw [show 2*(n+1)=2+2*n by omega,wv_add,pre,
            show output w I i+8*2=output w I (i+1) by rw [outNext],rowSum]
          change wv a.mem B (output w I i) 2+2^128*wv t.mem B (output w I (i+1)) (2*n)=_
          simp only [hlen,Nat.add_sub_cancel] at va
          exact compose_arith va vt
        · intro r hm
          simp only [List.mem_append] at hm ⊢
          rcases hm with old | new
          · exact old
          · rcases new with base | rot
            · exact Or.inl base
            · exact Or.inr (rotate_subset r (List.mem_append.mpr rot))

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Clear -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem columns_regs : Regs AdxTri8.columns := by
  unfold Regs Safe AdxTri8.columns
  decide

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8Block -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem setup_ok {s : State} {B : Addr} {Z w a I : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (.block (AdxTri8.setup ca)) s fun t =>
      t.gpr .rbp=off B (slot w a+8*I) ∧ t.mem=s.mem ∧ Keep [.rax,.rbp] s t := by
  have ld : ∀ k<32, InRegions (s.rd++s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  have add : off B (slot w a)+BitVec.ofNat 64 (8*I)=off B (slot w a+8*I) := off_off ..
  refine WP.mono (WP.keep [.rax,.rbp] (Q := fun t => t.gpr .rbp=off B (slot w a+8*I) ∧ t.mem=s.mem) ?_ rfl)
    fun t ⟨⟨p,m⟩,k⟩ => ⟨p,m,k⟩
  unfold AdxTri8.setup
  xrun [State.ea,hdr,hd,hdrOff,ld (sArr ca) (by have := hv.lt pa; unfold sArr; omega),ld (sFn 12) (by decide),
    show word s.mem B (8*sArr ca) = _ from hv.at pa,hI,AdxRect8.shift3,add]

theorem zero_ends {m : Mem} {B : Addr} {e n : Nat}
    (lo : word m B e=0) (hi : word m B (e+8*(n+1))=0) :
    wv m B e (n+2)=2^64*wv m B (e+8) n := by
  rw [show n+2=1+(n+1) by omega,wv_add,wv_add]
  simp only [wv,lo,Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  rw [show e+8+8*n=e+8*(n+1) by omega,hi]
  simp only [show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero,Nat.zero_add]

/-- `clearEnds`: the first and last of the block's sixteen output words are
zeroed. -/
theorem clearEnds_ok {s : State} {B : Addr} {Z w I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) (he : slot w aAcc+16*I+144≤Z) :
    let e := slot w aAcc+16+16*I
    WP isa AdxTri8.clearEnds s fun t =>
      word t.mem B e=0 ∧ word t.mem B (e+120)=0 ∧
      (∀ d, 8≤d → d+8≤120 → word t.mem B (e+d)=word s.mem B (e+d)) ∧
      Outside B e 128 s.mem t.mem ∧ t.gpr .rcx=off B (slot w aAcc+16*I) ∧ Keep [.rsi,.rcx,.rax] s t := by
  dsimp only
  have nowrap := hs.nowrap
  unfold AdxTri8.clearEnds
  refine WP.seq (WP.mono (headBases_ok hs hd hh hZ hI) fun a₀ ⟨pa₀,ma₀,ka₀⟩ => ?_)
  rw [show ([Instr.mov32 .rax (.imm 0),.store (AdxRotate8.at_ .rcx 16) .rax] : List Instr)=
    [.mov32 .rax (.imm 0)]++[.store (AdxRotate8.at_ .rcx 16) .rax] from rfl]
  refine WP.seq (WP.block_append (WP.mono (movZero_ok a₀ .rax) fun a ⟨za,_,_,kz⟩ => ?_))
  have ka : Keep [.rsi,.rcx,.rax] s a := (ka₀.trans kz.keep).mono (by simp)
  have ma : a.mem=s.mem := kz.2.1.trans ma₀
  have pa : a.gpr .rcx=off B (slot w aAcc+16*I) := (kz.gpr (by decide)).trans pa₀
  refine WP.mono (AdxRotate8.storeAt_ok (p := .rcx) (r := .rax) (hs.congr ka.2.2) pa
    (by omega : slot w aAcc+16*I+16+8≤Z)) fun b ⟨vb,ob,kb⟩ => ?_
  refine WP.mono (AdxRotate8.storeAt_ok (p := .rcx) (r := .rax) (hs.congr (ka.trans kb).2.2)
    ((kb.gpr (by simp)).trans pa) (by omega : slot w aAcc+16*I+136+8≤Z)) fun t ⟨vt,ot,kt⟩ => ?_
  have r8a : a.gpr .rax=0 := za
  have r8b : b.gpr .rax=0 := (kb.gpr (by simp)).trans r8a
  rw [ma] at ob
  refine ⟨?_,?_,?_,(ob.mono (by omega) (by omega)).trans (ot.mono (by omega) (by omega)),
    (kt.gpr (by simp)).trans ((kb.gpr (by simp)).trans pa),((ka.trans kb).trans kt).mono (by simp)⟩
  · rw [show slot w aAcc+16+16*I=slot w aAcc+16*I+16 by omega,ot.word (by omega) (by omega),vb,r8a]
  · rw [show slot w aAcc+16+16*I+120=slot w aAcc+16*I+136 by omega,vt,r8b]
  · intro d h1 h2
    rw [ot.word (by omega) (by omega),ob.word (by omega) (by omega)]

theorem block_ok {s : State} {B : Addr} {Z w a I : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hIndex : I+8≤w)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) :
    WP isa (AdxTri8.block ca) s fun t =>
      wv t.mem B (slot w aAcc+16+16*I) 16=AdxSquare.crossValue s.mem B (slot w a+8*I) 8 ∧
      Outside B (slot w aAcc+16+16*I) 128 s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have ar := AdxRect8.tile_ranges hIndex hIndex ha ha1 ha2
  have outZ : output w I 0+112≤Z := by unfold output at *; omega
  have endZ : slot w aAcc+16*I+144≤Z := by omega
  unfold AdxTri8.block
  refine WP.seq (WP.mono (setup_ok hs hd hZ hv pa hI) fun u ⟨pu,mu,ku⟩ => ?_)
  refine WP.seq (WP.mono (clearEnds_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd) (mu ▸ hh) hZ
    (mu ▸ hI) endZ) fun x ⟨lx,hx,_,ox,cx,kx⟩ => ?_)
  rw [mu] at ox
  have kux := ku.trans kx
  have px : x.gpr .rbp=off B (slot w a+8*I) := (kx.gpr (by decide)).trans pu
  have regs := columns_regs
  refine WP.seq (WP.mono (rowStep0_ok (lo := .r8) (hi := .r9) (tail := [.r10,.r11,.r12,.r13,.r14,.r15])
    (hs.congr kux.2.2) cx px (by simp only [List.length_cons,List.length_nil]; omega)
    (by unfold output at outZ; omega) regs.1 regs.2) fun y ⟨vy,zy,oy,ky⟩ => ?_)
  change Outside B (output w I 0) 16 x.mem y.mem at oy
  have sy := hs.congr (kux.trans ky).2.2
  have cy : y.gpr .rcx=off B (slot w aAcc+16*I) := (ky.gpr (by decide)).trans cx
  have py : y.gpr .rbp=off B (slot w a+8*I) := (ky.gpr (by decide)).trans px
  have rot : AdxTri8.rotate AdxTri8.columns=[.r10,.r11,.r12,.r13,.r14,.r15]++[.r8] := rfl
  have vlt : value y ([.r10,.r11,.r12,.r13,.r14,.r15]++[.r8])<2^(64*6) := by
    have h := value_zero_top (rs := [.r10,.r11,.r12,.r13,.r14,.r15]) zy
    rwa [show ([Reg.r10,.r11,.r12,.r13,.r14,.r15]++[Reg.r8]).length-1=6 from rfl] at h
  have outNext : output w I 1=output w I 0+16 := by unfold output; omega
  refine WP.mono (rows_ok 6 (i := 1) sy cy py (by omega)
    (by rw [outNext]; unfold output at outZ ⊢; omega) (by unfold output; omega)
    (by rw [rot]; exact rotate_regs regs) (by rw [rot]; rfl) (by rw [rot]; exact vlt))
    fun t ⟨vt,ot,kt⟩ => ?_
  rw [rot] at vt
  have input : rowSum y.mem B (slot w a+8*I) 1 6=rowSum s.mem B (slot w a+8*I) 1 6 :=
    rowSum_congr fun j hj => by
      rw [oy.word (by unfold output; omega) (by omega),ox.word (by omega) (by omega)]
  have e0 : word x.mem B (slot w a+8*I+8*0)=word s.mem B (slot w a+8*I+8*0) := ox.word (by omega) (by omega)
  have e1 : wv x.mem B (slot w a+8*I+8*(0+1)) 7=wv s.mem B (slot w a+8*I+8*(0+1)) 7 :=
    ox.wv (by omega) (by omega)
  have vy' : wv y.mem B (output w I 0) 2+2^128*value y ([.r10,.r11,.r12,.r13,.r14,.r15]++[.r8])=
      (word s.mem B (slot w a+8*I+8*0)).toNat*wv s.mem B (slot w a+8*I+8*(0+1)) (6+1) := by
    rw [← e0, ← e1]; exact vy
  rw [input] at vt
  have pre : wv t.mem B (output w I 0) 2=wv y.mem B (output w I 0) 2 :=
    ot.wv (by rw [outNext]; omega) (by omega)
  have v14 : wv t.mem B (output w I 0) 14=rowSum s.mem B (slot w a+8*I) 0 7 := by
    rw [show 14=2+2*6 from rfl,wv_add,pre,show output w I 0+8*2=output w I 1 by rw [outNext],vt,
      show rowSum s.mem B (slot w a+8*I) 0 7=(word s.mem B (slot w a+8*I+8*0)).toNat*
        wv s.mem B (slot w a+8*I+8*(0+1)) (6+1)+2^128*rowSum s.mem B (slot w a+8*I) 1 6 from rfl,
      show 64*2=128 from rfl]
    omega_using [vy']
  have low : word t.mem B (slot w aAcc+16+16*I)=0 := by
    rw [ot.word (by unfold output; omega) (by omega),oy.word (by unfold output; omega) (by omega),lx]
  have high : word t.mem B (slot w aAcc+16+16*I+8*(14+1))=0 := by
    rw [ot.word (by unfold output; omega) (by omega),oy.word (by unfold output; omega) (by omega),hx]
  refine ⟨?_,ox.trans ((oy.mono (by unfold output; omega) (by unfold output; omega)).trans
    (ot.mono (by unfold output; omega) (by unfold output; omega))),
    ((kux.trans ky).trans kt).mono (by decide)⟩
  rw [show 16=14+2 from rfl,zero_ends low high,
    show slot w aAcc+16+16*I+8=output w I 0 by unfold output; omega,v14]
  exact rowSum_cross s.mem B _ 7

end VG.Proof.Bignum.X86_64.AdxTri8

end
