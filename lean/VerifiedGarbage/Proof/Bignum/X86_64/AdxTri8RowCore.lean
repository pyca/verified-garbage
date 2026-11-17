module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTri8
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! ### `Bignum.X86_64.AdxTri8Chain`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTri8Word`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem word_ok (s : State) {k : Nat} {hi prev col : Reg} {v : BitVec 64} {c o : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8*k)))=some v) (hc : s.cf=some c) (ho : s.of=some o)
    (h1 : hi≠.rsi) (h2 : col≠hi) (h3 : col≠.rsi)
    (h4 : prev≠hi) (h5 : prev≠.rsi) (h6 : prev≠col) :
    WP isa (.block (AdxTri8.word k hi prev col)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      (t.gpr col).toNat+2^64*((t.gpr hi).toNat+c'.toNat+o'.toNat)=
        (s.gpr col).toNat+(s.gpr .rdx).toNat*v.toNat+(s.gpr prev).toNat+c.toNat+o.toNat ∧
      Keeps [hi,.rsi,col] s t := by
  rw [show AdxTri8.word k hi prev col = [.mulx hi .rsi (.mem (at_ .rbp (8*k)))] ++
    AdxDualAdd.word col (.reg .rsi) (.reg prev) from rfl,WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea,ca,oa,ka⟩ => ?_
  refine WP.mono (AdxDualAdd.word_ok a (a := .reg .rsi) (b := .reg prev) (vb := a.gpr prev) rfl
    (fun u ku => by simp only [readSrc]; rw [ku.gpr (by simp [h6])])
    (fun _ h => nomatch h) (fun _ h => nomatch h) (ca.trans hc) (oa.trans ho))
    fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
  have colA : a.gpr col=s.gpr col := ka.gpr (by simp [h2,h3])
  have prevA : a.gpr prev=s.gpr prev := ka.gpr (by simp [h4,h5])
  have hiT : t.gpr hi=a.gpr hi := kt.gpr (by simp [Ne.symm h2])
  rw [colA,prevA] at eq
  refine ⟨ct,ot,hct,hot,?_,(ka.trans kt).mono (by simp)⟩
  rw [hiT]
  omega_using [ea, eq]

theorem close_ok (s : State) {hi col : Reg} {c o : Bool}
    (hc : s.cf=some c) (ho : s.of=some o) (hz : s.gpr col=0) (hne : hi≠col) :
    WP isa (.block (AdxTri8.close hi col)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      (t.gpr col).toNat+2^64*(c'.toNat+o'.toNat)=
        (s.gpr col).toNat+(s.gpr hi).toNat+c.toNat+o.toNat ∧ Keeps [col] s t := by
  change WP isa (.block (AdxDualAdd.word col (.reg col) (.reg hi))) s _
  refine WP.mono (AdxDualAdd.word_ok s (a := .reg col) (b := .reg hi) (vb := s.gpr hi) rfl
    (fun t kt => by simp only [readSrc]; rw [kt.gpr (by simp [hne])])
    (fun _ h => nomatch h) (fun _ h => nomatch h) hc ho) fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
  rw [hz] at eq ⊢
  simp only [show (0 : BitVec 64).toNat=0 from rfl,Nat.add_zero,Nat.zero_add] at eq ⊢
  exact ⟨ct,ot,hct,hot,eq,kt⟩

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

def value (s : State) : List Reg → Nat
  | [] => 0
  | r::rs => (s.gpr r).toNat+2^64*value s rs

def Safe (r : Reg) : Prop := r≠.rsi ∧ r≠.rbp ∧ r≠.rdx ∧ r≠.rcx

theorem value_congr {s t : State} {rs : List Reg} (h : ∀ r ∈ rs, t.gpr r=s.gpr r) : value t rs=value s rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [value,value,h r (by simp),ih (fun r hr => h r (by simp [hr]))]

private theorem append_arith {L L' R H C O X P D U U' Q F A Ci Oi : Nat}
    (word : L'+R*(H+C+O)=L+X*D+P+Ci+Oi)
    (tail : U'+Q*F=U+X*A+H+C+O) :
    L'+R*U'+(R*Q)*F=(L+R*U)+X*(D+R*A)+P+Ci+Oi := by grind

theorem chain_ok (rs : List Reg) {s : State} {B : Addr} {Z e k : Nat}
    {hi other prev : Reg} {c o : Bool}
    (hs : Scr s B Z) (hp : s.gpr .rbp=off B e) (htop : value s rs<2^(64*(rs.length-1)))
    (hZ : e+8*(k+(rs.length-1)) ≤ Z) (hn : rs≠[]) (hd : rs.Nodup)
    (hh : Safe hi) (ho' : Safe other) (hne : hi≠other) (hp1 : prev≠hi) (hp2 : prev≠.rsi)
    (hrs : ∀ r ∈ rs, Safe r ∧ r≠hi ∧ r≠other ∧ r≠prev)
    (hc : s.cf=some c) (ho : s.of=some o) :
    WP isa (.block (AdxTri8.chain k hi other prev rs)) s fun t => ∃ c' o' : Bool,
      t.cf=some c' ∧ t.of=some o' ∧
      value t rs+2^(64*rs.length)*(c'.toNat+o'.toNat)=
        value s rs+(s.gpr .rdx).toNat*wv s.mem B (e+8*k) (rs.length-1)+
          (s.gpr prev).toNat+c.toNat+o.toNat ∧ Keeps ([hi,other,.rsi]++rs) s t := by
  induction rs generalizing s k hi other prev c o with
  | nil => exact False.elim (hn rfl)
  | cons col rs ih =>
    cases rs with
    | nil =>
      have cp := (hrs col (by simp)).2.2.2
      have hz : s.gpr col=0 := by
        apply BitVec.eq_of_toNat_eq
        simp only [value,List.length_cons,List.length_nil,Nat.sub_self,Nat.mul_zero,Nat.pow_zero] at htop
        simp only [show (0 : BitVec 64).toNat=0 from rfl]; omega_using [htop]
      refine WP.mono (close_ok s hc ho hz (Ne.symm cp)) fun t ⟨ct,ot,hct,hot,eq,kt⟩ => ?_
      refine ⟨ct,ot,hct,hot,?_,kt.mono (by simp)⟩
      simpa only [value,List.length_cons,List.length_nil,Nat.mul_one,Nat.sub_self,wv,
        Nat.mul_zero,Nat.add_zero] using eq
    | cons next rest =>
      have cs := hrs col (by simp)
      have nd : col∉next::rest ∧ (next::rest).Nodup := List.nodup_cons.mp hd
      have hkZ : e+8*k+8 ≤ Z := by simp only [List.length_cons] at hZ; omega_using [hZ]
      have hm : readSrc s (.mem (at_ .rbp (8*k)))=some (word s.mem B (e+8*k)) :=
        readSrc_word hs (AdxRotate8.ea_at hp (8*k)) hkZ
      simp only [AdxTri8.chain]
      rw [WP.block_append_iff]
      refine WP.mono (word_ok s hm hc ho hh.1 cs.2.1 cs.1.1 hp1 hp2 cs.2.2.2.symm)
        fun a ⟨ca,oa,hca,hoa,eq,ka⟩ => ?_
      have pa : a.gpr .rbp=off B e := (ka.gpr (by simp [Ne.symm hh.2.1,Ne.symm cs.1.2.1])).trans hp
      have tailPres : value a (next::rest)=value s (next::rest) := value_congr (by
        intro r hr
        have h := hrs r (by simp [hr])
        exact ka.gpr (by simp [h.2.1,h.1.1,show r≠col by intro e; subst r; exact nd.1 hr]))
      have topA : value a (next::rest)<2^(64*((next::rest).length-1)) := by
        rw [tailPres]
        have e1 : value s (col::next::rest)=(s.gpr col).toNat+2^64*value s (next::rest) := rfl
        have e2 : 64*((col::next::rest).length-1)=64+64*((next::rest).length-1) := by
          simp only [List.length_cons]; omega_using []
        rw [e1,e2,Nat.pow_add] at htop
        exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) htop)
      refine WP.mono (ih (hs.congr ka.2.2.2) pa topA (by simp only [List.length_cons] at *; omega_using [hZ])
        (by simp) nd.2 ho' hh hne.symm hne hh.1 ?_ hca hoa) fun t ⟨ct,ot,hct,hot,et,kt⟩ => ?_
      · intro r hr
        have h := hrs r (by simp [hr])
        exact ⟨h.1,h.2.2.1,h.2.1,h.2.1⟩
      have caPres : a.gpr .rdx=s.gpr .rdx := ka.gpr (by simp [Ne.symm hh.2.2.1,Ne.symm cs.1.2.2.1])
      have colPres : t.gpr col=a.gpr col := kt.gpr (by simp [cs.2.1,cs.2.2.1,cs.1.1,nd.1])
      rw [caPres,ka.2.1,tailPres] at et
      refine ⟨ct,ot,hct,hot,?_,(ka.trans kt).mono (by
        intro r hr
        simp only [List.mem_append] at hr ⊢
        rcases hr with h | h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> simp
        · rcases h with h | h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl <;> simp
          · exact Or.inr (List.mem_cons_of_mem _ h))⟩
      rw [show value t (col::next::rest)=(t.gpr col).toNat+2^64*value t (next::rest) from rfl,
        show value s (col::next::rest)=(s.gpr col).toNat+2^64*value s (next::rest) from rfl,colPres,show 64*(col::next::rest).length=64+64*(next::rest).length by simp; omega_using [],Nat.pow_add]
      have split : wv s.mem B (e+8*k) ((col::next::rest).length-1)=
          (word s.mem B (e+8*k)).toNat+2^64*wv s.mem B (e+8*(k+1)) ((next::rest).length-1) := by
        rw [show (col::next::rest).length-1=1+((next::rest).length-1) by simp; omega_using [],wv_add]
        simp only [wv,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.pow_zero,Nat.one_mul,Nat.mul_one]
        rw [show e+8*k+8=e+8*(k+1) by omega_using []]
      rw [split]
      exact append_arith eq et

end VG.Proof.Bignum.X86_64.AdxTri8

end

end

/-! ### `Bignum.X86_64.AdxTri8Value`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64

private theorem digit_bound {R Q A V : Nat} (ha : A<R) (hv : V<Q) : A+R*V<R*Q := by
  have h : R*V ≤ R*(Q-1) := Nat.mul_le_mul_left R (by omega_using [hv])
  have e : R+R*(Q-1)=R*Q := by
    calc
      _ = R*1+R*(Q-1) := by rw [Nat.mul_one]
      _ = R*(1+(Q-1)) := (Nat.mul_add ..).symm
      _ = R*Q := by rw [show 1+(Q-1)=Q by omega_using [hv]]
  omega_using [ha, h, e]

theorem value_lt (s : State) (rs : List Reg) : value s rs<2^(64*rs.length) := by
  induction rs with
  | nil => simp only [value,List.length_nil,Nat.mul_zero,Nat.pow_zero]; decide
  | cons r rs ih =>
    rw [value,List.length_cons,show 64*(rs.length+1)=64+64*rs.length by omega_using [],Nat.pow_add]
    exact digit_bound (s.gpr r).isLt ih

theorem value_append (s : State) (rs tail : List Reg) :
    value s (rs++tail)=value s rs+2^(64*rs.length)*value s tail := by
  induction rs with
  | nil => simp only [List.nil_append,value,List.length_nil,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  | cons r rs ih =>
    simp only [List.cons_append,value,List.length_cons,ih]
    rw [show 64*(rs.length+1)=64+64*rs.length by omega_using [],Nat.pow_add]
    rw [Nat.mul_add,Nat.add_assoc,Nat.mul_assoc]

theorem value_zero_top {s : State} {rs : List Reg} {top : Reg} (hz : s.gpr top=0) :
    value s (rs++[top])<2^(64*((rs++[top]).length-1)) := by
  rw [value_append]
  simp only [value,hz,show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero,
    List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_sub_cancel]
  exact value_lt s rs

end VG.Proof.Bignum.X86_64.AdxTri8

end

end


/-! ## AdxTri8Closed -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

private theorem mac_bound {R Q X U V : Nat} (hx : X<R) (hu : U<Q) (hv : V<Q) : V+X*U<R*Q := by
  have h : X*U ≤ (R-1)*(Q-1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have e : (Q-1)+(R-1)*(Q-1)+R=R*Q := by
    calc
      _ = ((R-1)+1)*(Q-1)+R := by rw [Nat.add_mul,Nat.one_mul]; omega_arith
      _ = R*(Q-1)+R := by rw [Nat.sub_add_cancel (by omega_arith : 1≤R)]
      _ = R*((Q-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = R*Q := by rw [Nat.sub_add_cancel (by omega_arith : 1≤Q)]
  omega_arith

private theorem no_carry {L Q C V : Nat} (h : L+Q*C=V) (hb : V<Q) : L=V := by
  have hc : C=0 := by
    by_contra ne
    have : Q ≤ Q*C := Nat.le_mul_of_pos_right _ (by omega_arith)
    omega_arith
  simpa only [hc,Nat.mul_zero,Nat.add_zero] using h

theorem last_mem (col : Reg) (rest : List Reg) : AdxTri8.last col rest ∈ col::rest := by
  induction rest generalizing col with
  | nil => simp [AdxTri8.last]
  | cons r rs ih => exact List.mem_cons_of_mem _ (ih r)

theorem dropLast_last (col : Reg) (rest : List Reg) :
    (col::rest).dropLast++[AdxTri8.last col rest]=col::rest := by
  induction rest generalizing col with
  | nil => rfl
  | cons r rs ih => simp only [AdxTri8.last,List.dropLast_cons_cons,List.cons_append,ih]

theorem last_ne {col next : Reg} {rest : List Reg} (hd : (col::next::rest).Nodup) :
    AdxTri8.last col (next::rest)≠col := by
  intro h
  have m := last_mem next rest
  rw [show AdxTri8.last col (next::rest)=AdxTri8.last next rest from rfl] at h
  rw [h] at m
  exact (List.nodup_cons.mp hd).1 m

/-- The value of the columns once their top one is zero: that of the others. -/
theorem value_top_zero {s : State} {col : Reg} {rest : List Reg}
    (hz : s.gpr (AdxTri8.last col rest)=0) :
    value s (col::rest)=value s (col::rest).dropLast := by
  conv => lhs; rw [← dropLast_last col rest]
  rw [value_append]
  simp only [value,hz,show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero]

theorem xorZero_ok (s : State) (r : Reg) :
    WP isa (.block [.alu32 .xor r (.reg r)]) s fun t =>
      t.gpr r=0 ∧ t.cf=some false ∧ t.of=some false ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu32,readSrc32,Option.bind_some,
    State.setReg32,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,rfl,fun r' hr => ?_,rfl,rfl,rfl⟩
  · simp only [RegUpd.gpr_setReg_self,BitVec.xor_self]; rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr,RegUpd.gpr_arithFlags]

theorem xorRax_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun t =>
      t.gpr .rax=0 ∧ t.cf=some false ∧ t.of=some false ∧ Keeps [.rax] s t := xorZero_ok s .rax

theorem wordF_ok (s : State) {k : Nat} {hi col : Reg} {v : BitVec 64} {c : Bool}
    (hm : readSrc s (.mem (at_ .rbp (8*k)))=some v) (hc : s.cf=some c)
    (h1 : hi≠.rsi) (h2 : col≠hi) (h3 : col≠.rsi) :
    WP isa (.block (AdxTri8.wordF k hi col)) s fun t => ∃ c' : Bool,
      t.cf=some c' ∧ t.of=s.of ∧
      (t.gpr col).toNat+2^64*((t.gpr hi).toNat+c'.toNat)=
        (s.gpr col).toNat+(s.gpr .rdx).toNat*v.toNat+c.toNat ∧ Keeps [hi,.rsi,col] s t := by
  rw [show AdxTri8.wordF k hi col=[.mulx hi .rsi (.mem (at_ .rbp (8*k)))]++[.adcx col (.reg .rsi)] from rfl,
    WP.block_append_iff]
  refine WP.mono (mulx_ok s hm (fun _ h => nomatch h) h1) fun a ⟨ea,ca,oa,ka⟩ => ?_
  refine WP.mono (adcx_ok a (src := .reg .rsi) (v := a.gpr .rsi) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun t ⟨ct,hct,ot,eq,kt⟩ => ?_
  have colA : a.gpr col=s.gpr col := ka.gpr (by simp [h2,h3])
  have hiT : t.gpr hi=a.gpr hi := kt.gpr (by simp [Ne.symm h2])
  refine ⟨ct,hct,ot.trans oa,?_,(ka.trans kt).mono (by simp)⟩
  rw [hiT]
  rw [colA] at eq
  omega_arith

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8RowCore -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem last_not_mem_dropLast {col : Reg} {rest : List Reg} (hd : (col::rest).Nodup) :
    AdxTri8.last col rest ∉ (col::rest).dropLast := by
  intro m
  have h := hd
  rw [← dropLast_last col rest,List.nodup_append] at h
  exact h.2.2 _ m _ (by simp) rfl

private theorem row_arith {Ct Cb Hc c1 Vb X v1 W Tt P O : Nat}
    (first : Ct+2^64*(Hc+c1)=Cb+X*v1)
    (tail : Tt+P*O=Vb+X*W+Hc+c1) :
    Ct+2^64*Tt+(2^64*P)*O=Cb+2^64*Vb+X*(v1+2^64*W) := by grind

/-- A row over `col::rest` (two columns or more): its top column is zeroed
first, so the result is the value of the others plus the row's products. -/
theorem rowCore_ok (col : Reg) (rest : List Reg) {s : State} {B : Addr} {Z e i : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rbp=off B e)
    (hZ : e+8*(i+(col::rest).length) ≤ Z) (hn : rest≠[]) (hd : (col::rest).Nodup)
    (hrs : ∀ r ∈ col::rest, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx) :
    WP isa (.block (AdxTri8.rowCore i col rest)) s fun t =>
      value t (col::rest)=value s (col::rest).dropLast+
        (word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) rest.length ∧
      Keeps (([.rdx,.rax,.rbx,.rsi] : List Reg)++col::rest) s t := by
  cases rest with
  | nil => exact absurd rfl hn
  | cons next rest =>
  have nd := List.nodup_cons.mp hd
  have cs := hrs col (by simp)
  have zm := last_mem col (next::rest)
  have zs := hrs _ zm
  have zc : AdxTri8.last col (next::rest)≠col := last_ne hd
  have zl : AdxTri8.last col (next::rest)=AdxTri8.last next rest := rfl
  have len : (col::next::rest).length=rest.length+2 := by simp
  have hm := readSrc_word hs (AdxRotate8.ea_at hp (8*i)) (by omega_using [hZ, len])
  unfold AdxTri8.rowCore
  rw [WP.block_append_iff]
  rw [show ([.mov .rdx (.mem (at_ .rbp (8*i))),.alu32 .xor (AdxTri8.last col (next::rest))
      (.reg (AdxTri8.last col (next::rest)))] : List Instr)=
    [.mov .rdx (.mem (at_ .rbp (8*i)))] ++ [.alu32 .xor (AdxTri8.last col (next::rest))
      (.reg (AdxTri8.last col (next::rest)))] from rfl,WP.block_append_iff]
  refine WP.mono (movMem_ok s hm) fun a ⟨pa,_,_,ka⟩ => ?_
  refine WP.mono (xorZero_ok a _) fun b ⟨zb,cb,ob,kb⟩ => ?_
  have kab := ka.trans kb
  have vb : value b (col::next::rest)=value s (col::next::rest).dropLast := by
    rw [value_top_zero zb]
    apply value_congr
    intro r hr
    have hr' : r ∈ col::next::rest := by
      rw [← dropLast_last col (next::rest)]; exact List.mem_append_left _ hr
    have h := hrs r hr'
    refine kab.gpr ?_
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨h.1.2.2.1,?_⟩
    intro e; subst e
    exact last_not_mem_dropLast hd hr
  have xb : b.gpr .rdx=word s.mem B (e+8*i) :=
    (kb.gpr (by simp only [List.mem_cons,List.not_mem_nil,or_false]; exact zs.1.2.2.1.symm)).trans pa
  have sb := hs.congr kab.2.2.2
  have pb : b.gpr .rbp=off B e := (kab.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,zs.1.2.1.symm⟩)).trans hp
  have hm1 := readSrc_word sb (AdxRotate8.ea_at pb (8*(i+1))) (by omega_using [hZ, len])
  rw [WP.block_append_iff]
  refine WP.mono (wordF_ok b hm1 cb (by decide) cs.2.2.1 cs.1.1) fun c ⟨c1,cc,oc,eqF,kc⟩ => ?_
  have pc : c.gpr .rbp=off B e := (kc.gpr (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,by decide,cs.1.2.1.symm⟩)).trans pb
  have nrC : value c (next::rest)=value b (next::rest) := value_congr fun r hr => by
    have h := hrs r (by simp [hr])
    refine kc.gpr ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨h.2.2.1,h.1.1,fun e => by subst e; exact nd.1 hr⟩
  have zcz : c.gpr (AdxTri8.last next rest)=0 := by
    rw [← zl]
    refine (kc.gpr ?_).trans zb
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨zs.2.2.1,zs.1.1,zc⟩
  have topC : value c (next::rest)<2^(64*((next::rest).length-1)) := by
    have h := value_zero_top (s := c) (rs := (next::rest).dropLast) zcz
    rwa [dropLast_last next rest] at h
  refine WP.mono (chain_ok (next::rest) (hs.congr (kab.trans kc).2.2.2) pc topC
    (by simp only [List.length_cons] at hZ ⊢; omega_using [hZ]) (by simp) nd.2
    (by unfold Safe; decide) (by unfold Safe; decide) (by decide) (by decide) (by decide)
    (fun r h => let q := hrs r (by simp [h]); ⟨q.1,q.2.1,q.2.2.1,q.2.2.1⟩) cc
    (oc.trans ob)) fun t ⟨c',o',_,_,eqT,kt⟩ => ?_
  have xc : c.gpr .rdx=b.gpr .rdx := kc.gpr (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,by decide,cs.1.2.2.1.symm⟩)
  have colT : t.gpr col=c.gpr col := kt.gpr (r := col) (by
    intro h
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with (h|h|h)|h
    exacts [cs.2.1 h,cs.2.2.1 h,cs.1.1 h,nd.1 (List.mem_cons.mpr h)])
  have mc : c.mem=s.mem := kc.2.1.trans kab.2.1
  rw [xc,xb,mc,nrC] at eqT
  rw [xb,kab.2.1,show (false : Bool).toNat=0 from rfl,Nat.add_zero] at eqF
  rw [show (false : Bool).toNat=0 from rfl,Nat.add_zero] at eqT
  have dl : (col::next::rest).dropLast=col::(next::rest).dropLast := List.dropLast_cons_cons
  have colB : b.gpr col=s.gpr col := kab.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨cs.1.2.2.1,zc.symm⟩)
  have vb' : (b.gpr col).toNat+2^64*value b (next::rest)=value s (col::next::rest).dropLast := vb
  have l1 : (next::rest).length-1=rest.length := by simp
  have l2 : (next::rest).length=rest.length+1 := by simp
  rw [l1,l2] at eqT
  have split : wv s.mem B (e+8*(i+1)) (rest.length+1)=
      (word s.mem B (e+8*(i+1))).toNat+2^64*wv s.mem B (e+8*(i+2)) rest.length := by
    rw [Nat.add_comm rest.length 1,wv_add]
    simp only [wv,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.pow_zero,Nat.one_mul]
    rw [show e+8*(i+1)+8=e+8*(i+2) by omega_arith]
  have total := row_arith eqF eqT
  rw [← split,vb',← colT] at total
  have vt : value t (col::next::rest)=(t.gpr col).toNat+2^64*value t (next::rest) := rfl
  have eqV : value t (col::next::rest)+(2^64*2^(64*(rest.length+1)))*(c'.toNat+o'.toNat)=
      value s (col::next::rest).dropLast+(word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) (rest.length+1) := by
    rw [vt]; exact total
  have vl : value s (col::next::rest).dropLast<2^(64*(rest.length+1)) := by
    have h := value_lt s (col::next::rest).dropLast
    rwa [List.length_dropLast,show (col::next::rest).length-1=rest.length+1 by simp] at h
  have bound : value s (col::next::rest).dropLast+
      (word s.mem B (e+8*i)).toNat*wv s.mem B (e+8*(i+1)) (rest.length+1)<2^64*2^(64*(rest.length+1)) :=
    mac_bound (word s.mem B (e+8*i)).isLt (wv_lt s.mem B (e+8*(i+1)) (rest.length+1)) vl
  rw [l2]
  refine ⟨no_carry eqV bound,(kab.trans (kc.trans kt)).mono ?_⟩
  intro r hr
  have zm' := zm
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr zm' ⊢
  grind

end VG.Proof.Bignum.X86_64.AdxTri8

end
