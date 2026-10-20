module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Chain
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Value
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory

/-! ## AdxTri8Closed -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

private theorem mac_bound {R Q X U V : Nat} (hx : X<R) (hu : U<Q) (hv : V<Q) : V+X*U<R*Q := by
  have h : X*U ≤ (R-1)*(Q-1) := Nat.mul_le_mul (by omega) (by omega)
  have e : (Q-1)+(R-1)*(Q-1)+R=R*Q := by
    calc
      _ = ((R-1)+1)*(Q-1)+R := by rw [Nat.add_mul,Nat.one_mul]; omega
      _ = R*(Q-1)+R := by rw [Nat.sub_add_cancel (by omega : 1≤R)]
      _ = R*((Q-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = R*Q := by rw [Nat.sub_add_cancel (by omega : 1≤Q)]
  omega

private theorem no_carry {L Q C V : Nat} (h : L+Q*C=V) (hb : V<Q) : L=V := by
  have hc : C=0 := by
    by_contra ne
    have : Q ≤ Q*C := Nat.le_mul_of_pos_right _ (by omega)
    omega
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
  omega

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
    rw [show e+8*(i+1)+8=e+8*(i+2) by omega]
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
