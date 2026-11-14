module

import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Scalars

/-! ### `Weierstrass.X86_64.JointGeneratorTable`, which only this module used -/

section

/-! A comb table's first row (`[m]G` for `m ≤ 2^(w-1)`) supplies the joint generator row directly. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def combGeneratorRow (n : Nat) {C : Curve} {w J H : Nat} {tbl : List (List (Nat×Nat))}
    {start : Nat×Nat} (hm : UnitMod C.p (2^(64*n))) (hC : Law C) (hT : CombOkW C w J tbl start)
    (hJ : 0<J) (hH : H<2^(w-1)) : JointGeneratorRow n C (G C) H where
  x a := (combAt tbl 0 (a-1)).1*2^(64*n)%C.p
  y a := (combAt tbl 0 (a-1)).2*2^(64*n)%C.p
  canonical _ _ _ _ := ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p)),
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))⟩
  point a ha hb _ := by
    rw [toM_mont hm,toM_mont hm]
    have hp := hT.entry 0 hJ (a-1) (by omega_using [hH, hb])
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.sub_add_cancel ha] at hp
    rw [hp]
    exact InvJ.affine hC _ _

theorem wordsVal_addr (mem : Mem) (base : Addr) (d o n : Nat) :
    wordsVal mem (off base d) o n=wordsVal mem base (d+o) n := by
  apply wordsVal_congr₂
  intro i _
  simp only [Mont.word,off,Offset.add_add,Nat.add_assoc]

theorem combGenerator_coordinates {n : Nat} {C : Curve} {w J a : Nat} {tbl : List (List (Nat×Nat))}
    {start : Nat×Nat}
    (hp : C.p<2^(64*n)) (hT : CombOkW C w J tbl start) (hJ : 0<J)
    {s : State} {T : Addr} (ht : TblMem s T (tcombWords n (2^(64*n)) C.p tbl))
    (ha : 1≤a) (hb : a<2^(w-1)+1) :
    wordsVal s.mem (off T (16*n*(a-1))) 0 n=(combAt tbl 0 (a-1)).1*2^(64*n)%C.p ∧
    wordsVal s.mem (off T (16*n*(a-1))) (8*n) n=(combAt tbl 0 (a-1)).2*2^(64*n)%C.p := by
  have he := tbl_entry (n:=n) (R:=2^(64*n)) (p:=C.p) (H:=2^(w-1)) (J:=J)
    ht hT.len hT.lenH (j:=0) (m:=a-1) hJ (by omega_using [ha, hb])
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))) hp)
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))) hp)
  rw [wordsVal_addr,wordsVal_addr,Nat.add_zero]
  simpa only [Nat.zero_mul,BitVec.add_zero] using he

theorem jointGenerator_of_table {c : Joint.Cfg} {C : Curve} {J size : Nat}
    {tbl : List (List (Nat×Nat))} {start : Nat×Nat}
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (hp : C.p<2^(64*c.K.M.n))
    {w H : Nat} (hT : CombOkW C w J tbl start) (hJ : 0<J) (hH : H<2^(w-1))
    {s : State} {T base : Addr} (ht : TblMem s T (tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl))
    (hout : ∀ i<(tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length,∀ b<8,
      size≤ofs base (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hsym : s.syms c.tsym=T) :
    JointGenerator c C base T size (combGeneratorRow c.K.M.n hm hC hT hJ hH) s := by
  have hlen : (tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length=J*(2^(w-1)*(2*c.K.M.n)) :=
    tcombWords_length (n:=c.K.M.n) (R:=2^(64*c.K.M.n)) (p:=C.p) hT.len hT.lenH
  have hlen' : 2^(w-1)*(2*c.K.M.n)≤(tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length := by
    rw [hlen]
    exact Nat.le_mul_of_pos_left _ hJ
  intro a ha hb _
  have coords := combGenerator_coordinates hp hT hJ ht ha (by omega_using [hH, hb])
  have hk : 16*c.K.M.n*(a-1)=16*(c.K.M.n*(a-1)) := Nat.mul_assoc ..
  have hka : c.K.M.n*(a-1)+c.K.M.n≤c.K.M.n*2^(w-1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega_using [hH, hb])
  have hl2 : 2^(w-1)*(2*c.K.M.n)=2*(c.K.M.n*2^(w-1)) := by
    rw [Nat.mul_comm (2^(w-1)),Nat.mul_assoc,Nat.mul_comm c.K.M.n]
  refine ⟨hsym,?_,?_,coords.1,coords.2⟩
  · intro i hi
    simp only [off,Offset.add_add]
    obtain ⟨r,hr,hreg⟩ := ht.rd
    exact ⟨r,hr,Region.contains_off hreg (by omega_using [hlen', hk, hka, hl2, hi])⟩
  · intro i hi b hb'
    have ho := hout (2*(c.K.M.n*(a-1))+2*i+b/8) (by omega_using [hlen', hka, hl2, hi, hb']) (b%8) (by omega_using [])
    simp only [off,Offset.add_add] at ho ⊢
    have he : 16*c.K.M.n*(a-1)+16*i+b=8*(2*(c.K.M.n*(a-1))+2*i+b/8)+b%8 := by omega_using [hk]
    rw [he]
    exact ho

end VG.Proof.Weierstrass.X86_64

end

end


/-! Reuse the verifier contract's existing width-seven comb table and certificate. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

/-- The joint loop's table of `[m]G`: `d`, one of the curve's tables of
constants, of `J` rows, whose first row holds `[m]G` for `m = 1 … 2^(d.w-1)`,
past the largest magnitude of the generator's digits: the comb's, or the
verifier's own (`Cfg.gtab`). -/
structure JointGTable (c : Cfg) (j : Joint.Cfg) (d : CombData) (J : Nat) : Prop where
  mem : (d.tsym,c.combWords d)∈c.combConsts
  ok : CombOkW c.C d.w J d.tbl d.start
  pos : 0<J
  top : jointGTop j<2^(d.w-1)
  sym : j.tsym=d.tsym

theorem JointGTable.ofComb {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hcd : c.comb=some d) (hT : CombOkW c.C d.w J d.tbl d.start) (hJ : 0<J)
    (ht : jointGTop j<2^(d.w-1)) (hs : j.tsym=d.tsym) : JointGTable c j d J :=
  ⟨comb_mem_consts hcd,hT,hJ,ht,hs⟩

theorem JointGTable.ofGTab {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hcd : c.gtab=some d) (hT : CombOkW c.C d.w J d.tbl d.start) (hJ : 0<J)
    (ht : jointGTop j<2^(d.w-1)) (hs : j.tsym=d.tsym) : JointGTable c j d J :=
  ⟨gtab_mem_consts hcd,hT,hJ,ht,hs⟩

def jointCombRow {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat} (hc : BaseCfgOk c) (hC : Law c.C)
    (hG : JointGTable c j d J) : JointGeneratorRow j.K.M.n c.C (G c.C) (jointGTop j) :=
  combGeneratorRow j.K.M.n (unitMod_pow_two hc.p_odd (64*j.K.M.n)) hC hG.ok hG.pos hG.top

theorem jointMid_generator {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hc : BaseCfgOk c) (hC : Law c.C) (hG : JointGTable c j d J)
    (hK : j.K=c.winCfg PX PY BP)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (h : Mid c s₀ (s₀.gpr .rcx) g s) :
    JointGenerator j c.C (s₀.gpr .rcx) (s₀.syms d.tsym) size
      (jointCombRow (j:=j) hc hC hG) s := by
  have hjn : j.K.M.n=c.n := by rw [hK]; rfl
  have table := tbl_of_held_mem hG.mem hp.tbls (by rw [hp.wr]; simp)
    (s:=s) (fun r hr => by rw [h.rd,hp.rd]; simp [hr]) h.unch
  have ws : c.combWords d=tcombWords j.K.M.n (2^(64*j.K.M.n)) c.C.p d.tbl := by
    simp only [Cfg.combWords,Cfg.R,hjn]
  have hpn : c.C.p<2^(64*j.K.M.n) := by rw [hjn]; exact hc.p_lt
  unfold jointCombRow
  apply jointGenerator_of_table (unitMod_pow_two hc.p_odd (64*j.K.M.n)) hC hpn
  · rw [←ws]
    exact table.1
  · rw [←ws]
    exact table.2
  · rw [hG.sym,h.syms]

end VG.Proof.Ecdsa.Verify.X86_64
