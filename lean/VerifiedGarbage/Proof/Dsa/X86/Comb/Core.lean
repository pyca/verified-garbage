module

import VerifiedGarbage.Proof.Dsa.X86.Comb.Setup
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Proof.Mont.X86.CombBuild
public import VerifiedGarbage.Proof.Dsa.FixedBaseCombContract
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.X86.CombTableState

/-! ### `Mont.X86.CombCanonical`, which only this module used -/

section

/-! Arithmetic table invariants imply the exact shared RSA word representation. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.Proof.Mont VG.Impl.Mont.X86.Dynamic

theorem TableAt.canonical {n context m g bits : Nat} {base : Addr} {mem : Mem}
    (T : TableAt n context m g bits base (fun _ => True) mem) :
    Spec.Rsa.wordsAt mem (off base (context+16*n)) (32*n)=Spec.Rsa.FixedBaseComb.table m g bits n := by
  rw [wordsAt_blocks]
  unfold Spec.Rsa.FixedBaseComb.table
  simp only [Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rw [wordsAt_canonical]
  have V := T j (List.mem_range.mp hj) trivial
  change wordsVal mem base (context+16*n+8*n*j) n = _ at V
  rw [V]
  rfl

theorem context_canonical {L : Impl.Dsa.FixedBaseComb.Layout} {m g : Nat} {base : Addr} {mem : Mem}
    (P : wordsVal mem base L.context L.n=m)
    (R : wordsVal mem base (L.context+8*L.n) L.n=2^(128*L.n)%m)
    (T : TableAt L.n L.context m g (32*L.e) base (fun _ => True) mem) :
    Spec.Rsa.wordsAt mem (off base L.context) (Proof.Dsa.FixedBaseComb.contextWords L)=
      Proof.Dsa.FixedBaseComb.context L m g := by
  have size : Proof.Dsa.FixedBaseComb.contextWords L=L.n+(L.n+32*L.n) := by
    unfold Proof.Dsa.FixedBaseComb.contextWords Spec.Rsa.FixedBaseComb.entries Spec.Rsa.FixedBaseComb.teeth
    omega_using []
  rw [size,wordsAt_append,wordsAt_append,wordsAt_canonical,wordsAt_canonical,P,R]
  have addr : L.context+8*L.n+8*L.n=L.context+16*L.n := by omega_using []
  rw [addr,T.canonical]
  simp only [Proof.Dsa.FixedBaseComb.context,List.append_assoc]

theorem table_of_context {L : Impl.Dsa.FixedBaseComb.Layout} {m g : Nat} {base : Addr} {mem : Mem}
    (mp : 0<m) (mb : m<2^(64*L.n))
    (H : Spec.Rsa.wordsAt mem (off base L.context) (Proof.Dsa.FixedBaseComb.contextWords L)=
      Proof.Dsa.FixedBaseComb.context L m g) :
    TableAt L.n L.context m g (32*L.e) base (fun _ => True) mem := by
  have size : Proof.Dsa.FixedBaseComb.contextWords L=2*L.n+32*L.n := by
    unfold Proof.Dsa.FixedBaseComb.contextWords Spec.Rsa.FixedBaseComb.entries Spec.Rsa.FixedBaseComb.teeth
    omega_using []
  have lists := congrArg (List.drop (2*L.n)) H
  rw [size,wordsAt_append,List.drop_left' (by simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range])] at lists
  unfold Proof.Dsa.FixedBaseComb.context at lists
  rw [List.drop_left' (by simp only [List.length_append,Spec.Rsa.toWords,List.length_map,List.length_range]; omega_using [])] at lists
  have addr : L.context+8*(2*L.n)=L.context+16*L.n := by omega_using []
  rw [addr] at lists
  intro j hj _
  have jn : j*L.n+L.n≤32*L.n := by
    have := Nat.mul_le_mul_right L.n (show j+1≤32 by omega_using [hj])
    simpa only [Nat.add_mul,Nat.one_mul] using this
  have block := congrArg (fun l : List (BitVec 64) => (l.drop (j*L.n)).take L.n) lists
  rw [wordsAt_slice _ _ _ _ _ _ jn,VG.Proof.Rsa.FixedBaseComb.table_entry _ _ _ _ _ hj] at block
  have V := wordsAt_value block
  have entryAddr : L.context+16*L.n+8*(j*L.n)=entry L.n (L.context+16*L.n) j := by
    unfold entry; ac_rfl
  rw [entryAddr,Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ mp) mb)] at V
  exact V

end VG.Proof.Mont.X86.Comb

end

end

/-! ### `Dsa.X86.Comb.Power`, which only this module used -/

section

/-! Shared-table exponentiation, including padding and Montgomery decoding. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

theorem power_ok {n e m g : Nat} {base : Addr} {s : State}
    (h : Supported n e) (pub : Bool) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (one : wordsVal s.mem base (slot n 3) n=1) :
    WP isa (VG.Impl.Mont.X86.Comb.combPower n e (context n) pub) s fun t =>
      Context n m base (layout n e).size t ∧
      wordsVal t.mem base (slot n 6) n=g^val32 s.mem base (slot n 8) e%m ∧
      Outs base (powerRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold VG.Impl.Mont.X86.Comb.combPower VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (powerInit_ok h C T) fun u ⟨Cu,Tu,Au,Xu,ESI,Ou,Ku⟩ => ?_)
  refine WP.seq (WP.mono (powerLoop_ok h pub Cu Tu Au Xu (val32_lt _ _ _ _) ESI)
    fun v ⟨Cv,Tv,Av,Ov,Kv⟩ => ?_)
  have O := Ou.trans Ov
  have Onev : wordsVal v.mem base (slot n 3) n=1 := (power_preserves_one h O).trans one
  refine WP.seq (WP.mono (context_mul_ok Cv (o := 6) (a := 6) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Onev]; exact C.gt_one)) fun t ⟨Ct,Kt,lt,Vt⟩ => WP.block_nil ?_)
  refine ⟨Ct,?_,?_,(Ku.trans Kv).trans ((OpKeep.keeps Kt).mono (by decide))⟩
  · have decoded := VG.Proof.Dsa.mont_decode (A := wordsVal v.mem base (slot n 6) n)
      (out := wordsVal t.mem base (slot n 6) n) (a := Spec.Rsa.powMod g (val32 s.mem base (slot n 8) e) m) C.coprime
      (by rw [Av,Nat.mod_mod]) (by rw [Vt,Onev])
    rw [Nat.mod_eq_of_lt lt,VG.Proof.Bignum.powMod_eq,Nat.mod_mod] at decoded
    exact decoded
  · have ot : Outs base (powerRanges n e) v.mem t.mem := Kt.mem.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [powerRanges,contextMod,accLen,words] <;> omega_using [])
    exact O.trans ot

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.Comb.PrepareCore`, which only this module used -/

section

/-! Public preparation constructs a canonical table and returns the public power. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt buildRanges)

def prepareRanges (n e : Nat) : List (Nat × Nat) :=
  setupRanges n ++ buildRanges n (context n) ++ powerRanges n e

theorem prepare_core_ok {n e m : Nat} {base : Addr} {s : State}
    (h : Supported n e) (hs : Scr s base (layout n e).size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1) :
    WP isa (core true n e) s fun t =>
      wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      Spec.Rsa.wordsAt t.mem (off base (context n)) (Proof.Dsa.FixedBaseComb.contextWords (layout n e))=
        Proof.Dsa.FixedBaseComb.context (layout n e) m (wordsVal s.mem base (slot n 5) n) ∧
      Outs base (prepareRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  have L := table_layout h
  have shape : 128*n<2^32 ∧ contextBytes n≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold core
  simp only [ite_true]
  refine WP.seq (WP.seq (WP.mono (setup_ok hs L.positive shape.1 shape.2 hv hm odd)
    fun u ⟨Cu,Oneu,Ru,Ou,Ku⟩ => ?_))
  have Gu : wordsVal u.mem base (slot n 5) n=wordsVal s.mem base (slot n 5) n := by
    rw [wordsVal_eq_val32,wordsVal_eq_val32]
    exact Ou.val32 (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  have Eu : val32 u.mem base (slot n 8) e=val32 s.mem base (slot n 8) e := Ou.val32 (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  refine WP.mono (VG.Proof.Mont.X86.Comb.build_ok L Cu Oneu Ru (power_bounds h).1 (power_bounds h).2.1)
    fun v ⟨Cv,Pv,Rv,Tv,Ov,Kv⟩ => ?_
  rw [Gu] at Tv
  have Ev : val32 v.mem base (slot n 8) e=val32 s.mem base (slot n 8) e := (Ov.val32 (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)).trans Eu
  have Onev : wordsVal v.mem base (slot n 3) n=1 := by
    rw [wordsVal_eq_val32,Ov.val32 (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,Oneu]
  refine WP.mono (power_ok h true Cv Tv Onev) fun t ⟨_,Vt,Ot,Kt⟩ => ?_
  refine ⟨by rw [Vt,Ev],?_,?_,(Ku.trans Kv).trans Kt⟩
  · have Pt : wordsVal t.mem base (context n) n=m := by
      rw [wordsVal_eq_val32,Ot.val32 (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,Pv]
    have Rt : wordsVal t.mem base (context n+8*n) n=2^(128*n)%m := by
      rw [wordsVal_eq_val32,Ot.val32 (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,Rv]
    exact VG.Proof.Mont.X86.Comb.context_canonical (L := layout n e) Pt Rt (power_preserves_table h Cv.scr Tv Ot)
  · have a : Outs base (prepareRanges n e) s.mem u.mem := Ou.mono (by
      intro r hr; exact List.mem_append_left _ (List.mem_append_left _ hr))
    have b : Outs base (prepareRanges n e) u.mem v.mem := Ov.mono (by
      intro r hr; exact List.mem_append_left _ (List.mem_append_right _ hr))
    have c : Outs base (prepareRanges n e) v.mem t.mem := Ot.mono (fun _ hr => List.mem_append_right _ hr)
    exact (a.trans b).trans c

end VG.Proof.Dsa.X86.Comb

end

end

/-! Common functional boundary for the public and private comb helpers. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/PrivateCore.lean`, which only this module imported.
section

/-! Private powers reuse exactly the retained public context supplied by the caller. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

def privateRanges (n e : Nat) : List (Nat × Nat) := setupRanges n ++ powerRanges n e

theorem private_core_ok {n e m : Nat} {base : Addr} {s : State}
    (h : Supported n e) (hs : Scr s base (layout n e).size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (H : Spec.Rsa.wordsAt s.mem (off base (context n)) (Proof.Dsa.FixedBaseComb.contextWords (layout n e))=
      Proof.Dsa.FixedBaseComb.context (layout n e) m (wordsVal s.mem base (slot n 5) n)) :
    WP isa (core false n e) s fun t =>
      wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      Outs base (privateRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  have L := table_layout h
  have T : TableAt n (context n) m (wordsVal s.mem base (slot n 5) n) (32*e) base (fun _ => True) s.mem :=
    VG.Proof.Mont.X86.Comb.table_of_context (L := layout n e) (by omega_using [hm])
      (hv ▸ wordsVal_lt s.mem base (slot n 0) n) H
  have size : contextBytes n≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold core
  simp only [Bool.false_eq_true,ite_false]
  refine WP.seq (WP.mono (contextStart_ok hs L.positive size hv hm odd) fun u ⟨Cu,One,Ou,Ku⟩ => ?_)
  have Tu := T.outs L hs Ou (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  have Eu : val32 u.mem base (slot n 8) e=val32 s.mem base (slot n 8) e := Ou.val32 (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  refine WP.mono (power_ok h false Cu Tu One) fun t ⟨_,V,O,K⟩ => ⟨by rw [V,Eu],?_,Ku.trans K⟩
  exact (Ou.mono (fun _ hr => List.mem_append_left _ hr)).trans
    (O.mono (fun _ hr => List.mem_append_right _ hr))

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def coreRanges (prepare : Bool) (n e : Nat) : List (Nat × Nat) :=
  if prepare then prepareRanges n e else privateRanges n e

def canonical (n e m g : Nat) (base : Addr) (mem : Mem) : Prop :=
  Spec.Rsa.wordsAt mem (off base (context n)) (Proof.Dsa.FixedBaseComb.contextWords (layout n e))=
    Proof.Dsa.FixedBaseComb.context (layout n e) m g

theorem core_ok {n e m : Nat} {base : Addr} {s : State}
    (h : Supported n e) (prepare : Bool) (hs : Scr s base (layout n e).size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (H : prepare=false → canonical n e m (wordsVal s.mem base (slot n 5) n) base s.mem) :
    WP isa (core prepare n e) s fun t =>
      wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      (prepare=true → canonical n e m (wordsVal s.mem base (slot n 5) n) base t.mem) ∧
      Outs base (coreRanges prepare n e) s.mem t.mem ∧ Keeps powerClob s t := by
  cases prepare with
  | true => exact WP.mono (prepare_core_ok h hs hv hm odd) fun t ⟨V,C,O,K⟩ => ⟨V,fun _ => C,O,K⟩
  | false => exact WP.mono (private_core_ok h hs hv hm odd (H rfl)) fun t ⟨V,O,K⟩ => ⟨V,(fun eq => Bool.noConfusion eq),O,K⟩

end VG.Proof.Dsa.X86.Comb
