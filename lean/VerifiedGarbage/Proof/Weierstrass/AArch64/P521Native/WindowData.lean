module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowCompleteAdd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowGroup
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Framework.Mem

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field

 def windowCopyLookup : Prog isa := .seq (.block windowCopy) (.block windowLookupCode)

 theorem window_copy_novec : ∀i∈windowCopy,vdstOf i=none := by decide

 theorem window_copy_lookup_ok {s : State} {base table : Addr} {k j : Nat}
    (hs : Scr s base 8192) (hj : j<105) (bound : canonicalPoint s.mem base 1288)
    (ht : LookupTableReadable s table) (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (zero : wordsVal s.mem base 280 9=0) (canonical : WindowTableCanonical s.mem table)
    (counter : s.gpr .x19=BitVec.ofNat 64 j)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa windowCopyLookup s fun t =>
      canonicalPoint t.mem base 1072 ∧ ordinaryPoint t.mem base 1072=ordinaryPoint s.mem base 1288 ∧
      canonicalPoint t.mem base 1504 ∧ ordinaryPoint t.mem base 1504=windowAffine s.mem table k j ∧
      Scr t base 8192 ∧ KeepRegs (clob 9) s t ∧
      (∀x,(ofs base x<1072 ∨ 1288≤ofs base x) → (ofs base x<1504 ∨ 1720≤ofs base x) →
        (ofs base x<2224 ∨ 2296≤ofs base x) → t.mem x=s.mem x) ∧
      t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31 := by
  rw [windowCopyLookup,WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec window_copy_novec
    (window_copy_ok hs bound)) fun u ⟨⟨ca,pa,ku,fu⟩,vu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have htu : LookupTableReadable u table :=
    ⟨(ku.gpr _ (by decide)).trans ht.reg,by rw [ku.rd,ku.wr]; exact ht.read⟩
  have oa : Outside base 0 8192 s.mem u.mem := fu.outside (by
    intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl <;> decide)
  have tableFrame := oa.unch_far apart.symm
  have tableKept (d : Nat) (hd : d+72≤3456) : wordsVal u.mem table d 9=wordsVal s.mem table d 9 :=
    tableFrame.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl hd) (by omega_arith)
  have ctu : WindowTableCanonical u.mem table := by
    intro d h1 hd
    rw [tableKept _ (by unfold lookupEntryOffset; omega_arith),tableKept _ (by unfold lookupEntryOffset; omega_arith)]
    exact canonical d h1 hd
  have zeroU : wordsVal u.mem base 280 9=0 := by
    rw [fu.wordsVal (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl <;> decide) (by decide),zero]
  have cu : u.gpr .x19=BitVec.ofNat 64 j := (ku.gpr _ (by decide)).trans counter
  have bu : ∀t<525,u.mem (off base (3304+t))=if k.testBit t then 1 else 0 := by
    intro t ht
    rw [fu.byte (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl <;> simp only <;> omega_arith) (by omega_arith),bits t ht]
  refine WP.mono (window_lookup_point_ok hu (by decide) hj htu zeroU ctu cu bu)
    fun t ⟨ce,pe,ht,pt,kt,ft,v29⟩ => ?_
  have same (d : Nat) (hd : d+72≤1504) : wordsVal t.mem base d 9=wordsVal u.mem base d 9 :=
    WindowLookupFrame.wordsVal ft (Or.inl hd) (by left; omega_arith) (by omega_arith)
  have sx := same 1072 (by decide)
  have sy := same 1144 (by decide)
  have sz := same 1216 (by decide)
  have affineSame : windowAffine u.mem table k j=windowAffine s.mem table k j := by
    unfold windowAffine windowX windowY
    have hd : magH 16 (combWin 5 k j)≤16 := magH_le (combWin_lt 5 k j)
    by_cases h0 : magH 16 (combWin 5 k j)=0
    · simp only [h0,ite_true]
    · simp only [h0,ite_false]
      rw [tableKept _ (by unfold lookupEntryOffset; omega_arith),tableKept _ (by unfold lookupEntryOffset; omega_arith)]
  refine ⟨?_,?_,ce,pe.trans affineSame,ht,(ku.mono (by decide)).trans kt,?_,?_,?_⟩
  · change wordsVal t.mem base 1072 9<_ ∧ wordsVal t.mem base 1144 9<_ ∧ wordsVal t.mem base 1216 9<_
    rw [sx,sy,sz]; exact ca
  · rw [←pa]
    simp only [ordinaryPoint,Nat.reduceAdd,sx,sy,sz]
  · intro x hc hl hn
    exact (ft x hl hn).trans (fu x (by
      intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl <;> simp only <;> omega_arith))
  · rw [v29,vu]
  · have vt : t.v .v31=u.v .v31 := by
      have pp := (show FieldPublic u t from ‹FieldPublic u t›)
      exact pp.v31
    rw [vt,vu]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

 theorem fin_point_zero {p z : Nat} [NeZero p] (hz : z<p) :
    Fin.ofNat p z=(0 : Fin p) ↔ z=0 := by
  rw [Fin.ext_iff,Fin.val_ofNat]
  simp only [Fin.val_zero,Nat.mod_eq_of_lt hz]

 theorem window_select_coordinate_transfer {C : Curve} {p : Nat} [NeZero p]
    (hp : C.p=p) (law : Law C) (ha : AM3 C)
    {X Y Z x y z OX OY OZ : Nat} {Q S : Point C}
    (az : Z<p) (ez : z<p)
    (value : (Fin.ofNat p OX,Fin.ofNat p OY,Fin.ofNat p OZ)=
      (if Z=0 then (Fin.ofNat p x,Fin.ofNat p y,Fin.ofNat p z)
      else if z=0 then (Fin.ofNat p X,Fin.ofNat p Y,Fin.ofNat p Z)
      else maddJF (Fin.ofNat p X) (Fin.ofNat p Y) (Fin.ofNat p Z) (Fin.ofNat p x) (Fin.ofNat p y)))
    (hQ : onCurve C Q=true) (hS : onCurve C S=true)
    (ia : InvJ C (Fin.ofNat C.p X) (Fin.ofNat C.p Y) (Fin.ofNat C.p Z) Q)
    (ie : InvJ C (Fin.ofNat C.p x) (Fin.ofNat C.p y) (Fin.ofNat C.p z) S)
    (zn : (Fin.ofNat C.p z : Fe C)=0 ∨ (Fin.ofNat C.p z : Fe C)=1)
    (separate : Q≠.infinity → S≠.infinity → Q≠S) :
    InvJ C (Fin.ofNat C.p OX) (Fin.ofNat C.p OY) (Fin.ofNat C.p OZ) (Spec.Weierstrass.add Q S) := by
  rcases C with ⟨q,a,b,gx,gy,n,len,qnz,nnz⟩
  dsimp only at hp
  subst q
  have v : (Fin.ofNat p OX,Fin.ofNat p OY,Fin.ofNat p OZ)=windowSelectF
      (Fin.ofNat p X,Fin.ofNat p Y,Fin.ofNat p Z) (Fin.ofNat p x,Fin.ofNat p y,Fin.ofNat p z) := by
    simpa only [windowSelectF,fin_point_zero az,fin_point_zero ez] using value
  have result := window_select_group law ha
    (A:=(Fin.ofNat p X,Fin.ofNat p Y,Fin.ofNat p Z))
    (E:=(Fin.ofNat p x,Fin.ofNat p y,Fin.ofNat p z)) hQ hS ia ie zn separate
  rw [←v] at result
  exact result

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field

 theorem window_add_value_select {m : Mem} {base : Addr}
    (ca : canonicalPoint m base 1072) (ce : canonicalPoint m base 1504) :
    windowAddValue m base=windowSelectF (ordinaryPoint m base 1072) (ordinaryPoint m base 1504) := by
  simp only [windowAddValue,windowSelectF,ordinaryPoint,Nat.reduceAdd,
    fin_point_zero ca.2.2,fin_point_zero ce.2.2]

 theorem window_complete_add_point_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (ca : canonicalPoint s.mem (s.gpr .x0) 1072) (ce : canonicalPoint s.mem (s.gpr .x0) 1504) :
    WP isa windowCompleteAdd s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧ ordinaryPoint t.mem (s.gpr .x0) 1072=
        windowSelectF (ordinaryPoint s.mem (s.gpr .x0) 1072) (ordinaryPoint s.mem (s.gpr .x0) 1504) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowStable s t ∧ t.gpr .x4=s.gpr .x19-1#64 := by
  refine WP.mono (window_complete_add_ok hs room ca ce) fun t ⟨b,p,f,k,c⟩ => ?_
  rw [window_add_value_select ca ce] at p
  exact ⟨b,p,f,k,c⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field

 def windowAddPhase : Prog isa := .seq windowCopyLookup windowCompleteAdd

 def WindowPhaseFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1072 ∨ 1720≤ofs base x) → (ofs base x<2224 ∨ 2296≤ofs base x) →
    (ofs base x<4080 ∨ 4584≤ofs base x) → m' x=m x

 structure WindowPublic (s t : State) : Prop where
  base : t.gpr .x0=s.gpr .x0
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  gp : ∀r∈fieldPublicRegs,r≠.x30 → t.gpr r=s.gpr r
  v29 : t.v .v29=s.v .v29
  v31 : t.v .v31=s.v .v31

 theorem window_add_phase_ok {s : State} {base table : Addr} {k j : Nat}
    (hs : Scr s base 8192) (hj : j<105) (bound : canonicalPoint s.mem base 1288)
    (ht : LookupTableReadable s table) (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (zero : wordsVal s.mem base 280 9=0) (canonical : WindowTableCanonical s.mem table)
    (counter : s.gpr .x19=BitVec.ofNat 64 j)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa windowAddPhase s fun t =>
      canonicalPoint t.mem base 1072 ∧ ordinaryPoint t.mem base 1072=
        windowSelectF (ordinaryPoint s.mem base 1288) (windowAffine s.mem table k j) ∧
      Scr t base 8192 ∧ WindowPhaseFrame base s.mem t.mem ∧ WindowPublic s t ∧
      t.gpr .x4=s.gpr .x19-1#64 := by
  rw [windowAddPhase,WP.seq_iff]
  refine WP.mono (window_copy_lookup_ok hs hj bound ht apart zero canonical counter bits)
    fun u ⟨ca,pa,ce,pe,hu,ku,fu,vu29,vu31⟩ => ?_
  have u0 := hu.x0
  have hsu : Scr u (u.gpr .x0) 8192 := by rw [u0]; exact hu
  have au : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [u0]; exact ca
  have eu : canonicalPoint u.mem (u.gpr .x0) 1504 := by rw [u0]; exact ce
  refine WP.mono (window_complete_add_point_ok hsu (by decide) au eu)
    fun t ⟨bt,pt,ft,kt,c4⟩ => ?_
  rw [u0] at bt pt ft
  rw [pa,pe] at pt
  have t0 : t.gpr .x0=s.gpr .x0 := kt.base.trans (ku.gpr _ (by decide))
  have gp : ∀r∈fieldPublicRegs,r≠.x30 → t.gpr r=s.gpr r := by
    intro r hr hn
    have pres : r∈preserved := (by decide : ∀r∈fieldPublicRegs,r∈preserved) r hr
    have fresh : r∉clob 9 := (by decide : ∀r∈fieldPublicRegs,r∉clob 9) r hr
    exact (kt.gp r pres hn).trans (ku.gpr r fresh)
  refine ⟨bt,pt,?_,?_,⟨t0,kt.rd.trans ku.rd,kt.wr.trans ku.wr,kt.sp.trans ku.sp,gp,
    kt.v29.trans vu29,kt.v31.trans vu31⟩,?_⟩
  · have ht := kt.scr hsu
    rw [kt.base,u0] at ht
    exact ht
  · intro x hx hn hf
    exact (ft x (by omega_arith) hf).trans (fu x (by omega_arith) (by omega_arith) hn)
  · rw [ku.gpr .x19 (by decide)] at c4
    exact c4

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 structure WindowData (base table : Addr) (k : Nat) (s : State) : Prop where
  scr : Scr s base 8192
  readable : LookupTableReadable s table
  canonical : WindowTableCanonical s.mem table
  zero : VG.Proof.Mont.wordsVal s.mem base 280 9=0
  bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0

 theorem WindowPhaseFrame.word {base : Addr} {m m' : Mem} (frame : WindowPhaseFrame base m m') {d : Nat}
    (ha : d+8≤1072 ∨ 1720≤d) (hb : d+8≤2224 ∨ 2296≤d) (hc : d+8≤4080 ∨ 4584≤d)
    (hd : d+8≤2^64) : VG.Proof.Mont.word m' base d=VG.Proof.Mont.word m base d := by
  exact (Mem.readW_congr fun i hi =>
    (frame _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
      (by rw [ofs_off base (by omega_arith)]; omega_arith)
      (by rw [ofs_off base (by omega_arith)]; omega_arith)).symm).symm

 theorem WindowPhaseFrame.wordsVal {base : Addr} {m m' : Mem} (frame : WindowPhaseFrame base m m') {d k : Nat}
    (ha : d+8*k≤1072 ∨ 1720≤d) (hb : d+8*k≤2224 ∨ 2296≤d) (hc : d+8*k≤4080 ∨ 4584≤d)
    (hd : d+8*k≤2^64) : VG.Proof.Mont.wordsVal m' base d k=VG.Proof.Mont.wordsVal m base d k := by
  apply wordsVal_of_words₂
  intro j hj
  exact WindowPhaseFrame.word frame (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

 theorem WindowPhaseFrame.table {base table : Addr} {m m' : Mem} (frame : WindowPhaseFrame base m m')
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩) (d : Nat) (hd : d+72≤3456) :
    VG.Proof.Mont.wordsVal m' table d 9=VG.Proof.Mont.wordsVal m table d 9 := by
  have outside : Outside base 0 8192 m m' := by
    intro x hx
    exact frame x (by omega_arith) (by omega_arith) (by omega_arith)
  have tf := outside.unch_far apart.symm
  exact tf.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl hd) (by omega_arith)

 theorem WindowData.of_frame {base table : Addr} {k : Nat} {s t : State}
    (data : WindowData base table k s) (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (frame : WindowPhaseFrame base s.mem t.mem) (zero : t.gpr .x0=s.gpr .x0)
    (tableReg : t.gpr .x26=s.gpr .x26) (rd : t.rd=s.rd) (wr : t.wr=s.wr) : WindowData base table k t := by
  refine ⟨⟨zero.trans data.scr.x0,wr.symm ▸ data.scr.wr,data.scr.nowrap,data.scr.enc⟩,
    ⟨tableReg.trans data.readable.reg,by rw [rd,wr]; exact data.readable.read⟩,?_,?_,?_⟩
  · intro d h1 hd
    rw [WindowPhaseFrame.table frame apart _ (by unfold lookupEntryOffset; omega_arith),
      WindowPhaseFrame.table frame apart _ (by unfold lookupEntryOffset; omega_arith)]
    exact data.canonical d h1 hd
  · rw [WindowPhaseFrame.wordsVal frame (by decide) (by decide) (by decide) (by decide)]
    exact data.zero
  · intro i hi
    have e : ofs base (off base (3304+i))=3304+i := by
      simpa only [BitVec.add_zero,Nat.add_zero] using (ofs_off base (d:=3304+i) (i:=0) (by omega_arith))
    rw [frame _ (by rw [e]; omega_arith) (by rw [e]; omega_arith) (by rw [e]; omega_arith)]
    exact data.bits i hi

 theorem WindowPhaseFrame.refl (base : Addr) (m : Mem) : WindowPhaseFrame base m m := fun _ _ _ _ => rfl

 theorem WindowPhaseFrame.trans {base : Addr} {m m' m'' : Mem}
    (h : WindowPhaseFrame base m m') (k : WindowPhaseFrame base m' m'') : WindowPhaseFrame base m m'' :=
  fun x a b c => (k x a b c).trans (h x a b c)

 theorem WindowPhaseFrame.affine {base table : Addr} {m m' : Mem}
    (frame : WindowPhaseFrame base m m') (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩) (k j : Nat) :
    windowAffine m' table k j=windowAffine m table k j := by
  have hd : magH 16 (combWin 5 k j)≤16 := magH_le (combWin_lt 5 k j)
  dsimp only [windowAffine,windowX,windowY]
  rw [WindowPhaseFrame.table frame apart _ (by unfold lookupEntryOffset; omega_arith),
    WindowPhaseFrame.table frame apart _ (by unfold lookupEntryOffset; omega_arith)]

end VG.Proof.Weierstrass.AArch64.P521Native
