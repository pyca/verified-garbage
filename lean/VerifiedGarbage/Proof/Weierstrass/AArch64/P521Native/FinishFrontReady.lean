module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAssemble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowFiveDoubles
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishProjectiveState

/-! Adjacent stages of the final P-521 window, sharing their machine-state interface. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

theorem finish_five_doubles_source : finishFiveDoubles=windowFiveDoubles := by
  rw [finishFiveDoubles,windowFiveDoubles,finish_doubling_loop_source,finish_counter_sources.2.2.2.2]

theorem finish_five_doubles_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (counter : s.gpr .x19=1#64) :
    WP isa (.seq (.block outerBlock144) finishFiveDoubles) s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1288=
        windowDbl (windowDbl (windowDbl (windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072))))) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧ t.gpr .x19=0#64 := by
  rw [WP.seq_iff]
  refine WP.mono (finish_counter_enter s) fun u ⟨cu,_,ku,vu⟩ => ?_
  have base : u.gpr .x0=s.gpr .x0 := ku.gpr .x0 (by decide)
  have hu : Scr u (u.gpr .x0) W := by rw [base]; exact hs.of_keeps ku (by decide)
  have bu : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [base,ku.mem]; exact bound
  have packed : u.gpr .x19=windowPacked 0 2 := by rw [cu,counter]; exact finish_counter_zero
  rw [finish_five_doubles_source]
  refine WP.mono (window_five_doubles_ok hu room bu (by decide : 0<4294967296) packed)
    fun t ⟨bt,pt,ft,kt,ct⟩ => ?_
  rw [base] at bt pt ft
  rw [ku.mem] at pt ft
  refine ⟨bt,pt,ft,?_,ct⟩
  constructor
  · exact kt.base.trans base
  · exact kt.rd.trans ku.rd
  · exact kt.wr.trans ku.wr
  · exact kt.sp.trans ku.sp
  · intro r hr h30 h19
    exact (kt.gp r hr h30 h19).trans (ku.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨h19,(by decide : ∀r∈preserved,r≠Reg.x2) r hr⟩))
  · rw [kt.v29,vu]
  · rw [kt.v31,vu]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

 theorem finish_double_frame_unch {base : Addr} {m m' : Mem} (h : WindowWorkFrame base m m') :
    Unch base [(1072,432),(4080,504)] m m' := by
  intro x hx
  exact h x (hx (1072,432) (by simp)) (hx (4080,504) (by simp))

 theorem finish_table_canonical_keep {base table : Addr} {m m' : Mem} {W : List (Nat × Nat)}
    (apart : TableWorkspaceApart base table 8192) (frame : Unch base W m m')
    (fits : ∀w∈W,w.1+w.2≤8192) (old : WindowTableCanonical m table) :
    WindowTableCanonical m' table := by
  have outside : Outside base 0 8192 m m' := frame.outside fun w hw => ⟨Nat.zero_le _,fits w hw⟩
  intro d lo hi
  rw [apart.wordsVal outside 9 (lookupEntryOffset d) (by unfold lookupEntryOffset; omega_arith),
    apart.wordsVal outside 9 (lookupEntryOffset d+72) (by unfold lookupEntryOffset; omega_arith)]
  exact old d lo hi

 theorem finish_affine_keep {base table : Addr} {m m' : Mem} {W : List (Nat × Nat)}
    (apart : TableWorkspaceApart base table 8192) (frame : Unch base W m m')
    (fits : ∀w∈W,w.1+w.2≤8192) (k j : Nat) :
    windowAffine m' table k j=windowAffine m table k j := by
  have outside : Outside base 0 8192 m m' := frame.outside fun w hw => ⟨Nat.zero_le _,fits w hw⟩
  have digit := magH_le (H:=16) (combWin_lt 5 k j)
  have xSame : windowX m' table (magH 16 (combWin 5 k j))=windowX m table (magH 16 (combWin 5 k j)) := by
    simp only [windowX]
    split
    · rfl
    · rw [apart.wordsVal outside 9 _ (by unfold lookupEntryOffset; omega_arith)]
  have ySame : windowY m' table (magH 16 (combWin 5 k j))=windowY m table (magH 16 (combWin 5 k j)) := by
    simp only [windowY]
    split
    · rfl
    · rw [apart.wordsVal outside 9 _ (by unfold lookupEntryOffset; omega_arith)]
  simp only [windowAffine,xSame,ySame]

 theorem finish_bits_keep {base : Addr} {m m' : Mem} {W : List (Nat × Nat)} {k : Nat}
    (frame : Unch base W m m') (apart : ∀w∈W,w.1+w.2≤3304 ∨ 3829≤w.1)
    (bits : ∀i<525,m (off base (3304+i))=if k.testBit i then 1 else 0) :
    ∀i<525,m' (off base (3304+i))=if k.testBit i then 1 else 0 := by
  intro i hi
  rw [frame _ (by
    intro w hw
    rw [ofs_off0 base (by omega_arith)]
    have bounds := apart w hw
    omega_arith)]
  exact bits i hi

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock144)

def finishDbl5 (P : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :=
  windowDbl (windowDbl (windowDbl (windowDbl (windowDbl P))))
def finishHomogeneous (P : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :=
  (P.1*P.2.2,(if P.2.2*P.2.2*P.2.2=0 then Fin.ofNat fieldPrime 1 else P.2.1),P.2.2*P.2.2*P.2.2)
def finishFrontReady : Prog isa :=
  .seq (.seq (.block outerBlock144) finishFiveDoubles) finishProjectivePrepare
def finishFrontWrites : List (Nat × Nat) := [(1072,432),(4080,504)]++finishProjectiveWrites

theorem finish_front_ready_ok {s : State} {table : Addr} {k : Nat}
    (hs : Scr s (s.gpr .x0) 8192) (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (counter : s.gpr .x19=1#64) (zero : wordsVal s.mem (s.gpr .x0) 280 9=0)
    (bb : wordsVal s.mem (s.gpr .x0) 568 9<fieldPrime) (oneBound : 1<fieldPrime)
    (apart : TableWorkspaceApart (s.gpr .x0) table 8192) (tableRead : LookupTableReadable s table)
    (canonical : WindowTableCanonical s.mem table)
    (bits : ∀i<525,s.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0) :
    WP isa finishFrontReady s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=finishHomogeneous (finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      Scr t (s.gpr .x0) 8192 ∧ LookupTableReadable t table ∧ WindowTableCanonical t.mem table ∧
      (∀i<525,t.mem (off (s.gpr .x0) (3304+i))=if k.testBit i then 1 else 0) ∧
      wordsVal t.mem (s.gpr .x0) 280 9=0 ∧ wordsVal t.mem (s.gpr .x0) 568 9<fieldPrime ∧
      t.gpr .x19=0#64 ∧ t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧
      Unch (s.gpr .x0) finishFrontWrites s.mem t.mem ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [finishFrontReady,WP.seq_iff]
  refine WP.mono (finish_five_doubles_ok hs (by decide) bound counter)
    fun u ⟨bu,pu,fu,ku,cu⟩ => ?_
  have uf := finish_double_frame_unch fu
  have hu : Scr u (s.gpr .x0) 8192 := by rw [←ku.base]; exact ku.scr hs
  have zeroU : wordsVal u.mem (s.gpr .x0) 280 9=0 := by rw [uf.wordsVal (by decide) (by decide),zero]
  refine WP.mono (finish_projective_prepare_ok hu bu zeroU oneBound)
    fun t ⟨E,ep,bt,xv,yv,zv,ez,ht,ut,c19,c20,c26,pub⟩ => ?_
  have allU : Unch (s.gpr .x0) finishFrontWrites s.mem t.mem := uf.trans ut
  have fits : ∀w∈finishFrontWrites,w.1+w.2≤8192 := by decide
  have point : ordinaryPoint t.mem (s.gpr .x0) 1072=finishHomogeneous (finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072)) := by
    have coords := ep.trans pu
    change (E 1072,E 1144,E 1216)=finishDbl5 (ordinaryPoint s.mem (s.gpr .x0) 1072) at coords
    rw [←coords]
    have eval := finish_projective_value E ez
    have ex := congrArg Prod.fst eval
    have ey := congrArg (fun P => P.2.1) eval
    have ezz := congrArg (fun P => P.2.2) eval
    dsimp only at ex ey ezz
    change (Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1072 9),
      Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1144 9),
      Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) 1216 9))=_
    rw [xv,yv,zv,ex,ey,ezz]
    rfl
  have readT : LookupTableReadable t table := by
    constructor
    · exact c26.trans ((ku.gp .x26 (by decide) (by decide) (by decide)).trans tableRead.reg)
    · intro d hd
      rw [pub.rd,pub.wr,ku.rd,ku.wr]
      exact tableRead.read d hd
  refine ⟨bt,point,ht,readT,finish_table_canonical_keep apart allU fits canonical,
    finish_bits_keep allU (by decide) bits,?_,?_,c19.trans cu,?_,?_,allU,pub.rd.trans ku.rd,pub.wr.trans ku.wr,pub.sp.trans ku.sp,?_,?_,?_⟩
  · rw [allU.wordsVal (by decide) (by decide),zero]
  · rw [allU.wordsVal (by decide) (by decide)]; exact bb
  · exact c20.trans (ku.gp .x20 (by decide) (by decide) (by decide))
  · exact c26.trans (ku.gp .x26 (by decide) (by decide) (by decide))

  · exact (pub.gpr .x27 (by decide)).trans (ku.gp .x27 (by decide) (by decide) (by decide))
  · exact (pub.gpr .x28 (by decide)).trans (ku.gp .x28 (by decide) (by decide) (by decide))
  · exact pub.v31.trans ku.v31

end VG.Proof.Weierstrass.AArch64.P521Native

end
