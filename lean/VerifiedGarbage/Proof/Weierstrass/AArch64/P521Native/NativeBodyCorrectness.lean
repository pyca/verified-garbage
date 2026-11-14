module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeFront
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeWindow
public import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Finish
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareSelected
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Weierstrass.Words
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishTransfer
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowAffineGroup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowRun
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowGroup
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildGroup

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

 def windowDoublesF {F : Type _} [Lean.Grind.CommRing F] : Nat → (F×F×F) → (F×F×F)
  | 0,A => A
  | n+1,A => let D := windowDoublesF n A; dblJF D.1 D.2.1 D.2.2

 def windowNonfinalF {F : Type _} [Lean.Grind.CommRing F] [DecidableEq F] (E : Nat → F×F×F) :
    Nat → (F×F×F) → (F×F×F)
  | 0,A => A
  | j+1,A => windowNonfinalF E j (windowSelectF (windowDoublesF 5 A) (E (j+1)))

 theorem window_doubles_group {C : Curve} (law : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) (e n : Nat) {A : Fe C×Fe C×Fe C}
    (current : InvJ C A.1 A.2.1 A.2.2 (mul e P)) :
    InvJ C (windowDoublesF n A).1 (windowDoublesF n A).2.1 (windowDoublesF n A).2.2 (mul (2^n*e) P) := by
  induction n with
  | zero => simpa only [windowDoublesF,Nat.pow_zero,Nat.one_mul] using current
  | succ n ih =>
    have doubled := InvJ.dbl law ha (law.onCurve_mul hP (2^n*e)) ih
    rw [law.add_mul_mul hP] at doubled
    have same : 2^n*e+2^n*e=2^(n+1)*e := by rw [Nat.pow_succ,Nat.mul_two,Nat.add_mul]
    rw [same] at doubled
    exact doubled

 theorem window_nonfinal_group {C : Curve} (law : Law C) (ha : AM3 C) (order : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (nonzero : P≠.infinity) (hn : 64≤C.n)
    {k J : Nat} (hk : k<C.n) (E : Nat → Fe C×Fe C×Fe C)
    (entries : ∀j,1≤j → j<J → InvJ C (E j).1 (E j).2.1 (E j).2.2
      (Window5.winPt C P (k+16*Window5.geom J) j))
    (affine : ∀j,1≤j → j<J → (E j).2.2=0 ∨ (E j).2.2=1) :
    ∀(n : Nat) (A : Fe C×Fe C×Fe C),n<J →
      InvJ C A.1 A.2.1 A.2.2 (mul (Window5.winE (k+16*Window5.geom J) J (n+1)) P) →
      InvJ C (windowNonfinalF E n A).1 (windowNonfinalF E n A).2.1 (windowNonfinalF E n A).2.2
        (mul (Window5.winE (k+16*Window5.geom J) J 1) P)
  | 0,A,_,current => current
  | n+1,A,top,current => by
    let e := Window5.winE (k+16*Window5.geom J) J (n+2)
    have doubled := window_doubles_group law ha hP e 5 current
    change InvJ C (windowDoublesF 5 A).1 (windowDoublesF 5 A).2.1 (windowDoublesF 5 A).2.2 (mul (32*e) P) at doubled
    have hQ := law.onCurve_mul hP (32*e)
    have hS := Window5.onCurve_winPt law hP (k+16*Window5.geom J) (n+1)
    have different : mul (32*e) P≠.infinity → Window5.winPt C P (k+16*Window5.geom J) (n+1)≠.infinity →
        mul (32*e) P≠Window5.winPt C P (k+16*Window5.geom J) (n+1) := by
      intro hQ0 _
      have he : 1≤e := by
        by_contra h
        have e0 : e=0 := by omega_arith
        rw [e0,Nat.mul_zero,Window5.mul_zero_pt] at hQ0
        exact hQ0 rfl
      exact (window_noexc_nonfinal law order hP nonzero hn hk top (by omega_arith) he).1
    have step := window_select_group law ha (A:=windowDoublesF 5 A) (E:=E (n+1)) hQ hS doubled
      (entries (n+1) (by omega_arith) top) (affine (n+1) (by omega_arith) top) different
    have w := Window5.win_add law hP (k:=k+16*Window5.geom J) (J:=J) (j:=n+1) (Nat.le_add_left _ _) top
    change Spec.Weierstrass.add (mul (32*e) P) (Window5.winPt C P (k+16*Window5.geom J) (n+1))=_ at w
    rw [w] at step
    exact window_nonfinal_group law ha order hP nonzero hn hk E entries affine n _ (by omega_arith) step

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

-- Keep the doubling formula opaque while comparing its fivefold iteration.
private theorem window_doubles_step (n : Nat) (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowDoublesF (n+1) A=windowDbl (windowDoublesF n A) := rfl

 theorem window_five_generic (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowFiveValue A=windowDoublesF 5 A := by
  unfold windowFiveValue
  rw [window_doubles_step,window_doubles_step,window_doubles_step,window_doubles_step,window_doubles_step]
  rfl

 theorem window_affine_generic (m : Mem) (table : Addr) (k j : Nat) :
    windowAffine m table k j=windowAffineN fieldPrime m table k j := rfl

 theorem window_run_generic (m : Mem) (table : Addr) (k n : Nat) (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowNonfinal m table k n A=windowNonfinalF (fun j => windowAffineN fieldPrime m table k j) n A := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    simp only [windowNonfinal,windowNonfinalF,ih,windowStepValue,window_five_generic,window_affine_generic]

 theorem window_run_group_transfer {C : Curve} {p : Nat} [NeZero p]
    (hp : C.p=p) (law : Law C) (ha : AM3 C) (order : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (nonzero : P≠.infinity) (hn : 64≤C.n)
    {k steps : Nat} (hk : k<C.n) (hSteps : steps<105) (m : Mem) (table : Addr)
    {AX AY AZ OX OY OZ : Nat}
    (value : (Fin.ofNat p OX,Fin.ofNat p OY,Fin.ofNat p OZ)=
      windowNonfinalF (fun j => windowAffineN p m table (k+16*Window5.geom 105) j) steps
        (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ))
    (canonical : ∀d,1≤d → d≤16 → wordsVal m table (lookupEntryOffset d+72) 9<C.p)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d+72) 9)) 1 (mul d P))
    (current : InvJ C (Fin.ofNat C.p AX) (Fin.ofNat C.p AY) (Fin.ofNat C.p AZ)
      (mul (Window5.winE (k+16*Window5.geom 105) 105 (steps+1)) P)) :
    InvJ C (Fin.ofNat C.p OX) (Fin.ofNat C.p OY) (Fin.ofNat C.p OZ)
      (mul (Window5.winE (k+16*Window5.geom 105) 105 1) P) := by
  rcases C with ⟨q,a,b,gx,gy,n,len,qnz,nnz⟩
  dsimp only at hp
  subst q
  let E := fun j => windowAffineN p m table (k+16*Window5.geom 105) j
  have reps (j : Nat) := window_affine_repA law m table (k+16*Window5.geom 105) j canonical entries
  have invs : ∀j,1≤j → j<105 → InvJ _ (E j).1 (E j).2.1 (E j).2.2
      (Window5.winPt _ P (k+16*Window5.geom 105) j) := by
    intro j _ _
    exact InvJ.of_rep01 (reps j).1 (reps j).2
  have zs : ∀j,1≤j → j<105 → (E j).2.2=0 ∨ (E j).2.2=1 := by
    intro j _ _
    exact (reps j).2.symm
  change (Fin.ofNat p OX,Fin.ofNat p OY,Fin.ofNat p OZ)=
    windowNonfinalF E steps (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ) at value
  have result := window_nonfinal_group law ha order hP nonzero hn hk E invs zs steps
    (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ) hSteps current
  rw [←value] at result
  exact result

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime montBase)
open VG.Impl.Weierstrass.AArch64.P521Native (config)
open Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

abbrev nativeScalar (s : State) := ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) 66)
abbrev nativePeerBytes (s : State) := Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) 133

private theorem NativeApiDecode_native_prime : config.C.p=fieldPrime := by
  dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,Spec.P521.curve,Spec.P521.p,fieldPrime]
private theorem NativeApiDecode_native_radix : 2^(64*config.n)=montBase := by
  dsimp only [montBase]
  congr 1
private theorem NativeApiDecode_field_relabel {p q R S n a : Nat} [NeZero p] [NeZero q]
    (hp : p=q) (hr : R=S) (h : Fin.ofNat q n=toM q S a) : Fin.ofNat p n=toM p R a := by
  cases hp
  cases hr
  exact h

theorem native_api_decode {s args loaded ready : State} {P : Point config.C}
    (pre : PrepareStackPre s)
    (keep : Keeps [.x2,.x3,.x4,.x6,.x26] (allocated 3456 s) args)
    (stage : St₁ config none args (s.gpr .x3) loaded)
    (core : PrepareCorePost args loaded (s.gpr .x3) (s.gpr .x2) ready)
    (privateArg : args.gpr .x3=s.gpr .x1) (peerPlus : args.gpr .x2=s.gpr .x2+BitVec.ofNat 64 1)
    (selected : peerPoint config.C ready.mem (s.gpr .x3)=P) :
    ∃x y,
      ofBytes (((nativePeerBytes s).drop 1).take config.C.len)=x ∧
      ofBytes ((nativePeerBytes s).drop (config.C.len+1))=y ∧
      word ready.mem (s.gpr .x3) 3232=mask (VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y) ∧
      (∀h : VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y,P=.affine ⟨x,h.2.1⟩ ⟨y,h.2.2.1⟩) ∧
      wordsVal ready.mem (s.gpr .x3) 2368 9=nativeScalar s ∧
      wordsVal ready.mem (s.gpr .x3) 3944 10=nativeScalar s%2^521+recodeOffset := by
  obtain ⟨peer,checked,_,_,fields,offset,_,original,_,_,_,_,flag,px,py,_,_,_,peerX,peerY⟩ := core
  have loadedFrame : Outside (s.gpr .x3) 0 8192 s.mem loaded.mem := fun x hx =>
    (stage.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun keep.mem x)
  have tagSame : loaded.mem (s.gpr .x2)=s.mem (s.gpr .x2) := by
    have h := keep_of_disjoint' loadedFrame pre.args.peer_apart (by decide) (i:=0) (by decide) (by decide)
    simpa only [BitVec.add_zero] using h
  have xParsed : ofBytes (((nativePeerBytes s).drop 1).take config.C.len)=sv config (s.gpr .x3) peer E := by
    change ofBytes (((Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1+2*config.C.len)).drop 1).take config.C.len)=_
    rw [VG.Proof.Ecdh.AArch64.peer_bytes,List.drop_one,List.tail_cons,List.take_left' (length_bytesAt _ _ _),
      peerX,stage.e,shAt_none,Nat.shiftRight_zero]
    simp only [ev,keep.mem,peerPlus]
    rfl
  have yParsed : ofBytes ((nativePeerBytes s).drop (config.C.len+1))=sv config (s.gpr .x3) peer QY := by
    change ofBytes ((Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1+2*config.C.len)).drop (config.C.len+1))=_
    rw [VG.Proof.Ecdh.AArch64.peer_bytes,List.drop_succ_cons,List.drop_left' (length_bytesAt _ _ _),peerY,
      bytesAt_keep loadedFrame (pre.args.peer_apart.sub_left (Offset.sub_base _ (by decide))) (by decide) (by decide)]
  have guard : prepareCoreValid (s.gpr .x3) loaded peer (s.gpr .x2) ↔
      VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) (sv config (s.gpr .x3) peer E) (sv config (s.gpr .x3) peer QY) := by
    simp only [prepareCoreValid,VG.Proof.Ecdh.AArch64.PeerOk,tagSame,VG.Proof.Ecdh.Valid]
    constructor
    · rintro ⟨⟨⟨tag,xb⟩,yb⟩,curve⟩; exact ⟨tag,xb,yb,curve⟩
    · rintro ⟨tag,xb,yb,curve⟩; exact ⟨⟨⟨tag,xb⟩,yb⟩,curve⟩
  have xReady := (NativeApiDecode_field_relabel NativeApiDecode_native_prime NativeApiDecode_native_radix (fields 2800 (by decide)).2).trans px
  have yReady := (NativeApiDecode_field_relabel NativeApiDecode_native_prime NativeApiDecode_native_radix (fields 3160 (by decide)).2).trans py
  have dLoaded : wordsVal loaded.mem (s.gpr .x3) 2368 9=nativeScalar s := by
    have h := stage.d
    rw [shAt_none,Nat.shiftRight_zero] at h
    simp only [dv,keep.mem,keep.gpr .x1 (by decide)] at h
    exact h
  have kLoaded : wordsVal loaded.mem (s.gpr .x3) 2296 9=nativeScalar s := by
    have h := stage.k
    simp only [kv,keep.mem,privateArg] at h
    exact h
  refine ⟨_,_,xParsed,yParsed,?_,?_,original.trans dLoaded,?_⟩
  · simpa only [mask,guard] using flag
  · intro valid
    have hg := guard.mpr valid
    rw [ite_eq_left hg] at xReady yReady
    rw [←selected]
    exact congrArg₂ (@Point.affine config.C) (VG.Proof.EcKey.fe_eq valid.2.1 xReady)
      (VG.Proof.EcKey.fe_eq valid.2.2.1 yReady)
  · rw [offset,kLoaded]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

 theorem window_affine_at_eq (C : Curve) (m : Mem) (table : Addr) (k j : Nat) :
    windowAffineAt C m table k j=windowAffineN C.p m table k j := rfl

 theorem finish_sum_table_rep {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    {m : Mem} {base table : Addr} {d k : Nat} (offset : k=d+16*Window5.geom 105)
    {P : Point C} (hP : onCurve C P=true)
    (b : Fin.ofNat C.p (wordsVal m base 568 9)=Fin.ofNat C.p C.b)
    (current : InvJ C (pointAt C m base 1072).1 (pointAt C m base 1072).2.1 (pointAt C m base 1072).2.2
      (mul (Window5.winE k 105 1) P))
    (canonical : WindowTableCanonical m table)
    (rows : ∀i,i<16 → Rep C (Fin.ofNat C.p (wordsVal m table (216*i) 9))
      (Fin.ofNat C.p (wordsVal m table (216*i+72) 9)) 1 (mul (i+1) P)) :
    Rep C (finishSumAt C m base table k).1 (finishSumAt C m base table k).2.1
      (finishSumAt C m base table k).2.2 (mul d P) := by
  have yBound : ∀j,1≤j → j≤16 → wordsVal m table (lookupEntryOffset j+72) 9<C.p := by
    intro j lo hi
    rw [hp]
    exact (canonical j lo hi).2
  have entries : ∀j,1≤j → j≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset j) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset j+72) 9)) 1 (mul j P) := by
    intro j lo hi
    have row := rows (j-1) (by omega_using [hi])
    simpa only [lookupEntryOffset,Nat.sub_add_cancel lo] using row
  have digit := window_affine_repA law m table k 0 yBound entries
  rw [←window_affine_at_eq] at digit
  exact finish_sum_rep law ha offset hP b current digit

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

 structure NativeConstants (base : Addr) (g : Reg → BitVec 64) (V : Prop) [Decidable V] (out : Addr) (s : State) : Prop where
  b : wordsVal s.mem base 568 9<fieldPrime
  one : wordsVal s.mem base 352 9=1
  modulus : ModOkA config.MP' 8192 config.C.p s.mem base
  order : wordsVal s.mem base 136 9=config.C.n
  saved : Spill.Saved base g Cfg.saved s.mem
  flag : word s.mem base 3232=mask V
  outReg : s.gpr .x20=out
  outFit : out.toNat+66≤2^64
  outW : (⟨out,66⟩ : Region)∈s.wr
  outApart : Region.Disjoint ⟨out,66⟩ ⟨base,8192⟩

 theorem native_low_word {base : Addr} {m m' : Mem}
    (low : ∀d,d<856 → m' (off base d)=m (off base d)) {d : Nat} (hd : d+8≤856) :
    word m' base d=word m base d := by
  apply Mem.readW_congr
  intro i hi
  change m' (off base d+BitVec.ofNat 64 i)=m (off base d+BitVec.ofNat 64 i)
  rw [VG.Offset.add_ofNat_add_ofNat]
  exact low _ (by omega_arith)

 theorem native_low_words {base : Addr} {m m' : Mem}
    (low : ∀d,d<856 → m' (off base d)=m (off base d)) {d k : Nat} (hd : d+8*k≤856) :
    wordsVal m' base d k=wordsVal m base d k := by
  apply wordsVal_of_words₂
  intro j hj
  exact native_low_word low (by omega_arith)

 theorem NativeConstants.of_low {base out : Addr} {g : Reg → BitVec 64} {V : Prop} [Decidable V] {s t : State}
    (h : NativeConstants base g V out s) (low : ∀d,d<856 → t.mem (off base d)=s.mem (off base d))
    (flag : word t.mem base 3232=word s.mem base 3232) (outReg : t.gpr .x20=s.gpr .x20) (wr : t.wr=s.wr) :
    NativeConstants base g V out t := by
  refine ⟨?_,?_,?_,?_,?_,flag.trans h.flag,outReg.trans h.outReg,h.outFit,wr.symm ▸ h.outW,h.outApart⟩
  · rw [native_low_words low (by decide)]; exact h.b
  · rw [native_low_words low (by decide)]; exact h.one
  · refine {h.modulus with val:=?_}
    change wordsVal t.mem base 64 9=config.C.p
    rw [native_low_words low (by decide)]
    exact h.modulus.val
  · rw [native_low_words low (by decide)]; exact h.order
  · intro p hp
    change word t.mem base p.2=g p.1
    rw [native_low_word low (by have e:=saved_lt p hp; omega_arith)]
    exact h.saved p hp

 theorem NativeConstants.finish_pre {base table out : Addr} {g : Reg → BitVec 64} {V : Prop} [Decidable V]
    {s t : State} {k : Nat} (h : NativeConstants base g V out s) (post : NativeAfterWindow base table k s t)
    (tableApart : TableWorkspaceApart base table 8192) : FinishPre t table k g V out := by
  have c := h.of_low post.lowMemory post.flag post.outputPointer post.wr
  have ws : Scr t (t.gpr .x0) 8192 := by rw [post.workspace]; exact post.data.scr
  refine {
    workspace:=ws
    point:=by rw [post.workspace]; exact post.point
    counter:=post.counter
    zero:=by rw [post.workspace]; exact post.data.zero
    b:=by rw [post.workspace]; exact c.b
    oneBound:=by rw [post.workspace,c.one]; decide +kernel
    fieldOne:=by decide +kernel
    tableApart:=by rw [post.workspace]; exact tableApart
    tableRead:=post.data.readable
    tableCanonical:=post.data.canonical
    bits:=by rw [post.workspace]; exact post.data.bits
    modulus:=by rw [post.workspace]; exact c.modulus
    order:=by rw [post.workspace]; exact c.order
    saved:=by rw [post.workspace]; exact c.saved
    flag:=by rw [post.workspace]; exact c.flag
    outReg:=c.outReg
    outFit:=c.outFit
    outW:=c.outW
    outApart:=by rw [post.workspace]; exact c.outApart }

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config windowLoop finishAndWrite)

 def nativeContinuation : Prog isa := .seq windowLoop finishAndWrite

 theorem native_continuation_ok (hc : BaseCfgOk config) {s : State} {base table out : Addr} {k : Nat}
    {g : Reg → BitVec 64} {V : Prop} [Decidable V]
    (data : WindowData base table k s) (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (tableApart : TableWorkspaceApart base table 8192)
    (bound : canonicalPoint s.mem base 1072) (counter : s.gpr .x19=105#64)
    (constants : NativeConstants base g V out s) :
    WP isa nativeContinuation s fun t => ∃mid xv,
      NativeAfterWindow base table k s mid ∧ xv<fieldPrime ∧
      Fin.ofNat fieldPrime xv=(finishSum mid.mem base table k).1*(finishSum mid.mem base table k).2.2^(fieldPrime-2) ∧
      VG.Spec.Ecdsa.bytesAt t.mem out 66=(if finishFullAccept mid table k V then VG.Spec.Weierstrass.toBytes 66 xv else List.replicate 66 0) ∧
      (t.gpr .x0).setWidth 32=(if finishFullAccept mid table k V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧ t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  rw [nativeContinuation,WP.seq_iff]
  refine WP.mono (native_window_ok data apart bound counter) fun mid post => ?_
  have pre := constants.finish_pre post tableApart
  have c := constants.of_low post.lowMemory post.flag post.outputPointer post.wr
  have one : wordsVal mid.mem (mid.gpr .x0) 352 9=1 := by rw [post.workspace]; exact c.one
  refine WP.mono (finish_ok_one hc pre one) fun t ⟨x,b,value,bytes,ret,saved,rd,wr,sp,g27,g28,v31⟩ => ?_
  rw [post.workspace] at value
  exact ⟨mid,x,post,b,value,bytes,ret,saved,rd.trans post.rd,wr.trans post.wr,sp.trans post.sp,
    g27.trans (post.tailGP .x27 (by decide)),g28.trans (post.tailGP .x28 (by decide)),v31.trans post.vector31⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass

 def nativeBodyPhases : Prog isa := .seq nativeFront nativeContinuation

 theorem native_body_phases_wp {s : State} {Q : State → Prop} (h : WP isa nativeBodyPhases s Q) :
    WP isa body s Q := by
  simp only [nativeBodyPhases,nativeFront,nativeRecodeArithmetic,nativeFrontArithmetic,nativeContinuation,
    body,sequence,List.foldr_cons,List.foldr_nil,VG.WP.seq_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)] at h ⊢
  exact h

 theorem native_body_continue (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) {s : State} (pre : PrepareStackPre s)
    {Q : State → Prop} (next : ∀front,NativeApiFrontPost s front → WP isa nativeContinuation front Q) :
    WP isa body (allocated 3456 s) Q := by
  apply native_body_phases_wp
  rw [nativeBodyPhases,WP.seq_iff]
  exact WP.mono (native_front_api_ok hc law ha order orderBound pre) next

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64

 structure NativeBodyPre (s : State) : Prop where
  stack : PrepareStackPre s
  outFit : (s.gpr .x0).toNat+66≤2^64
  outW : (⟨s.gpr .x0,66⟩ : Region)∈s.wr
  outApart : Region.Disjoint ⟨s.gpr .x0,66⟩ ⟨s.gpr .x3,8192⟩

 theorem native_body_pre {s : State}
    (h : (VG.Spec.Ecdh.Instance.exchangeContract VG.Spec.EcKey.P521.inst abi 3456).pre s) : NativeBodyPre s := by
  have stack := prepare_stack_pre h
  sig_pre [VG.Spec.Ecdh.Instance.exchangeContract,VG.Spec.Ecdh.Instance.exchangeSig,
    VG.Spec.EcKey.P521.inst,VG.Spec.P521.curve,VG.Spec.EcKey.scratchWords,VG.AArch64.abi,VG.AArch64.argRegs] at h
  obtain ⟨_,_,wr,_,_,apart,_,_,_,_,_,_,outFit,_,_,_⟩ := h
  exact ⟨stack,outFit,by rw [wr]; simp,apart⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)
open VG.Proof.Ed25519.AArch64 (Keeps)

 theorem native_ready_constants (hc : BaseCfgOk config) {s args loaded ready : State}
    (pre : NativeBodyPre s) (keep : Keeps [.x2,.x3,.x4,.x6,.x26] (allocated 3456 s) args)
    (stage : St₁ config none args (s.gpr .x3) loaded)
    (core : PrepareCorePost args loaded (s.gpr .x3) (s.gpr .x2) ready)
    {V : Prop} [Decidable V] (flag : word ready.mem (s.gpr .x3) 3232=mask V) :
    NativeConstants (s.gpr .x3) args.gpr V (s.gpr .x0) ready := by
  obtain ⟨_,_,_,_,_,_,_,_,one,modulus,order,saved⟩ := prepare_selected_ready hc stage core
  obtain ⟨_,_,_,_,fields,_,_,_,_,_,g20,_,_,_,_,_,wr,_⟩ := core
  have outReg : ready.gpr .x20=s.gpr .x0 :=
    g20.trans (stage.x20.trans (keep.gpr .x0 (by decide)))
  have outW : (⟨s.gpr .x0,66⟩ : Region)∈ready.wr := by
    rw [wr,stage.wr,keep.wr]
    exact List.mem_cons_of_mem _ pre.outW
  exact ⟨(fields 568 (by decide)).1,one,modulus,order,saved,flag,outReg,pre.outFit,outW,pre.outApart⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config body)
open VG.Proof.Ed25519.AArch64 (Keeps)

 def NativeBodyRawPost (s t : State) : Prop :=
  ∃ready, ∃ P : Point config.C, ∃front mid xv x y,
    ofBytes (((nativePeerBytes s).drop 1).take config.C.len)=x ∧
    ofBytes ((nativePeerBytes s).drop (config.C.len+1))=y ∧
    (∀h : VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y,P=.affine ⟨x,h.2.1⟩ ⟨y,h.2.2.1⟩) ∧
    onCurve config.C P=true ∧ P≠.infinity ∧ wordsVal ready.mem (s.gpr .x3) 3944 10<32^105 ∧
    wordsVal ready.mem (s.gpr .x3) 3944 10=nativeScalar s%2^521+recodeOffset ∧
    NativeArithmeticPost config.C (s.gpr .x3) (s.sp-3456#64) P (wordsVal ready.mem (s.gpr .x3) 3944 10) ready front ∧
    NativeAfterWindow (s.gpr .x3) (s.sp-3456#64) (wordsVal ready.mem (s.gpr .x3) 3944 10) front mid ∧
    wordsVal mid.mem (s.gpr .x3) 2368 9=nativeScalar s ∧
    Fin.ofNat config.C.p (wordsVal mid.mem (s.gpr .x3) 568 9)=Fin.ofNat config.C.p config.C.b ∧
    xv<fieldPrime ∧ Fin.ofNat fieldPrime xv=
      (finishSum mid.mem (s.gpr .x3) (s.sp-3456#64) (wordsVal ready.mem (s.gpr .x3) 3944 10)).1*
      (finishSum mid.mem (s.gpr .x3) (s.sp-3456#64) (wordsVal ready.mem (s.gpr .x3) 3944 10)).2.2^(fieldPrime-2) ∧
    VG.Spec.Ecdsa.bytesAt t.mem (s.gpr .x0) 66=(if finishFullAccept mid (s.sp-3456#64)
      (wordsVal ready.mem (s.gpr .x3) 3944 10) (VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y)
      then VG.Spec.Weierstrass.toBytes 66 xv else List.replicate 66 0) ∧
    (t.gpr .x0).setWidth 32=(if finishFullAccept mid (s.sp-3456#64)
      (wordsVal ready.mem (s.gpr .x3) 3944 10) (VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y) then 1 else 0) ∧
    (∀r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧
    t.rd=(allocated 3456 s).rd ∧ t.wr=(allocated 3456 s).wr ∧ t.sp=(allocated 3456 s).sp ∧
    t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31

 theorem native_body_raw_ok (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) {s : State} (pre : NativeBodyPre s) :
    WP isa body (allocated 3456 s) (NativeBodyRawPost s) := by
  apply native_body_continue hc law ha order orderBound pre.stack
  intro front frontPost
  obtain ⟨args,loaded,ready,P,keep,stage,core,hP,pne,kbound,arith,outPointer,
    spFront,v31Front,g27Front,g28Front,rdFront,wrFront,_,privateArg,peerPlus,selected⟩ := frontPost
  obtain ⟨x,y,parsedX,parsedY,flagReady,selectedP,originalD,offset⟩ :=
    native_api_decode pre.stack keep stage core privateArg peerPlus selected
  have constantsReady := native_ready_constants hc pre keep stage core flagReady
  have constants := constantsReady.of_low arith.lowMemory arith.flag arith.outputPointer arith.wr
  have bound : canonicalPoint front.mem (s.gpr .x3) 1072 := by
    change wordsVal front.mem (s.gpr .x3) 1072 9<_ ∧ wordsVal front.mem (s.gpr .x3) 1144 9<_ ∧ wordsVal front.mem (s.gpr .x3) 1216 9<_
    rw [arith.accumulatorX,arith.accumulatorY,arith.accumulatorZ]
    have hp : config.C.p=fieldPrime := by
      dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,VG.Spec.P521.curve,VG.Spec.P521.p,fieldPrime]
    have hge := hc.p_ge
    rw [hp] at hge
    omega_arith
  refine WP.mono (native_continuation_ok hc arith.data pre.stack.table_scratch.symm pre.stack.tableApart bound
    arith.counter constants) fun t ⟨mid,xv,window,xb,value,bytes,ret,saved,rd,wr,sp,g27,g28,v31⟩ => ?_
  have dMid : wordsVal mid.mem (s.gpr .x3) 2368 9=nativeScalar s :=
    window.originalD.trans (arith.originalD.trans originalD)
  have bMid : Fin.ofNat config.C.p (wordsVal mid.mem (s.gpr .x3) 568 9)=Fin.ofNat config.C.p config.C.b := by
    rw [native_low_words window.lowMemory (by decide),native_low_words arith.lowMemory (by decide)]
    exact prepare_selected_b hc core
  refine ⟨ready,P,front,mid,xv,x,y,parsedX,parsedY,selectedP,hP,pne,kbound,offset,
    arith,window,dMid,bMid,xb,value,bytes,ret,?_,rd.trans rdFront,wr.trans wrFront,sp.trans spFront,
    g27.trans g27Front,g28.trans g28Front,v31.trans v31Front⟩
  intro r hr
  have fresh : ∀r∈Cfg.saved.map Prod.fst,r∉[Reg.x2,Reg.x3,Reg.x4,Reg.x6,Reg.x26] := by decide
  exact (saved r hr).trans (keep.gpr r (fresh r hr))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (windowLoop)

 theorem window_initial_group {C : Curve} {m : Mem} {base : Addr} {k : Nat} {P : Point C}
    (zero : wordsVal m base 1216 9=0) (below : k+16*Window5.geom 105<32^105) :
    InvJ C (pointAt C m base 1072).1 (pointAt C m base 1072).2.1
      (pointAt C m base 1072).2.2 (mul (Window5.winE (k+16*Window5.geom 105) 105 105) P) := by
  rw [Window5.winE_top below,Window5.mul_zero_pt]
  refine Or.inl ⟨rfl,?_⟩
  change Fin.ofNat C.p (wordsVal m base 1216 9)=0
  rw [zero]
  rfl

 theorem window_loop_group_ok {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C) (order : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (nonzero : P≠.infinity) (hn : 64≤C.n)
    {s : State} {base table : Addr} {k : Nat} (hk : k<C.n)
    (data : WindowData base table (k+16*Window5.geom 105) s)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (bound : canonicalPoint s.mem base 1072) (counter : s.gpr .x19=105#64)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal s.mem table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal s.mem table (lookupEntryOffset d+72) 9)) 1 (mul d P))
    (current : InvJ C (pointAt C s.mem base 1072).1 (pointAt C s.mem base 1072).2.1
      (pointAt C s.mem base 1072).2.2 (mul (Window5.winE (k+16*Window5.geom 105) 105 105) P)) :
    WP isa windowLoop s fun t =>
      canonicalPoint t.mem base 1072 ∧
      InvJ C (pointAt C t.mem base 1072).1 (pointAt C t.mem base 1072).2.1
        (pointAt C t.mem base 1072).2.2 (mul (Window5.winE (k+16*Window5.geom 105) 105 1) P) ∧
      WindowData base table (k+16*Window5.geom 105) t ∧ WindowPhaseFrame base s.mem t.mem ∧ WindowStepPublic s t ∧
      t.gpr .x19=1#64 ∧ t.gpr .x4=0#64 := by
  refine WP.mono (window_loop_104 data apart bound counter) fun t ⟨b,p,d,f,pub,c19,c4⟩ => ?_
  rw [window_run_generic] at p
  have canonical : ∀d,1≤d → d≤16 → wordsVal s.mem table (lookupEntryOffset d+72) 9<C.p := by
    intro d h1 hd
    rw [hp]
    exact (data.canonical d h1 hd).2
  have group := window_run_group_transfer (steps:=104) hp law ha order hP nonzero hn hk (by decide)
    s.mem table p canonical entries current
  exact ⟨b,group,d,f,pub,c19,c4⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64

private theorem native_prime : config.C.p=fieldPrime := by
  dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,Spec.P521.curve,Spec.P521.p,fieldPrime]

private def outputResult (r : Option (List Byte)) (ret : BitVec 32) (bytes : List Byte) (n : Nat) : Prop :=
  match r with
  | some result => ret=1 ∧ bytes=result
  | none => ret=0 ∧ bytes=List.replicate n 0

private theorem output_post {r : Option (List Byte)} {z bytes : List Byte} {ret : BitVec 32}
    {Q : Prop} [Decidable Q] {n : Nat}
    (spec : r=if Q then some z else none)
    (hb : bytes=if decide Q then z else List.replicate n 0)
    (hr : ret=if decide Q then 1 else 0) :
    outputResult r ret bytes n := by
  rw [spec]
  by_cases h : Q
  · simp only [h,ite_true,decide_true,outputResult] at hb hr ⊢
    exact ⟨hr,hb⟩
  · simp only [h,ite_false,decide_false,Bool.false_eq_true,outputResult] at hb hr ⊢
    exact ⟨hr,hb⟩

 theorem native_body_correctness (_hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) {s t : State} (pre : PrepareStackPre s)
    (raw : NativeBodyRawPost s t) : EPost config s t := by
  obtain ⟨ready,P,front,mid,xv,x,y,parseX,parseY,selected,hP,pne,kbound,offset,arith,window,
    original,b,xb,value,bytes,ret,saved,rd,wr,sp,g27,g28,v31⟩ := raw
  let d := nativeScalar s
  let k := wordsVal ready.mem (s.gpr .x3) 3944 10
  have hn : 64≤config.C.n := by decide +kernel
  have orderSize : config.C.n≤2^521 := by decide +kernel
  have goodOffset (hd : d<config.C.n) : k=d+16*Window5.geom 105 := by
    have below : d<2^521 := Nat.lt_of_lt_of_le hd orderSize
    change k=d+recodeOffset
    exact offset.trans (congrArg (fun z => z+recodeOffset) (Nat.mod_eq_of_lt below))
  have canonical : ∀j,1≤j → j≤16 → wordsVal front.mem (s.sp-3456#64) (lookupEntryOffset j+72) 9<config.C.p := by
    intro j lo hi
    rw [native_prime]
    exact (arith.data.canonical j lo hi).2
  have entries : ∀j,1≤j → j≤16 → Rep config.C (Fin.ofNat config.C.p (wordsVal front.mem (s.sp-3456#64) (lookupEntryOffset j) 9))
      (Fin.ofNat config.C.p (wordsVal front.mem (s.sp-3456#64) (lookupEntryOffset j+72) 9)) 1 (mul j P) := by
    intro j lo hi
    have row := (arith.affine (j-1) (by omega_using [hi])).1
    simpa only [lookupEntryOffset,Nat.sub_add_cancel lo] using row
  have current (hd : d<config.C.n) : InvJ config.C (pointAt config.C mid.mem (s.gpr .x3) 1072).1
      (pointAt config.C mid.mem (s.gpr .x3) 1072).2.1 (pointAt config.C mid.mem (s.gpr .x3) 1072).2.2
      (mul (Window5.winE k 105 1) P) := by
    have initial := window_initial_group (C:=config.C) (P:=P) arith.accumulatorZ (show d+16*Window5.geom 105<32^105 by rw [←goodOffset hd]; exact kbound)
    have p := window.value
    rw [window_run_generic] at p
    change ordinaryPoint mid.mem (s.gpr .x3) 1072=windowNonfinalF (fun j => windowAffineN fieldPrime front.mem (s.sp-3456#64) k j) 104 (ordinaryPoint front.mem (s.gpr .x3) 1072) at p
    rw [goodOffset hd] at p ⊢
    exact window_run_group_transfer native_prime law ha order hP pne hn hd (by decide) front.mem (s.sp-3456#64)
      p canonical entries initial
  have rows : ∀i,i<16 → Rep config.C (Fin.ofNat config.C.p (wordsVal mid.mem (s.sp-3456#64) (216*i) 9))
      (Fin.ofNat config.C.p (wordsVal mid.mem (s.sp-3456#64) (216*i+72) 9)) 1 (mul (i+1) P) := by
    intro i hi
    rw [WindowPhaseFrame.table window.frame pre.table_scratch.symm _ (by omega_using [hi]),
      WindowPhaseFrame.table window.frame pre.table_scratch.symm _ (by omega_using [hi])]
    exact (arith.affine i hi).1
  have result (hd : d<config.C.n) : Rep config.C (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).1
      (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).2.1
      (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).2.2 (mul d P) :=
    finish_sum_table_rep native_prime law ha (goodOffset hd) hP b (current hd) window.data.canonical rows
  have val := finish_value_transfer native_prime value
  have bound : xv<config.C.p := by rw [native_prime]; exact xb
  have spec := VG.Proof.Ecdh.exchange_eq_of_lt law
    (bs:=nativePeerBytes s) (by rw [length_bytesAt]; rfl)
    (b0:=s.mem (s.gpr .x2)) (by
      change (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1+2*config.C.len)).head?=_
      rw [peer_bytes]; rfl) parseX parseY selected result bound val
  have accept : finishFullAccept mid (s.sp-3456#64) k (VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y)=
      decide ((1≤d ∧ d<config.C.n) ∧ VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y ∧ (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).2.2≠0) := by
    unfold finishFullAccept
    rw [window.workspace,original]
    rw [decide_eq_decide]
    have nz := not_congr (finish_zero_transfer native_prime mid.mem (s.gpr .x3) (s.sp-3456#64) k)
    constructor
    · rintro ⟨⟨v,lo,hi⟩,z⟩; exact ⟨⟨lo,hi⟩,v,nz.mp z⟩
    · rintro ⟨⟨lo,hi⟩,v,z⟩; exact ⟨⟨v,lo,hi⟩,nz.mpr z⟩
  change (match Spec.Ecdh.exchange config.C d (nativePeerBytes s) with
    | some z => (t.gpr .x0).setWidth 32=1 ∧ Spec.Ecdsa.bytesAt t.mem (s.gpr .x0) 66=z
    | none => (t.gpr .x0).setWidth 32=0 ∧ Spec.Ecdsa.bytesAt t.mem (s.gpr .x0) 66=List.replicate 66 0)
  change Spec.Ecdh.exchange config.C d (nativePeerBytes s) =
    if (1≤d ∧ d<config.C.n) ∧ VG.Proof.Ecdh.Valid config.C (s.mem (s.gpr .x2)) x y ∧
      (finishSumAt config.C mid.mem (s.gpr .x3) (s.sp-3456#64) k).2.2≠0
    then some (toBytes 66 xv) else none at spec
  rw [accept] at bytes ret
  exact output_post spec bytes ret

end VG.Proof.Weierstrass.AArch64.P521Native
