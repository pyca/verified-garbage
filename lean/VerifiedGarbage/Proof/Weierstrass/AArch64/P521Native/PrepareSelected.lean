module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareCore
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildGroup
public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime montBase)
open VG.Impl.Weierstrass.AArch64.P521Native (config)
open VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (QY PX PY)

private theorem native_prime : config.C.p=fieldPrime := by
  simp only [config,VG.Impl.Ecdsa.AArch64.p521,VG.Spec.P521.curve,VG.Spec.P521.p,fieldPrime]

private theorem native_radix : 2^(64*config.n)=montBase := by
  dsimp only [montBase]
  congr 1

private theorem relabel_field {p q R S n a : Nat} [NeZero p] [NeZero q]
    (hp : p=q) (hr : R=S) (h : Fin.ofNat q n=toM q S a) : Fin.ofNat p n=toM p R a := by
  cases hp
  cases hr
  exact h

private theorem canonical_one {p n : Nat} [NeZero p] (hp : 1<p) (hn : n<p)
    (h : Fin.ofNat p n=(1 : Fin p)) : n=1 := by
  have e : n%p=1%p := ofNat_eq_ofNat.mp h
  simpa only [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hp] using e

def prepareSelected (base : Addr) (s peer : State) (q : Addr) : Point config.C :=
  if prepareCoreValid base s peer q then
    .affine (Fin.ofNat config.C.p (sv config base peer E))
      (Fin.ofNat config.C.p (sv config base peer QY)) else G config.C

private theorem peer_formula (c : Cfg) (b4 : Prop) [Decidable b4] (x y : Nat) :
    (if ((b4 ∧ x<c.C.p) ∧ y<c.C.p) ∧ VG.Proof.Ecdh.AArch64.OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
      then Point.affine (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y) else G c.C)=
    VG.Proof.Ecdh.AArch64.peerPt c b4 x y := by
  unfold VG.Proof.Ecdh.AArch64.peerPt
  split
  · rename_i h
    apply congrArg₂ (@Point.affine c.C)
    · exact VG.Proof.EcKey.fe_eq h.1.1.2 rfl
    · exact VG.Proof.EcKey.fe_eq h.1.2 rfl
  · rfl

private theorem prepare_selected_peer (base : Addr) (s peer : State) (q : Addr) :
    prepareSelected base s peer q=VG.Proof.Ecdh.AArch64.peerPt config (s.mem q=4)
      (sv config base peer E) (sv config base peer QY) :=
  peer_formula config (s.mem q=4) _ _

private theorem ordinary_one (c : Cfg) (hc : BaseCfgOk c) {p R n : Nat} [NeZero p]
    (hp : c.C.p=p) (hr : 2^(64*c.n)=R) (hR : UnitMod p R)
    {base : Addr} {m : Mem} {g : Reg → BitVec 64} (fixed : Fixed c base g m)
    (hn : n<p) (value : Fin.ofNat p n=toM p R (wordsVal m base (c.sl ONEP) c.n)) : n=1 := by
  have onep:=fixed.onep
  rw [hp,hr] at onep
  rw [onep,toM_one hR] at value
  exact canonical_one (by have h:=hc.p_ge; rw [hp] at h; omega_arith) hn value

theorem prepare_selected_oncurve (hc : BaseCfgOk config) (base : Addr) (s peer : State) (q : Addr) :
    onCurve config.C (prepareSelected base s peer q)=true := by
  rw [prepare_selected_peer]
  exact VG.Proof.Ecdh.AArch64.peerPt_onCurve hc _ _ _

theorem prepare_selected_nonzero (base : Addr) (s peer : State) (q : Addr) :
    prepareSelected base s peer q≠.infinity := by
  unfold prepareSelected
  split <;> simp only [G,ne_eq,reduceCtorEq,not_false_eq_true]

 theorem prepare_selected_ready (hc : BaseCfgOk config) {args s t : State} {base q : Addr}
    (stage : St₁ config none args base s) (post : PrepareCorePost args s base q t) :
    ∃P : Point config.C,onCurve config.C P=true ∧ P≠.infinity ∧ peerPoint config.C t.mem base=P ∧
      wordsVal t.mem base 2800 9<fieldPrime ∧ wordsVal t.mem base 3160 9<fieldPrime ∧
      wordsVal t.mem base 424 9=1 ∧ wordsVal t.mem base 280 9=0 ∧ wordsVal t.mem base 352 9=1 ∧
      ModOkA config.MP' 8192 config.C.p t.mem base ∧ wordsVal t.mem base 136 9=config.C.n ∧
      Spill.Saved base args.gpr Cfg.saved t.mem := by
  obtain ⟨peer,checked,fixed,_,fields,_,_,_,_,_,_,_,_,px,py,_,_,frame,_,_⟩:=post
  have x := relabel_field native_prime native_radix (fields 2800 (by decide)).2
  have y := relabel_field native_prime native_radix (fields 3160 (by decide)).2
  have x' := x.trans px
  have y' := y.trans py
  have pp : peerPoint config.C t.mem base=prepareSelected base s peer q := by
    dsimp only [peerPoint,prepareSelected]
    rw [x',y']
    split <;> rfl
  have oneField : wordsVal t.mem base 424 9=1 :=
    ordinary_one config hc native_prime native_radix p521_mont_unit fixed
      (fields 424 (by decide)).1 (fields 424 (by decide)).2
  have same (d : Nat) (bound : d+72≤8192) (hd : ∀w∈prepareCoreWrites,d+72≤w.1 ∨ w.1+w.2≤d) :
      wordsVal t.mem base d 9=wordsVal s.mem base d 9 := frame.wordsVal hd (by
        have h:=stage.scr.enc
        omega_arith)
  refine ⟨prepareSelected base s peer q,prepare_selected_oncurve hc _ _ _ _,prepare_selected_nonzero _ _ _ _,pp,
    (fields 2800 (by decide)).1,(fields 3160 (by decide)).1,oneField,?_,?_,?_,?_,?_⟩
  · rw [same 280 (by decide) (by decide)]; exact stage.fixed.zero
  · rw [same 352 (by decide) (by decide)]; exact stage.fixed.one
  · apply modP_of hc
    change wordsVal t.mem base 64 9=config.C.p
    rw [same 64 (by decide) (by decide)]; exact stage.fixed.mp
  · rw [same 136 (by decide) (by decide)]; exact stage.fixed.mn
  · exact Saved.unch stage.fixed.saved (by decide) frame

private theorem ordinary_b (c : Cfg) (hc : BaseCfgOk c)
    {base : Addr} {m : Mem} {g : Reg → BitVec 64} {n : Nat} (fixed : Fixed c base g m)
    (value : Fin.ofNat c.C.p n=toM c.C.p (2^(64*c.n)) (wordsVal m base (c.sl BM) c.n)) :
    Fin.ofNat c.C.p n=Fin.ofNat c.C.p c.C.b := by
  rw [fixed.bm] at value
  dsimp only [Cfg.mont,Cfg.R] at value
  rw [toM_mont (unitMod_pow_two hc.p_odd (64*c.n))] at value
  exact value

theorem prepare_selected_b (hc : BaseCfgOk config) {args s t : State} {base q : Addr}
    (post : PrepareCorePost args s base q t) :
    Fin.ofNat config.C.p (wordsVal t.mem base 568 9)=Fin.ofNat config.C.p config.C.b := by
  obtain ⟨_,checked,fixed,_,fields,_⟩:=post
  exact ordinary_b config hc fixed
    (relabel_field native_prime native_radix (fields 568 (by decide)).2)

end VG.Proof.Weierstrass.AArch64.P521Native
