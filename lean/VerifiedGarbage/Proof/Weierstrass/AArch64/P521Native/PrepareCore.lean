module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareReady
public import VerifiedGarbage.Proof.Ecdh.AArch64.Prefix
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Peer validation and ordinary-field/scalar preparation compose without a valid-peer assumption. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime montBase)
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

private theorem prime_config : config.C.p=fieldPrime := by
  simp only [config, VG.Impl.Ecdsa.AArch64.p521, VG.Spec.P521.curve, VG.Spec.P521.p, fieldPrime]

def prepareCore : Prog isa := .seq preparePeer (.seq prepareCheck prepareFieldScalar)

def prepareCoreValid (base : Addr) (s peer : State) (q : Addr) : Prop :=
  VG.Proof.Ecdh.AArch64.PeerOk config base peer
    (((s.mem q=4) ∧ sv config base peer E<config.C.p) ∧ sv config base peer QY<config.C.p)

instance {base : Addr} {s peer : State} {q : Addr} : Decidable (prepareCoreValid base s peer q) := inferInstanceAs (Decidable
  (VG.Proof.Ecdh.AArch64.PeerOk config base peer (((s.mem q=4) ∧ sv config base peer E<config.C.p) ∧ sv config base peer QY<config.C.p)))

def prepareCoreWrites : List (Nat × Nat) :=
  (slW config [R2P,BP,QY]++[(config.sl FLAG,8)])++
  (slW config [QXM,QYM,TMP,W0,W1,W2,W3,PY]++[(config.sl FLAG,8)])++prepareReadyWrites

def PrepareCorePost (args s : State) (base q : Addr) (t : State) : Prop :=
  ∃peer checked,
      Fixed config base args.gpr checked.mem ∧
      Scr t base 8192 ∧
      (∀d∈[2800,3160,424,496,568],wordsVal t.mem base d 9<fieldPrime ∧
        Fin.ofNat fieldPrime (wordsVal t.mem base d 9)=toM fieldPrime montBase (wordsVal checked.mem base d 9)) ∧
      wordsVal t.mem base 3944 10=wordsVal s.mem base 2296 9%2^521+recodeOffset ∧
      wordsVal t.mem base 3944 10<32^105 ∧ wordsVal t.mem base 2368 9=wordsVal s.mem base 2368 9 ∧
      t.gpr .x19=80 ∧ t.gpr .x5=1 ∧ t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧
      word t.mem base 3232=mask (prepareCoreValid base s peer q) ∧
      toM config.C.p (2^(64*config.n)) (sv config base checked PX)=
        (if prepareCoreValid base s peer q then Fin.ofNat config.C.p (sv config base peer E) else Fin.ofNat config.C.p config.C.gx) ∧
      toM config.C.p (2^(64*config.n)) (sv config base checked PY)=
        (if prepareCoreValid base s peer q then Fin.ofNat config.C.p (sv config base peer QY) else Fin.ofNat config.C.p config.C.gy) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ Unch base prepareCoreWrites s.mem t.mem ∧
      sv config base peer E=sv config base s E ∧
      sv config base peer QY=VG.Spec.Weierstrass.ofBytes
        (VG.Spec.Ecdsa.bytesAt s.mem (q+BitVec.ofNat 64 (1+config.C.len)) config.C.len)

theorem prepare_core_ok (hc : BaseCfgOk config) {args s : State} {base q : Addr}
    (stage : St₁ config none args base s) (hq : s.gpr .x6=q)
    (hin : (⟨q,133⟩ : Region)∈s.rd++s.wr) (apart : Region.Disjoint ⟨q,133⟩ ⟨base,8192⟩) :
    WP isa prepareCore s (PrepareCorePost args s base q) := by
  unfold PrepareCorePost
  rw [prepareCore]
  refine WP.seq (WP.mono (prepare_peer_ok hc stage.scr hq hin apart)
    fun peer ⟨hsPeer,kp,up,r2,bp,yPeer,flagPeer⟩ => ?_)
  have fixedPeer := stage.fixed.unch hc.n10 stage.scr.nowrap
    ((fixedOk_slW (l:=[R2P,BP,QY]) (by decide)).append fixedOk_flag) up
  have flag : word peer.mem base (config.sl FLAG)=mask (s.mem q=4) := by
    rw [flagPeer,stage.flag,BitVec.allOnes_and]
  refine WP.seq (WP.mono (prepare_validate_ok hc hsPeer fixedPeer r2 bp flag)
    fun checked ⟨hsChecked,kg,kr,kw,uc,flagChecked,pxBound,pyBound,pxValue,pyValue⟩ => ?_)
  have fixedChecked := fixedPeer.unch hc.n10 stage.scr.nowrap
    ((fixedOk_slW (l:=[QXM,QYM,TMP,W0,W1,W2,W3,PY]) (by decide)).append fixedOk_flag) uc
  have pos : 0<config.C.p := by have h:=hc.p_ge; omega_arith
  have canonical (d : Nat) (hd : d∈[2800,3160,424,496,568]) : wordsVal checked.mem base d 9<fieldPrime := by
    have casesD : d=2800 ∨ d=3160 ∨ d=424 ∨ d=496 ∨ d=568 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hd
    rw [←prime_config]
    rcases casesD with rfl|rfl|rfl|rfl|rfl
    · exact pxBound
    · exact pyBound
    · rw [show wordsVal checked.mem base 424 9=wordsVal checked.mem base (config.sl ONEP) config.n from rfl,fixedChecked.onep]
      exact Nat.mod_lt _ pos
    · rw [show wordsVal checked.mem base 496 9=wordsVal checked.mem base (config.sl AP) config.n from rfl,fixedChecked.ap]
      exact Nat.mod_lt _ pos
    · rw [show wordsVal checked.mem base 568 9=wordsVal checked.mem base (config.sl BM) config.n from rfl,fixedChecked.bm]
      exact Nat.mod_lt _ pos
  have keyPeer : wordsVal peer.mem base 2296 9=wordsVal s.mem base 2296 9 := up.wordsVal (by decide) (by decide)
  have keyChecked : wordsVal checked.mem base 2296 9=wordsVal peer.mem base 2296 9 := uc.wordsVal (by decide) (by decide)
  have originalPeer : wordsVal peer.mem base 2368 9=wordsVal s.mem base 2368 9 := up.wordsVal (by decide) (by decide)
  have originalChecked : wordsVal checked.mem base 2368 9=wordsVal peer.mem base 2368 9 := uc.wordsVal (by decide) (by decide)
  refine WP.mono (prepare_field_scalar_ok hsChecked canonical)
    fun t ⟨hst,fields,offset,bound,ctr,one,orig,flagSame,out,table,keepReady,unchReady⟩ => ?_
  refine ⟨peer,checked,fixedChecked,hst,fields,?_,bound,?_,ctr,one,?_,?_,?_,pxValue,pyValue,?_,?_,up.trans (uc.trans unchReady),?_,yPeer⟩
  · rw [offset,keyChecked,keyPeer]
  · rw [orig,originalChecked,originalPeer]
  · rw [out,kg .x20 (by decide),kp.gpr .x20 (by decide)]
  · rw [table,kg .x26 (by decide),kp.gpr .x26 (by decide)]
  · rw [flagSame]
    exact flagChecked
  · rw [keepReady.rd,kr,kp.rd]
  · rw [keepReady.wr,kw,kp.wr]
  · exact up.wordsVal (d:=config.sl E) (k:=config.n) (by decide) (by decide)

end VG.Proof.Weierstrass.AArch64.P521Native
