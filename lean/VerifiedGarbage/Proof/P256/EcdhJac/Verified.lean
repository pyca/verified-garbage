module

import VerifiedGarbage.Proof.P256.EcdhJac.Timing
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.P256.EcdhJac.Window
public import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk
public import VerifiedGarbage.Proof.P256.EcdhJac.State
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.P256.EcdhJac.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.P256.EcdhJac.Exchange
import VerifiedGarbage.Proof.P256.EcdhInverse.Inverse
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
import Mathlib.Data.BitVec
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.P256.EcdhInverse.Update
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import VerifiedGarbage.Proof.P256.EcdhJac.DbluCertificate
public import VerifiedGarbage.Proof.P256.EcdhJac.OutCertificate
public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdh.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdh.AArch64.Lit
import Mathlib.Tactic.FieldSimp
import VerifiedGarbage.Proof.Ecdh.AArch64.Verified
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Spec.Ecdh.P256
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved

/-! ### `P256.EcdhJac.Adapter`, which only this module used -/

section

/-! ### `P256.EcdhJac.Multiply`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.AArch64 Spec.Weierstrass

/-- The multiplication has restored its temporary ABI saves. The existing
fixed-count inversion can now finish the internal multiplication contract. -/
structure MulReady (base : Addr) (g : Reg → BitVec 64) (P : Point C) (k : Nat)
    (s t : State) : Prop where
  scr : Scr t base 8192
  fixed : VG.Proof.Ecdsa.AArch64.Fixed p256 base g t.mem
  extra : ∀ r∈[Reg.x26,.x27,.x28],t.gpr r=s.gpr r
  x20 : t.gpr .x20=s.gpr .x20
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  flag : word t.mem base (p256.sl FLAG)=word s.mem base (p256.sl FLAG)
  d : sv p256 base t D=sv p256 base s D
  q : 1≤k → k<C.n → Rep C (tmv C 4 base t K.R.x)
    (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) (mul k P)
  rz_lt : sv p256 base t RZ<C.p

theorem finishInverse_ok (hc : CfgOk p256) {ip : Prog isa} {W : List (Nat × Nat)}
    (hfixed : FixedOk p256 W)
    (hslots : ∀ i,i<45 → i∉[ACC,TMP] → ∀w∈W,
      p256.sl i+8*p256.n≤w.1 ∨ w.1+w.2≤p256.sl i)
    (hflag : ∀w∈W,p256.sl FLAG+8≤w.1 ∨ w.1+w.2≤p256.sl FLAG) {base : Addr} {g : Reg → BitVec 64}
    {P : Point C} {k : Nat} {s t : State} (hw : MulReady base g P k s t)
    (hip : WP isa ip t fun u => KeepRegs (powClob p256.n) t u ∧
      Unch base W t.mem u.mem ∧ wordsVal u.mem base (p256.sl ACC) p256.n<C.p ∧
      toM C.p (2^(64*p256.n)) (wordsVal u.mem base (p256.sl ACC) p256.n)=
        toM C.p (2^(64*p256.n)) (wordsVal t.mem base (p256.sl RZ) p256.n)^(C.p-2))
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ u,MulPost p256 base g P k s u → WP isa rest u R) :
    WP isa (.seq ip rest) t R := by
  refine WP.seq (WP.mono hip
    fun u ⟨ku,hu,lu,vu⟩=>h u ?_)
  have keep : ∀ {i},i<45 → i∉[ACC,TMP] → sv p256 base u i=sv p256 base t i :=
    fun hi hn=>sv_unch hu hc.n10 hw.scr.nowrap hi (hslots _ hi hn)
  refine ⟨hw.scr.of_keepRegs ku (x0_not_powClob hc.n10),
    hw.fixed.unch hc.n10 hw.scr.nowrap hfixed hu,?_,?_,
    ku.rd.trans hw.rd,ku.wr.trans hw.wr,?_,?_,?_,lu,?_,?_⟩
  · intro r hr
    rw [ku.gpr r (by
      have hh : ∀ r∈[Reg.x26,.x27,.x28],r∉powClob 4 := by decide
      exact hh r hr),hw.extra r hr]
  · rw [ku.gpr .x20 (x20_not_powClob hc.n10),hw.x20]
  · exact (hu.word hflag (by decide)).trans hw.flag
  · exact (keep (by decide) (by decide)).trans hw.d
  · intro hk hn
    change Rep C (toM _ _ (sv p256 base u RX)) (toM _ _ (sv p256 base u RY))
      (toM _ _ (sv p256 base u RZ)) _
    rw [keep (i:=RX) (by decide) (by decide),keep (i:=RY) (by decide) (by decide),
      keep (i:=RZ) (by decide) (by decide)]
    exact hw.q hk hn
  · change _=toM _ _ (sv p256 base u RZ) ^ _
    rw [keep (i:=RZ) (by decide) (by decide)]
    exact vu
  · rw [keep (i:=RZ) (by decide) (by decide)]
    exact hw.rz_lt

end VG.Proof.P256.EcdhJac

end

end


/-! ## `Prep` -/

@[expose] public section

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 (p256)
open VG.Proof.Ecdsa.AArch64 (CfgOk sv)
open Spec.Weierstrass

abbrev c := VG.Impl.Ecdsa.AArch64.p256

def prepWrites : List (Nat×Nat) := [(c.winK,40),(c.winBits,320)]

theorem prep_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base 8192)
    {g : Reg→BitVec 64} (hf : VG.Proof.Ecdsa.AArch64.Fixed c base g s.mem) {P : Point C}
    (hpx : sv c base s VG.Impl.Ecdh.AArch64.PX<C.p)
    (hpy : sv c base s VG.Impl.Ecdh.AArch64.PY<C.p)
    (hrep : Rep C (tmv C 4 base s K.P.x) (tmv C 4 base s K.P.y) (tmv C 4 base s K.P.z) P) :
    WP isa Impl.P256.EcdhJac.prep s fun t=>
      Frame base prepWrites s t ∧ Fixed base P (sv c base s VG.Impl.Ecdsa.AArch64.K) t ∧
      KeepRegs (.x19::clob 4) s t := by
  have hk : wordsVal s.mem base (c.sl VG.Impl.Ecdsa.AArch64.K) 4<2^256 := wordsVal_lt ..
  rw [Impl.P256.EcdhJac.prep]
  refine WP.seq (WP.mono (addConst_ok hs (n:=4) (src:=c.sl VG.Impl.Ecdsa.AArch64.K)
    (dst:=c.winK) (c:=offset) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      decide +kernel) (by
      have hb : offset+2^256<2^(64*(4+1)) := by decide +kernel
      omega_using [hk, hb])) fun s₁ ⟨e₁,k₁,o₁⟩=>?_)
  have hs₁:=hs.of_keepRegs k₁ (x0_not_clob _)
  refine WP.mono (bits_ok hs₁ (n:=5) (src:=c.winK) (dst:=c.winBits)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨b₂,k₂,o₂⟩=>?_
  have unch : Unch base prepWrites s.mem t.mem := o₁.unch.trans o₂.unch
  have frame : Frame base prepWrites s t := ⟨(k₁.mono clob_regs).trans (k₂.mono (by decide)),unch⟩
  have ft := hf.unch hc.n10 hs.nowrap (show VG.Proof.Ecdsa.AArch64.FixedOk c prepWrites from by unfold VG.Proof.Ecdsa.AArch64.FixedOk; decide) unch
  have hw (x : Nat) (hx : x∈ro) : wordsVal t.mem base x 4=wordsVal s.mem base x 4 :=
    unch.wordsVal (by
      have hh : ∀ x∈ro,∀ w∈prepWrites,x+32≤w.1 ∨ w.1+w.2≤x := by decide
      exact hh x hx) (by
      have hh : ∀ x∈ro,x+32≤2^64 := by decide
      exact hh x hx)
  have hv (x : Nat) (hx : x∈ro) : tmv C 4 base t x=tmv C 4 base s x := by
    unfold tmv; rw [hw x hx]
  refine ⟨frame,⟨⟨frame.scr regs_x0 hs,VG.Proof.Ecdsa.AArch64.modP_of hc.toBaseCfgOk ft.mp,
    (by decide),?_,fun _ _=>rfl⟩,ft.zero,?_,?_,?_⟩,(k₁.mono (by decide)).trans (k₂.mono (by decide))⟩
  · intro x hx
    change x∈[c.sl VG.Impl.Ecdsa.AArch64.AP,c.sl VG.Impl.Ecdsa.AArch64.BM,
      c.sl VG.Impl.Ecdsa.AArch64.ZERO,c.sl VG.Impl.Ecdh.AArch64.PX,c.sl VG.Impl.Ecdh.AArch64.PY,
      c.sl VG.Impl.Ecdsa.AArch64.ONEP] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact lt_of_eq_of_lt ft.ap (Nat.mod_lt _ (by have hh:=hc.p_ge; omega_using [hh]))
    · exact lt_of_eq_of_lt ft.bm (Nat.mod_lt _ (by have hh:=hc.p_ge; omega_using [hh]))
    · exact lt_of_eq_of_lt ft.zero (by decide)
    · change wordsVal t.mem base K.P.x 4<C.p
      rw [hw K.P.x (by decide)]; exact hpx
    · change wordsVal t.mem base K.P.y 4<C.p
      rw [hw K.P.y (by decide)]; exact hpy
    · exact lt_of_eq_of_lt ft.onep (Nat.mod_lt _ (by have hh:=hc.p_ge; omega_using [hh]))
  · rw [hv _ (by decide),hv _ (by decide),hv _ (by decide)]; exact hrep
  · change toM c.C.p (2^(64*c.n)) (wordsVal t.mem base (c.sl VG.Impl.Ecdsa.AArch64.ONEP) c.n)=1
    rw [ft.onep]
    change toM c.C.p (2^(64*c.n)) (c.mont 1)=1
    rw [VG.Proof.Ecdsa.AArch64.toM_cmont hc]
    rfl
  · intro i hi
    have hh:=b₂ i (by omega_using [hi])
    rw [e₁] at hh
    exact hh

end VG.Proof.P256.EcdhJac

end

/-! ## `Adapter` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.AArch64

theorem mulWithInverse_of_window (hc : CfgOk p256) {ip : Prog isa} {W : List (Nat × Nat)}
    (hfixed : FixedOk p256 W)
    (hslots : ∀ i,i<45 → i∉[VG.Impl.Ecdsa.AArch64.ACC,VG.Impl.Ecdsa.AArch64.TMP] → ∀w∈W,
      p256.sl i+8*p256.n≤w.1 ∨ w.1+w.2≤p256.sl i)
    (hflag : ∀w∈W,p256.sl VG.Impl.Ecdsa.AArch64.FLAG+8≤w.1 ∨ w.1+w.2≤p256.sl VG.Impl.Ecdsa.AArch64.FLAG)
    (hip : ∀ {s : State} {base : Addr},Scr s base 8192 → ModOkA p256.MP' 8192 C.p s.mem base →
      wordsVal s.mem base (p256.sl VG.Impl.Ecdsa.AArch64.RZ) p256.n<C.p →
      WP isa ip s fun t => KeepRegs (powClob p256.n) s t ∧ Unch base W s.mem t.mem ∧
        wordsVal t.mem base (p256.sl VG.Impl.Ecdsa.AArch64.ACC) p256.n<C.p ∧
        toM C.p (2^(64*p256.n)) (wordsVal t.mem base (p256.sl VG.Impl.Ecdsa.AArch64.ACC) p256.n)=
          toM C.p (2^(64*p256.n)) (wordsVal s.mem base (p256.sl VG.Impl.Ecdsa.AArch64.RZ) p256.n)^(C.p-2))
    (hw : ∀ {base : Addr} {P : Point C} {k : Nat} {s : State},onCurve C P=true → k<2^256 →
      Fixed base P k s → WP isa Impl.P256.EcdhJac.window s (WindowPost base P k s)) :
    MulWithInverseOk p256 mq ip := by
  intro base s hs g hf P hP hpx hpy hrep rest R h
  have hk : sv p256 base s VG.Impl.Ecdsa.AArch64.K<2^256 := wordsVal_lt ..
  apply WP.assoc'
  refine WP.seq (WP.mono (prep_ok hc hs hf hpx hpy hrep) fun u ⟨fu,hu,ku⟩=>?_)
  refine WP.seq (WP.mono (wrapped_ok hu (fun v hv=>hw hP hk hv)) fun t ht=>?_)
  have ready : MulReady base g P (sv p256 base s VG.Impl.Ecdsa.AArch64.K) s t := by
    have unch : Unch base (prepWrites++wrappedWrites) s.mem t.mem := fu.unch.trans ht.frame.unch
    refine ⟨ht.field.scr,hf.unch hc.n10 hs.nowrap (by unfold FixedOk; decide) unch,?_,?_,
      ht.frame.regs.rd.trans fu.regs.rd,ht.frame.regs.wr.trans fu.regs.wr,?_,?_,ht.point,?_⟩
    · intro r hr
      rw [ht.restored r (by
        have hh : ∀ r∈[Reg.x26,.x27,.x28],r∈extraRegs := by decide
        exact hh r hr),ku.gpr r (by
        have hh : ∀ r∈[Reg.x26,.x27,.x28],r∉Reg.x19::clob 4 := by decide
        exact hh r hr)]
    · rw [ht.restored .x20 (by decide),ku.gpr .x20 (by decide)]
    · exact unch.word (by decide) (by decide)
    · exact unch.wordsVal (by decide) (by decide)
    · exact ht.field.lt K.R.z (by decide)
  exact finishInverse_ok hc hfixed hslots hflag ready
    (hip ready.scr (modP_of hc.toBaseCfgOk ready.fixed.mp) ready.rz_lt) h

end VG.Proof.P256.EcdhJac

end

end

end


/-! Public ECDH contract and ABI, composed with a separately certified
secret-scalar multiplication. -/

@[expose] public section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Mont

private theorem ungroup {s t : State} {tr}
    (h : Exec isa (Impl.P256.EcdhJac.Frontend.exchange p256 mq Impl.P256.EcdhInverse.inverse) s tr t) :
    Exec isa Impl.P256.EcdhJac.exchange s tr t := by
  cases h with
  | seq a h => cases h with
    | seq b h => cases h with
      | seq c h => cases h with
        | seq d h => cases h with
          | seq m h => cases m with
            | seq p w =>
              simpa only [Impl.P256.EcdhJac.exchange, Impl.P256.EcdhJac.c, List.append_assoc] using
                (Exec.seq a (Exec.seq b (Exec.seq c (Exec.seq d (Exec.seq p (Exec.seq w h))))))

theorem correct_of_mul (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hm : MulWithInverseOk p256 mq Impl.P256.EcdhInverse.inverse)
    (s : State) (hs : ecdhAArch64.pre s) :
    ∃ tr t,Exec isa Impl.P256.EcdhJac.exchange s tr t ∧
      abiPreserved s t ∧ ecdhAArch64.post s t := by
  obtain ⟨tr,t,he,hsv,hu,hpost⟩ := Frontend.exchangeWith_ok (p256_ok hI) hL hm rfl
    middle_callsKeep middle_keepsUntouched (pre_of hs)
  have ex := ungroup he
  refine ⟨tr,t,ex,⟨?_,Exec.sp ex,Exec.preservedV ex keepsV⟩,post_of hpost⟩
  intro r hr
  by_cases hh : r∈untouched
  · exact hu r hh
  · apply hsv r
    revert hh
    revert r
    decide

theorem verified_of_mul (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hm : MulWithInverseOk p256 mq Impl.P256.EcdhInverse.inverse) :
    Verified AArch64.target Impl.P256.EcdhJac.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi) :=
  Verified.of_correct (correct_of_mul hL hI hm) (constantTime hL hI hm) implies

/-- Width-five Jacobian ECDH satisfies the unchanged public contract. -/
theorem verified (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hO : Weierstrass.PrimeOrder Spec.P256.curve)
    (hT : Weierstrass.InvToM Spec.P256.curve.p) :
    Verified AArch64.target Impl.P256.EcdhJac.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi) :=
  verified_of_mul hL hI (mulWithInverse_of_window (p256_ok hI)
    (W:=EcdhInverse.inverseMemory) (by unfold FixedOk; decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun hs hm hx => EcdhInverse.inverse_ok VG.Proof.P256.p_prime hT
      (invLayP (p256_ok hI)) (by decide) (Weierstrass.unitMod_pow_two (p256_ok hI).p_odd _) hs
      (modOkA_inv (p256_ok hI) hm (.inl rfl) rfl rfl) hx
      (p256_ok hI).inv_p)
    (window_ok hL (p256_ok hI).am3 hO))


/-- ECDH over P-256 as it is emitted, its cleanup included
(`Impl.Ecdh.AArch64.Fn.exchangeP256`), meets its contract in constant time and
returns without secret residue. -/
theorem exchange_scrubbed (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hO : Weierstrass.PrimeOrder Spec.P256.curve)
    (hT : Weierstrass.InvToM Spec.P256.curve.p) :
    VerifiedScrubbed AArch64.target VG.Impl.Ecdh.AArch64.Fn.exchangeP256
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi) 32 :=
  VG.AArch64.Scrub.verifiedScrubbedAll (api := Spec.Ecdh.P256.exchangeApi)
    { code := Impl.P256.EcdhJac.exchange, verified := verified hL hI hO hT } _
    (VG.Proof.EcKey.AArch64.Scrub.exchangeOk _) (by dsimp only; lit_decide)

end VG.Proof.P256.EcdhJac
