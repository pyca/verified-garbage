module

import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombBodyCT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombBodyCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombInput
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPointTail
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerKeep
public import VerifiedGarbage.Proof.Ecdsa.X86.CombPrefix
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombStagesCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86.JacState
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86.NafPublicFields
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Weierstrass.X86.WinEntry
import VerifiedGarbage.Proof.Weierstrass.X86.WinLoop
import VerifiedGarbage.Proof.Weierstrass.X86.WinSelect
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdh.X86.Peer
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPoints
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerCT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.X86.Finish
meta import VerifiedGarbage.Proof.Ecdsa.X86.Inv
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lays
meta import VerifiedGarbage.Proof.Ecdsa.X86.Middle
meta import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
meta import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
meta import VerifiedGarbage.Proof.Ecdsa.X86.Setup
meta import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Mont.Words128
meta import VerifiedGarbage.Proof.Mont.X86.Csub
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.P256Red
meta import VerifiedGarbage.Proof.Mont.X86.RedRow
meta import VerifiedGarbage.Proof.Mont.X86.Row
meta import VerifiedGarbage.Proof.Mont.X86.SparseShift
meta import VerifiedGarbage.Proof.Mont.X86.SparseStep
meta import VerifiedGarbage.Proof.Mont.X86.Step
meta import VerifiedGarbage.Proof.P256.Prime
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.Weierstrass.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.InvToM
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Weierstrass.Window5
meta import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.X86.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
meta import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
meta import VerifiedGarbage.Proof.Weierstrass.X86.JacState
meta import VerifiedGarbage.Proof.Weierstrass.X86.Loop
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafArithmeticTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafPublicFields
meta import VerifiedGarbage.Proof.Weierstrass.X86.NafTableFields
meta import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
meta import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming
meta import VerifiedGarbage.Proof.Weierstrass.X86.Rep
meta import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
meta import VerifiedGarbage.Proof.Weierstrass.X86.WinEntry
meta import VerifiedGarbage.Proof.Weierstrass.X86.WinLoop
meta import VerifiedGarbage.Proof.Weierstrass.X86.WinSelect
meta import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.X25519.X86.Fold

/-! # Verification with the static comb table address -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86

structure VCombPre (c : Cfg) (s : State) : Prop extends
    VPre c s (Abi.constRegions (fun n => (s.syms n).setWidth 64) c.combConsts) where
  tbls : TblsHeld c s (below (s.gpr .esp) c.stk :: s.wr)
  pk_stack : Region.Disjoint ⟨ptr s 0, 1 + 2 * c.C.len⟩ (below (s.gpr .esp) 4)
  dg_stack : Region.Disjoint ⟨ptr s 1, c.C.len⟩ (below (s.gpr .esp) 4)
  sig_stack : Region.Disjoint ⟨ptr s 2, 2 * c.C.len⟩ (below (s.gpr .esp) 4)

variable {c : Cfg}

theorem VCombPre.sp4 {s : State} (hp : VCombPre c s) : 4 ≤ (s.gpr .esp).toNat := by
  have := Cfg.stk_ge c; have := hp.toVPre.sp_lo; omega

theorem VPre.symAddr {s t : State} {extra : List Region} {name : String}
    (hp : VPre c s extra) (h : SymAddrPost name s t) (hsp : 4 ≤ (s.gpr .esp).toNat) : VPre c t extra := by
  have he := h.gpr .esp (by decide)
  have ha : ∀ j < 4, arg t j = arg s j := fun j hj => h.arg hsp (by have := hp.sp_fit; omega)
  have haa : argAddr t 0 = argAddr s 0 := by simp only [argAddr, he]
  exact {
    rd := by simpa only [ptr, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), haa, h.rd] using hp.rd
    wr := by simpa only [ptr, ha 3 (by decide), h.wr] using hp.wr
    pk_sc := by simpa only [ptr, ha 0 (by decide), ha 3 (by decide)] using hp.pk_sc
    dg_sc := by simpa only [ptr, ha 1 (by decide), ha 3 (by decide)] using hp.dg_sc
    sig_sc := by simpa only [ptr, ha 2 (by decide), ha 3 (by decide)] using hp.sig_sc
    args_sc := by simpa only [ptr, haa, ha 3 (by decide)] using hp.args_sc
    ret_sc := by simpa only [ptr, he, ha 3 (by decide)] using hp.ret_sc
    pk_fit := by rw [ha 0 (by decide)]; exact hp.pk_fit
    dg_fit := by rw [ha 1 (by decide)]; exact hp.dg_fit
    sig_fit := by rw [ha 2 (by decide)]; exact hp.sig_fit
    sc_fit := by rw [ha 3 (by decide)]; exact hp.sc_fit
    sp_fit := by rw [he]; exact hp.sp_fit
    sp_lo := by rw [he]; exact hp.sp_lo
    stk_sc := by simpa only [stkR, ptr, he, ha 3 (by decide)] using hp.stk_sc }

theorem VKeep.abi {s₀ s : State} {extra : List Region} (hp : VPre c s₀ extra) (K : VKeep c s₀ s) :
    abiPreserved s₀ s := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact K.saved (.ebx, 0) (by decide)
    · exact K.saved (.esi, 4) (by decide)
    · exact K.saved (.edi, 8) (by decide)
    · exact K.saved (.ebp, 12) (by decide)
    · exact K.esp
  · exact K.ret hp

theorem vPrefixTables {s t : State} (hp : VCombPre p256Comb s) (P : SymAddrPost p256d.tsym s t) :
    VCombTables t := by
  have hp' := hp.toVPre.symAddr P hp.sp4
  have held := hp.tbls.symAddr (Nat.le_trans (by decide) (Cfg.stk_ge _)) hp.toVPre.sp_lo P
  have ht := tbl_of_held (c := p256Comb) (d := p256d) (base := ptr t 3) rfl held
    (by rw [hp'.wr]; simp) (fun r hr => by rw [hp'.rd]; simp only [P.syms] at hr; simp [hr]) (Unch.refl _ _ _)
  simpa only [VCombTables, P.addr, P.syms] using ht

def vCombCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.verifyComb p256Comb
materialize_code vCombCode

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem vComb_sp : SpOk vCombCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem vCombBody_sp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.verifyCombBody p256Comb) p256Comb.stk :=
  SpOk.right (a := p256Comb.tableAddr) vComb_sp

theorem vComb_ok (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) {s₀ : State} (hp : VCombPre p256Comb s₀) :
    WP isa vCombCode s₀ fun s' => abiPreserved s₀ s' ∧ VPost p256Comb s₀ s' := by
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h; have e : p256d = d := Option.some.inj h; rw [← e]; exact p256Comb_shape
  refine WP.seq (WP.mono (symFrame_ok p256d.tsym s₀ hp.sp4) fun s₁ P => ?_)
  have hp₁ := hp.toVPre.symAddr P hp.sp4
  have ht := vPrefixTables hp P
  refine WP.mono (verifyCombBody_ok (p256Comb_ok hI) hC (p256Comb_tables hC) hCo p256Comb_am3 hp₁
    (fun d hd => by have e : p256d = d := Option.some.inj hd; subst d; exact ht) signComb_spG vCombBody_sp)
    fun s₂ ⟨K, post⟩ => ?_
  have ha := K.abi hp₁
  have he := P.gpr .esp (by decide)
  refine ⟨⟨fun r hr => (ha.1 r hr).trans (P.gpr r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)), ?_⟩, ?_⟩
  · have ht := ha.2
    rw [he] at ht
    exact ht.trans (P.ret hp.sp4 (by have := hp.sp_fit; omega))
  · have harg : ∀ j < 4, arg s₁ j = arg s₀ j := fun j hj => P.arg hp.sp4 (by have := hp.sp_fit; omega)
    have hpk := prefix_bytesAt P hp.pk_stack (by change 65 ≤ 2 ^ 64; decide)
    have hdg := prefix_bytesAt P hp.dg_stack (by change 32 ≤ 2 ^ 64; decide)
    have hsig := prefix_bytesAt P hp.sig_stack (by change 64 ≤ 2 ^ 64; decide)
    simpa only [VPost, ptr, harg 0 (by decide), harg 1 (by decide), harg 2 (by decide), hpk, hdg, hsig] using post

def VCombPub (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ j < 4, arg s j = arg t j) ∧ s.syms p256d.tsym = t.syms p256d.tsym ∧
    Spec.Ecdsa.bytesAt s.mem (ptr s 0) (1+2*p256Comb.C.len)=Spec.Ecdsa.bytesAt t.mem (ptr t 0) (1+2*p256Comb.C.len) ∧
    Spec.Ecdsa.bytesAt s.mem (ptr s 2) (2*p256Comb.C.len)=Spec.Ecdsa.bytesAt t.mem (ptr t 2) (2*p256Comb.C.len)

theorem vComb_ct (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : ConstantTime isa (VCombPre p256Comb) VCombPub vCombCode := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have preCT : RelCT isa (fun s t => VCombPre p256Comb s ∧ VCombPre p256Comb t ∧ VCombPub s t)
      p256Comb.tableAddr (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    exact ⟨by rw [symFrame_trace h.1.sp4 e₁, symFrame_trace h.2.1.sp4 e₂, h.2.2.1], trivial⟩
  have pre := preCT.wpDep (F := fun s t => SymAddrPost p256d.tsym s t) (by
    intro s t h
    change WP isa (.frame (.symPush .eax p256d.tsym) (.block []) (.pop .ecx 1)) s
      (SymAddrPost p256d.tsym s) ∧ WP isa (.frame (.symPush .eax p256d.tsym) (.block []) (.pop .ecx 1)) t
      (SymAddrPost p256d.tsym t)
    exact ⟨symFrame_ok p256d.tsym s h.1.sp4, symFrame_ok p256d.tsym t h.2.1.sp4⟩)
  refine pre.seq ?_
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨_, a, b, ⟨hp, hq, he, ha, hg, pk, sig⟩, P, Q⟩ := h
  have he' : s.gpr .esp = t.gpr .esp := by rw [P.gpr .esp (by decide), Q.gpr .esp (by decide), he]
  have ha' : ∀ j < 4, arg s j = arg t j := by
    intro j hj
    rw [P.arg hp.sp4 (by have := hp.sp_fit; omega), Q.arg hq.sp4 (by have := hq.sp_fit; omega), ha j hj]
  have hpub : VInputEq p256Comb s t := by
    apply VInputEq.of_bytes
    · have ps := prefix_bytesAt P hp.pk_stack (by change 65≤2^64; decide)
      have pt := prefix_bytesAt Q hq.pk_stack (by change 65≤2^64; decide)
      simpa only [ptr,P.arg (j:=0) hp.sp4 (by have:=hp.sp_fit; omega),
        Q.arg (j:=0) hq.sp4 (by have:=hq.sp_fit; omega),ps,pt] using pk
    · have ps := prefix_bytesAt P hp.sig_stack (by change 64≤2^64; decide)
      have pt := prefix_bytesAt Q hq.sig_stack (by change 64≤2^64; decide)
      simpa only [ptr,P.arg (j:=2) hp.sp4 (by have:=hp.sp_fit; omega),
        Q.arg (j:=2) hq.sp4 (by have:=hq.sp_fit; omega),ps,pt] using sig
  exact vCombBody_rel (p256Comb_ok hI) hC (p256Comb_tables hC) p256Comb_shape p256Comb_am3
    (hp.toVPre.symAddr P hp.sp4) (hq.toVPre.symAddr Q hq.sp4)
    (vPrefixTables hp P) (vPrefixTables hq Q) he' ha' hpub (by rw [P.addr, Q.addr, hg]) signComb_spG vCombBody_sp
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.Verify.X86
