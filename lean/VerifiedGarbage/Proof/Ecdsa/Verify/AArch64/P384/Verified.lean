module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic

import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.P384.EcdhDouble.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Lit
import VerifiedGarbage.Proof.P384.GTable9Shape
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedTable
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointPrep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedBridge
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Impl.AArch64Instrs
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide9Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointStepTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSource
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointChecks
/-!
# ECDSA verification over P-384 on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and
`Law` for its group law, which the registration file supplies: `Proof.P384.law` and
`invSound_of_toM`), so the joint loop (`Joint.verify_ok`) gives the contract's postcondition, its
doublings the register-allocated ones of ECDH (`P384.EcdhDouble.dblsOk`, `ctRD`), its generator's
multiples those of `VG_P384_GTAB` (`Proof.P384.gtabOk9`); `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register (`abiPreserved_of`).
Constant time relative to the contract's public inputs (`Joint.verify_public_ct`): the loop
branches on the digits of `u = e s⁻¹` and `v = r s⁻¹`, from the digest and the signature, and on
the coordinates of the key, and reads the entries of those digits; around them, by taint tracking,
the only branches are on loop counters and every other address is an argument plus a constant or
a counter.
-/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/GContract.lean`, which only this module imported.
section

/-!
# ECDSA verification over P-384 on AArch64 with its own table: the contract

`Contract.lean`'s contract with the verifier's table of `[m]G`, `m = 1 … 256`
(`P384Joint.p384v`, in the static `VG_P384_GTAB`) in place of the comb's: the
facts of `Spec.Ecdsa.P384.inst.verifyContract` with those constants, by name,
and the precondition the proofs are written against (`VPreT`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P384

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.Verify.AArch64 (P384Joint.p384v)
open VG.Impl.Ecdsa.AArch64 (p384)

/-- The verifier's table at its static, held, not wrapping around, and apart from the regions
`wr`. -/
def TblHeldG (s : State) (wr : List Region) : Prop :=
  (∀ i < P384Joint.p384v.combWords.length,
    s.mem.readW (s.syms P384Joint.p384v.tsym + BitVec.ofNat 64 (8 * i)) 64 =
      P384Joint.p384v.combWords.getD i 0) ∧
  (s.syms P384Joint.p384v.tsym).toNat + 8 * P384Joint.p384v.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms P384Joint.p384v.tsym, 8 * P384Joint.p384v.combWords.length⟩ r

theorem p384v_combConsts :
    P384Joint.p384v.combConsts = [(P384Joint.p384v.tsym, P384Joint.p384v.combWords)] := rfl

/-- The table has `256 · 12` words. -/
theorem p384v_combWords_length : P384Joint.p384v.combWords.length = 3072 := by
  rw [Joint.p384v_words]
  exact (Proof.Weierstrass.tcombWords_length (n := 6) (R := p384.R) (p := p384.C.p)
    (H := 256) (tbl := Impl.P384.p384G9) Proof.P384.p384G9_length Proof.P384.p384G9_rows).trans rfl

/-- The memory of the contract's witness: the table at `0x100000`. -/
@[irreducible] def satMemG : Mem := constMem 0x100000 P384Joint.p384v.combWords

theorem satMemG_held : ∀ i < P384Joint.p384v.combWords.length,
    satMemG.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = P384Joint.p384v.combWords.getD i 0 := by
  unfold satMemG
  exact constMem_held _ _ (by rw [p384v_combWords_length]; omega)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vfG (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P384.curve (bytesAt m pk 97) (hashToInt Spec.P384.curve (bytesAt m digest 48)) (bytesAt m sig 96)

def verifyGAArch64 : Contract AArch64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .x0, 97⟩
    let digest : Region := ⟨s.gpr .x1, 48⟩
    let sig : Region := ⟨s.gpr .x2, 96⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [pk, digest, sig, ⟨s.syms P384Joint.p384v.tsym, 8 * P384Joint.p384v.combWords.length⟩] ∧
      s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧
      (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeldG s [scratch]
  post s s' := (s'.gpr .x0).setWidth 32 = if vfG s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧ s₁.syms P384Joint.p384v.tsym = s₂.syms P384Joint.p384v.tsym

/-- The shared contract's precondition, from its facts. -/
theorem spec_preG {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, 97⟩, ⟨s.gpr .x1, 48⟩, ⟨s.gpr .x2, 96⟩,
      ⟨s.syms P384Joint.p384v.tsym, 8 * P384Joint.p384v.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x3, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 97⟩ ⟨s.gpr .x3, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x1, 48⟩ ⟨s.gpr .x3, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x2, 96⟩ ⟨s.gpr .x3, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 97 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 48 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 96 ≤ 2 ^ 64) (f3 : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeldG s [⟨s.gpr .x3, 8192⟩])
    (hal : (s.syms P384Joint.p384v.tsym).toNat % 64 = 0) :
    (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p384v_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2,
    f3⟩

/-- A state satisfying the precondition: the table at `0x100000`. -/
def satStateG : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem := satMemG
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

theorem sat_specG :
    (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pre
      satStateG := by
  have hl := p384v_combWords_length
  have held : ∀ i < P384Joint.p384v.combWords.length, satStateG.mem.readW (satStateG.syms P384Joint.p384v.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = P384Joint.p384v.combWords.getD i 0 := satMemG_held
  refine spec_preG (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_singleton]
    rintro r rfl; exact Region.disjoint_of_sep (by decide)

theorem impliesG : verifyGAArch64.Implies
    (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p384v_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, -, ht, hw, h1, h2, h3, -, -, -, h4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, h4, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    sig_implies_post [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi,
      AArch64.argRegs, p384v_combConsts, Abi.withConsts, verifyGAArch64, vfG]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p384v_combConsts,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, -, h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hsp, hsy⟩
  sat := ⟨satStateG, sat_specG⟩

theorem jacPublicG_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P384.inst.verifyContract
      (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pub s₁ s₂) :
    JacPublicT p384 "VG_P384_GTAB" s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P384.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P384.curve,Spec.Ecdsa.scratchWords,AArch64.abi,AArch64.argRegs,p384v_combConsts,
    Abi.withConsts] at pub
  obtain ⟨hsp,hsy,inputs,h0,h1,h2,h3⟩ := pub
  refine ⟨⟨hsp,fun r hr => ?_⟩,hsy,?_,?_,?_⟩
  · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  all_goals
    have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append,Weierstrass.length_bytesAt])
    have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  · exact front.1
  · exact front.2
  · exact parts.2

/-- The precondition the proofs are written against. -/
theorem vpreG_of {s : State} (h : verifyGAArch64.pre s) : VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords s := by
  obtain ⟨h1,h2,h3,h4,h5,h6,held,fit,hdw⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6,⟨by rw [h1]; simp [show P384Joint.p384v.tsym="VG_P384_GTAB" from rfl],held,fit,hdw _ (by simp)⟩⟩

end VG.Proof.Ecdsa.Verify.AArch64.P384
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointFinal.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

def pointRanges : List (Nat×Nat) := genW ++ winX p384 ++ winW P384Joint.K ++ PubNaf.cacheW P384Joint.K

theorem point_bounds : ∀w∈pointRanges,w.1+w.2≤8192 := by decide

theorem point_fixed : FixedOk p384 pointRanges := by unfold FixedOk; decide

/-- The joint path preserves all flag/scalar inputs to the unchanged final check. -/
theorem finalState_of_joint {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
 (h : Mid p384 s₀ base g s) (hs : Scr t base size)
 (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hu : Unch base pointRanges s.mem t.mem)
 (hx : sv p384 base t RX<p384.C.p) (hz : sv p384 base t RZ<p384.C.p) :
 FinalState p384 s₀ base g t := by
 have same (i : Nat) (hi : i∈[RM',K]) : sv p384 base t i=sv p384 base s i := by
  apply hu.wordsVal
  · have he : ∀i∈[RM',K],∀w∈pointRanges,p384.sl i+48≤w.1 ∨ w.1+w.2≤p384.sl i := by decide
    exact he i hi
  · have he : ∀i∈[RM',K],p384.sl i+48≤2^64 := by decide
    exact he i hi
 refine ⟨hs,hw.trans h.wr,hr.trans h.rd,h.fixed.unch (by decide) h.scr.nowrap point_fixed hu,
  ?_,?_,?_,hz,?_,?_,hx⟩
 · rw [hu.word (by decide) (by decide)]
   exact h.flag
 · rw [same RM' (by simp)]; exact h.rm_lt
 · change toM _ _ (sv p384 base t RM')=_
   rw [same RM' (by simp)]; exact h.rm
 · exact unch_whole (h.unch.trans hu) (by
     intro w hw
     rcases List.mem_append.mp hw with hw|hw
     · rw [List.mem_singleton.mp hw]; exact Nat.le_refl _
     · exact point_bounds w hw)
 · rw [same K (by simp)]; exact h.k
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointPoints.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

theorem points_ok (hc : CfgOk p384) (hC : Law p384.C) (hO : PrimeOrder p384.C)
 (hn : 17≤p384.C.n) (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
 (hD : ∀ base, DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 {s₀ s : State} {base : Addr} {g : Reg→BitVec 64} (hm : Mid p384 s₀ base g s)
 (ht : TblPreW P384Joint.p384v.combWords s₀ (s₀.syms "VG_P384_GTAB") base)
 {P : Point p384.C} (hP : onCurve p384.C P=true)
 (hr : Rep p384.C (tmv p384.C p384.n base s (p384.sl PX)) (tmv p384.C p384.n base s (p384.sl PY))
  (tmv p384.C p384.n base s (p384.sl ONEP)) P) :
 WP isa P384Joint.points s fun t=>FinalState p384 s₀ base g t ∧
  Rep p384.C (tmv p384.C p384.n base t (p384.sl RX)) (tmv p384.C p384.n base t (p384.sl RY))
   (tmv p384.C p384.n base t (p384.sl RZ))
   (add (mul (sv p384 base s U) (G p384.C)) (mul (sv p384 base s V) P)) := by
 have source₀ := FixedGenerator.of_pre hc hC hT ht rfl
 have source := source₀.unch hm.unch (by decide) hm.rd hm.wr hm.syms
 have hp := unitMod_pow_two hc.p_odd (64*P384Joint.K.M.n)
 have hone : P384Joint.K.one<p384.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
 have one : toM p384.C.p (2^(64*P384Joint.K.M.n)) (p384.mont 1)=1 := by
  rw [show P384Joint.K.M.n=p384.n from rfl,toM_cmont hc.toBaseCfgOk]; rfl
 have pn : p384.C.p<2^(64*P384Joint.K.M.n) := by
  simpa only [show P384Joint.K.M.n=p384.n from rfl] using hc.p_lt
 rw [P384Joint.points]
 apply WP.assoc
 refine WP.seq (WP.mono_syms (prepare_ok hc hC hm.scr hm.fixed hm.px_lt hm.py_lt hr)
   fun a ⟨sa,ma,fa,_,_,ua,ra,wa,_,za,ga⟩ sy=>?_)
 have srca := source.unch ua (by decide) ra wa sy
 have az : tmv p384.C P384Joint.K.M.n base a P384Joint.K.P.z=1 := by
  rw [show P384Joint.K.M.n=p384.n from rfl]; exact za
 have vb : sv p384 base s V<2^(64*P384Joint.K.M.n) := by
  rw [show P384Joint.K.M.n=p384.n from rfl]
  exact wordsVal_lt ..
 have ub : sv p384 base s U<2^(64*P384Joint.K.M.n) := by
  rw [show P384Joint.K.M.n=p384.n from rfl]
  exact wordsVal_lt ..
 refine WP.mono (window_source_ok (nafLayQ hc (by decide) (by decide)) hp hC hc.am3 pn hone one hO hn hP hc.onG
  (hD base) sa ma fa az vb
  ub srca ga)
  fun t ⟨st,kt,ut,_,lt,rep⟩=>?_
 have un : Unch base pointRanges s.mem t.mem := by
  simpa only [pointRanges,List.append_assoc] using ua.trans ut
 have ltr : ∀x∈[p384.sl RX,p384.sl RY,p384.sl RZ],wordsVal t.mem base x p384.n<p384.C.p := by
  simpa only [P384Joint.K,Cfg.winCfg,Cfg.MP',Cfg.pt] using lt
 have rr : Rep p384.C (tmv p384.C p384.n base t (p384.sl RX)) (tmv p384.C p384.n base t (p384.sl RY))
  (tmv p384.C p384.n base t (p384.sl RZ))
  (add (mul (sv p384 base s U) (G p384.C)) (mul (sv p384 base s V) P)) := by
  simpa only [P384Joint.K,Cfg.winCfg,Cfg.MP',Cfg.pt] using rep
 exact ⟨finalState_of_joint hm st (kt.rd.trans ra) (kt.wr.trans wa) un (ltr _ (by simp)) (ltr _ (by simp)),rr⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointMain.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
/-- The interleaved multiplication retains all validation and the original public postcondition. -/
theorem verify_ok (hc : CfgOk p384) (hC : Law p384.C) (hO : PrimeOrder p384.C)
 (hn : 17≤p384.C.n) (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
 (hD : ∀ base, Weierstrass.AArch64.DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R
   P384Joint.K.D (Weierstrass.AArch64.dblVR P384Joint.K))
 {s : State} (hp : VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords s) :
 WP isa P384Joint.verify s fun t=>
  (∀r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p384 s t :=
 verify_of_joint hc hC P384Joint.points P384Joint.verify rfl
  (fun {_} {_} {_} {_} hm ht {_} hP hr=>points_ok hc hC hO hn hT hD hm ht hP hr) hp
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointPrepTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64

theorem prepare_relCT {base : Addr}
 (h9 : PubNafWide.Prep9Checks P384Joint.KG (p384.sl U))
 (h5 : PubNaf.PrepChecks P384Joint.K (p384.sl V)) :
 RelCT isa (fun s t=>Scr s base 8192 ∧ Scr t base 8192 ∧ s.sp=t.sp ∧
  sv p384 base s U=sv p384 base t U ∧ sv p384 base s V=sv p384 base t V)
 (.seq P384Joint.prep9 (PubNaf.prep P384Joint.K (p384.sl V))) (fun _ _=>True) := by
 intro s t ts tt s' t' ⟨hs,ht,sp,hu,hv⟩ es et
 cases es with | seq gs ps =>
 cases et with | seq gt pt =>
 have regs:=PubNaf.regs_ok9 6 (by decide) (by decide)
 have tr:=PubNafWide.prep9_relCT P384Joint.KG regs (by decide) (by decide) (by decide) (by decide) h9
   _ _ _ _ _ _ ⟨hs,ht,sp,hu⟩ gs gt
 obtain ⟨_,_,xs,⟨ss,_⟩,ks,us⟩:=PubNafWide.prep9_ok P384Joint.KG regs hs
   (src:=p384.sl U) (by decide) (by decide) (by decide) (by decide)
 obtain ⟨_,_,xt,⟨st,_⟩,kt,ut⟩:=PubNafWide.prep9_ok P384Joint.KG regs ht
   (src:=p384.sl U) (by decide) (by decide) (by decide) (by decide)
 obtain ⟨_,rfl⟩:=Exec.det gs xs
 obtain ⟨_,rfl⟩:=Exec.det gt xt
 have vv : wordsVal _ base (p384.sl V) 6=wordsVal _ base (p384.sl V) 6 :=
   (us.wordsVal (Or.inl (by decide)) (by decide)).trans
    (hv.trans (ut.wordsVal (Or.inl (by decide)) (by decide)).symm)
 have tp:=PubNaf.prep_relCT P384Joint.K regs (by decide) (by decide) (by decide) (by decide) h5
   _ _ _ _ _ _ ⟨ss,st,ks.sp.trans (sp.trans kt.sp.symm),vv⟩ ps pt
 exact ⟨by rw [tr.1,tp.1],trivial⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointDigitsTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

theorem jointDigits_relCT {C : Curve} {base T : Addr} {P G A : Point C} {s₀ t₀ : State} {u v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hA : onCurve C A=true)
 (hF₁ : NafFixed P384Joint.K C base s₀ P v) (hF₂ : NafFixed P384Joint.K C base t₀ P v)
 (g₁ : GeneratorInput C base T G u s₀) (g₂ : GeneratorInput C base T G u t₀)
 (checks : DigitChecks P384Joint.K)
 (mixed : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D)
 (hj : j<385) :
 RelCT isa (fun s t=>
  (∃E,FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (digitLive P384Joint.K) E s t) ∧
  JointDoublePost P384Joint.K C base 8192 P s₀ s j A ∧
  JointDoublePost P384Joint.K C base 8192 P t₀ t j A ∧ s.syms=s₀.syms ∧ t.syms=t₀.syms)
 P384Joint.digits (fun s t=>
  (∃E,FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (loopLive P384Joint.K) E s t) ∧
  JointDigitPost P384Joint.K C base 8192 P s₀ s j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 9 u j)) ∧
  JointDigitPost P384Joint.K C base 8192 P t₀ t j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 9 u j)) ∧
  s.syms=s₀.syms ∧ t.syms=t₀.syms) := by
 intro s t ts tt s' t' ⟨⟨E,pair⟩,hs,ht,sys,syt⟩ es et
 have fs:=fixedStep_of_source hL hp hC hM3 hone hG hF₁ g₁.source g₁.bytes g₁.one
 have ft:=fixedStep_of_source hL hp hC hM3 hone hG hF₂ g₂.source g₂.bytes g₂.one
 obtain ⟨_,_,exs,postS⟩:=digits_ok hL hp hC hM3 hone hP hA hF₁ fs hj sys hs
 obtain ⟨_,_,ext,postT⟩:=digits_ok hL hp hC hM3 hone hP hA hF₂ ft hj syt ht
 obtain ⟨_,rfl⟩:=Exec.det es exs
 obtain ⟨_,rfl⟩:=Exec.det et ext
 have result : ts=tt ∧ ∃E,FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K)
   (loopLive P384Joint.K) E s' t' := by
  cases es with
  | seq ps gs => cases et with
    | seq pt gt =>
     obtain ⟨he,E',hpair⟩:=digit_relCT hL hp hone checks hF₁ hF₂ hj
      _ _ _ _ _ _ ⟨pair,hs.st,ht.st,hs.cache,ht.cache,hs.x19,ht.x19⟩ ps pt
     obtain ⟨_,_,e1,h1⟩:=jointDigit_ok hL hp hC hM3 hone hP hA hs.st hF₁ hs.cache hj hs.x19 hs.dlt hs.d
     obtain ⟨_,_,e2,h2⟩:=jointDigit_ok hL hp hC hM3 hone hP hA ht.st hF₂ ht.cache hj ht.x19 ht.dlt ht.d
     obtain ⟨_,rfl⟩:=Exec.det ps e1
     obtain ⟨_,rfl⟩:=Exec.det pt e2
     have a:=g₁.current hj ((Exec.syms ps).trans sys) h1
     have b:=g₂.current hj ((Exec.syms pt).trans syt) h2
     have pair' : FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K)
       (loopLive P384Joint.K) E' _ _ := hpair.sub (by decide)
     have ev : E' (p384.sl ONEP)=1 := by
      rw [←pair'.left.val _ (by decide)]
      exact a.2
     obtain ⟨hg,res⟩:=fixedDigit_relCT hL hC hp hone ev hj mixed
      _ _ _ _ _ _ ⟨pair',a.1,b.1⟩ gs gt
     exact ⟨by rw [he,hg],res⟩
 exact ⟨result.1,result.2,postS,postT,(Exec.syms es).trans sys,(Exec.syms et).trans syt⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointLoopTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ed25519.AArch64 (read_x)
open Spec.Weierstrass

theorem jointLoop_relCT {C : Curve} {base T : Addr} {P G : Point C} {s₀ t₀ : State} {u v : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hF₁ : NafFixed P384Joint.K C base s₀ P v) (hF₂ : NafFixed P384Joint.K C base t₀ P v)
 (g₁ : GeneratorInput C base T G u s₀) (g₂ : GeneratorInput C base T G u t₀)
 (checks : StepChecks P384Joint.K)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) P384Joint.double)
 (mixed : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D) :
 RelCT isa (JointRelation C base P G u v 384 s₀ t₀)
  (.loop P384Joint.step (.nonzero .x .x19)) (JointRelation C base P G u v 0 s₀ t₀) := by
 let I := fun j s t=>1≤j ∧ j≤384 ∧ JointRelation C base P G u v j s₀ t₀ s t
 have step : ∀j,RelCT isa (I j) P384Joint.step (fun s t=>
   eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
   (eval (.nonzero .x .x19) s=some false → JointRelation C base P G u v 0 s₀ t₀ s t) ∧
   (eval (.nonzero .x .x19) s=some true → ∃n<j,I n s t)) := by
  intro j
  by_cases hj : 1≤j
  · by_cases hn : j≤384
    · have e : j-1+1=j := by omega
      refine (jointStep_relCT hL hp hC hM3 hone hP hG hF₁ hF₂ g₁ g₂ checks hD hct mixed
       (j:=j-1) (by omega)).mono (P':=I j) (fun _ _ h=>by rw [e]; exact h.2.2) ?_
      intro s t h
      have xs:=h.2.1.x19
      have xt:=h.2.2.1.x19
      refine ⟨by simp only [eval,State.read,xs,xt],fun he=>?_,fun he=>?_⟩
      · have hz : j-1=0 := by
         by_contra hz
         have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
          rw [bne_iff_ne]
          intro hh
          have hh':=congrArg BitVec.toNat hh
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
          exact hz hh'
         have ht : eval (.nonzero .x .x19) s=some true := by
          change some (s.read .x .x19 != 0)=some true
          rw [read_x,xs,hb]
         rw [ht] at he
         cases he
        simpa only [hz] using h
      · have hz : j-1≠0 := by
         intro hz
         simp only [eval,State.read,xs,hz] at he
         cases he
        exact ⟨j-1,by omega,by omega,by omega,h⟩
    · exact RelCT.of_false (fun _ _ h=>hn h.2.1)
  · exact RelCT.of_false (fun _ _ h=>hj h.1)
 exact (RelCT.loop I step 384).mono (fun _ _ h=>⟨by decide,by decide,h⟩) (fun _ _ h=>h)
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointWindowTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

theorem jointWindow_relCT {C : Curve} {base T : Addr} {u v : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hpn : C.p<2^(64*P384Joint.K.M.n)) (hone_lt : P384Joint.K.one<C.p)
 (hone : toM C.p (2^(64*P384Joint.K.M.n)) P384Joint.K.one=1)
 (hc : WindowChecks P384Joint.K)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) P384Joint.double)
 (mixed : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D)
 (hO : PrimeOrder C) (hn17 : 17≤C.n) {P G : Point C} (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hv : v<2^(64*P384Joint.K.M.n)) (hu : u<2^(64*P384Joint.K.M.n)) {E : Nat→Fe C}
 (hz1 : E P384Joint.K.P.z=1) :
 RelCT isa (fun s t=>FieldPair P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (winRo P384Joint.K) E s t ∧
  (Scr s base 8192 ∧ ModOkA P384Joint.K.M 8192 C.p s.mem base ∧ NafFixed P384Joint.K C base s P v) ∧
  (Scr t base 8192 ∧ ModOkA P384Joint.K.M 8192 C.p t.mem base ∧ NafFixed P384Joint.K C base t P v) ∧
  GeneratorInput C base T G u s ∧ GeneratorInput C base T G u t)
 P384Joint.window (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  have hn0 := hL.win.n0
  intro s t ts tt s' t' ⟨pair, ⟨hs₁, hM₁, hF₁⟩, ⟨hs₂, hM₂, hF₂⟩,g₁,g₂⟩ es et
  rw [P384Joint.window] at es et
  cases es with | seq e1 es => cases es with | seq ec es => cases es with | seq e2 es =>
  cases es with | seq e3 es => cases es with | seq e4 e5 =>
  cases et with | seq f1 et => cases et with | seq fc et => cases et with | seq f2 et =>
  cases et with | seq f3 et => cases et with | seq f4 f5 =>
  -- The table.
  have hPz : P384Joint.K.P.z ∈ winRo P384Joint.K := by simp [winRo]
  obtain ⟨tr1, E1, p1⟩ := table_relCT hL hp hc.table _ _ _ _ _ _ pair e1 f1
  obtain ⟨_, _, x1, S1⟩ := table_ok hL hp hC hM3 hO hn17 hP hs₁ hM₁ hF₁
    ((pair.left.val _ hPz).trans hz1)
  obtain ⟨_, rfl⟩ := Exec.det e1 x1
  obtain ⟨_, _, y1, T1⟩ := table_ok hL hp hC hM3 hO hn17 hP hs₂ hM₂ hF₂
    ((pair.right.val _ hPz).trans hz1)
  obtain ⟨_, rfl⟩ := Exec.det f1 y1
  -- The cache, from which each run's loop goes on.
  have hsub : ∀ x ∈ winRo P384Joint.K ++ winTblSlots P384Joint.K, x ∈ tblLive P384Joint.K 8 := by
    intro x hx
    simp only [tblLive, winTblSlots, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inr hx
  have trc := (cache_relCT hL hp hc (P := P) _ _ _ _ _ _ ⟨p1.sub hsub, S1.tbl, T1.tbl⟩ ec fc).1
  have pc := (cache_relCT hL hp hc (P := P) _ _ _ _ _ _ ⟨p1.sub hsub, S1.tbl, T1.tbl⟩ ec fc).2
  have side : ∀ {a₀ a a' : State} {ta : List Leak}, Scr a₀ base 8192 → NafFixed P384Joint.K C base a₀ P v →
      NSt P384Joint.K C base 8192 P a₀ a → Exec isa (PubNaf.cache P384Joint.K) a ta a' →
      NafFixed P384Joint.K C base a' P v ∧ NSt P384Joint.K C base 8192 P a' a' ∧ CacheOk P384Joint.K C base a' ∧
        KeepRegs (nafClob P384Joint.K.M.n) a₀ a' ∧ Unch base (winW P384Joint.K ++ cacheW P384Joint.K) a₀.mem a'.mem := by
    intro a₀ a a' ta h₀ hF S ea
    obtain ⟨_, _, xa, sc, kc, Uc, Mc, Tc, Cc⟩ := cacheTo_ok hL hp S.scr S.mod S.tbl 8 (Nat.le_refl _)
    obtain ⟨_, rfl⟩ := Exec.det ea xa
    have U : Unch base (winW P384Joint.K ++ cacheW P384Joint.K) a₀.mem a'.mem := (S.unch.trans Uc).mono fun w hw => by
      simp only [List.mem_append] at hw ⊢
      rcases hw with hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
      · exact Or.inl (loopW_sub P384Joint.K w hw)
    exact ⟨hF.rebase hL U h₀.nowrap, ⟨sc, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, Mc, Tc⟩, Cc,
      S.keep.trans kc, U⟩
  obtain ⟨G₁, Sc1, Cc1, kc₁, uc₁⟩ := side hs₁ hF₁ S1 ec
  obtain ⟨G₂, Tc1, Cc2, kc₂, uc₂⟩ := side hs₂ hF₂ T1 fc
  have gen₁:=g₁.rebase uc₁ kc₁.rd kc₁.wr ((Exec.syms ec).trans (Exec.syms e1))
  have gen₂:=g₂.rebase uc₂ kc₂.rd kc₂.wr ((Exec.syms fc).trans (Exec.syms f1))
  -- `D = O` and the count.
  obtain ⟨tr2, ⟨E2, p2⟩, a19, b19⟩ := head_relCT hL hone_lt hc _ _ _ _ _ _ pc e2 f2
  obtain ⟨_, _, x2, S2, C2, _, Dl2, DJ2⟩ := head_ok hL hone_lt G₁ Sc1 Cc1 hv
  obtain ⟨_, rfl⟩ := Exec.det e2 x2
  obtain ⟨_, _, y2, T2, D2, _, Dl2', DJ2'⟩ := head_ok hL hone_lt G₂ Tc1 Cc2 hv
  obtain ⟨_, rfl⟩ := Exec.det f2 y2
  have top := jointPoint_topB (B:=64*P384Joint.K.M.n) (u:=u) (v:=v) G P hu hv 9
  change jointPoint G P u v 385 9=.infinity at top
  have hz:=Naf5.residual_zero_top hv
  change Naf5.residual v 385=0 at hz
  have dj {a : State} (h : InvJ C (tmv C P384Joint.K.M.n base a P384Joint.K.D.x)
    (tmv C P384Joint.K.M.n base a P384Joint.K.D.y) (tmv C P384Joint.K.M.n base a P384Joint.K.D.z)
    (mul (2*Naf5.residual v 385) P)) :
    InvJ C (tmv C P384Joint.K.M.n base a P384Joint.K.D.x)
    (tmv C P384Joint.K.M.n base a P384Joint.K.D.y) (tmv C P384Joint.K.M.n base a P384Joint.K.D.z)
    (add (jointPoint G P u v 385 9) (jointPoint G P u v 385 9)) := by
      rw [top]
      rw [hz,Nat.mul_zero,Spec.Weierstrass.mul] at h
      exact h
  obtain ⟨tr3, p3, I3, J3, sy3, ty3⟩:=jointDigits_relCT hL hp hC hM3 hone_lt hP hG
    (hC.onCurve_add (jointPoint_curve hC hG hP u v 385 9) (jointPoint_curve hC hG hP u v 385 9))
    G₁ G₂ gen₁ gen₂ hc.step.digit mixed (j:=384) (by decide)
    _ _ _ _ _ _ ⟨⟨E2,p2⟩,⟨S2,a19,Dl2,dj DJ2,C2⟩,⟨T2,b19,Dl2',dj DJ2',D2⟩,
      Exec.syms e2,Exec.syms f2⟩ e3 f3
  rw [jointPoint_step hC hG hP u v 384 9] at I3 J3
  obtain ⟨tr4, ⟨E4,p4⟩, I4, J4, _, _⟩:=jointLoop_relCT hL hp hC hM3 hone_lt hP hG
    G₁ G₂ gen₁ gen₂ hc.step hD hct mixed _ _ _ _ _ _ ⟨p3,I3,J3,sy3,ty3⟩ e4 f4
  -- Projective coordinates.
  have tr5 := hc.finish _ _ _ _ _ _ trivial trivial
    ⟨p4.sp, fun q hq => pub_x0 p4 (Taint.mem_ofRegs.mp hq)⟩ e5 f5
  obtain ⟨_, _, x5, S5, -, -⟩ := jointFinish_ok hL hp hC hpn hone_lt hone G₁ I4.st I4.rlt I4.r
  obtain ⟨_, rfl⟩ := Exec.det e5 x5
  obtain ⟨_, _, y5, T5, -, -⟩ := jointFinish_ok hL hp hC hpn hone_lt hone G₂ J4.st J4.rlt J4.r
  obtain ⟨_, rfl⟩ := Exec.det f5 y5
  refine ⟨by rw [tr1, trc, tr2, tr3, tr4, tr5], ?_, fun q hq => ?_⟩
  · exact (Exec.rdwr x5).2.2.trans (p4.sp.trans (Exec.rdwr y5).2.2.symm)
  · simp only [Taint.mem_ofRegs, List.mem_singleton] at hq
    subst hq
    exact S5.scr.x0.trans T5.scr.x0.symm

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointPointsTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

structure JointWinPublic (base T : Addr) (P : Point p384.C) (u v : Nat) (s t : State) : Prop where
 win : NafWinPublic p384 base P v s t
 leftU : sv p384 base s U=u
 rightU : sv p384 base t U=u
 sourceLeft : FixedGenerator p384.C base 8192 (G p384.C) T s
 sourceRight : FixedGenerator p384.C base 8192 (G p384.C) T t

theorem jointMul_relCT (hc : CfgOk p384) (hC : Law p384.C)
 (hO : PrimeOrder p384.C) (hn17 : 17≤p384.C.n)
 (h9 : PubNafWide.Prep9Checks P384Joint.KG (p384.sl U))
 (h5 : PubNaf.PrepChecks P384Joint.K (p384.sl V))
 (hwin : WindowChecks P384Joint.K)
 (hD : ∀ base, DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) P384Joint.double)
 (mixed : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D)
 {base T : Addr} {P : Point p384.C} {u v : Nat} (hP : onCurve p384.C P=true) :
 RelCT isa (JointWinPublic base T P u v) P384Joint.points
 (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
 rw [P384Joint.points]
 apply RelCT.assoc
 intro s t ts tt s' t' h es et
 obtain ⟨_,fs⟩:=h.win.left.fixed
 obtain ⟨_,ft⟩:=h.win.right.fixed
 cases es with | seq ps ws =>
 cases et with | seq pt wt =>
 have he:=(prepare_relCT h9 h5 _ _ _ _ _ _
   ⟨h.win.left.scr,h.win.right.scr,h.win.sp,h.leftU.trans h.rightU.symm,
     h.win.left.scalar.trans h.win.right.scalar.symm⟩ ps pt).1
 obtain ⟨_,_,xs,ss,ms,Fs,vs,sps,us,rs,ws',_,zs,gs⟩:=
   prepare_ok hc hC h.win.left.scr fs h.win.left.px h.win.left.py h.win.left.rep
 obtain ⟨_,rfl⟩:=Exec.det ps xs
 obtain ⟨_,_,xt,st,mt,Ft,vt,spt,ut,rt,wt',_,zt,gt⟩:=
   prepare_ok hc hC h.win.right.scr ft h.win.right.px h.win.right.py h.win.right.rep
 obtain ⟨_,rfl⟩:=Exec.det pt xt
 rw [h.win.left.scalar] at Fs
 rw [h.win.right.scalar] at Ft
 rw [h.leftU] at gs
 rw [h.rightU] at gt
 have Is : Inv P384Joint.K.M base 8192 p384.C.p (·∈winSlots P384Joint.K) (winRo P384Joint.K)
   (tmv p384.C P384Joint.K.M.n base _) _ := ⟨ss,ms,winRo_slots _,Fs.ro_lt,fun _ _=>rfl⟩
 have It : Inv P384Joint.K.M base 8192 p384.C.p (·∈winSlots P384Joint.K) (winRo P384Joint.K)
   (tmv p384.C P384Joint.K.M.n base _) _ := ⟨st,mt,winRo_slots _,Ft.ro_lt,fun _ _=>rfl⟩
 have pair : FieldPair P384Joint.K.M base 8192 p384.C.p (·∈winSlots P384Joint.K) (winRo P384Joint.K) _ _ _ :=
   ⟨Is,It.congr_env (by
     intro x hx
     simp only [show P384Joint.K.M.n=p384.n from rfl]
     exact (vt x hx).trans ((h.win.fields x hx).symm.trans (vs x hx).symm)),
    sps.trans (h.win.sp.trans spt.symm)⟩
 have vb : v<2^(64*P384Joint.K.M.n) := by
   rw [←h.win.left.scalar,show P384Joint.K.M.n=p384.n from rfl]
   exact wordsVal_lt ..
 have ub : u<2^(64*P384Joint.K.M.n) := by
   rw [←h.leftU,show P384Joint.K.M.n=p384.n from rfl]
   exact wordsVal_lt ..
 have zs':=zs
 have zt':=zt
 simp only [P384Joint.K,Cfg.winCfg,Cfg.pt] at zs' zt'
 rw [←show P384Joint.K.M.n=p384.n from rfl] at zs' zt'
 have genS : GeneratorInput p384.C base T (G p384.C) u _ :=
   ⟨h.sourceLeft.unch us (by decide) rs ws' (Exec.syms ps),gs,zs'⟩
 have genT : GeneratorInput p384.C base T (G p384.C) u _ :=
   ⟨h.sourceRight.unch ut (by decide) rt wt' (Exec.syms pt),gt,zt'⟩
 have one : toM p384.C.p (2^(64*P384Joint.K.M.n)) (p384.mont 1)=1 := by
   rw [show P384Joint.K.M.n=p384.n from rfl,toM_cmont hc.toBaseCfgOk]; rfl
 obtain ⟨hw,post⟩:=jointWindow_relCT (nafLayQ hc (by decide) (by decide))
   (unitMod_pow_two hc.p_odd (64*P384Joint.K.M.n)) hC hc.am3 (by simpa only [show P384Joint.K.M.n=p384.n from rfl] using hc.p_lt)
   (Nat.mod_lt _ (by have := hc.p_ge; omega)) one hwin (hD base) hct mixed hO hn17 hP hc.onG vb ub zs'
   _ _ _ _ _ _ ⟨pair,⟨ss,ms,Fs⟩,⟨st,mt,Ft⟩,genS,genT⟩ ws wt
 exact ⟨by rw [he,hw],post⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointBoundaryTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

theorem points_relCT (hc : CfgOk p384) (hC : Law p384.C)
 (hO : PrimeOrder p384.C) (hn : 17≤p384.C.n)
 (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
 (h9 : PubNafWide.Prep9Checks P384Joint.KG (p384.sl U))
 (h5 : PubNaf.PrepChecks P384Joint.K (p384.sl V))
 (hwin : WindowChecks P384Joint.K)
 (hD : ∀ base, DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) P384Joint.double)
 (mixed : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D)
 {s₀ t₀ : State} (hs : VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords s₀)
 (ht : VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords t₀) :
 RelCT isa (JointBoundaryT p384 "VG_P384_GTAB" s₀ t₀) P384Joint.points (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
 intro s t ts tt s' t' ⟨pub,⟨gs,ms⟩,⟨gt,mt⟩,sp⟩ es et
 let P:=peerPt p384 (s₀.mem (s₀.gpr .x0)=4) (keyX p384 s₀) (keyY p384 s₀)
 have hP : onCurve p384.C P=true:=peerPt_onCurve hc _ _ _
 have peer:=mid_peer_public pub ms mt
 have wins : NafWinPublic p384 (s₀.gpr .x3) P (publicV p384 s₀) s t := by
   refine ⟨⟨ms.scr,⟨gs,ms.fixed⟩,ms.px_lt,ms.py_lt,ms.peer_rep hc hC,mid_publicV ms⟩,
     ⟨mt.scr,⟨gt,mt.fixed⟩,mt.px_lt,mt.py_lt,?_,(mid_publicV mt).trans pub.v.symm⟩,
     sp,peer.1,peer.2⟩
   change Rep _ _ _ _ (peerPt p384 _ _ _)
   rw [pub.peerPoint]
   exact mt.peer_rep hc hC
 have base : s₀.gpr .x3=t₀.gpr .x3 := pub.ptrs.2 .x3 (by decide)
 have tableT : TblPreW P384Joint.p384v.combWords t₀ (s₀.syms "VG_P384_GTAB") (s₀.gpr .x3) := by
   rw [base,pub.table]
   exact ht.tbl
 have srcS:=(FixedGenerator.of_pre hc hC hT hs.tbl rfl).unch ms.unch (by decide) ms.rd ms.wr ms.syms
 have symT : t₀.syms "VG_P384_GTAB"=s₀.syms "VG_P384_GTAB" := pub.table.symm
 have srcT:=(FixedGenerator.of_pre hc hC hT tableT symT).unch mt.unch (by decide) mt.rd mt.wr mt.syms
 exact jointMul_relCT hc hC hO hn h9 h5 hwin hD hct mixed hP _ _ _ _ _ _
   ⟨wins,mid_publicU ms,(mid_publicU mt).trans pub.u.symm,srcS,srcT⟩ es et
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointTopTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass.AArch64
theorem verify_cut_generic {c : Cfg} {points : Prog isa} {s s' : State} {t : List Leak}
    (he : Exec isa (.seq (.block (Cfg.args c)) <| .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
      .seq (.block (Cfg.loadS c)) <| .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
      .seq (Impl.Ecdh.AArch64.Cfg.validate c) <| .seq (Cfg.scalars c) <|
      .seq c.nPow <| .seq (Cfg.uv c) <| .seq points (Cfg.tail c)) s t s') :
    ∃ a b tp tq tt,Exec isa (jointPrefix c) s tp a ∧
      Exec isa points a tq b ∧
      Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.tail c) b tt s' ∧ t=tp++tq++tt := by
  cases he with
  | seq e0 e => cases e with
    | seq e1 e => cases e with
      | seq e2 e => cases e with
        | seq e3 e => cases e with
          | seq e4 e => cases e with
            | seq e5 e => cases e with
              | seq e6 e => cases e with
                | seq e7 e => cases e with
                  | seq ep et =>
                    have nil : ∀ a : State,Exec isa (.block []) a [] a := fun _ => .block rfl
                    have pre := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4
                      (.seq e5 (.seq e6 (.seq e7 (nil _))))))))
                    exact ⟨_,_,_,_,_,pre,ep,et,by simp only [List.append_nil,List.append_assoc]⟩

theorem jointVerify_cut {s s' : State} {t : List Leak}
    (he : Exec isa Impl.Ecdsa.Verify.AArch64.P384Joint.verify s t s') :
    ∃ a b tp tq tt,Exec isa (jointPrefix p384) s tp a ∧
      Exec isa Impl.Ecdsa.Verify.AArch64.P384Joint.points a tq b ∧
      Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.tail p384) b tt s' ∧ t=tp++tq++tt := by
  exact verify_cut_generic he

/-- The new points stage has the same public leakage boundary as the original verifier. -/
theorem jointVerify_ct_of_points
    (hc : CfgOk p384)
    (hbefore : ConstantTime isa (fun _ => True)
      (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (jointPrefix p384))
    (hpoints : ∀ s₀ t₀,VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords s₀ →
      VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords t₀ →
      RelCT isa (JointBoundaryT p384 "VG_P384_GTAB" s₀ t₀) Impl.Ecdsa.Verify.AArch64.P384Joint.points
        (AArch64.Taint.Agree (Taint.ofRegs [.x0])))
    (htail : FieldCT (Impl.Ecdsa.Verify.AArch64.Cfg.tail p384)) :
    ConstantTime isa (VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords) (JacPublicT p384 "VG_P384_GTAB")
      Impl.Ecdsa.Verify.AArch64.P384Joint.verify := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  obtain ⟨a₁,b₁,tp₁,tq₁,tt₁,ep₁,eq₁,et₁,h₁⟩ := jointVerify_cut e₁
  obtain ⟨a₂,b₂,tp₂,tq₂,tt₂,ep₂,eq₂,et₂,h₂⟩ := jointVerify_cut e₂
  have ht := hbefore _ _ _ _ _ _ trivial trivial pub.ptrs ep₁ ep₂
  obtain ⟨_,_,wp₁,m₁⟩ := jointPrefix_ok hc pre₁
  obtain ⟨_,_,wp₂,m₂⟩ := jointPrefix_ok hc pre₂
  obtain ⟨_,rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_,rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3=s₂.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  have sp : a₁.sp=a₂.sp := (Exec.rdwr ep₁).2.2.trans
    (pub.ptrs.1.trans (Exec.rdwr ep₂).2.2.symm)
  have boundary : JointBoundaryT p384 "VG_P384_GTAB" s₁ s₂ a₁ a₂ := by
    refine ⟨pub,m₁,?_,sp⟩
    rw [base]; exact m₂
  obtain ⟨hq,tailpub⟩ := hpoints s₁ s₂ pre₁ pre₂ _ _ _ _ _ _ boundary eq₁ eq₂
  have hf := htail _ _ _ _ _ _ trivial trivial tailpub et₁ et₂
  rw [h₁,h₂,ht,hq,hf]

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem verify_public_ct (hc : CfgOk p384) (hC : Law p384.C) (hO : PrimeOrder p384.C)
 (hn : 17≤p384.C.n) (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
 (hD : ∀ base, VG.Proof.Weierstrass.AArch64.DblSpec P384Joint.K p384.C base 8192 P384Joint.double
   P384Joint.K.R P384Joint.K.D (VG.Proof.Weierstrass.AArch64.dblVR P384Joint.K)) :
 ConstantTime isa (VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords) (JacPublicT p384 "VG_P384_GTAB")
  P384Joint.verify := by
 apply jointVerify_ct_of_points hc before_ct
 · intro s₀ t₀ hs ht
   exact points_relCT hc hC hO hn hT prep9_checks prep5_checks window_checks hD double_ct mixed_checks hs ht
 · exact tail_ct
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

/-- The allocated doubling does what the loop's must. -/
theorem dbl_spec (hI : Weierstrass.AArch64.InvSounds) (base : Addr) :
    Weierstrass.AArch64.DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R
      P384Joint.K.D (Weierstrass.AArch64.dblVR P384Joint.K) :=
  (P384.EcdhDouble.dblsOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI))
    (Ecdh.AArch64.winAQ (p384_ok hI)) (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _) base _ rfl).1

theorem verify_callsKeep : CallsKeep verifyP384 := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP384 := by lit_decide

theorem verify_keepsV : verifyP384.allInstrs keepsV = true := by lit_decide

theorem verify_a64 (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start)
    (s : State) (hs : verifyGAArch64.pre s) :
    ∃ t s', Exec isa verifyP384 s t s' ∧ abiPreserved s s' ∧ verifyGAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := Joint.verify_ok (p384_ok hI) hL hO (by decide) hT (dbl_spec hI)
    (vpreG_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_callsKeep verify_untouched verify_keepsV hsv, hpost⟩

theorem verify_ct (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start) :
    ConstantTime isa
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pre
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pub
      verifyP384 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact Joint.verify_public_ct (p384_ok hI) hL hO (by decide) hT (dbl_spec hI) _ _ _ _ _ _
    (vpreG_of (impliesG.pre _ pre₁)) (vpreG_of (impliesG.pre _ pre₂)) (jacPublicG_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start) :
    Verified AArch64.target verifyP384
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hO hI hT, impliesG.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_a64 hL hO hI hT s (impliesG.pre _ hs)
  exact ⟨t, s', he, ha, impliesG.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64.P384
