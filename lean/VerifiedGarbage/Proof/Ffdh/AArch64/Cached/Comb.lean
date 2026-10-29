module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InitControls
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Step
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
/-! The complete native cached exponentiation, from canonical R² to ordinary g^x. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Loop.lean`, which only this module imported.
section

/-! The complete fixed public row schedule reconstructs the unrevealed scalar. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Spec.Rsa.FixedBaseComb (rows exponent)
open VG.Proof.Rsa.FixedBaseComb (high high_step high_top high_zero rows_pos rows_small)

theorem comb_loop (M : Mont) {p : Parameters} {bs : List Byte} {s : State}
 (start : Running p bs 0 (rows p.N) s) (positive : 0<p.N) (width : p.N≤8192)
 (size : bs.length<2^31) (widthBound : p.N≤8*bs.length) (bound : Spec.Rsa.os2ip bs<2^p.N) :
 WP isa (.loop (Comb.step M.mm) (.nonzero .x .x3)) s fun t =>
 Running p bs (Spec.Rsa.os2ip bs) 0 t ∧ StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 let x := Spec.Rsa.os2ip bs
 let d := rows p.N
 have dPositive : 0<d := rows_pos positive
 have dBound : d≤1639 := (rows_small width).1
 let I := fun n t => 0<n ∧ n≤d ∧ Running p bs (high p.N x n) n t ∧
  StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t
 refine WP.loop (M:=isa) I ?_ d s ?_
 · intro n t h
   obtain ⟨nPositive,nBound,run,stable,keep⟩ := h
   have eq : n=(n-1)+1 := by omega
   have rowBound : n-1<rows p.N := by change n-1<d;omega
   have input : Running p bs (high p.N x ((n-1)+1)) ((n-1)+1) t := by rw [←eq];exact run
   refine WP.mono (running_step M input size widthBound (by change n-1+5*d<2^63;omega) bound) ?_
   rintro u ⟨runU,stableU,indexU,keepU⟩
   have powerEq := high_step p.N x (n-1) rowBound
   rw [←powerEq] at runU
   have totalStable := stable.trans stableU
   have totalKeep : Keep mmRegs s u := (keep.trans keepU).mono (by simp)
   by_cases last : n=1
   · left
     refine ⟨?_,?_,totalStable,totalKeep⟩
     · rw [eval_nonzero,indexU]
       change some (BitVec.ofNat 64 (n-1) != 0#64)=some false
       subst n;decide
     · simpa only [last,Nat.sub_self,high_zero p.N x bound] using runU
   · right
     refine ⟨?_,n-1,by omega,by omega,by omega,runU,totalStable,totalKeep⟩
     rw [eval_nonzero,indexU]
     change some (BitVec.ofNat 64 (n-1) != 0#64)=some true
     rw [ofNat_nonzero (by omega : n-1<2^64),decide_eq_true (by omega : 0<n-1)]
 · refine ⟨dPositive,Nat.le_refl _,?_,StableHeader.refl _ _,Keep.refl _ _⟩
   simpa only [d,high_top] using start

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Decode.lean`, which only this module imported.
section

/-! Conversion out of Montgomery form produces exactly the ordinary public value. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem power_decode (M : Mont) {p : Parameters} {E : Nat} {s : State} (h : Power p E s) :
 WP isa (M.mm 6 6 7) s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P ∧
 Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound7 : wv s.mem p.B (slot p.w 7) p.w<p.P := by rw [h.one];exact p.modulusPositive
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 7<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound7) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have eq : wv t.mem p.B (slot p.w 6) p.w*2^(64*p.w)%p.P=
  Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P := by
  simpa only [h.one,h.value,Nat.mul_one,Nat.mod_mod] using productT
 have cancel := VG.Proof.Bignum.mont_cancel p.coprime eq
 rw [Nat.mod_eq_of_lt boundT] at cancel
 have decoded : wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P := by
  simpa only [VG.Proof.Bignum.powMod_eq,Nat.mod_mod] using cancel
 exact ⟨modT,decoded,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem reassoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
 WP isa (.seq a (.seq b c)) s Q ↔ WP isa (.seq (.seq a b) c) s Q := by
 exact ⟨WP.assoc',WP.assoc⟩

theorem comb_correct (M : Mont) {p : Parameters} {bs : List Byte} {s : State}
 (start : Initial p bs s) (positive : 0<p.N) (width : p.N≤8192)
 (size : bs.length<2^31) (widthBound : p.N≤8*bs.length) (bound : Spec.Rsa.os2ip bs<2^p.N)
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)) :
 WP isa (VG.Impl.Ffdh.AArch64.Cached.Comb.code M.mm) s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G (Spec.Rsa.os2ip bs) p.P ∧
 Controls p.B p.src p.ctx bs.length p.N t ∧ ReadEnv p bs t ∧
 StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.code
 rw [reassoc,WP.seq_iff]
 refine WP.mono (initial_power M start) ?_
 rintro a ⟨powerA,controlsA,readsA,stableA,keepA⟩
 rw [reassoc,WP.seq_iff]
 refine WP.mono (init_controls powerA controlsA readsA pointer) ?_
 rintro b ⟨runB,stableB,keepB⟩
 rw [WP.seq_iff]
 refine WP.mono (comb_loop M runB positive width size widthBound bound) ?_
 rintro c ⟨runC,stableC,keepC⟩
 refine WP.mono (power_decode M runC.power) ?_
 rintro t ⟨modT,valueT,frameT,keepT⟩
 exact ⟨modT,valueT,runC.controls.after_arrays frameT,runC.reads.after_arrays frameT keepT (by simp),
  ((stableA.trans stableB).trans stableC).trans (StableHeader.of_arrays frameT),
  (((keepA.trans keepB).trans keepC).trans keepT).mono (by simp)⟩

end VG.Proof.Ffdh.AArch64.Cached
