module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InitControls
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Loop
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Decode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The complete native cached exponentiation, from canonical R² to ordinary g^x. -/
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
