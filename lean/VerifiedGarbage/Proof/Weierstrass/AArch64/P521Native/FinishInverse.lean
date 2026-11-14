module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeInverse
import VerifiedGarbage.Proof.Framework.Block

/-! The final inversion is the same proved ordinary/Montgomery round trip. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field (toMontValue)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native

def finishInversePhase : Prog isa := sequence [
  .block (representationMemoryCode representationToCode 1216),
  .block outerBlock167,callInvModP,.block outerBlock168,
  .block (representationMemoryCode representationFromCode 2152)]

private theorem inverse_wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem finish_inverse_phase_wp {s : State} {Q : State → Prop} :
    WP isa finishInversePhase s Q ↔ WP isa normalizeInversePhase s Q := by
  have save : outerBlock167=[.vop (.ins .d2 .v29 0 .x30)] := by decide
  have restore : outerBlock168=[.umov .x .x30 .v29 0] := by decide
  have inversion : config.pPow=.seq (.block outerBlock167) (.seq callInvModP (.block outerBlock168)) := by
    rw [save,restore]
    rfl
  simp only [finishInversePhase,normalizeInversePhase,sequence,List.foldr_cons,List.foldr_nil,inversion]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_nil_iff] | (apply inverse_wp_post_iff; intro t)

theorem finish_inverse_phase_ok (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config)
    {s : State} {base : Addr} (hs : Scr s base 8192)
    (hM : ModOkA config.MP' 8192 config.C.p s.mem base)
    (bound : wordsVal s.mem base 1216 9<fieldPrime) :
    WP isa finishInversePhase s fun t =>
      wordsVal t.mem base 2152 9<fieldPrime ∧
      Fin.ofNat fieldPrime (wordsVal t.mem base 2152 9)=
        Fin.ofNat fieldPrime (wordsVal s.mem base 1216 9)^(fieldPrime-2) ∧
      Unch base normalizeInverseWrites s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧ t.gpr .x30=s.gpr .x30 ∧ t.v .v31=s.v .v31 ∧
      wordsVal t.mem base 1216 9=toMontValue (wordsVal s.mem base 1216 9) ∧
      (∀r∈[Reg.x27,Reg.x28],t.gpr r=s.gpr r) := by
  exact finish_inverse_phase_wp.mpr (normalize_inverse_phase_ok hc hs hM bound)

end VG.Proof.Weierstrass.AArch64.P521Native
