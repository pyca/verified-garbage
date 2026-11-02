module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundTimingPre
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCall
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # A callable round reveals no candidate, witness, exponent or result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.RoundCall VG.Impl.Mont.X86

theorem call_trace {round : Prog isa} {name : String}
    (verified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    RelCT isa (fun s t => Ready g capacity p s ∧ Ready g capacity p t) (call name round) (fun _ _ => True) := by
  refine VG.X86.RelCT.callWithReturn verified.1 verified.2.1 [below p 8] [⟨g.W, g.L⟩] ?_
  intro s t ⟨S, T⟩
  refine ⟨S.callPre v length fit far, T.callPre v length fit far, S.sp.trans T.sp.symm, ?_⟩
  rw [S.entry_eq, T.entry_eq]
  exact S.publicInputs v T fit far

theorem setup_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block [.mov .edx (.mem (at_ .esp 24))]) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

theorem setup_ready {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (I : Input g capacity p s) :
    WP isa (.block [.mov .edx (.mem (at_ .esp 24))]) s (Ready g capacity p) := by
  obtain ⟨c, b, S, odd, large, witness⟩ := I
  refine wp_movS S.ready.caller.readLen fun a A _ => WP.block_nil ?_
  have Da := WitnessMont.data_outside v S
    (show Outside g.W (g.array 6) (4 * g.words) s.mem a.mem from by rw [A.mem]; exact Outside.refl _ _ _ _)
    A.keeps (by decide) (by decide)
  refine ⟨⟨c, b, Da, odd, large, by rw [A.mem]; exact witness⟩, ?_, A.gpr⟩
  apply BitVec.eq_of_toNat_eq
  rw [A.other .edi (by decide), S.ready.scratch.edi_toNat, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by have := S.ready.scratch.nowrap; have := v.headerFit; omega)).symm

def InputPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ Input g capacity p s ∧ Input g capacity p t

theorem code_trace {round : Prog isa} {name : String}
    (verified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (noSp : NoSp round) (stack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (InputPair g capacity p) (code name round) (Pair g [.edi]) := by
  have raw : RelCT isa (InputPair g capacity p) (code name round) (fun _ _ => True) := by
    unfold code
    refine RelCT.seq (Q := fun _ _ => True) ?_ (call_trace verified v length fit far)
    intro s t tr ur u z H E G
    obtain ⟨trace, _⟩ := setup_raw _ _ _ _ _ _ H.1.2.2 E G
    exact ⟨trace, wp_result (setup_ready v H.2.1) E, wp_result (setup_ready v H.2.2) G⟩
  intro s t tr ur u z H E G
  have trace := (raw _ _ _ _ _ _ H E G).1
  have post {a : State} (I : Input g capacity p a) :
      WP isa (code name round) a fun t => Context g t ∧ Keeps [.eax, .ecx, .edx] a t := by
    obtain ⟨c, b, S, odd, large, witness⟩ := I
    exact WP.mono (code_ok (b := b) verified noSp stack v length S odd large witness fit far lengthFar)
      fun _ ⟨D, _, _, _, K⟩ => ⟨D.ready.context, K⟩
  obtain ⟨Cu, Ku⟩ := wp_result (post H.2.1) E
  obtain ⟨Cz, Kz⟩ := wp_result (post H.2.2) G
  exact ⟨trace, pair_of_keeps H.1 Cu Cz Ku Kz (by decide) (by decide)⟩

end VG.Proof.RsaKeyGen.X86.RoundCall
