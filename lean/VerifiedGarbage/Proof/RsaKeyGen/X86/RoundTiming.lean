module

public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundEntry
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundPre
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCall
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! ### `RsaKeyGen.X86.RoundTimingPre`, which only this module used -/

section

/-! # A shared round exposes only the workspace pointer, capacity and width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

def Input (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c b, Prepare.Data g c capacity p s ∧ c % 2 = 1 ∧ 3 ≤ c ∧
    val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c

def Ready (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Input g capacity p s ∧ Arguments g capacity s

theorem Ready.sp {g : Geometry} {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g capacity p s) : s.gpr .esp = p := by
  obtain ⟨c, b, D, _, _, _⟩ := S.1
  exact D.ready.caller.sp

theorem Ready.entry_eq {g : Geometry} {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g capacity p s) :
    (pushed args s).callEntry.withRegions [below p 8] [⟨g.W, g.L⟩] = entry g s := by
  unfold entry
  rw [callEntry_argAddr0, S.sp]
  rfl

theorem Ready.callPre {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (R : Ready g capacity p s) (length : g.L = 8 * capacity)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    CallPre (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96) args [below p 8] [⟨g.W, g.L⟩] s := by
  obtain ⟨c, b, S, odd, large, witness⟩ := R.1
  refine ⟨?_, ?_, ?_⟩
  · rw [R.entry_eq]
    exact entry_pre v length S R.2 odd large witness (by rw [R.sp]; exact fit) (by rw [R.sp]; exact far)
  · rw [← R.sp]
    apply Covers.of_mem
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ S.ready.context.ws.wr)
  · apply Covers.of_mem
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact List.mem_cons_of_mem _ S.ready.context.ws.wr

theorem Ready.width {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (R : Ready g capacity p s) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    Proof.Rsa.Mont.wOf (entry g s).mem g.W = g.w := by
  obtain ⟨c, b, S, _, _, _⟩ := R.1
  have F := entry_frame (by rw [R.sp]; omega_using [fit]) S.ready.scratch.nowrap
    (by rw [R.sp]; exact far.sub_right (below_sub (by decide : 12 ≤ 108) fit))
  exact (S.ready.modulus.keep v F (by simp) (by simp)).width

theorem Ready.publicInputs {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s t : State}
    (S : Ready g capacity p s) (T : Ready g capacity p t) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub (entry g s) (entry g t) := by
  have sa := fun {i} (hi : i < 2) => entry_arg S.2 (by rw [S.sp]; omega_using [fit]) hi
  have ta := fun {i} (hi : i < 2) => entry_arg T.2 (by rw [T.sp]; omega_using [fit]) hi
  obtain ⟨c, b, D, _, _, _⟩ := S.1
  have bound : g.W.toNat < 2 ^ 32 := by have := D.ready.scratch.nowrap; have := v.headerFit; omega_arith
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  have sp : (entry g s).gpr .esp = (entry g t).gpr .esp := by
    change (pushed args s).callEntry.gpr .esp = (pushed args t).callEntry.gpr .esp
    rw [callEntry_esp', callEntry_esp', S.sp, T.sp]
  have width : [Proof.Rsa.Mont.wOf (entry g s).mem g.W] = [Proof.Rsa.Mont.wOf (entry g t).mem g.W] := by
    rw [S.width v fit far, T.width v fit far]
  sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes]
  simp only [sa (by decide : 0 < 2), sa (by decide : 1 < 2), ta (by decide : 0 < 2), ta (by decide : 1 < 2), ↓reduceIte, ptr]
  exact ⟨sp, width, trivial, trivial⟩

end VG.Proof.RsaKeyGen.X86.RoundCall

end

end


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
  exact (Nat.mod_eq_of_lt (by have := S.ready.scratch.nowrap; have := v.headerFit; omega_arith)).symm

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
