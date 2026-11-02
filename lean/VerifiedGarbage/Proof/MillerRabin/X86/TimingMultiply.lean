module

import VerifiedGarbage.Proof.MillerRabin.X86.TimingCall
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.MillerRabin.X86.CallSetup
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingCallPre

/-! # A prepared product retains the round's public base across the call -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.MillerRabin.X86

structure MulInput (g : Geometry) (capacity b : Nat) (p : BitVec 32) (s : State) : Prop where
  context : Context g s
  modulus : ∃ c, Modulus g c s.mem ∧ c % 2 = 1 ∧ val32 s.mem g.W (g.array b) g.words < c
  caller : Caller g capacity p s

theorem mulSetup_raw (b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
      (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm 6), .mov .edx (.mem (at_ .esp 24))])
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block [.mov .eax (.imm 0), .mov .ecx (.imm 6), .mov .edx (.mem (at_ .esp 24))])
    (.block []) rfl rfl rfl rfl

theorem MulInput.setup {g : Geometry} {capacity b : Nat} {p : BitVec 32} {s : State}
    (I : MulInput g capacity b p s) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm 6), .mov .edx (.mem (at_ .esp 24))])
      s (MulReady g capacity b p) := by
  refine WP.mono (mulSetup_ok I.context capacity b I.caller.readLen) fun t ⟨A, mem, K⟩ => ?_
  obtain ⟨c, M, _, lt⟩ := I.modulus
  refine ⟨I.context.keepMem K (by decide) mem, ⟨c, ?_, ?_⟩, A, ?_, ?_, ?_⟩
  · rw [mem]; exact M
  · rw [mem]; exact lt
  · rw [K.1 .esp (by decide), I.caller.sp]; exact I.caller.low
  · rw [K.1 .esp (by decide), I.caller.sp]; exact I.caller.stackFar
  · exact (K.1 .esp (by decide)).trans I.caller.sp

theorem mulY_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (right : Proof.Rsa.Mont.Operand b) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ MulInput g capacity b p s ∧ MulInput g capacity b p t)
      (mulY name code b) (fun _ _ => True) := by
  unfold mulY
  refine RelCT.seq (Q := fun _ _ => True) ?_ (mulCall_trace (p := p) verified v length right)
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, _⟩ := mulSetup_raw b _ _ _ _ _ _ H.2.2 E G
  exact ⟨trace, wp_result S.setup E, wp_result T.setup G⟩

theorem mulY_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (right : Proof.Rsa.Mont.Operand b) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ MulInput g capacity b p s ∧ MulInput g capacity b p t)
      (mulY name code b) (Pair g [.edi]) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  have trace := (mulY_trace verified v length right _ _ _ _ _ _ ⟨H, S, T⟩ E G).1
  have post (a : State) (I : MulInput g capacity b p a) :
      WP isa (mulY name code b) a fun t => Context g t ∧ Keeps [.eax, .ecx, .edx] a t := by
    obtain ⟨c, M, odd, lt⟩ := I.modulus
    refine WP.mono (mulY_ok verified noSp stack v I.context length M right odd lt I.caller.readLen
      (by rw [I.caller.sp]; exact I.caller.low) (by rw [I.caller.sp]; exact I.caller.stackFar)) ?_
    intro t R
    exact ⟨R.2.2.2.1, R.2.2.1⟩
  obtain ⟨Cu, Ku⟩ := wp_result (post s S) E
  obtain ⟨Cz, Kz⟩ := wp_result (post t T) G
  exact ⟨trace, pair_of_keeps H Cu Cz Ku Kz (by decide) (by decide)⟩

end VG.Proof.MillerRabin.X86
