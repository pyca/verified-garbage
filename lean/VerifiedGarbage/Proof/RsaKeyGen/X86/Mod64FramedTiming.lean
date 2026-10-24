module

import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayTiming
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Array
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext

/-! # Native exponent reduction keeps its frame and its word count public -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic

theorem array_noSp (n src exponent : Nat) : NoSp (VG.Impl.RsaKeyGen.X86.Mod64.array n src exponent) := by
  apply NoSp.of_all
  have bitSafe (e : Nat) : (VG.Impl.RsaKeyGen.X86.Mod64.bit e).all (fun i => !Taint.clobbers i .esp) = true := by rfl
  simp only [Code.allInstrs_eq, VG.Impl.RsaKeyGen.X86.Mod64.array,
    VG.Impl.RsaKeyGen.X86.Mod64.arrayStep, instrs, List.all_append,
    VG.Impl.RsaKeyGen.X86.Mod64.word, VG.Impl.RsaKeyGen.X86.Mod64.steps, List.all_flatMap, bitSafe]
  rfl

def FramedInput (g : ArrayGeometry) (candidate exponent : Nat) (s : State) : Prop :=
  20 ≤ (s.gpr .esp).toNat ∧ ArrayContext g candidate exponent (allocFrame 20 s)

theorem framed_pointer {g : ArrayGeometry} (v : g.Valid) {candidate exponent : Nat} {s : State}
    (S : FramedInput g candidate exponent s) (positive : 0 < exponent) :
    WP isa (.frame (.alloc 20) (VG.Impl.RsaKeyGen.X86.Mod64.array g.n g.src g.exponent) (.free 20)) s
      (fun t => t.gpr .edi = g.workspace) := by
  refine WP.frameAlloc (by decide) (by decide) (by decide) S.1 (array_noSp _ _ _) ?_
  refine WP.mono (array_ok v S.2 positive) fun t ⟨T, _, _, _⟩ => ?_
  rw [freed_gpr _ _ (by decide)]
  exact T.workspace

theorem framed_trace {g : ArrayGeometry} (v : g.Valid) {candidate exponent other otherExponent : Nat}
    (positive : 0 < exponent) (otherPositive : 0 < otherExponent) :
    RelCT isa (fun s t => FramedInput g candidate exponent s ∧ FramedInput g other otherExponent t)
      (.frame (.alloc 20) (VG.Impl.RsaKeyGen.X86.Mod64.array g.n g.src g.exponent) (.free 20))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have raw : RelCT isa (fun s t => FramedInput g candidate exponent s ∧ FramedInput g other otherExponent t)
      (.frame (.alloc 20) (VG.Impl.RsaKeyGen.X86.Mod64.array g.n g.src g.exponent) (.free 20)) (fun _ _ => True) := by
    apply RelCT.frameAlloc
    refine (array_trace v (candidate := candidate) (other := other) positive otherPositive).mono ?_ (fun _ _ _ => trivial)
    rintro _ _ ⟨s, t, ⟨S, T⟩, rfl, rfl⟩
    exact ⟨S.2, T.2⟩
  intro s t tr ur u z ⟨S, T⟩ E G
  refine ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1, ?_⟩
  apply agree_regs
  intro r mem
  change r ∈ ([.edi] : List Reg) at mem
  obtain rfl := List.mem_singleton.mp mem
  exact (wp_result (framed_pointer v S positive) E).trans (wp_result (framed_pointer v T otherPositive) G).symm

end VG.Proof.RsaKeyGen.X86.Mod64
