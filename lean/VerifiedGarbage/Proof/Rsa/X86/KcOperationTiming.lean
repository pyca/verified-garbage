module
public import VerifiedGarbage.Proof.Rsa.X86.KcABI
public import VerifiedGarbage.Proof.Rsa.X86.KcFrames

import VerifiedGarbage.Proof.Rsa.X86.KcBodyTiming
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
import VerifiedGarbage.Proof.Rsa.X86.KcEntryTiming
import VerifiedGarbage.Proof.Rsa.X86.KcArgumentsEq
import VerifiedGarbage.Proof.Rsa.X86.KcObservations
import VerifiedGarbage.Proof.Rsa.X86.KcBounds
import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
import VerifiedGarbage.Proof.Rsa.X86.KcInstalled
import VerifiedGarbage.Proof.Rsa.X86.KcBuffers
import VerifiedGarbage.Proof.Rsa.X86.KcResources
import VerifiedGarbage.Proof.Rsa.X86.KcBodyPublic
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The complete key-validation operation leaks only the contract's declared public inputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.KeyCheck
open VG.Impl.Rsa.X86.KeyCheckRt (code)

theorem operation_trace {full : Bool} {s t : State} (a : ABI full s) (b : ABI full t)
    (args : ∀ i < scratchArg full + 2, arg s i = arg t i) (sp : s.gpr .esp = t.gpr .esp)
    (modulus : inputBytes (caller full s) s.mem 0 = inputBytes (caller full t) t.mem 0)
    (exponent : inputBytes (caller full s) s.mem 1 = inputBytes (caller full t) t.mem 1)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa (code full) s tr sf) (et : Exec isa (code full) t ur tf) : tr = ur := by
  have a1 := args 1 (by cases full <;> decide)
  have ac := args (scratchArg full) (by omega)
  have al := args (scratchArg full + 1) (by omega)
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := (entry_relCT full _ _ _ _ _ _
        ⟨sp, ac, (a.stackArgument (by omega : scratchArg full < scratchArg full + 2)).readSrc,
          (b.stackArgument (by omega : scratchArg full < scratchArg full + 2)).readSrc⟩ e1 f1).1
      obtain ⟨hs, _, ks, os⟩ := wp_result (installed_ok a) e1
      obtain ⟨ht, _, kt, ot⟩ := wp_result (installed_ok b) f1
      have hv : Inputs (caller full s) v := by
        have j := ht.argsEq args
        simpa only [caller, argumentPointer, ← a1, ← ac, ← al] using j
      have pair : Pair (caller full s) u v :=
        ⟨hs, hv, (ks.1 _ (by decide)).trans (sp.trans (kt.1 _ (by decide)).symm)⟩
      have same (i : Nat) (hi : 2 * i < scratchArg full)
          (initial : inputBytes (caller full s) s.mem i = inputBytes (caller full t) t.mem i) :
          inputBytes (caller full s) u.mem i = inputBytes (caller full s) v.mem i := by
        have ns := VG.Proof.Bignum.scratch_bytes os
          (by have := (a.inputLength hi).2; have := a.width.2.1; omega)
          (a.inApart _ (a.inputMember hi))
        have nt := VG.Proof.Bignum.scratch_bytes ot
          (by have := (b.inputLength hi).2; have := b.width.2.1; omega)
          (b.inApart _ (b.inputMember hi))
        change inputBytes (caller full s) u.mem i = inputBytes (caller full s) s.mem i at ns
        change inputBytes (caller full t) v.mem i = inputBytes (caller full t) t.mem i at nt
        have align : inputBytes (caller full s) v.mem i = inputBytes (caller full t) v.mem i := by
          simp only [inputBytes, caller, CallGeometry.buffer]
          rw [args (2 * i) (by omega), args (2 * i + 1) (by omega)]
        exact ns.trans (initial.trans (align.trans nt).symm)
      have len : Lengths (caller full s) := a.lengths_ok
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have espu : u.gpr .esp = s.gpr .esp := ks.1 _ (by decide)
          have span : argSpan full = 4 + 4 * (scratchArg full + 2) := by unfold argSpan; omega
          have fit : (u.gpr .esp).toNat + argSpan (caller full s).full ≤ 2 ^ 32 := by
            rw [espu]; change _ + argSpan full ≤ _; have := a.stackBound; omega
          have apart : ∀ r ∈ (caller full s).writes,
              Region.Disjoint ⟨(u.gpr .esp).setWidth 64, argSpan (caller full s).full⟩ r := by
            intro r hr
            simp only [CallGeometry.writes, List.mem_singleton] at hr
            subst r
            rw [espu]
            change Region.Disjoint ⟨_, argSpan full⟩ _
            rw [span]
            exact VG.X86.Taint.frame_disjoint (by have := a.stackBound; omega) a.retApart a.argsApart
          have eq2 := (body_relCT (caller full s) len _ fit apart _ _ _ _ _ _
            ⟨⟨pair, rfl⟩, same 0 (by cases full <;> decide) modulus, same 1 (by cases full <;> decide) exponent⟩ e2 f2).1
          obtain ⟨hx, kx⟩ := wp_result (body_ok hs len (a.numberBounds u.mem)) e2
          obtain ⟨hy, ky⟩ := wp_result (body_ok hv len (a.numberBounds v.mem)) f2
          have next := pair.after hx.1 hy.1 kx ky (by decide)
          have eq3 := (publicRestore_relCT _ _ _ _ _ _ next.workspace e3 f3).1
          rw [eq1, eq2, eq3]

theorem constantTime (full : Bool) : ConstantTime isa (contract full).pre
    (contract full).pub (code full) := by
  intro s t tr ur sf tf hs ht h es et
  have args := arguments_eq h
  have bytes := publicBytes_eq h
  exact operation_trace (abi_of hs) (abi_of ht) args.2 args.1 bytes.1 bytes.2 es et

end VG.Proof.Rsa.X86.KeyCheck
