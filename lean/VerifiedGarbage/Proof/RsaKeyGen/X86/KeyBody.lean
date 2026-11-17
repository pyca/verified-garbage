module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent

/-! ### `RsaKeyGen.X86.KeySized`, which this module and modules that import it used -/

section

/-! # Complete native import, derivation and masked export at every supported width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def BodyOutcome (E : Environment) (m : Mem) (t : State) : Prop :=
  WrittenCore E.outputs
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) t

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyEntry`, which this module and modules that import it used -/

section

/-! # Establish the native key workspace from cdecl argument sixteen -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyArgs.lean`, which only this module imported.
section

/-! # Key argument copying retains all eighteen cdecl inputs -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

theorem copy_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {i : Nat} (index : i < 18) :
    WP isa (.block (copy i)) s fun t =>
      Context base size p inputs t ∧ t.mem.readW (off base (4 * i)) 32 = inputs i ∧
      Outside base (4 * i) 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold copy
  refine wp_movS (C.read i index) fun a A _ => ?_
  have Sa := C.scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by have := C.header; omega)) (Sa.write (by have := C.header; omega)) fun t T => WP.block_nil ?_
  have O : Outside base (4 * i) 4 s.mem t.mem := by
    rw [T.mem, A.mem]
    exact writeW32_outside _ _ _ (by omega)
  have K := A.keeps.widen (T.keeps [])
  have F : Frame [⟨base, size⟩] s.mem t.mem := VG.Proof.MillerRabin.X86.workspaceGlobalFrame (g := ⟨base, size, 0⟩) (rs := [(4 * i, 4)])
    (Outs.of_outside O (List.mem_singleton_self _))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change 4 * i + 4 ≤ size; have := C.header; omega)
  exact ⟨C.keep K F, by rw [T.mem, Mem.readW_writeW_self32, A.gpr], O, K⟩

theorem copies_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {n : Nat} (bound : n ≤ 18) :
    WP isa (copies n) s fun t =>
      Context base size p inputs t ∧ (∀ i < n, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      Outside base 0 (4 * n) s.mem t.mem ∧ Keeps [.eax] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨C, by intro i index; omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | succ n ih =>
    change WP isa (.seq (copies n) (.block (copy n))) s _
    refine WP.seq (WP.mono (ih C (by omega)) fun a ⟨A, valuesA, Oa, Ka⟩ => ?_)
    refine WP.mono (copy_ok A (by omega)) fun t ⟨T, valueT, Ot, Kt⟩ => ?_
    refine ⟨T, ?_, ?_, Ka.trans Kt⟩
    · intro i index
      by_cases last : i = n
      · subst i; exact valueT
      · have same := BitVec.eq_of_toNat_eq (Ot.w32 (d := 4 * i) (by omega) (by omega))
        exact same.trans (valuesA i (by omega))
    · exact (Oa.mono (by decide) (by omega)).trans (Ot.mono (by omega) (by omega))

end VG.Proof.RsaKeyGen.X86.KeyArgs
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.RsaKeyGen.X86.CandidateArgs

structure Entry (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s : State) : Prop where
  workspace : Ws s base size
  header : 72 ≤ size
  pointer : (inputs 16).setWidth 64 = base
  stack : StkOk p base size
  sp : s.gpr .esp = p
  fit : p.toNat + 92 ≤ 2 ^ 32
  separate : (argsRegion p).Disjoint ⟨base, size⟩
  read : ∀ i < 18, readSrc s (.mem (arg i)) = some (inputs i)
  deep : DeepStk p base size

theorem enter_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (E : Entry base size p inputs s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.enter s fun t =>
      Context base size p inputs t ∧ (∀ i < 18, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      Outside base 0 72 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.Key.enter
  refine WP.seq (wp_movS (E.read 16 (by decide)) fun a A _ => WP.block_nil ?_)
  have Sa : Scr a base size := by
    refine ⟨?_, ?_, E.workspace.nowrap, ?_⟩
    · rw [A.gpr]
      exact E.pointer
    · rw [A.keeps.2.2]
      exact E.workspace.wr
    · rw [A.other .esp (by decide), E.sp]
      exact E.stack
  have C : Context base size p inputs a := by
    refine ⟨Sa, E.header, (A.other .esp (by decide)).trans E.sp, E.fit, E.separate, ?_, E.deep⟩
    intro i index
    have address : a.ea (arg i) = s.ea (arg i) := by
      change addr (a.gpr .esp) _ = addr (s.gpr .esp) _
      rw [A.other .esp (by decide)]
    have same : readSrc a (.mem (arg i)) = readSrc s (.mem (arg i)) := by
      show a.load32 (a.ea (arg i)) = s.load32 (s.ea (arg i))
      simp only [State.load32, address, A.keeps.2.1, A.keeps.2.2, A.mem]
    exact same.trans (E.read i index)
  refine WP.mono (copies_ok C (by decide : 18 ≤ 18)) fun t ⟨T, values, O, K⟩ => ?_
  rw [A.mem] at O
  exact ⟨T, values, O, (A.keeps.mono (by decide)).widen K⟩

end VG.Proof.RsaKeyGen.X86.KeyArgs

end

end

/-! # Native cdecl argument entry composes with the complete key body -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys

structure EntryInput (E : Environment) (p : BitVec 32) (s : State) : Prop where
  arguments : KeyArgs.Entry E.base E.size p E.argument s
  outWrite : ∀ i < 7, InRegions s.wr (E.outputRegion i).base (E.outputRegion i).len
  exponentRead : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len
  argsOutput : ∀ i < 7, (KeyArgs.argsRegion p).Disjoint (E.outputRegion i)

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem enter_input_ok {E : Environment} {p : BitVec 32} {s : State} (v : E.Valid) (I : EntryInput E p s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.enter s fun t =>
      Input E t ∧ Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  refine WP.mono (KeyArgs.enter_ok I.arguments) fun t ⟨C, header, O, K⟩ => ?_
  have dimensions := v.widths
  have ws : Ws t E.base E.size E.n 32 :=
    ⟨C.scratch, v.bankFit, by omega_using [dimensions], by omega_using [dimensions]⟩
  have input : Input E t := by
    refine ⟨v, ws, header, ?_, ?_⟩
    · intro i hi
      rw [K.2.2]
      exact I.outWrite i hi
    · rw [K.2.1, K.2.2]
      exact I.exponentRead
  have frame : Frame [E.workspaceRegion] s.mem t.mem :=
    outs_scratch_frame (by have := C.scratch.nowrap; omega_using [this])
      (Outs.of_outside (rs := [(0, 72)]) O (List.mem_singleton_self _))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; change 0 + 72 ≤ E.size; exact I.arguments.header)
  exact ⟨input, frame, K⟩

end VG.Proof.RsaKeyGen.X86.Key
