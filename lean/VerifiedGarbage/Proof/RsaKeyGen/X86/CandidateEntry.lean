module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.MillerRabin.X86.Caller

/-! ### `RsaKeyGen.X86.CandidateArgContext`, which only this module used -/

section

/-! # Workspace header writes leave every original candidate argument readable -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

def argsRegion (p : BitVec 32) : Region := ⟨(p + 20#32).setWidth 64, 44⟩

structure Context (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base size
  header : 48 ≤ size
  sp : s.gpr .esp = p
  fit : p.toNat + 64 ≤ 2 ^ 32
  separate : (argsRegion p).Disjoint ⟨base, size⟩
  read : ∀ i < 11, readSrc s (.mem (arg i)) = some (inputs i)

theorem Context.address {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {i : Nat} (index : i < 11) :
    s.ea (arg i) = off (argsRegion p).base (4 * i) := by
  change addr (s.gpr .esp) (20 + 4 * i) = _
  rw [C.sp, addr_eq (by have := C.fit; omega_using [index, this])]
  have start : (p + 20#32).setWidth 64 = off (p.setWidth 64) 20 := addr_eq (by have := C.fit; omega_using [this])
  change off (p.setWidth 64) (20 + 4 * i) = off ((p + 20#32).setWidth 64) (4 * i)
  rw [start]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

theorem Context.keep {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s t : State}
    (C : Context base size p inputs s) (K : Keeps [.eax] s t) (F : Frame [⟨base, size⟩] s.mem t.mem) :
    Context base size p inputs t := by
  have spT : t.gpr .esp = p := (K.1 .esp (by decide)).trans C.sp
  have C0 : Context base size p inputs t := by
    refine ⟨C.scratch.of_keeps K (by decide), C.header, spT, C.fit, C.separate, ?_⟩
    intro i index
    have eaT : t.ea (arg i) = s.ea (arg i) := by
      change addr (t.gpr .esp) _ = addr (s.gpr .esp) _
      rw [K.1 .esp (by decide)]
    have memory : t.mem.readW (s.ea (arg i)) 32 = s.mem.readW (s.ea (arg i)) 32 := by
      rw [C.address index]
      exact F.readW (r := argsRegion p)
        (Offset.contains_base _ (by change 4 * i + 4 ≤ 44; omega_using [index]) (by omega_using [index] : 4 * i < 2 ^ 64))
        (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact C.separate) (by decide)
    have same : readSrc t (.mem (arg i)) = readSrc s (.mem (arg i)) := by
      show t.load32 (t.ea (arg i)) = s.load32 (s.ea (arg i))
      simp only [State.load32, eaT, K.2.1, K.2.2, memory]
    exact same.trans (C.read i index)
  exact C0

end VG.Proof.RsaKeyGen.X86.CandidateArgs

end

end

/-! # The cdecl candidate entry establishes its workspace from argument nine -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateArgs.lean`, which only this module imported.
section

/-! # Native argument copying retains the used-output pointer through every round -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

theorem copy_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {i : Nat} (index : i < 11) :
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
    (C : Context base size p inputs s) {n : Nat} (bound : n ≤ 11) :
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

theorem code_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) :
    WP isa code s fun t =>
      Context base size p inputs t ∧ (∀ i < 11, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      t.mem.readW (off base 44) 32 = inputs 2 ∧ Outside base 0 48 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold code
  refine WP.seq (WP.mono (copies_ok C (by decide : 11 ≤ 11)) fun a ⟨A, valuesA, Oa, Ka⟩ => ?_)
  unfold saveUsed
  refine wp_movS (readSrc_sc A.scratch (d := 8) (by have := C.header; omega)) fun b B _ => ?_
  have Kb := Ka.trans B.keeps
  have Sb := C.scratch.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (by have := C.header; omega)) (Sb.write (by have := C.header; omega)) fun t T => WP.block_nil ?_
  have Ot : Outside base 44 4 a.mem t.mem := by
    rw [T.mem, B.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Kbt := B.keeps.widen (T.keeps [])
  have F : Frame [⟨base, size⟩] a.mem t.mem := VG.Proof.MillerRabin.X86.workspaceGlobalFrame (g := ⟨base, size, 0⟩) (rs := [(44, 4)])
    (Outs.of_outside Ot (List.mem_singleton_self _))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact C.header)
  refine ⟨A.keep Kbt F, ?_, ?_, (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)), Ka.trans Kbt⟩
  · intro i index
    exact (BitVec.eq_of_toNat_eq (Ot.w32 (d := 4 * i) (Or.inl (by omega)) (by omega))).trans (valuesA i index)
  · rw [T.mem, Mem.readW_writeW_self32, B.gpr]
    exact valuesA 2 (by decide)

end VG.Proof.RsaKeyGen.X86.CandidateArgs
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.RsaKeyGen.X86.CandidateArgs

structure Entry (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s : State) : Prop where
  workspace : Ws s base size
  header : 48 ≤ size
  pointer : (inputs 9).setWidth 64 = base
  stack : StkOk p base size
  sp : s.gpr .esp = p
  fit : p.toNat + 64 ≤ 2 ^ 32
  separate : (argsRegion p).Disjoint ⟨base, size⟩
  read : ∀ i < 11, readSrc s (.mem (arg i)) = some (inputs i)

theorem enter_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (E : Entry base size p inputs s) :
    WP isa enter s fun t =>
      Context base size p inputs t ∧ (∀ i < 11, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      t.mem.readW (off base 44) 32 = inputs 2 ∧ Outside base 0 48 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  unfold enter
  refine WP.seq (wp_movS (E.read 9 (by decide)) fun a A _ => WP.block_nil ?_)
  have Sa : Scr a base size := by
    refine ⟨?_, ?_, E.workspace.nowrap, ?_⟩
    · rw [A.gpr]; exact E.pointer
    · rw [A.keeps.2.2]; exact E.workspace.wr
    · rw [A.other .esp (by decide), E.sp]; exact E.stack
  have C : Context base size p inputs a := by
    refine ⟨Sa, E.header, (A.other .esp (by decide)).trans E.sp, E.fit, E.separate, ?_⟩
    intro i index
    have address : a.ea (arg i) = s.ea (arg i) := by
      change addr (a.gpr .esp) _ = addr (s.gpr .esp) _
      rw [A.other .esp (by decide)]
    have same : readSrc a (.mem (arg i)) = readSrc s (.mem (arg i)) := by
      show a.load32 (a.ea (arg i)) = s.load32 (s.ea (arg i))
      simp only [State.load32, address, A.keeps.2.1, A.keeps.2.2, A.mem]
    exact same.trans (E.read i index)
  refine WP.mono (code_ok C) fun t ⟨T, values, usedPtr, O, K⟩ => ?_
  rw [A.mem] at O
  exact ⟨T, values, usedPtr, O, (A.keeps.mono (by decide)).widen K⟩

end VG.Proof.RsaKeyGen.X86.CandidateArgs
