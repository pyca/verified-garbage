module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvanceMath

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.Words32
/-! # Stack metadata after one sieve iteration -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveSaveHit.lean`, which only this module imported.
section

/-! # Save the trial result and form the all-ones continuation mask -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem saveHit_ok {p : BitVec 32} {s : State} (C : StackContext p s) :
    WP isa (.block (saveHit stackSlots)) s fun t =>
      t.gpr .ecx = s.gpr .eax - 1 ∧
      t.mem = s.mem.writeW (off (p.setWidth 64) 16) (s.gpr .eax) ∧
      Outside (p.setWidth 64) 16 4 s.mem t.mem ∧ Keeps [.ecx] s t ∧ StackContext p t := by
  change WP isa (.block ([.store (slot 16) .eax] ++ [.mov .ecx (.reg .eax), .alu .sub .ecx (.imm 1)])) s _
  refine WP.block_append (WP.mono (C.store 16 (by decide) .eax) fun a ⟨M, O, K, Ca⟩ => ?_)
  refine wp_movS rfl fun b B _ => wp_subS rfl fun t T _ => WP.block_nil ?_
  have keep : Keeps [.ecx] s t := ((K.mono (by decide)).widen B.keeps).trans T.keeps
  refine ⟨?_, ?_, ?_, keep, C.keep keep (by decide)⟩
  · rw [T.gpr, B.gpr, K.1 .eax (by decide)]
  · rw [T.mem, B.mem, M]
  · rw [T.mem, B.mem]; exact O

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveCursor.lean`, which only this module imported.
section

/-! # Advance the static prime/inverse pointer by one pair -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem advanceCursor_ok {p : BitVec 32} {s : State} (C : StackContext p s) :
    WP isa (.block (advanceCursor stackSlots)) s fun t =>
      t.mem = s.mem.writeW (off (p.setWidth 64) 8) (s.mem.readW (off (p.setWidth 64) 8) 32 + 8) ∧
      Outside (p.setWidth 64) 8 4 s.mem t.mem ∧ Keeps [.edx] s t ∧ StackContext p t := by
  change WP isa (.block [.mov .edx (.mem (slot 8)), .alu .add .edx (.imm 8), .store (slot 8) .edx]) s _
  refine wp_movS (C.read 8 (by decide)) fun a A _ => wp_addS rfl fun b B _ => ?_
  have K : Keeps [.edx] s b := A.keeps.trans B.keeps
  refine WP.mono ((C.keep K (by decide)).store 8 (by decide) .edx) fun t ⟨M, O, Kt, Ct⟩ => ?_
  refine ⟨?_, ?_, K.widen Kt, Ct⟩
  · rw [M, B.mem, A.mem, B.gpr, A.gpr]
  · rw [B.mem, A.mem] at O; exact O

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveCount.lean`, which only this module imported.
section

/-! # A masked public countdown stops the sieve on its first divisor -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem advanceCount_ok {p : BitVec 32} {s : State} (C : StackContext p s)
    {q : Nat} (positive : 0 < q) (bound : q < 2 ^ 32) (hit : Bool)
    (count : s.mem.readW (off (p.setWidth 64) 12) 32 = BitVec.ofNat 32 q)
    (mask : s.gpr .ecx = BitVec.ofNat 32 hit.toNat - 1) :
    WP isa (.block (advanceCount stackSlots)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (nextCount q hit) ∧
      t.mem = s.mem.writeW (off (p.setWidth 64) 12) (BitVec.ofNat 32 (nextCount q hit)) ∧
      Outside (p.setWidth 64) 12 4 s.mem t.mem ∧ Keeps [.eax] s t ∧ StackContext p t ∧
      t.zf = some (BitVec.ofNat 32 (nextCount q hit) == 0#32) := by
  change WP isa (.block [.mov .eax (.mem (slot 12)), .alu .sub .eax (.imm 1),
    .alu .and .eax (.reg .ecx), .store (slot 12) .eax, .alu .cmp .eax (.imm 0)]) s _
  refine wp_movS (C.read 12 (by decide)) fun a A _ => wp_subS rfl fun b B _ => ?_
  refine wp_logicS (.inl rfl) rfl fun c D => ?_
  have K : Keeps [.eax] s c := (A.keeps.trans B.keeps).trans D.keeps
  have M : c.mem = s.mem := D.mem.trans (B.mem.trans A.mem)
  have value : c.gpr .eax = BitVec.ofNat 32 (nextCount q hit) := by
    rw [D.gpr, B.gpr, A.gpr, count, B.other .ecx (by decide), A.other .ecx (by decide), mask]
    exact nextCount_word positive bound hit
  change WP isa (.block ([.store (slot 12) .eax] ++ [.alu .cmp .eax (.imm 0)])) c _
  refine WP.block_append (WP.mono ((C.keep K (by decide)).store 12 (by decide) .eax)
    fun d ⟨Md, O, Kd, Cd⟩ => ?_)
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  have keep : Keeps [.eax] s t := (K.widen Kd).widen (T.keeps [])
  refine ⟨?_, ?_, ?_, keep, C.keep keep (by decide), ?_⟩
  · rw [T.gpr, Kd.1 .eax (by decide)]
    exact value
  · rw [T.mem, Md, M, value]
  · rw [M] at O
    rw [T.mem]
    exact O
  · rw [Z, Kd.1 .eax (by decide), value]
    change some (BitVec.ofNat 32 (nextCount q hit) - 0#32 == 0#32) = _
    rw [BitVec.sub_zero]

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveAdvance.lean`, which only this module imported.
section

/-! # The complete sieve transition records a hit and advances one static entry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

def advancedMem (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) : Mem :=
  ((m.writeW (off (p.setWidth 64) 16) (BitVec.ofNat 32 hit.toNat)).writeW
    (off (p.setWidth 64) 8) (m.readW (off (p.setWidth 64) 8) 32 + 8)).writeW
      (off (p.setWidth 64) 12) (BitVec.ofNat 32 (nextCount q hit))

theorem advance_ok {p : BitVec 32} {s : State} (C : StackContext p s)
    {q : Nat} (positive : 0 < q) (bound : q < 2 ^ 32) (hit : Bool)
    (count : s.mem.readW (off (p.setWidth 64) 12) 32 = BitVec.ofNat 32 q)
    (result : s.gpr .eax = BitVec.ofNat 32 hit.toNat) :
    WP isa (.block (advance stackSlots)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (nextCount q hit) ∧ t.mem = advancedMem p s.mem q hit ∧
      Outside (p.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t ∧ StackContext p t ∧
      t.zf = some (BitVec.ofNat 32 (nextCount q hit) == 0#32) := by
  unfold advance
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (saveHit_ok C) fun a ⟨mask, Ma, Oa, Ka, Ca⟩ => ?_)
  refine WP.block_append (WP.mono (advanceCursor_ok Ca) fun b ⟨Mb, Ob, Kb, Cb⟩ => ?_)
  have cursor : a.mem.readW (off (p.setWidth 64) 8) 32 = s.mem.readW (off (p.setWidth 64) 8) 32 :=
    BitVec.eq_of_toNat_eq (Oa.w32 (d := 8) (by decide) (by decide))
  have countB : b.mem.readW (off (p.setWidth 64) 12) 32 = BitVec.ofNat 32 q :=
    (BitVec.eq_of_toNat_eq (Ob.w32 (d := 12) (by decide) (by decide))).trans
      ((BitVec.eq_of_toNat_eq (Oa.w32 (d := 12) (by decide) (by decide))).trans count)
  have maskB : b.gpr .ecx = BitVec.ofNat 32 hit.toNat - 1 := by
    rw [Kb.1 .ecx (by decide), mask, result]
  refine WP.mono (advanceCount_ok Cb positive bound hit countB maskB) fun t ⟨V, Mc, Oc, Kc, Ct, Z⟩ => ?_
  refine ⟨V, ?_, ?_, ((Ka.mono (by decide)).widen Kb).widen Kc, Ct, Z⟩
  · unfold advancedMem
    rw [Mc, Mb, cursor, Ma, result]
  · exact ((Oa.mono (by decide) (by decide)).trans (Ob.mono (by decide) (by decide))).trans
      (Oc.mono (by decide) (by decide))

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.Proof.Mont

theorem stack_write_ne {m : Mem} {p : BitVec 32} {a b : Nat} {value : BitVec 32}
    (apart : b + 4 ≤ a ∨ a + 4 ≤ b) (aFit : a + 4 ≤ 20) (bFit : b + 4 ≤ 20) :
    (m.writeW (off (p.setWidth 64) a) value).readW (off (p.setWidth 64) b) 32 =
      m.readW (off (p.setWidth 64) b) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ apart (by omega) (by omega)) (by decide)

theorem advancedMem_candidate (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 0) 32 = m.readW (off (p.setWidth 64) 0) 32 := by
  unfold advancedMem
  rw [stack_write_ne (by decide) (by decide) (by decide),
    stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]

theorem advancedMem_ending (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 4) 32 = m.readW (off (p.setWidth 64) 4) 32 := by
  unfold advancedMem
  rw [stack_write_ne (by decide) (by decide) (by decide),
    stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]

theorem advancedMem_cursor (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 8) 32 = m.readW (off (p.setWidth 64) 8) 32 + 8 := by
  unfold advancedMem
  rw [stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

theorem advancedMem_count (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 12) 32 = BitVec.ofNat 32 (nextCount q hit) :=
  Mem.readW_writeW_self32 _ _ _

theorem advancedMem_hit (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 16) 32 = BitVec.ofNat 32 hit.toNat := by
  unfold advancedMem
  rw [stack_write_ne (by decide) (by decide) (by decide),
    stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

end VG.Proof.RsaKeyGen.X86.Sieve
