module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvancedMem
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialDivisor
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Rc2.PairMem

/-! ### `RsaKeyGen.X86.SieveLoad`, which this module and modules that import it used -/

section

/-! # Load a static prime/inverse pair and reset the whole-word accumulator -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveTable.lean`, which only this module imported.
section

/-! # Read a certified prime/inverse pair from the shared static -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.TrialTable32 VG.Proof.RsaKeyGen.TrialTable32

theorem table_words {m : Mem} {p : Addr} {i : Nat} (bound : i < 1024)
    (read : m.readW p 64 = BitVec.ofNat 64 (entry i)) :
    m.readW p 32 = BitVec.ofNat 32 (tabEntry i) ∧
    m.readW (p + BitVec.ofNat 64 4) 32 = inverse (BitVec.ofNat 32 (tabEntry i)) := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Rc2.Word32.readW64_lo, read, BitVec.extractLsb'_toNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (entry_bound bound), Nat.shiftRight_zero,
      entry_low bound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
        have := (VG.Proof.RsaKeyGen.tabEntry_facts bound).2.2; omega)]
  · apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Rc2.Word32.readW64_hi, read, BitVec.extractLsb'_toNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (entry_bound bound), Nat.shiftRight_eq_div_pow,
      entry_high bound, Nat.mod_eq_of_lt (inverse (BitVec.ofNat 32 (tabEntry i))).isLt]

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

theorem loadPrime_ok {sp cursor candidate : BitVec 32} {s : State} (C : StackContext sp s)
    {i : Nat} (bound : i < 1024) (nowrap : cursor.toNat + 8 ≤ 2 ^ 32)
    (cursorSlot : s.mem.readW (off (sp.setWidth 64) 8) 32 = cursor)
    (candidateSlot : s.mem.readW (off (sp.setWidth 64) 0) 32 = candidate)
    (lowRead : InRegions (s.rd ++ s.wr) (addr cursor 0) 4)
    (highRead : InRegions (s.rd ++ s.wr) (addr cursor 4) 4)
    (table : s.mem.readW (cursor.setWidth 64) 64 = BitVec.ofNat 64 (TrialTable32.entry i)) :
    WP isa (.block (loadPrime stackSlots)) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (tabEntry i) ∧
      t.gpr .esi = TrialTable32.inverse (BitVec.ofNat 32 (tabEntry i)) ∧
      t.gpr .edi = candidate ∧ t.gpr .ebp = 0#32 ∧ t.mem = s.mem ∧
      Keeps [.edx, .ebx, .esi, .edi, .ebp] s t ∧ StackContext sp t := by
  obtain ⟨lo, hi⟩ := table_words bound table
  have address0 : addr cursor 0 = cursor.setWidth 64 := by
    rw [addr_eq (by omega_using []), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have address4 : addr cursor 4 = cursor.setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [nowrap])
  change WP isa (.block [.mov .edx (.mem (slot 8)), .mov .ebx (.mem ⟨.edx, 0⟩),
    .mov .esi (.mem ⟨.edx, 4⟩), .mov .edi (.mem (slot 0)), .mov .ebp (.imm 0)]) s _
  refine wp_movS (C.read 8 (by decide)) fun a A _ => ?_
  have edxA : a.gpr .edx = cursor := A.gpr.trans cursorSlot
  have readLow : readSrc a (.mem ⟨.edx, 0⟩) = some (BitVec.ofNat 32 (tabEntry i)) := by
    have R := readSrc_mem edxA (by rw [A.rd, A.wr]; exact lowRead)
    rw [A.mem, address0, lo] at R
    exact R
  refine wp_movS readLow fun b B _ => ?_
  have edxB : b.gpr .edx = cursor := (B.other .edx (by decide)).trans edxA
  have readHigh : readSrc b (.mem ⟨.edx, 4⟩) = some (TrialTable32.inverse (BitVec.ofNat 32 (tabEntry i))) := by
    have R := readSrc_mem edxB (by rw [B.rd, B.wr, A.rd, A.wr]; exact highRead)
    rw [B.mem, A.mem, address4, hi] at R
    exact R
  refine wp_movS readHigh fun c D _ => ?_
  have K : Keeps [.edx, .ebx, .esi] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps
  have M : c.mem = s.mem := D.mem.trans (B.mem.trans A.mem)
  have readCandidate : readSrc c (.mem (slot 0)) = some candidate := by
    rw [(C.keep K (by decide)).read 0 (by decide), M, candidateSlot]
  refine wp_movS readCandidate fun d E _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have keep : Keeps [.edx, .ebx, .esi, .edi, .ebp] s t := ((K.mono (by decide)).widen E.keeps).widen T.keeps
  refine ⟨?_, ?_, ?_, T.gpr, T.mem.trans (E.mem.trans M), keep, C.keep keep (by decide)⟩
  · rw [T.other .ebx (by decide), E.other .ebx (by decide), D.other .ebx (by decide)]
    exact B.gpr
  · rw [T.other .esi (by decide), E.other .esi (by decide)]
    exact D.gpr
  · rw [T.other .edi (by decide)]
    exact E.gpr

end VG.Proof.RsaKeyGen.X86.Sieve

end

end

/-! # One sieve iteration advances its public cursor and records exact divisibility -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveTrial.lean`, which only this module imported.
section

/-! # One static table entry tests the unchanged candidate exactly -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

theorem StateAt.trial {g : Geometry} (v : g.Valid) {c i q : Nat} {s : State}
    (H : StateAt g c i q s) (index : i < 1024) :
    WP isa (.seq (.block (loadPrime stackSlots)) (VG.Impl.RsaKeyGen.X86.Trial.divisor 4)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (c % tabEntry i = 0)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧ StackContext g.sp t := by
  have readTable : s.mem.readW ((g.cursor i).setWidth 64) 64 = BitVec.ofNat 64 (TrialTable32.entry i) := by
    rw [v.cursor_addr index]
    exact H.context.tableWords i index
  refine WP.seq (WP.mono (loadPrime_ok H.context.stack index (v.cursor_fit index) H.cursor H.candidate
    (H.context.tableRead i index 0 (by decide)) (H.context.tableRead i index 4 (by decide)) readTable)
    fun a ⟨prime, inv, ptr, zero, M, K, Ca⟩ => ?_)
  have facts := VG.Proof.RsaKeyGen.tabEntry_facts index
  have primeVal : (a.gpr .ebx).toNat = tabEntry i := by
    rw [prime, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have endValue : a.mem.readW (addr (a.gpr .esp) 4) 32 = g.candidate + BitVec.ofNat 32 (4 * (2 * g.w)) := by
    change a.mem.readW (a.ea (slot 4)) 32 = _
    rw [Ca.address 4 (by decide), M, H.ending]
    unfold Geometry.ending
    rw [show 8 * g.w = 4 * (2 * g.w) by omega]
  refine WP.mono (Trial.divisor_ok a g.candidate g.w 4 v.positive (by have := v.widthBound; omega)
    (by have := v.candidateFit; omega) (by
      intro j bound
      rw [K.2.1, K.2.2]
      exact H.context.candidateRead j bound)
    (Ca.access 4 (by decide)) endValue ptr zero
    (by rw [primeVal]; exact facts.2.1) (by rw [primeVal]; have := facts.2.2; omega)
    (by rw [primeVal]; exact facts.1) (by
      rw [primeVal, inv]
      exact VG.Proof.RsaKeyGen.TrialTable32.inverse_entry index)) fun t ⟨V, Mt, Kt⟩ => ?_
  refine ⟨?_, Mt.trans M, (K.mono (by decide)).widen Kt, Ca.keep Kt (by decide)⟩
  rw [V, M, primeVal]
  change BitVec.ofNat 32 (decide (val32 s.mem (g.candidate.setWidth 64) 0 (2 * g.w) % tabEntry i = 0)).toNat = _
  rw [H.context.candidateValue]

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

def dividesAt (c i : Nat) : Bool := decide (c % tabEntry i = 0)

theorem StateAt.step {g : Geometry} (v : g.Valid) {c i q : Nat} {s : State}
    (H : StateAt g c i q s) (index : i < 1024) (positive : 0 < q) (bound : q < 2 ^ 32) :
    WP isa (step stackSlots) s fun t =>
      StateAt g c (i + 1) (nextCount q (dividesAt c i)) t ∧
      t.mem.readW (off (g.sp.setWidth 64) 16) 32 = BitVec.ofNat 32 (dividesAt c i).toNat ∧
      t.zf = some (BitVec.ofNat 32 (nextCount q (dividesAt c i)) == 0#32) ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.Sieve.step
  apply WP.assoc
  refine WP.seq (WP.mono (H.trial v index) fun a ⟨result, M, K, Ca⟩ => ?_)
  refine WP.mono (advance_ok Ca positive bound (dividesAt c i) (by rw [M]; exact H.count) result)
    fun t ⟨_, Mt, O, Kt, _, Z⟩ => ?_
  have outside : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem := by rw [M] at O; exact O
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := K.widen Kt
  have mem : t.mem = advancedMem g.sp s.mem q (dividesAt c i) := by rw [Mt, M]
  refine ⟨⟨H.context.keep v keep (by decide) (outsideStack_frame outside), ?_, ?_, ?_, ?_⟩, ?_, Z, outside, keep⟩
  · rw [mem, advancedMem_candidate]; exact H.candidate
  · rw [mem, advancedMem_ending]; exact H.ending
  · rw [mem, advancedMem_cursor, H.cursor]
    unfold Geometry.cursor
    rw [BitVec.add_assoc]
    change g.table + (BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 8) = _
    rw [← BitVec.ofNat_add]
    congr 2 <;> omega
  · rw [mem, advancedMem_count]
  · rw [mem, advancedMem_hit]

end VG.Proof.RsaKeyGen.X86.Sieve
