module

import VerifiedGarbage.Proof.Mont.X86.Compact.TimingValue
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingPair
import VerifiedGarbage.Proof.Mont.X86.Compact.Setup
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift

/-! # Public multiplicand pointers and counters for either CIOS product row -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

def rowSource (modulus : Bool) : List Instr :=
  if modulus then Compact.arrayPtr .ecx 0 else Compact.operandPtr .ecx 4 .edx

def sourceNumber (g : Geometry) (modulus : Bool) : Nat := if modulus then g.mo else g.b

theorem source_fit {g : Geometry} (v : g.Valid) (modulus : Bool) :
    sourceNumber g modulus + 4 * g.N ≤ g.L := by
  cases modulus
  · exact v.lay.b_le
  · exact v.lay.mo_le

theorem sourcePointer_relCT {g : Geometry} (v : g.Valid) (modulus : Bool) :
    RelCT isa (Pair g [.ebp, .edi]) (.block (rowSource modulus)) (Pair g [.ecx, .ebp, .edi]) := by
  have fit : 128 ≤ g.L := by have := v.lay.header; have := v.lay.scr; omega
  cases modulus
  · exact operandPointer_relCT v .ecx .edx 4 ((g.W.toNat + g.b) % 2 ^ 32) rightPtr_relCT
      (by decide) (by decide) (by decide) (by
        intro s C
        have := C.metadata.bIndex
        omega) (fun _ C => C.metadata.right) (by decide) (by decide)
  · exact arrayPointer_relCT v .ecx 0 ((g.W.toNat + g.mo) % 2 ^ 32) modulusPtr_relCT
      (by omega) (fun _ C => C.metadata.modulus) (by decide) (by decide)

theorem sourcePointer_ok {g : Geometry} (v : g.Valid) (modulus : Bool) {s : State} (C : Context g s)
    {t : State} (M : t.mem = s.mem) (hw : Ws t g.W g.L) (ha : Args t g.W g.L g.A) :
    WP isa (.block (rowSource modulus)) t fun u => PtrAt u g.W .ecx (sourceNumber g modulus) ∧
      u.mem = t.mem ∧ Keeps [.ecx, .edx] t u := by
  have fit : 128 ≤ g.L := by have := v.lay.header; have := v.lay.scr; omega
  cases modulus
  · exact Metadata.right_ptr (by rw [M]; exact C.metadata) hw ha v.base fit
  · exact Metadata.modulus_ptr (by rw [M]; exact C.metadata) hw ha v.base fit

theorem zeroCarry_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.ebp, .edi]) (.block [.mov .ebx (.imm 0)]) (Pair g [.ebp, .edi]) := by
  refine lift_readonly v (checkedProgramChange (hint := .block [])
    (τ' := timingTaint [.ebp, .edi, .ebx]) rfl rfl) ?_
  intro s
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨T.mem, T.keeps.mono (by decide)⟩

theorem setup_relCT {g : Geometry} (v : g.Valid) (modulus : Bool) (w : Nat) :
    RelCT isa (fun s t => Pair g [.ebp, .edi] s t ∧ PtrAt s g.W .edi g.S ∧ PtrAt t g.W .edi g.S ∧
        PtrAt s g.W .ebp w ∧ PtrAt t g.W .ebp w)
      (.block (([.mov .ebx (.imm 0)] : List Instr) ++ rowSource modulus ++ Compact.lenTimes .esi .eax 0))
      (fun s t => Pair g [.edi, .ebp, .ecx, .esi] s t ∧
        RowPointers g (sourceNumber g modulus) w s ∧ RowPointers g (sourceNumber g modulus) w t) := by
  have raw : RelCT isa (Pair g [.ebp, .edi])
      (.block (([.mov .ebx (.imm 0)] : List Instr) ++ rowSource modulus ++ Compact.lenTimes .esi .eax 0))
      (Pair g [.esi, .ecx, .ebp, .edi]) := by
    rw [List.append_assoc]
    exact RelCT.block_append (RelCT.seq (zeroCarry_relCT v)
      (RelCT.block_append (RelCT.seq (sourcePointer_relCT v modulus)
        (length_relCT v .esi .eax 0 rowLength_relCT (by decide) (by decide)))))
  intro s t tr ur u z H E G
  obtain ⟨trace, P⟩ := raw _ _ _ _ _ _ H.1 E G
  obtain ⟨Pu, _, _⟩ := wp_result (setup_ok v H.1.1 (rowSource modulus) (sourceNumber g modulus) w
    H.2.1 H.2.2.2.1 (fun _ M hw ha => sourcePointer_ok v modulus H.1.1 M hw ha)) E
  obtain ⟨Pz, _, _⟩ := wp_result (setup_ok v H.1.2.1 (rowSource modulus) (sourceNumber g modulus) w
    H.2.2.1 H.2.2.2.2 (fun _ M hw ha => sourcePointer_ok v modulus H.1.2.1 M hw ha)) G
  exact ⟨trace, pair_regs P (by decide), Pu, Pz⟩

end VG.Proof.Mont.X86.Compact
