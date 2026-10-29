module

public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyParts
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.KeyCopyPart
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Framework.KernelRfl
/-! # Consecutive key copies keep their source addresses public -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/KeyCopyTiming.lean`, which only this module imported.
section

/-! # Key copies reveal public addresses and component lengths only -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def keyCopyTaint : VG.X86.Taint.T :=
  { workspaceTaint false with regs := .ofList [.edi, .esi, .edx, .ecx] }

theorem keyCopyPart_relCT (input : Pointer) (len : Nat) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s input = pointerValue base t input ∧ s.gpr .edx = t.gpr .edx)
      (Generate.copyPart input len) (VG.X86.Taint.Agree keyCopyTaint) := by
  unfold Generate.copyPart
  refine RelCT.seq (R := VG.X86.Taint.Agree keyCopyTaint) ?_ ?_
  · apply RelCT.block_append
    refine RelCT.seq (R := VG.X86.Taint.Agree { keyCopyTaint with regs := .ofList [.edi, .esi, .edx] }) ?_ ?_
    · intro s t tr ur sf tf ⟨S, T, P, D⟩ E F
      have Trace := (pointer_relCT input base size hz _ _ _ _ _ _ ⟨S, T, P⟩ E F).1
      obtain ⟨PS, KS, _⟩ := wp_result (pointer_ok S hz input) E
      obtain ⟨PT, KT, _⟩ := wp_result (pointer_ok T hz input) F
      refine ⟨Trace, ?_⟩
      apply agree_regs (rs := [.edi, .esi, .edx])
      intro reg member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · rw [KS.1 _ (by decide), KT.1 _ (by decide)]
        exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
      · exact PS.trans (P.trans PT.symm)
      · rw [KS.1 _ (by decide), KT.1 _ (by decide)]; exact D
    · exact erased_relCT _ (.block [.mov .ecx (.imm 0)]) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
  · exact checkedProgramChange (τ' := { keyCopyTaint with flags := true })
      (hint := .loop keyCopyTaint (.block [])) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure KeyPartsCall (base : Addr) (size : Nat) (out : BitVec 32)
    (parts : List (Pointer × Nat)) (s : State) : Prop where
  scr : Scr s base size
  ready : ∀ part ∈ parts, KeyPartReady s base (out.setWidth 64) (keyPartsSize parts) part
  dest : s.gpr .edx = out
  write : ∀ i < keyPartsSize parts, InRegions s.wr (off (out.setWidth 64) i) 1

theorem keyParts_relCT (parts : List (Pointer × Nat)) (base : Addr) (size : Nat) (out : BitVec 32)
    (hz : Layout.saved ≤ size) (ho : out.toNat + keyPartsSize parts ≤ 2 ^ 32)
    (small : keyPartsSize parts < 2 ^ 32)
    (A : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, keyPartsSize parts⟩) :
    RelCT isa (fun s t => KeyPartsCall base size out parts s ∧ KeyPartsCall base size out parts t ∧
      ∀ part ∈ parts, pointerValue base s part.1 = pointerValue base t part.1)
      (Generate.copyParts parts) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  induction parts generalizing out with
  | nil =>
    apply RelCT.block_nil
    intro s t ⟨S, T, _⟩
    apply agree_regs (rs := [.edi])
    intro reg member
    obtain rfl := List.mem_singleton.mp member
    exact BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
  | cons part tail ih =>
    obtain ⟨input, len⟩ := part
    have total : keyPartsSize ((input, len) :: tail) = len + keyPartsSize tail := rfl
    have lenBound : len ≤ keyPartsSize ((input, len) :: tail) := by rw [total]; omega
    have firstSub : Region.Sub ⟨out.setWidth 64, len⟩
        ⟨out.setWidth 64, keyPartsSize ((input, len) :: tail)⟩ := by
      simpa only [BitVec.add_zero] using Offset.sub_base (out.setWidth 64) (d := 0) (by omega : 0 + len ≤ _)
    let R := fun s t => KeyPartsCall base size out ((input, len) :: tail) s ∧
      KeyPartsCall base size out ((input, len) :: tail) t ∧
      ∀ part ∈ (input, len) :: tail, pointerValue base s part.1 = pointerValue base t part.1
    let after := fun s t => ∃ s0 t0, R s0 t0 ∧
      (Spec.Rsa.bytesAt s.mem (out.setWidth 64) len =
        (Spec.Rsa.bytesAt s0.mem ((pointerValue base s0 input).setWidth 64) len).map
          (fun b => (b.setWidth 32 &&& s0.gpr .ebx).setWidth 8) ∧
        s.gpr .edx = out + BitVec.ofNat 32 len ∧ s.gpr .ebx = s0.gpr .ebx ∧
        Outside (out.setWidth 64) 0 len s0.mem s.mem ∧ Keeps [.eax, .ecx, .edx, .esi] s0 s) ∧
      (Spec.Rsa.bytesAt t.mem (out.setWidth 64) len =
        (Spec.Rsa.bytesAt t0.mem ((pointerValue base t0 input).setWidth 64) len).map
          (fun b => (b.setWidth 32 &&& t0.gpr .ebx).setWidth 8) ∧
        t.gpr .edx = out + BitVec.ofNat 32 len ∧ t.gpr .ebx = t0.gpr .ebx ∧
        Outside (out.setWidth 64) 0 len t0.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .esi] t0 t)
    have first : RelCT isa R (Generate.copyPart input len) after := by
      intro s t tr ur sf tf H E F
      obtain ⟨S, T, P⟩ := H
      have Trace := (keyCopyPart_relCT input len base size hz _ _ _ _ _ _
        ⟨S.scr, T.scr, P _ List.mem_cons_self, S.dest.trans T.dest.symm⟩ E F).1
      have one {s : State} (S : KeyPartsCall base size out ((input, len) :: tail) s) :=
        let B := S.ready (input, len) List.mem_cons_self
        keyCopyPart_ok S.scr hz
          (show KeyPartReady s base (out.setWidth 64) len (input, len) from
            ⟨B.positive, B.fits, B.read, B.apart.sub_right firstSub⟩)
          (by omega : len < 2 ^ 32) (by omega : out.toNat + len ≤ 2 ^ 32) S.dest rfl
          (fun i hi => S.write i (by omega))
      exact ⟨Trace, s, t, ⟨S, T, P⟩, wp_result (one S) E, wp_result (one T) F⟩
    unfold Generate.copyParts
    refine RelCT.seq first ?_
    cases tail with
    | nil =>
      apply RelCT.block_nil
      intro s t ⟨s0, t0, ⟨S, T, _⟩, ⟨_, _, _, _, Ks⟩, ⟨_, _, _, _, Kt⟩⟩
      apply agree_regs (rs := [.edi])
      intro reg member
      obtain rfl := List.mem_singleton.mp member
      rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]
      exact BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
    | cons next remaining =>
      intro s t tr ur sf tf ⟨s0, t0, ⟨S, T, P⟩, ⟨_, Ds, _, Os, Ks⟩, ⟨_, Dt, _, Ot, Kt⟩⟩ E F
      have positive : 0 < keyPartsSize (next :: remaining) := by
        have H := (S.ready next (List.mem_cons_of_mem _ List.mem_cons_self)).positive
        change 0 < next.2 + keyPartsSize remaining
        omega
      let nextOut := out + BitVec.ofNat 32 len
      have nextAddr : nextOut.setWidth 64 = off (out.setWidth 64) len := addr_eq (by rw [total] at ho; omega)
      have nextNat : nextOut.toNat = out.toNat + len := by
        simp only [nextOut, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : len < 2 ^ 32), Nat.mod_eq_of_lt (by rw [total] at ho; omega : out.toNat + len < 2 ^ 32)]
      have tailSub : Region.Sub ⟨nextOut.setWidth 64, keyPartsSize (next :: remaining)⟩
          ⟨out.setWidth 64, keyPartsSize ((input, len) :: next :: remaining)⟩ := by
        rw [nextAddr]; exact Offset.sub_base _ (by rw [total])
      have keep {a b : State} (C : KeyPartsCall base size out ((input, len) :: next :: remaining) a)
          (D : b.gpr .edx = nextOut) (O : Outside (out.setWidth 64) 0 len a.mem b.mem)
          (K : Keeps [.eax, .ecx, .edx, .esi] a b) : KeyPartsCall base size nextOut (next :: remaining) b := by
        refine ⟨C.scr.of_keeps K (by decide), ?_, D, ?_⟩
        · intro part member
          have B := (C.ready part (List.mem_cons_of_mem _ member)).keep C.scr hz
            (O.mono (Nat.le_refl _) (by omega)) A K
          exact ⟨B.positive, B.fits, B.read, B.apart.sub_right tailSub⟩
        · intro i hi
          rw [K.2.2, nextAddr, off, off, Offset.add_add]
          exact C.write (len + i) (by rw [total]; omega)
      apply ih nextOut (by rw [nextNat]; rw [total] at ho; omega) (by rw [total] at small; omega)
        (A.sub_right tailSub) _ _ _ _ _ _ ⟨keep S Ds Os Ks, keep T Dt Ot Kt, ?_⟩ E F
      intro part member
      rw [external_pointer S.scr hz Os (A.sub_right firstSub) Ks part.1,
        external_pointer T.scr hz Ot (A.sub_right firstSub) Kt part.1]
      exact P part (List.mem_cons_of_mem _ member)

end VG.Proof.Dsa.X86
