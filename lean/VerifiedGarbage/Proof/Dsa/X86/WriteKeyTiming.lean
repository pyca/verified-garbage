module

public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyFrame
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyParts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Framework.KernelRfl
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `Dsa.X86.KeyPartsTiming`, which only this module used -/

section

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
    have lenBound : len ≤ keyPartsSize ((input, len) :: tail) := by rw [total]; omega_using []
    have firstSub : Region.Sub ⟨out.setWidth 64, len⟩
        ⟨out.setWidth 64, keyPartsSize ((input, len) :: tail)⟩ := by
      simpa only [BitVec.add_zero] using Offset.sub_base (out.setWidth 64) (d := 0) (by omega_using [total] : 0 + len ≤ _)
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
          (by omega_using [small, total] : len < 2 ^ 32) (by omega_using [ho, lenBound] : out.toNat + len ≤ 2 ^ 32) S.dest rfl
          (fun i hi => S.write i (by omega_using [total, hi]))
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
        omega_using [H]
      let nextOut := out + BitVec.ofNat 32 len
      have nextAddr : nextOut.setWidth 64 = off (out.setWidth 64) len := addr_eq (by rw [total] at ho; omega_using [ho, positive])
      have nextNat : nextOut.toNat = out.toNat + len := by
        simp only [nextOut, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega_using [small, total] : len < 2 ^ 32), Nat.mod_eq_of_lt (by rw [total] at ho; omega_using [ho, positive] : out.toNat + len < 2 ^ 32)]
      have tailSub : Region.Sub ⟨nextOut.setWidth 64, keyPartsSize (next :: remaining)⟩
          ⟨out.setWidth 64, keyPartsSize ((input, len) :: next :: remaining)⟩ := by
        rw [nextAddr]; exact Offset.sub_base _ (by rw [total])
      have keep {a b : State} (C : KeyPartsCall base size out ((input, len) :: next :: remaining) a)
          (D : b.gpr .edx = nextOut) (O : Outside (out.setWidth 64) 0 len a.mem b.mem)
          (K : Keeps [.eax, .ecx, .edx, .esi] a b) : KeyPartsCall base size nextOut (next :: remaining) b := by
        refine ⟨C.scr.of_keeps K (by decide), ?_, D, ?_⟩
        · intro part member
          have B := (C.ready part (List.mem_cons_of_mem _ member)).keep C.scr hz
            (O.mono (Nat.le_refl _) (by omega_using [total])) A K
          exact ⟨B.positive, B.fits, B.read, B.apart.sub_right tailSub⟩
        · intro i hi
          rw [K.2.2, nextAddr, off, off, Offset.add_add]
          exact C.write (len + i) (by rw [total]; omega_using [hi])
      apply ih nextOut (by rw [nextNat]; rw [total] at ho; omega_using [ho]) (by rw [total] at small; omega_using [small])
        (A.sub_right tailSub) _ _ _ _ _ _ ⟨keep S Ds Os Ks, keep T Dt Ot Kt, ?_⟩ E F
      intro part member
      rw [external_pointer S.scr hz Os (A.sub_right firstSub) Ks part.1,
        external_pointer T.scr hz Ot (A.sub_right firstSub) Kt part.1]
      exact P part (List.mem_cons_of_mem _ member)

end VG.Proof.Dsa.X86

end

end


/-! # Serialization uses only public layout information for its trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure KeyWriteReady (base : Addr) (size pLen qLen : Nat) (out : BitVec 32) (s : State) : Prop where
  scr : Scr s base size
  ready : ∀ part ∈ [(.input .p, 2 * pLen + qLen), (.local t2, pLen), (.input .nonce, qLen)],
    KeyPartReady s base (out.setWidth 64) (3 * pLen + 2 * qLen) part
  pointer : pointerValue base s (.input .out) = out
  write : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (off (out.setWidth 64) i) 1

theorem keyWriteHead_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) :
    WP isa (.block [.mov .ebx (.mem (sc (Layout.field .mask))),
      .mov .edx (.mem (sc (Layout.field .out)))]) s fun t =>
      t.gpr .edx = pointerValue base s (.input .out) ∧ Keeps [.ebx, .edx] s t ∧ t.mem = s.mem := by
  have bound : 8256 ≤ size := hz
  refine wp_movS (readSrc_sc hs (by change 8248 ≤ size; omega_using [bound])) fun u su _ => ?_
  refine wp_movS (readSrc_sc (hs.of_keeps su.keeps (by decide)) (by change 8228 ≤ size; omega_using [bound])) fun t ut _ => WP.block_nil ?_
  exact ⟨by rw [ut.gpr, su.mem]; rfl,
    (su.keeps.mono (by decide)).trans (ut.keeps.mono (by decide)), ut.mem.trans su.mem⟩

theorem writeKey_relCT (base : Addr) (size pLen qLen : Nat) (out : BitVec 32)
    (hz : Layout.saved ≤ size) (ho : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (small : 3 * pLen + 2 * qLen < 2 ^ 32)
    (A : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩) :
    RelCT isa (fun s t => KeyWriteReady base size pLen qLen out s ∧ KeyWriteReady base size pLen qLen out t ∧
      pointerValue base s (.input .p) = pointerValue base t (.input .p) ∧
      pointerValue base s (.input .nonce) = pointerValue base t (.input .nonce))
      (Generate.writeKey pLen qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let parts : List (Pointer × Nat) := [(.input .p, 2 * pLen + qLen), (.local t2, pLen), (.input .nonce, qLen)]
  have count : keyPartsSize parts = 3 * pLen + 2 * qLen := by simp [parts, keyPartsSize]; omega_using []
  unfold Generate.writeKey Core.sequence
  dsimp only [List.foldr]
  refine RelCT.seq (R := fun s t => KeyPartsCall base size out parts s ∧ KeyPartsCall base size out parts t ∧
      ∀ part ∈ parts, pointerValue base s part.1 = pointerValue base t part.1) ?_
    (RelCT.seq (keyParts_relCT parts base size out hz (by rw [count]; exact ho)
      (by rw [count]; exact small) (by rw [count]; exact A))
      (RelCT.seq result_relCT (RelCT.block_nil (fun _ _ h => h))))
  intro s t tr ur sf tf ⟨S, T, P, X⟩ E F
  have G : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
  have Agree : VG.X86.Taint.Agree (workspaceTaint false) s t := by
    apply agree_regs (rs := [.edi]); intro reg member
    obtain rfl := List.mem_singleton.mp member; exact G
  have Check : VG.Taint.check taint (workspaceTaint false)
      (.block [.mov .ebx (.mem (sc (Layout.field .mask))), .mov .edx (.mem (sc (Layout.field .out)))])
      (.block []) = some (workspaceTaint false) := rfl
  obtain ⟨Ds, Ks, Ms⟩ := wp_result (keyWriteHead_ok S.scr hz) E
  obtain ⟨Dt, Kt, Mt⟩ := wp_result (keyWriteHead_ok T.scr hz) F
  have ptr {a b : State} (K : Keeps [.ebx, .edx] a b) (M : b.mem = a.mem) (p : Pointer) :
      pointerValue base b p = pointerValue base a p := by
    cases p <;> simp only [pointerValue, M, K.1 .edi (by decide)]
  have call {a b : State} (R : KeyWriteReady base size pLen qLen out a)
      (D : b.gpr .edx = pointerValue base a (.input .out)) (K : Keeps [.ebx, .edx] a b) (M : b.mem = a.mem) :
      KeyPartsCall base size out parts b := by
    refine ⟨R.scr.of_keeps K (by decide), ?_, D.trans R.pointer, ?_⟩
    · intro part member
      have B := R.ready part member
      rw [count]
      exact ⟨B.positive, by rw [ptr K M]; exact B.fits,
        by rw [ptr K M, K.2.1, K.2.2]; exact B.read, by rw [ptr K M]; exact B.apart⟩
    · rw [count, K.2.2]; exact R.write
  refine ⟨(VG.Taint.check_sound Check Agree E F).1, call S Ds Ks Ms, call T Dt Kt Mt, ?_⟩
  intro part member
  rw [ptr Ks Ms, ptr Kt Mt]
  simp only [parts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact P
  · simp only [pointerValue, G]
  · exact X

end VG.Proof.Dsa.X86
