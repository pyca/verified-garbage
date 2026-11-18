module

public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.DerivingEntry
import VerifiedGarbage.Proof.Dsa.X86.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
import VerifiedGarbage.Proof.Dsa.X86.KeyPartsReady
import VerifiedGarbage.Proof.Dsa.X86.Persistent
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyFrame
public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyParts
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `Dsa.X86.KeyOutputReady`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.WriteKeyTiming`, which only this module used -/

section

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

end

end

/-! # Output resources retained across domain checks and exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure KeyOutputReady (L : CallLayout) (out : BitVec 32) (s : State) : Prop where
  pointer : pointerValue L.base s (.input .out) = out
  write : ∀ i < 3 * L.pLen + 2 * L.qLen, InRegions s.wr (off (out.setWidth 64) i) 1
  params : Region.Disjoint ⟨(pointerValue L.base s (.input .p)).setWidth 64, 2 * L.pLen + L.qLen⟩
    ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩
  scalar : Region.Disjoint ⟨(pointerValue L.base s (.input .nonce)).setWidth 64, L.qLen⟩
    ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩

theorem KeyOutputReady.keep {L : CallLayout} {out : BitVec 32} {s t : State}
    (R : KeyOutputReady L out s) (E : Execution L.base s t) : KeyOutputReady L out t := by
  have ptr (f : Field) (stable : StablePointer (.input f)) := runFrame_pointer E.mem E.keeps (by decide) stable
  exact ⟨(ptr .out (by decide)).trans R.pointer, by rw [E.keeps.2.2]; exact R.write,
    by rw [ptr .p (by decide)]; exact R.params, by rw [ptr .nonce (by decide)]; exact R.scalar⟩

theorem KeyOutputReady.shape {L : CallLayout} {out : BitVec 32} {s t : State} {regs : List Reg}
    (R : KeyOutputReady L out s) (O : Outs L.base shapeRanges s.mem t.mem) (K : Keeps regs s t) :
    KeyOutputReady L out t := by
  exact ⟨(shapeFrame_field O (by decide)).trans R.pointer, by rw [K.2.2]; exact R.write,
    by rw [shapeFrame_field O (by decide : Field.p ≠ .mask ∧ Field.p ≠ .digestPrefixLen)]; exact R.params,
    by rw [shapeFrame_field O (by decide : Field.nonce ≠ .mask ∧ Field.nonce ≠ .digestPrefixLen)]; exact R.scalar⟩

theorem KeyOutputReady.writeReady {L : CallLayout} {out : BitVec 32} {s : State}
    (R : KeyOutputReady L out s) (C : CallReady L s)
    (P : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩) :
    KeyWriteReady L.base L.size L.pLen L.qLen out s := by
  have W := L.lengths
  refine ⟨C.moduli.scr, ?_, R.pointer, R.write⟩
  intro part member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (C.buffers _ P).keyPart (by omega) R.params
  · exact localKeyPart C.moduli.scr (by omega_using [W]) (Nat.le_trans (C.moduli.wideFit (by decide)) L.extent) A
  · exact (C.buffers _ X).keyPart (by omega) R.scalar

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.DeriveFailureTiming`, which this module and modules that import it used -/

section

/-! # Invalid-domain clearing has a fixed public byte count -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveFailureHead_ok {s : State} {base : Addr} {size len : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) :
    WP isa (.block [.mov .esi (.mem (sc (Layout.field .out))),
      .mov .ecx (.imm (BitVec.ofNat 32 len)), .mov .eax (.imm 0)]) s fun t =>
      t.gpr .esi = pointerValue base s (.input .out) ∧ t.gpr .ecx = BitVec.ofNat 32 len ∧
      t.gpr .eax = 0 ∧ Keeps [.esi, .ecx, .eax] s t := by
  have bound : 8256 ≤ size := hz
  refine wp_movS (readSrc_sc hs (by change 8228 ≤ size; omega_using [bound])) fun s1 U1 _ => ?_
  refine wp_movS rfl fun s2 U2 _ => ?_
  refine wp_movS rfl fun s3 U3 _ => WP.block_nil ⟨?_, ?_, U3.gpr, ?_⟩
  · rw [U3.other _ (by decide), U2.other _ (by decide), U1.gpr]; rfl
  · rw [U3.other _ (by decide), U2.gpr]
  · exact ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (U3.keeps.mono (by decide))

theorem deriveFailure_relCT (pLen qLen : Nat) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .out) = pointerValue base t (.input .out))
      (Generate.deriveFailure pLen qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Generate.deriveFailure Core.sequence
  dsimp only [List.foldr]
  refine RelCT.seq (R := VG.X86.Taint.Agree failureTaint) ?_
    (RelCT.seq (checkedProgramChange (τ' := { failureTaint with flags := true })
      (hint := .loop failureTaint (.block [])) (by kernel_rfl) (by kernel_rfl)) (RelCT.block_nil (fun _ _ h => h)))
  intro s t tr ur sf tf ⟨S, T, P⟩ E F
  have G : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  have Agree : VG.X86.Taint.Agree (workspaceTaint false) s t := by
    apply agree_regs (rs := [.edi]); intro reg member
    obtain rfl := List.mem_singleton.mp member; exact G
  have Head : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.mov .esi (.mem (sc (Layout.field .out))),
        .mov .ecx (.imm (BitVec.ofNat 32 (3 * pLen + 2 * qLen))), .mov .eax (.imm 0)])
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
    erased_relCT _ (.block [.mov .esi (.mem (sc 0)), .mov .ecx (.imm 0), .mov .eax (.imm 0)])
      (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
  obtain ⟨Ps, Cs, As, Ks⟩ := wp_result (deriveFailureHead_ok S hz) E
  obtain ⟨Pt, Ct, At, Kt⟩ := wp_result (deriveFailureHead_ok T hz) F
  refine ⟨(Head _ _ _ _ _ _ Agree E F).1, ?_⟩
  apply agree_regs (rs := [.edi, .esi, .ecx, .eax])
  intro reg member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact G
  · exact Ps.trans (P.trans Pt.symm)
  · exact Cs.trans Ct.symm
  · exact As.trans At.symm

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.DerivingLayout`, which this module and modules that import it used -/

section

/-! # Public call layout obtained from installed domain arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def derivingInputs (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen),
    (.input .nonce, qLen), (.input .p, 2 * pLen + qLen)]

def derivingPointers (s : State) : Pointer → BitVec 32
  | .input .p => arg s 2
  | .input .q => arg s 2 + arg s 4
  | .input .g => arg s 2 + arg s 4 + arg s 6
  | .input .nonce => arg s 5
  | _ => 0

def derivingParams (s : State) : Spec.Dsa.Params := Spec.Dsa.paramsBytes (arg s 4).toNat (arg s 6).toNat
  (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)

def derivingLayout (s : State) (A : DerivingABI s) : CallLayout where
  sp := s.gpr .esp
  base := argumentPointer s 7
  size := (arg s 8).toNat * 8
  pLen := (arg s 4).toNat
  qLen := (arg s 6).toNat
  p := (derivingParams s).p
  q := (derivingParams s).q
  widths := A.lengths
  extent := A.used
  inputs := derivingInputs (arg s 4).toNat (arg s 6).toNat
  pointers := derivingPointers s
  stable := by
    intro input hi
    simp only [derivingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
  digestPrefix := min (arg s 4).toNat (Spec.Dsa.bitLength (derivingParams s).q / 8)

theorem derivingInputs_shape (pLen qLen : Nat) :
    ∀ input ∈ derivingInputs pLen qLen, ShapePointer input.1 := by
  intro input hi
  simp only [derivingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide

theorem derivingInstalled_ready {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t) :
    ShapeCallReady (derivingLayout s A) (arg s 4).toNat t := by
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (2, .p) ∈ Generate.deriveArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨X, _⟩ := I.input (by decide : (5, .nonce) ∈ Generate.deriveArguments) A.scalarBound
    (by rw [A.rd, A.wr]; simp) A.scalarScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowScalar.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega_using [this]) Bytes Qptr Gptr
  refine ⟨I.keeps.1 .esp (by decide), I.scr, ?_, ?_, ?_, ?_,
    congrArg BitVec.toNat (I.arguments (4, .digestLen) (by decide))⟩
  · intro input hi
    simp only [derivingLayout, derivingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact P
    · exact Q
    · exact G
    · exact X
    · change CallerBuffer t _ _ (.input .p) (2 * (arg s 4).toNat + (arg s 6).toNat)
      rw [← A.keyLength]; exact Params
  · intro input hi
    simp only [derivingLayout, derivingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact I.arguments (2, .p) (by decide)
    · exact I.qPointer
    · exact I.gPointer
    · exact I.arguments (5, .nonce) (by decide)
    · exact I.arguments (2, .p) (by decide)
  · exact (congrArg (fun k : Spec.Dsa.Params => k.p) Value).symm
  · exact (congrArg (fun k : Spec.Dsa.Params => k.q) Value).symm

theorem derivingLayout_eq {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i < 9, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (derivingParams s).p = (derivingParams t).p)
    (Q : (derivingParams s).q = (derivingParams t).q) : derivingLayout s A = derivingLayout t B := by
  have A0 := args 2 (by decide)
  have A2 := args 4 (by decide)
  have A3 := args 6 (by decide)
  have A4 := args 7 (by decide)
  have A5 := args 8 (by decide)
  have Ax := args 5 (by decide)
  have pointers : derivingPointers s = derivingPointers t := by
    funext p
    cases p with
    | input f => cases f <;> simp only [derivingPointers, A0, A2, A3, Ax]
    | «local» d => rfl
    | signatureS => rfl
  simp only [derivingLayout, SP, argumentPointer, A2, A3, A4, A5, P, Q, pointers]

theorem derivingInstalled_output {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t) :
    KeyOutputReady (derivingLayout s A) (arg s 0) t := by
  refine ⟨I.arguments (0, .out) (by decide), ?_, ?_, ?_⟩
  · intro i hi
    change i < 3 * (arg s 4).toNat + 2 * (arg s 6).toNat at hi
    rw [I.keeps.2.2, A.wr]
    refine ⟨_, List.mem_cons_self, Offset.contains_base _ ?_ ?_⟩
    · have := A.outLength; omega_using [hi, this]
    · have := A.outBound; have := A.outLength; omega_using [hi]
  · change Region.Disjoint ⟨(pointerValue (argumentPointer s 7) t (.input .p)).setWidth 64, 2 * (arg s 4).toNat + (arg s 6).toNat⟩
      ⟨argumentPointer s 0, 3 * (arg s 4).toNat + 2 * (arg s 6).toNat⟩
    rw [I.arguments (2, .p) (by decide), ← A.keyLength, ← A.outLength]
    exact A.keyOut
  · change Region.Disjoint ⟨(pointerValue (argumentPointer s 7) t (.input .nonce)).setWidth 64, (arg s 6).toNat⟩
      ⟨argumentPointer s 0, 3 * (arg s 4).toNat + 2 * (arg s 6).toNat⟩
    rw [I.arguments (5, .nonce) (by decide), ← A.outLength]
    exact A.scalarOut

end VG.Proof.Dsa.X86

end

end

/-! # Whole domain-deriving traces from common public arguments and domain values -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/DeriveBodyTiming.lean`, which only this module imported.
section

/-! # Exponentiation and output copies preserve the public layout -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (Params : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs)
    (ho : out.toNat + (3 * L.pLen + 2 * L.qLen) ≤ 2 ^ 32)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩) :
    RelCT isa (fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t)
      (.seq (Generate.deriveCompute L.pLen L.qLen) (Generate.writeKey L.pLen L.qLen))
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)) := by
  have W := L.lengths
  refine RelCT.seq (R := fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t) ?_ ?_
  · intro s t tr ur sf tf ⟨Pair, S, T⟩ E F
    obtain ⟨Trace, Pair'⟩ := deriveCompute_relCT L (.inl ⟨_, P, Nat.le_refl _⟩)
      (.inl ⟨_, Q, Nat.le_refl _⟩) (.inl ⟨_, G, Nat.le_refl _⟩) (.inl ⟨_, X, Nat.le_refl _⟩)
      _ _ _ _ _ _ Pair E F
    have Es := (wp_result (deriveCompute_ok Pair.1.moduli (Pair.1.buffers _ G) (Pair.1.buffers _ X) rfl rfl) E).2.2.2
    have Et := (wp_result (deriveCompute_ok Pair.2.moduli (Pair.2.buffers _ G) (Pair.2.buffers _ X) rfl rfl) F).2.2.2
    exact ⟨Trace, Pair', S.keep Es, T.keep Et⟩
  · apply (writeKey_relCT L.base L.size L.pLen L.qLen out L.saved ho (by omega) A).mono ?_ (fun _ _ h => h)
    intro s t ⟨Pair, S, T⟩
    exact ⟨S.writeReady Pair.1 Params X A, T.writeReady Pair.2 Params X A,
      Pair.pointer (.inl ⟨_, P, Nat.le_refl _⟩), Pair.pointer (.inl ⟨_, X, Nat.le_refl _⟩)⟩

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/DeriveSizedTiming.lean`, which only this module imported.
section

/-! # Derivation branches only on the public domain shape -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveSized_relCT (L : CallLayout) (out : BitVec 32) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (Params : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8))
    (ho : out.toNat + (3 * L.pLen + 2 * L.qLen) ≤ 2 ^ 32)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t ∧
      KeyOutputReady L out s ∧ KeyOutputReady L out t)
      (Generate.deriveSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let R := fun s t => (shapeValid L.p L.q → CallPair L s t) ∧
    Scr s L.base L.size ∧ Scr t L.base L.size ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t
  unfold Generate.deriveSized
  refine RelCT.seq (M := isa) (R := fun s t => R s t ∧ s.zf = some (!decide (shapeValid L.p L.q)) ∧
      t.zf = some (!decide (shapeValid L.p L.q))) ?_
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  · intro s t tr ur sf tf ⟨S, T, Os, Ot⟩ E F
    have Trace := (shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ ⟨S, T⟩ E F).1
    obtain ⟨Zs, Ms, Ks, Fs⟩ := wp_result (shapeCall_ok S P Q stable hd) E
    obtain ⟨Zt, Mt, Kt, Ft⟩ := wp_result (shapeCall_ok T P Q stable hd) F
    exact ⟨Trace, ⟨fun h => ⟨(Ms h).ready, (Mt h).ready⟩,
      S.scr.of_keeps Ks (by decide), T.scr.of_keeps Kt (by decide), Os.shape Fs Ks, Ot.shape Ft Kt⟩, Zs, Zt⟩
  · by_cases valid : shapeValid L.p L.q
    · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (deriveBody_relCT L out P Q G X Params ho A).mono
        (fun _ _ H => ⟨H.1 valid, H.2.2.2⟩) (fun _ _ h => h)
    · simp only [valid, decide_false, Bool.not_false, ite_true]
      exact (deriveFailure_relCT L.pLen L.qLen L.base L.size L.saved).mono
        (fun _ _ H => ⟨H.2.1, H.2.2.1, H.2.2.2.1.pointer.trans H.2.2.2.2.pointer.symm⟩) (fun _ _ h => h)

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem derivingOperationWith_agrees {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i < 9, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (derivingParams s).p = (derivingParams t).p)
    (Q : (derivingParams s).q = (derivingParams t).q)
    (sized : Nat → Nat → Prog isa) (Is It : Mem → Prop)
    (Cs : Is s.mem) (Ct : It t.mem)
    (stableS : ∀ {a b}, Outside (argumentPointer s 7) 0 8272 a b → Is a → Is b)
    (stableT : ∀ {a b}, Outside (argumentPointer t 7) 0 8272 a b → It a → It b)
    (sizedCT : RelCT isa (fun u v =>
      Installed (argumentPointer s 7) ((arg s 8).toNat*8) Generate.deriveArguments 2 4 6 s u ∧
      Installed (argumentPointer t 7) ((arg t 8).toNat*8) Generate.deriveArguments 2 4 6 t v ∧
      Is u.mem ∧ It v.mem)
      (sized (arg s 4).toNat (arg s 6).toNat) (VG.X86.Taint.Agree (workspaceTaint false)))
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Generate.deriveKeyWith sized) s tr sf) (F : Exec isa (Generate.deriveKeyWith sized) t ur tf) : tr = ur := by
  let L := derivingLayout s A
  have LayoutEq := derivingLayout_eq A B args SP P Q
  have Size := args 8 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 7 (by decide))
  have PL := args 4 (by decide)
  have QL := args 6 (by decide)
  have DL := args 4 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s u ∧
    Installed (argumentPointer t 7) ((arg t 8).toNat * 8) Generate.deriveArguments 2 4 6 t v ∧ Is u.mem ∧ It v.mem
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.1.compare K2 O2, by rw [O1]; exact H.2.2.1, by rw [O2]; exact H.2.2.2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, derivingLayout, Base, Size] using H.2.1.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (4, .pLen) (by decide)), ?_⟩
    simpa only [L, derivingLayout, Base, PL] using congrArg BitVec.toNat (H.2.1.arguments (4, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (6, .qLen) (by decide)), ?_⟩
    simpa only [L, derivingLayout, Base, QL] using congrArg BitVec.toNat (H.2.1.arguments (6, .qLen) (by decide))
  have Sized := sizedCT
  have Dispatch := generationDispatch_relCT sized [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Generate.deriveEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Generate.deriveEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 7 Generate.deriveArguments _ _ _ _ _ _
        ⟨SP, args 7 (by decide), (A.stackArgument (by decide : 7 < 9)).readSrc,
          (B.stackArgument (by decide : 7 < 9)).readSrc⟩ E1 F1
      obtain ⟨I,Oi⟩ := wp_result (derivingEntry_precise A) E1
      obtain ⟨J,Oj⟩ := wp_result (derivingEntry_precise B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J,stableS Oi Cs,stableT Oj Ct⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]


theorem derivingOperation_agrees {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i < 9, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (derivingParams s).p = (derivingParams t).p)
    (Q : (derivingParams s).q = (derivingParams t).q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (Generate.deriveKey) s tr sf) (F : Exec isa (Generate.deriveKey) t ur tf) : tr = ur := by
  let L := derivingLayout s A
  have LayoutEq := derivingLayout_eq A B args SP P Q
  have DL := args 4 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 7) ((arg s 8).toNat*8) Generate.deriveArguments 2 4 6 s u ∧
    Installed (argumentPointer t 7) ((arg t 8).toNat*8) Generate.deriveArguments 2 4 6 t v
  have Sized : RelCT isa R (Generate.deriveSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (deriveSized_relCT L (arg s 0) (arg s 4).toNat
      (by simp [L, derivingLayout, derivingInputs]) (by simp [L, derivingLayout, derivingInputs])
      (by simp [L, derivingLayout, derivingInputs]) (by simp [L, derivingLayout, derivingInputs])
      (by simp [L, derivingLayout, derivingInputs]) (derivingInputs_shape _ _) rfl
      (by change (arg s 0).toNat + (3 * (arg s 4).toNat + 2 * (arg s 6).toNat) ≤ _
          rw [← A.outLength]; exact A.outBound)
      (by change Region.Disjoint _ ⟨argumentPointer s 0, 3 * (arg s 4).toNat + 2 * (arg s 6).toNat⟩
          rw [← A.outLength]; exact A.outScratch.symm)).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨derivingInstalled_ready A H.1, ?_, derivingInstalled_output A H.1, ?_⟩
    · simpa only [L, LayoutEq, DL] using derivingInstalled_ready B H.2
    · simpa only [L, LayoutEq, args 0 (by decide)] using derivingInstalled_output B H.2
  exact derivingOperationWith_agrees A B args SP P Q Generate.deriveSized (fun _ => True)
    (fun _ => True) trivial trivial (fun _ _ => trivial) (fun _ _ => trivial)
    (Sized.mono (fun _ _ H => ⟨H.1,H.2.1⟩) (fun _ _ h => h)) E F

end VG.Proof.Dsa.X86
