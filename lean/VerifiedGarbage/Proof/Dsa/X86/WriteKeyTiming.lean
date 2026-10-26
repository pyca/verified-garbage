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
import VerifiedGarbage.Proof.Dsa.X86.KeyPartsTiming
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

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
  refine wp_movS (readSrc_sc hs (by change 8248 ≤ size; omega)) fun u su _ => ?_
  refine wp_movS (readSrc_sc (hs.of_keeps su.keeps (by decide)) (by change 8228 ≤ size; omega)) fun t ut _ => WP.block_nil ?_
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
  have count : keyPartsSize parts = 3 * pLen + 2 * qLen := by simp [parts, keyPartsSize]; omega
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
