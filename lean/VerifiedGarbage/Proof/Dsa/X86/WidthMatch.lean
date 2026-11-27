module

public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! ### `Dsa.X86.PublicCompare`, which this module and modules that import it used -/

section

/-! # Comparisons used only for dispatch on public lengths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem publicCompare_ok {s : State} {base : Addr} {size value wanted : Nat} (f : Field)
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hv : (pointerValue base s (.input f)).toNat = value)
    (hb : wanted < 2 ^ 32) :
    WP isa (.block [.mov .eax (.mem (sc (Layout.field f))), .alu .cmp .eax (.imm (BitVec.ofNat 32 wanted))]) s fun t =>
      t.zf = some (decide (value = wanted)) ∧ Keeps [.eax] s t ∧ t.mem = s.mem := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds f
  have bound : Layout.field f + 4 ≤ size := by omega_using [hz, B]
  refine wp_movS (readSrc_sc hs bound) fun u su _ => ?_
  refine wp_cmpS rfl fun t ut zt => WP.block_nil ⟨?_, su.keeps.trans (ut.keeps [] |>.mono (by simp)), ut.mem.trans su.mem⟩
  rw [zt, su.gpr]
  change some (pointerValue base s (.input f) - BitVec.ofNat 32 wanted == 0) = _
  have W : pointerValue base s (.input f) = BitVec.ofNat 32 value := by
    rw [← hv]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 32 (pointerValue base s (.input f))).symm
  rw [W, sub_beq (by rw [← hv]; exact (pointerValue base s (.input f)).isLt) hb]

end VG.Proof.Dsa.X86

end

end

/-! # Testing two public component widths with one fallback continuation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem falseCompare_ok (s : State) :
    WP isa (.block [.mov .eax (.imm 0), .alu .cmp .eax (.imm 1)]) s fun t =>
      t.zf = some false ∧ Keeps [.eax] s t ∧ t.mem = s.mem := by
  refine wp_movS rfl fun u U _ => ?_
  refine wp_cmpS rfl fun t T Z => WP.block_nil ⟨?_, U.keeps.trans ((T.keeps []).mono (by simp)), T.mem.trans U.mem⟩
  rw [Z, U.gpr]
  rfl

theorem widthMatch_ok {s : State} {base : Addr} {size pLen qLen wp wq : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hp : (pointerValue base s (.input .pLen)).toNat = pLen)
    (hq : (pointerValue base s (.input .qLen)).toNat = qLen)
    (bp : wp < 2 ^ 32) (bq : wq < 2 ^ 32) :
    WP isa (Entry.widthMatch wp wq) s fun t =>
      t.zf = some (decide (pLen = wp ∧ qLen = wq)) ∧ Keeps [.eax] s t ∧ t.mem = s.mem := by
  unfold Entry.widthMatch
  refine WP.seq (WP.mono (publicCompare_ok .pLen hs hz hp bp) fun u ⟨Z, K, O⟩ => ?_)
  by_cases P : pLen = wp
  · refine WP.ite true (by simp only [eval, Z, P, decide_true]) (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (publicCompare_ok (value := qLen) .qLen (hs.of_keeps K (by decide)) hz
      (by simpa only [pointerValue, O] using hq) bq) fun t ⟨Z2, K2, O2⟩ => ?_
    exact ⟨by simpa only [P, true_and] using Z2, K.trans K2, O2.trans O⟩
  · refine WP.ite false (by simp only [eval, Z, P, decide_false]) (fun h => Bool.noConfusion h) (fun _ => ?_)
    exact WP.mono (falseCompare_ok u) fun t ⟨Z2, K2, O2⟩ =>
      ⟨by simpa only [P, false_and, decide_false] using Z2, K.trans K2, O2.trans O⟩

end VG.Proof.Dsa.X86
