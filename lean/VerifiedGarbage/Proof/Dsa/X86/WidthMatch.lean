module
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Pointer

import VerifiedGarbage.Proof.Dsa.X86.PublicCompare
import VerifiedGarbage.Proof.Mont.X86.Instr

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
