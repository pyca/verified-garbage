module

import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddInput
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Add
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8AddChain
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! Add the input block and saved overflow before its register product. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem ea_carry {s : State} {B : Addr} {e : Nat} (hc : s.gpr .rcx = off B e) (he : 8 ≤ e) :
    s.ea AdxRotate8.blockCarry = off B (e - 8) := by
  change s.gpr .rcx + BitVec.ofInt 64 (-8) = off B (e - 8)
  rw [hc, show BitVec.ofInt 64 (-8) = 0 - BitVec.ofNat 64 8 from rfl]
  exact Offset.add_ofNat_add_neg B he

/-- The block carry, a bit, into the carry flag. -/
theorem carryIn_ok {s : State} {v : BitVec 64} (hm : readSrc s (.mem AdxRotate8.blockCarry) = some v)
    (hv : v.toNat ≤ 1) :
    WP isa (.block AdxRotate8.carryIn) s fun t =>
      t.cf = some (decide (v.toNat = 1)) ∧ Keeps [.rax] s t := by
  unfold AdxRotate8.carryIn
  rw [show ([Instr.mov .rax (.mem AdxRotate8.blockCarry), .alu .add .rax (.imm (-1))] : List Instr) =
    [.mov .rax (.mem AdxRotate8.blockCarry)] ++ [.alu .add .rax (.imm (-1))] from rfl, WP.block_append_iff]
  refine WP.mono (movMem_ok s hm) fun a ⟨va, _, _, ka⟩ => ?_
  have hx : (BitVec.signExtend 64 (-1 : BitVec 32)).toNat = 2 ^ 64 - 1 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', va]
  refine ⟨?_, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  · simp only [RegUpd.cf_setReg, RegUpd.cf_arithFlags, hx, Option.some.injEq, decide_eq_decide]
    omega_using [hv]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, ka.1 r (by simp [hr])]

theorem addInputCarry_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 8 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z) (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa (.block AdxRotate8.addInputCarry) s fun t =>
      cols t + 2^512 * (t.gpr .rax).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 ∧
      (t.gpr .rax).toNat ≤ 1 ∧ t.cf = some false ∧
      Keeps [.rdx,.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxRotate8.addInputCarry
  rw [List.append_assoc, WP.block_append_iff]
  have hm := readSrc_word hs (ea_carry hc he) (show eU - 8 + 8 ≤ Z by omega)
  refine WP.mono (carryIn_ok hm hb) fun a ⟨ca, ka⟩ => ?_
  rw [WP.block_append_iff]
  have src : ∀ k < 8, ∀ t, Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] a t →
      readSrc t (.mem (AdxRotate8.at_ .rsi (8 * k))) = some (word s.mem B (eO + 8 * k)) := by
    intro k hk t kt
    rw [kt.readMem (by simp [AdxRotate8.at_]) (by intro r h; nomatch h),
      ka.readMem (by simp [AdxRotate8.at_]) (by intro r h; nomatch h)]
    exact readSrc_word hs (ea_at ho (8 * k)) (by omega)
  refine WP.mono (chain_ok a _ _ ca src (fun _ _ _ h => nomatch h)) fun b ⟨cb, hcb, eb, kb⟩ => ?_
  rw [show ([Instr.mov32 .rax (.imm 0), .adcx .rax (.reg .rax)] : List Instr) =
    [.mov32 .rax (.imm 0)] ++ [.adcx .rax (.reg .rax)] from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok b .rax) fun c ⟨zc, cc, _, kc⟩ => ?_
  refine WP.mono (capture_ok c (cc.trans hcb) zc) fun t ⟨hct, et, kt⟩ => ?_
  rw [number_words, cols_keep ka.keep (by decide)] at eb
  have ct : cols t = cols b := (cols_keep kt.keep (by decide)).trans (cols_keep kc.keep (by decide))
  have dv : (decide ((word s.mem B (eU - 8)).toNat = 1)).toNat = (word s.mem B (eU - 8)).toNat := by
    by_cases h1 : (word s.mem B (eU - 8)).toNat = 1
    · simp [h1]
    · simp only [h1, decide_false, Bool.toNat_false]; omega_using [hb, h1]
  rw [dv] at eb
  refine ⟨?_, ?_, hct, (ka.trans (kb.trans (kc.trans kt))).mono (by simp)⟩
  · rw [ct, et]; omega_using [eb]
  · rw [et]; exact Bool.toNat_le _

theorem accumulate_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 8 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z) (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa AdxRotate8.accumulate s fun t =>
      cols t + 2 ^ 512 * (word t.mem B (eU - 8)).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 ∧
      (word t.mem B (eU - 8)).toNat ≤ 1 ∧ Outside B (eU - 8) 8 s.mem t.mem ∧
      Keep [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.accumulate
  refine WP.seq (WP.mono (addInputCarry_ok hs hc ho he huZ hoZ hb) fun b ⟨eb,bb,_,kb⟩ => ?_)
  refine WP.mono (storeMem_ok (hs.congr kb.2.2.2)
    (ea_carry ((kb.gpr (by decide)).trans hc) he) (show eU - 8 + 8 ≤ Z by omega))
    fun t ⟨wt,ot,kt⟩ => ?_
  refine ⟨?_,?_,?_,(kb.keep.trans kt).mono (by simp)⟩
  · rw [wt, cols_keep kt (by simp)]; exact eb
  · rw [wt]; exact bb
  · rw [kb.2.1] at ot; exact ot
end VG.Proof.Bignum.X86_64.AdxRotate8
