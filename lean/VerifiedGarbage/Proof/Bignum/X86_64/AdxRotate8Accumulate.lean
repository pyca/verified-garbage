module
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Add
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8AddChain
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Framework.AddrArith

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

/-- `add rdx, -1` of a bit: CF is the bit, OF is clear. -/
theorem addNeg1_ok (s : State) (hb : (s.gpr .rdx).toNat ≤ 1) :
    WP isa (.block [.alu .add .rdx (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      t.cf = some (decide ((s.gpr .rdx).toNat = 1)) ∧ t.of = some false ∧ t.mem = s.mem ∧
      Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have hv : s.gpr .rdx = 0 ∨ s.gpr .rdx = 1 := by
    rcases (show (s.gpr .rdx).toNat = 0 ∨ (s.gpr .rdx).toNat = 1 by omega) with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h))
  refine ⟨?_, ?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [State.setReg, arithFlags, State.setFlags]
    rcases hv with h | h <;> rw [h] <;> decide
  · simp only [State.setReg, arithFlags, State.setFlags]
    rcases hv with h | h <;> rw [h] <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem carryIn_ok {s : State} {B : Addr} {Z eU : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (he : 8 ≤ eU) (huZ : eU ≤ Z)
    (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa (.block AdxRotate8.carryIn) s fun t =>
      t.cf = some (decide ((word s.mem B (eU - 8)).toNat = 1)) ∧ t.of = some false ∧
      t.mem = s.mem ∧ Keeps [.rdx] s t := by
  unfold AdxRotate8.carryIn
  rw [show ([Instr.mov .rdx (.mem AdxRotate8.blockCarry), .alu .add .rdx (.imm (BitVec.ofInt 32 (-1)))]) =
    [.mov .rdx (.mem AdxRotate8.blockCarry)] ++ [.alu .add .rdx (.imm (BitVec.ofInt 32 (-1)))] from rfl,
    WP.block_append_iff]
  have hm := readSrc_word hs (ea_carry hc he) (show eU - 8 + 8 ≤ Z by omega)
  refine WP.mono (movMem_ok s (dst := .rdx) hm) fun a ⟨da,_,_,ka⟩ => ?_
  refine WP.mono (addNeg1_ok a (by rw [da]; exact hb)) fun t ⟨ct,ot,mt,kt⟩ => ?_
  rw [da] at ct
  exact ⟨ct, ot, mt.trans ka.2.1, (ka.trans kt).mono (by simp)⟩

private theorem bit_toNat (C : Nat) (h : C ≤ 1) : (decide (C = 1)).toNat = C := by
  rcases (show C = 0 ∨ C = 1 by omega) with rfl | rfl <;> rfl

theorem addInputCarry_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 8 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z)
    (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa (.block AdxRotate8.addInputCarry) s fun t =>
      cols t + 2^512 * (t.gpr .rax).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 ∧
      (t.gpr .rax).toNat ≤ 1 ∧ t.cf = some false ∧
      Keeps [.rdx,.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxRotate8.addInputCarry
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (carryIn_ok hs hc he huZ hb) fun a ⟨ca,_,ma,ka⟩ => ?_
  rw [WP.block_append_iff]
  have src : ∀ k < 8, ∀ t, Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] a t →
      readSrc t (.mem (AdxRotate8.at_ .rsi (8 * k))) = some (word s.mem B (eO + 8 * k)) := by
    intro k hk t kt
    rw [kt.readMem (by simp [AdxRotate8.at_]) (by intro r h; nomatch h),
      ka.readMem (by simp [AdxRotate8.at_]) (by intro r h; nomatch h)]
    exact readSrc_word hs (ea_at ho (8 * k)) (by omega)
  refine WP.mono (chain_ok a _ _ ca src (fun _ _ _ h => nomatch h)) fun b ⟨cb, hcb, eb, kb⟩ => ?_
  rw [show ([Instr.mov32 .rax (.imm 0), .adcx .rax (.reg .rax)]) =
    [.mov32 .rax (.imm 0)] ++ [.adcx .rax (.reg .rax)] from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok b .rax) fun c ⟨zc, cc, _, kc⟩ => ?_
  refine WP.mono (capture_ok c (cc.trans hcb) zc) fun t ⟨hct, et, kt⟩ => ?_
  have cA := cols_keep ka.keep (by decide)
  have cC := cols_keep kc.keep (by decide)
  have cT := cols_keep kt.keep (by decide)
  rw [number_words, cA, bit_toNat _ hb] at eb
  refine ⟨?_, ?_, hct, (ka.trans (kb.trans (kc.trans kt))).mono (by decide)⟩
  · rw [cT, cC, et]; omega_using [eb]
  · rw [et]; exact Bool.toNat_le _

theorem accumulate_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 8 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z)
    (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
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
