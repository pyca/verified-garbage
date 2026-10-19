module
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Store
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddChain
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddClose
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The final input block consumes both saved carries. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem ea_tileCarry {s : State} {B : Addr} {e : Nat} (hc : s.gpr .rcx = off B e) (he : 16 ≤ e) :
    s.ea AdxRotate8.tileCarry = off B (e - 16) := by
  change s.gpr .rcx + BitVec.ofInt 64 (-16) = off B (e - 16)
  rw [hc, show BitVec.ofInt 64 (-16) = 0 - BitVec.ofNat 64 16 from rfl]
  exact Offset.add_ofNat_add_neg B he

theorem tailAdd_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 16 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z)
    (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa (.block AdxRotate8.tailAdd) s fun t =>
      cols t + 2 ^ 512 * (t.gpr .rax).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 + (word s.mem B (eU - 16)).toNat ∧
      (t.gpr .rax).toNat ≤ 2 ∧ t.mem = s.mem ∧
      Keeps [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.tailAdd
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (carryIn_ok hs hc (by omega) huZ hb) fun a ⟨ca,oa,ma,ka⟩ => ?_
  rw [show ([Instr.mov32 .rax (.imm 0), .mov .rdx (.mem AdxRotate8.tileCarry)] ++ _) =
    [Instr.mov32 .rax (.imm 0)] ++ ([.mov .rdx (.mem AdxRotate8.tileCarry)] ++ _) from rfl,
    WP.block_append_iff]
  refine WP.mono (movZero_ok a .rax) fun b ⟨zb,cb,ob,kb⟩ => ?_
  rw [WP.block_append_iff]
  have kab := ka.trans kb
  have hm := readSrc_word (hs.congr kab.2.2.2) (ea_tileCarry ((kab.gpr (by decide)).trans hc) he)
    (show eU - 16 + 8 ≤ Z by omega)
  refine WP.mono (movMem_ok b (dst := .rdx) hm) fun c ⟨dc,cc,oc,kc⟩ => ?_
  have kac := kab.trans kc
  rw [WP.block_append_iff]
  have srcA : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs c t →
      readSrc t (.mem (AdxRotate8.at_ .rsi (8*k))) = some (word s.mem B (eO+8*k)) := by
    intro k hk t kt
    rw [kt.readMem (by simp [AdxDualAdd.regs, AdxRotate8.at_]) (by intro r h; nomatch h),
      kac.readMem (by simp [AdxRotate8.at_]) (by intro r h; nomatch h)]
    exact readSrc_word hs (ea_at ho (8*k)) (by omega)
  have dc' : c.gpr .rdx = word s.mem B (eU - 16) := by rw [dc, kab.2.1]
  have zc : c.gpr .rax = 0 := (kc.gpr (by decide)).trans zb
  have srcB : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs c t →
      readSrc t (.reg (if k = 0 then .rdx else .rax)) =
        some (if k = 0 then word s.mem B (eU - 16) else 0) := by
    intro k _ t kt
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, readSrc, kt.gpr (r := .rdx) (by decide), dc']
    · simp only [hk, ↓reduceIte, readSrc, kt.gpr (r := .rax) (by decide), zc]
  have cC : c.cf = some (decide ((word s.mem B (eU - 8)).toNat = 1)) := cc.trans (cb.trans ca)
  have oC : c.of = some false := oc.trans (ob.trans oa)
  refine WP.mono (AdxDualAdd.chain_ok c _ _ _ _ cC oC srcA srcB
    (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h)) fun d ⟨cd,od,hcd,hod,ed,kd⟩ => ?_
  refine WP.mono (AdxDualAdd.close_ok d hcd hod ((kd.gpr (by decide)).trans zc))
    fun t ⟨et,_,_,kt⟩ => ?_
  rw [number_words, cols_keep kac.keep (by decide)] at ed
  simp only [number, Nat.reduceEqDiff, ↓reduceIte,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
    Bool.toNat_false] at ed
  have bit : (decide ((word s.mem B (eU - 8)).toNat = 1)).toNat = (word s.mem B (eU - 8)).toNat := by
    rcases (show (word s.mem B (eU - 8)).toNat = 0 ∨ (word s.mem B (eU - 8)).toNat = 1 by omega) with h | h <;>
      rw [h] <;> rfl
  rw [bit] at ed
  refine ⟨?_, ?_, kt.2.1.trans (kd.2.1.trans kac.2.1),
    (kac.trans (kd.trans kt)).mono (by simp [AdxDualAdd.regs])⟩
  · rw [cols_keep kt.keep (by decide), et]; omega_using [ed]
  · rw [et]; have b1 := Bool.toNat_le cd; have b2 := Bool.toNat_le od; omega

theorem tailCore_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 16 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z)
    (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa AdxRotate8.tailCore s fun t =>
      wv t.mem B eO 8 + 2 ^ 512 * (t.gpr .rax).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 +
          (word s.mem B (eU - 16)).toNat ∧
      (t.gpr .rax).toNat ≤ 3 ∧ Outside B eO 64 s.mem t.mem ∧
      Keep [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.tailCore
  refine WP.seq (WP.mono (tailAdd_ok hs hc ho he huZ hoZ hb) fun b ⟨eb,bb,mb,kb⟩ => ?_)
  refine WP.mono (storeCols_ok (hs.congr kb.2.2.2) ((kb.gpr (by decide)).trans ho) hoZ)
    fun t ⟨vt, ot, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, (kb.keep.trans kt).mono (by decide)⟩
  · rw [vt, kt.gpr (r := .rax) (by simp)]
    omega_using [eb]
  · rw [kt.gpr (r := .rax) (by simp)]
    omega_using [bb]
  · rw [mb] at ot; exact ot
end VG.Proof.Bignum.X86_64.AdxRotate8
