module
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules

/-! # Saving System V callee-saved registers in caller scratch -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def savedMem (s : State) (B : Addr) : Mem :=
  (((((s.mem.writeW (off B 0) (s.gpr .rbx)).writeW (off B 8) (s.gpr .rbp)).writeW
    (off B 16) (s.gpr .r12)).writeW (off B 24) (s.gpr .r13)).writeW
    (off B 32) (s.gpr .r14)).writeW (off B 40) (s.gpr .r15)

theorem savedMem_word (s : State) (B : Addr) (i : Nat) (hi : i < 6) :
    word (savedMem s B) B (8 * i) = s.gpr (saved.getD i .rax) := by
  have other (mem : Mem) (v : BitVec 64) (d e : Nat) (h : e + 8 ≤ d ∨ d + 8 ≤ e)
      (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
      word (mem.writeW (off B d) v) B e = word mem B e :=
    (writeW_outside mem B v hd).word h he
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [savedMem, show 8 * 0 = 0 from rfl, show 8 * 1 = 8 from rfl,
      show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl, show 8 * 4 = 32 from rfl, show 8 * 5 = 40 from rfl]
    simp (disch := decide) only [other, word_writeW_self]
    rfl

theorem savedMem_frame (s : State) (B : Addr) : Outside B 0 48 s.mem (savedMem s B) := by
  intro x hx
  have h48 : 48 ≤ ofs B x := by omega
  unfold savedMem
  rw [writeW_outside _ B _ (d := 40) (by decide) x (Or.inr h48),
    writeW_outside _ B _ (d := 32) (by decide) x (Or.inr (by omega)),
    writeW_outside _ B _ (d := 24) (by decide) x (Or.inr (by omega)),
    writeW_outside _ B _ (d := 16) (by decide) x (Or.inr (by omega)),
    writeW_outside _ B _ (d := 8) (by decide) x (Or.inr (by omega)),
    writeW_outside _ B _ (d := 0) (by decide) x (Or.inr (by omega))]

theorem save_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : 48 ≤ Z) :
    WP isa (.block SignVerify.save) s fun t =>
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Outside B 0 48 s.mem t.mem ∧ Keep [] s t := by
  have he : SignVerify.save = [.store { base := .r11, disp := 0 } .rbx,
      .store { base := .r11, disp := 8 } .rbp, .store { base := .r11, disp := 16 } .r12,
      .store { base := .r11, disp := 24 } .r13, .store { base := .r11, disp := 32 } .r14,
      .store { base := .r11, disp := 40 } .r15] := rfl
  rw [he]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = savedMem s B) ?_ rfl)
    fun t ⟨hm, hk⟩ => ⟨fun i hi => by rw [hm]; exact savedMem_word s B i hi,
      by rw [hm]; exact savedMem_frame s B, hk⟩
  have h0 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by omega)
  xrun [State.ea, h11, h0, show B + BitVec.ofInt 64 0 = off B 0 from rfl,
    show B + BitVec.ofInt 64 8 = off B 8 from rfl, show B + BitVec.ofInt 64 16 = off B 16 from rfl,
    show B + BitVec.ofInt 64 24 = off B 24 from rfl, show B + BitVec.ofInt 64 32 = off B 32 from rfl,
    show B + BitVec.ofInt 64 40 = off B 40 from rfl,
    hs.st (d := 0) (by omega), hs.st (d := 8) (by omega), hs.st (d := 16) (by omega),
    hs.st (d := 24) (by omega), hs.st (d := 32) (by omega), hs.st (d := 40) hZ]
  simp only [savedMem, show off B 0 = B by simp [off]]

end VG.Proof.Dsa.X86_64
