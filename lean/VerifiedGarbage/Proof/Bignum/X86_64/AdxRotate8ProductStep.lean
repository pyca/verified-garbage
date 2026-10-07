import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Store
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit

/-! Multiply a modulus block by one stored cancellation digit. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem storeMem_ok {s : State} {B : Addr} {Z e : Nat} {m : MemOp} {r : Reg}
    (hs : Scr s B Z) (hp : s.ea m = off B e) (he : e + 8 ≤ Z) :
    WP isa (.block [.store m r]) s fun t =>
      word t.mem B e = s.gpr r ∧ Outside B e 8 s.mem t.mem ∧ Keep [] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B e) (s.gpr r)) ?_ rfl)
    fun t ⟨hm, kt⟩ => ?_
  · xrun [hp, hs.st he]
  · rw [hm]
    exact ⟨word_writeW_self _ _ _ _, writeW_outside _ _ _ (by omega), kt⟩

theorem storeAt_ok {s : State} {B : Addr} {Z e d : Nat} {p r : Reg}
    (hs : Scr s B Z) (hp : s.gpr p = off B e) (he : e + d + 8 ≤ Z) :
    WP isa (.block [.store (at_ p d) r]) s fun t =>
      word t.mem B (e + d) = s.gpr r ∧ Outside B (e + d) 8 s.mem t.mem ∧ Keep [] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (e + d)) (s.gpr r)) ?_ rfl)
    fun t ⟨hm, kt⟩ => ?_
  · xrun [ea_at hp d, hs.st he]
  · rw [hm]
    exact ⟨word_writeW_self _ _ _ _, writeW_outside _ _ _ (by omega), kt⟩

theorem productStep_ok {s : State} {B : Addr} {Z eU eO eN k : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (hp : s.gpr .rbp = off B eN)
    (ho : s.gpr .rsi = off B eO) (huZ : eU + 8 * k + 8 ≤ Z)
    (hoZ : eO + 8 * k + 8 ≤ Z) (hnZ : eN + 64 ≤ Z) :
    WP isa (AdxRotate8.productStep k) s fun t =>
      (word t.mem B (eO + 8 * k)).toNat + 2 ^ 64 * cols t =
        cols s + (word s.mem B (eU + 8 * k)).toNat * wv s.mem B eN 8 ∧
      Outside B (eO + 8 * k) 8 s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hsrc := readSrc_word hs (ea_at hc (8 * k)) huZ
  unfold AdxRotate8.productStep
  refine WP.seq (WP.mono (movMem_ok s (dst := .rdx) hsrc) fun a ⟨ha, _, _, ka⟩ => ?_)
  refine WP.seq (WP.mono (core_mem (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans hp) hnZ)
    fun b ⟨eb, _, _, kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.mono (storeAt_ok (hs.congr kab.2.2.2) ((kab.gpr (by decide)).trans ho) hoZ)
    fun t ⟨wt, ot, kt⟩ => ?_
  rw [ha, ka.2.1, cols_keep ka.keep (by decide)] at eb
  refine ⟨?_, ?_, (kab.keep.trans kt).mono (by simp)⟩
  · rw [wt, cols_keep kt (by simp)]; exact eb
  · rw [kab.2.1] at ot; exact ot
end VG.Proof.Bignum.X86_64.AdxRotate8
