module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-! Selecting and storing a cancellation digit without changing the columns. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

def digitValue (s : State) (mi : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((s.gpr .r8).toNat * mi.toNat)

theorem cols_keep {s t : State} {rs : List Reg} (hk : Keep rs s t)
    (h : ∀ r ∈ [Reg.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15], r ∉ rs) : cols t = cols s := by
  unfold cols
  rw [hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp)),
    hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp)),
    hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp))]

theorem digit_ok {s : State} {B : Addr} {Z e m j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B e) (hi : s.gpr .rsi = idx m)
    (he : e + 8 * m + 8 * j + 8 ≤ Z)
    (hm : readSrc s (.mem (hdr sMinv)) = some mi) :
    WP isa (.block (AdxRotate8.digit (AdxRotate8.atx .rcx .rsi (64 + 8 * j)))) s fun t =>
      t.gpr .rdx = digitValue s mi ∧ cols t = cols s ∧
      word t.mem B (e + 8 * m + 8 * j) = digitValue s mi ∧
      Outside B (e + 8 * m + 8 * j) 8 s.mem t.mem ∧ Keep [.rdx, .rax] s t := by
  have hm' : s.load64 (s.gpr .rdi + BitVec.ofInt 64 (8 * (sMinv : Int))) = some mi := hm
  simp only [State.load64] at hm'
  unfold AdxRotate8.digit
  rw [show [Instr.mov .rdx (.reg .r8), .mulx .rax .rdx (.mem (hdr sMinv)),
      .store (AdxRotate8.atx .rcx .rsi (64 + 8 * j)) .rdx] =
    [.mov .rdx (.reg .r8), .mulx .rax .rdx (.mem (hdr sMinv))] ++
      [.store (AdxRotate8.atx .rcx .rsi (64 + 8 * j)) .rdx] from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun t => t.gpr .rdx = digitValue s mi ∧ t.mem = s.mem) ?_ rfl)
    fun a ⟨⟨hd, ma⟩, ka⟩ => ?_
  · xrun [execMulx, State.ea, hdr, hm']
    rfl
  refine WP.mono (storeMem_ok (hs.congr ka.2.2)
    (ea_atx ((ka.gpr (by decide)).trans hc) ((ka.gpr (by decide)).trans hi) (8 * j)) he)
    fun t ⟨wt, ot, kt⟩ => ?_
  have kat := ka.trans kt
  exact ⟨(kt.gpr (by decide)).trans hd, cols_keep kat (by decide), wt.trans hd, ma ▸ ot,
    kat.mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxRotate8
