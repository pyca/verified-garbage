module

public import VerifiedGarbage.Impl.AesXts.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# XTS-AES on PPC64LE: multiplication by `α`

`mulA` run once, in continuation-passing style, with its memory as explicit
writes (`alphaMem`): the canonical words of `mulAlpha_words64`
(`Proof/AesXts/Alpha.lean`), from the mask `0 − (hi >> 63)` (`mask_87`) and
the low word's top bit (`ushr63`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LE
open VG.Spec.Aes (bytesAt)

/-- The memory after `mulA` on the tweak at `Q`. -/
def alphaMem (m : Mem) (Q : Addr) : Mem :=
  (m.writeW Q ((m.readW Q 64 <<< 1) ^^^
      (if (m.readW (Q + BitVec.ofNat 64 8) 64).msb then (0x87 : BitVec 64) else 0))).writeW
    (Q + BitVec.ofNat 64 8) ((m.readW (Q + BitVec.ofNat 64 8) 64 <<< 1) |||
      (if (m.readW Q 64).msb then (1 : BitVec 64) else 0))

theorem ushr63 (x : BitVec 64) : x >>> 63 = if x.msb then (1 : BitVec 64) else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := x.isLt
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [decide_eq_true h]; show _ = 1; omega
  · rw [decide_eq_false h]; show _ = 0; omega

theorem mask_87 (x : BitVec 64) :
    (BitVec.ofNat 64 0 - x >>> 63) &&& BitVec.ofNat 64 0x87 = if x.msb then (0x87 : BitVec 64) else 0 := by
  rw [ushr63]; cases x.msb <;> decide

theorem wp_or {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem mulA_wp {s : State} {Q : Addr} {rest : List Instr} {Φ : State → Prop}
    (hq : s.gpr .r16 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8)
    (k : ∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = alphaMem s.mem Q → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (mulA ++ rest)) s Φ := by
  simp only [mulA, List.cons_append, List.nil_append]
  refine wp_ld (a := Q) (by decide) (by decide) (by rw [hq]; simp) r0 fun s₁ u₁ => ?_
  refine wp_ld (a := Q + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₁.other _ (by decide), hq])
    (by rw [u₁.rd, u₁.wr]; exact r8) fun s₂ u₂ => ?_
  refine wp_lsr (by decide) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => ?_
  refine wp_li (by decide) fun s₆ u₆ => wp_and fun s₇ u₇ => ?_
  refine wp_lsr (by decide) fun s₈ u₈ => wp_lsl (by decide) fun s₉ u₉ => wp_xor fun s₁₀ u₁₀ => ?_
  refine wp_lsl (by decide) fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => ?_
  have q₁₂ : s₁₂.gpr .r16 = Q := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hq]
  have m₁₂ : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hL : s₂.gpr .r9 = s.mem.readW Q 64 := by rw [u₂.other _ (by decide), u₁.gpr]
  have hH : s₂.gpr .r10 = s.mem.readW (Q + BitVec.ofNat 64 8) 64 := by rw [u₂.gpr, u₁.mem]
  have lo : s₁₂.gpr .r9 = (s.mem.readW Q 64 <<< 1) ^^^
      (if (s.mem.readW (Q + BitVec.ofNat 64 8) 64).msb then (0x87 : BitVec 64) else 0) := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₉.other .r11 (by decide),
      u₈.other .r9 (by decide), u₈.other .r11 (by decide), u₇.gpr, u₇.other .r9 (by decide), u₆.gpr,
      u₆.other .r11 (by decide), u₆.other .r9 (by decide), u₅.gpr, u₅.other .r9 (by decide), u₄.gpr,
      u₄.other .r11 (by decide), u₄.other .r9 (by decide), u₃.gpr, u₃.other .r9 (by decide), hL, hH, mask_87]
  have hi : s₁₂.gpr .r10 = (s.mem.readW (Q + BitVec.ofNat 64 8) 64 <<< 1) |||
      (if (s.mem.readW Q 64).msb then (1 : BitVec 64) else 0) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other .r12 (by decide), u₁₀.other .r10 (by decide), u₁₀.other .r12 (by decide),
      u₉.other .r10 (by decide), u₉.other .r12 (by decide), u₈.gpr, u₈.other .r10 (by decide),
      u₇.other .r10 (by decide), u₇.other .r9 (by decide), u₆.other .r10 (by decide),
      u₆.other .r9 (by decide), u₅.other .r10 (by decide), u₅.other .r9 (by decide), u₄.other .r10 (by decide),
      u₄.other .r9 (by decide), u₃.other .r10 (by decide), u₃.other .r9 (by decide), hL, hH, ushr63]
  refine wp_std (a := Q) (by decide) (by decide) (by rw [q₁₂]; simp)
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w0)
    fun s₁₃ u₁₃ => ?_
  refine wp_std (a := Q + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₁₃.gpr, q₁₂])
    (by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
        exact w8)
    fun s₁₄ u₁₄ => ?_
  refine k s₁₄ (fun r h9 h10 h11 h12 => ?_) ?_ ?_ ?_
  · rw [u₁₄.gpr, u₁₃.gpr, u₁₂.other _ h10, u₁₁.other _ h10, u₁₀.other _ h9, u₉.other _ h9, u₈.other _ h12,
      u₇.other _ h11, u₆.other _ h12, u₅.other _ h11, u₄.other _ h12, u₃.other _ h11, u₂.other _ h10,
      u₁.other _ h9]
  · rw [u₁₄.mem, u₁₃.gpr, u₁₃.mem, m₁₂, lo, hi]; rfl
  · rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd,
      u₁.rd]
  · rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr,
      u₁.wr]

theorem alphaMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (alphaMem m Q) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))

theorem alphaMem_bytes (m : Mem) (Q : Addr) : bytesAt (alphaMem m Q) Q 16 = Spec.Xts.mulAlpha (bytesAt m Q 16) :=
  AesXts.mulAlpha_words64 m Q

end VG.Proof.AesXts.PPC64LE
