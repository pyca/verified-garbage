module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.AesOcb.RISCV64.PadTo
public import VerifiedGarbage.Proof.AesOcb.RISCV64.RestTag
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesOcb.RISCV64

/-!
# AES-OCB on RISC-V: checking the tag (`recv`, `cmp`) and the mask (`mask`)

Untrusted: everything here is checked by Lean. `recv` copies the received
tag, padded with zeros, to `W` (`recv_ok`); `cmp` copies the first `tl`
bytes of the tag `open` computes, padded with zeros, to `W + vO`, and sets
`a0` to 1 if the two blocks are equal and 0 if not, without a branch
(`cmp_ok`: `1 − (0 <ᵤ x)` of the OR `x` of the XORs of their doublewords,
`cmpTail_ok`); `mask` ANDs every byte of the data, whose address it loads
from its slot in `W`, with `0 − a0`: the data stays if the tags were equal,
and is zeroed if not (`mask_ok`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/CmpMask.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros blockAtMem)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.AesGcm.RISCV64 (copyLoop_ok LoopPre LoopOut in_left in_off covers_off covers_left covers_prefix Keeps
  bytesAt_succ in_of_covers words_eq add_ofNat_assoc)

/-- The registers `recv` and `cmp` write. -/
abbrev cmpRegs : List Reg := [.t0, .t1, .t2, .t3, .a0, .a1, .a2, .a3]

/-- A copy of `tl` bytes from `S` to `W + d`, which holds 16 zero bytes. -/
theorem padCopy_ok {W : Addr} {s : State} (hw : Covers [⟨W, 2560⟩] s.wr) {S : Addr} {d tl : Nat}
    (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (hSr : Covers [⟨S, tl⟩] (s.rd ++ s.wr))
    (hSd : (⟨S, tl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩)
    (hz : bytesAt s.mem (W + BitVec.ofNat 64 d) 16 = zeros 16) (ha0 : s.gpr .a0 = S)
    (ha1 : s.gpr .a1 = W + BitVec.ofNat 64 d) (ha2 : s.gpr .a2 = BitVec.ofNat 64 tl) :
    WP isa Impl.AesGcm.RISCV64.copyLoop s fun s' => bytesAt s'.mem (W + BitVec.ofNat 64 d) 16 =
        bytesAt s.mem S tl ++ zeros (16 - tl) ∧
      Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem ∧ LoopOut s S (W + BitVec.ofNat 64 d) tl s' := by
  have lp : LoopPre s S (W + BitVec.ofNat 64 d) tl :=
    ⟨ha0, ha1, ha2, h1, by omega, hSr, covers_prefix (covers_off hw hd (by decide)) h16,
      hSd.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm, lo⟩ => ⟨?_, ?_, lo⟩
  · rw [hm, Proof.AesGcm.RISCV64.pad_bytes hz _ (by rw [length_bytesAt]; exact h16), length_bytesAt]
    rfl
  · rw [hm]
    exact (Proof.AesGcm.RISCV64.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩

/-- `recv`: the received tag (`tl` bytes at `T`, in `s9`), padded with zeros at `W`. -/
theorem recv_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) (hal : (V .s0).toNat % 8 = 0)
    {tl : Nat} (h8 : V .s8 = BitVec.ofNat 64 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (hTr : Covers [⟨V .s9, tl⟩] (s.rd ++ s.wr)) (hTd : (⟨V .s9, tl⟩ : Region).Disjoint ⟨V .s0, 2560⟩) :
    WP isa recv s fun s' => bytesAt s'.mem (V .s0 + BitVec.ofNat 64 tagO) 16 =
        bytesAt s.mem (V .s9) tl ++ zeros (16 - tl) ∧
      Frame [⟨V .s0 + BitVec.ofNat 64 tagO, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ cmpRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := E.perm.w
  have hTd' : (⟨V .s9, tl⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 tagO, 16⟩ :=
    hTd.sub_right (Lay.wSub (by decide))
  have hA : WP isa (.block (zero16 tagO ++ [Impl.AesGcm.RISCV64.mov .a0 .s9, Impl.AesGcm.RISCV64.mov .a1 .s0,
      Impl.AesGcm.RISCV64.mov .a2 .s8])) s fun s₂ =>
      bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 tagO) 16 = zeros 16 ∧
      Frame [⟨V .s0 + BitVec.ofNat 64 tagO, 16⟩] s.mem s₂.mem ∧
      s₂.gpr .a0 = V .s9 ∧ s₂.gpr .a1 = V .s0 + BitVec.ofNat 64 tagO ∧ s₂.gpr .a2 = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.sp = s.sp :=
    WP.block_append (WP.mono (zero16_ok (s := s) (d := tagO) hal (by decide) E.s0 (in_off hw (by decide) (by decide))
      (in_off hw (by decide) (by decide))) fun s₁ B₁ =>
      wp_mv fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_mv fun t₃ u₃ => WP.block_nil
        ⟨by rw [u₃.mem, u₂.mem, u₁.mem]; exact bytesAt_of_zero B₁.val,
          by rw [u₃.mem, u₂.mem, u₁.mem]; exact B₁.frame,
          by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, B₁.gpr _ (by decide), E.s9],
          by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), B₁.gpr _ (by decide), E.s0]
             exact (BitVec.add_zero _).symm,
          by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), E.s8, h8],
          fun r a b c d => by rw [u₃.other _ d, u₂.other _ c, u₁.other _ b, B₁.gpr r (by simp [a])],
          by rw [u₃.rd, u₂.rd, u₁.rd, B₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr, B₁.wr],
          by rw [u₃.sp, u₂.sp, u₁.sp, B₁.sp]⟩)
  unfold recv
  refine WP.seq (WP.mono hA fun s₂ ⟨hz, fz, a0, a1, a2, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  have hT₂ : bytesAt s₂.mem (V .s9) tl = bytesAt s.mem (V .s9) tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd') (by omega)
  refine WP.mono (padCopy_ok (W := V .s0) (d := tagO) (by rw [wr₂]; exact hw) (by decide) h1 h16
    (by rw [rd₂, wr₂]; exact hTr) hTd' hz a0 a1 a2) fun s' ⟨hb, hf, lo⟩ => ?_
  obtain ⟨rd', wr', sp'⟩ := lo.keeps
  exact ⟨by rw [hb, hT₂], fz.trans hf, fun r hr => by
      rw [lo.other r (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr)
        (ne_of_not_mem hr), g₂ r (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr)],
    by rw [sp', sp₂], by rw [rd', rd₂], by rw [wr', wr₂]⟩

/-- `1 − (0 <ᵤ x)`: 1 iff `x` is 0. -/
theorem sltu_value (x : BitVec 64) :
    BitVec.ofNat 64 1 - (if BitVec.ofNat 64 0 < x then 1 else 0) = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hl : BitVec.ofNat 64 0 < x := by rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hl), ite_eq_right_of_eq_false _ _ (eq_false h)]; decide

/-- `cmpTail`: `a0` is 1 iff the 16 bytes at `W` and `W + vO` are equal. -/
theorem cmpTail_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) (hal : (V .s0).toNat % 8 = 0) :
    WP isa (.block cmpTail) s fun s' =>
      s'.gpr .a0 = (if bytesAt s.mem (V .s0 + BitVec.ofNat 64 tagO) 16 =
        bytesAt s.mem (V .s0 + BitVec.ofNat 64 vO) 16 then 1 else 0) ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h31 := E.s0
  have r₀ := E.perm.wR (show 0 + 8 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 336 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 8 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 344 + 8 ≤ 2560 by decide)
  have hrun : WP isa (.block cmpTail) s fun s' =>
      s'.gpr .a0 = BitVec.ofNat 64 1 - (if BitVec.ofNat 64 0 < ((s.mem.readW (V .s0 + BitVec.ofNat 64 0) 64 ^^^
          s.mem.readW (V .s0 + BitVec.ofNat 64 336) 64) |||
        (s.mem.readW (V .s0 + BitVec.ofNat 64 8) 64 ^^^ s.mem.readW (V .s0 + BitVec.ofNat 64 344) 64))
        then 1 else 0) ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
    simp only [cmpTail, vO, tagO]
    refine wp_ld (off := 0) (a := V .s0 + BitVec.ofNat 64 0) (by decide) (by rw [h31])
      (Spill.al8 hal (by decide)) r₀ fun s₁ u₁ => ?_
    refine wp_ld (off := 336) (a := V .s0 + BitVec.ofNat 64 336) (by decide)
      (by rw [u₁.other _ (by decide), h31]) (Spill.al8 hal (by decide)) (by rw [u₁.rd, u₁.wr]; exact r₁)
      fun s₂ u₂ => ?_
    refine wp_xor fun s₃ u₃ => ?_
    refine wp_ld (off := 8) (a := V .s0 + BitVec.ofNat 64 8) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h31])
      (Spill.al8 hal (by decide)) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r₂) fun s₄ u₄ => ?_
    refine wp_ld (off := 344) (a := V .s0 + BitVec.ofNat 64 344) (by decide)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h31])
      (Spill.al8 hal (by decide))
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r₃) fun s₅ u₅ => ?_
    refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (imm := 0) (by decide) fun s₈ u₈ =>
      wp_sltu fun s₉ u₉ => wp_li (imm := 1) (by decide) fun s₁₀ u₁₀ => wp_sub fun s₁₁ u₁₁ => WP.block_nil ?_
    have m₁ : s₁.mem = s.mem := u₁.mem
    have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
    have x₃ : s₃.gpr .t1 = s.mem.readW (V .s0 + BitVec.ofNat 64 0) 64 ^^^
        s.mem.readW (V .s0 + BitVec.ofNat 64 336) 64 := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, m₁]
    have x₆ : s₆.gpr .t2 = s.mem.readW (V .s0 + BitVec.ofNat 64 8) 64 ^^^
        s.mem.readW (V .s0 + BitVec.ofNat 64 344) 64 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₅.gpr, m₃, m₄]
    have x₇ : s₇.gpr .t1 = (s.mem.readW (V .s0 + BitVec.ofNat 64 0) 64 ^^^
          s.mem.readW (V .s0 + BitVec.ofNat 64 336) 64) |||
        (s.mem.readW (V .s0 + BitVec.ofNat 64 8) 64 ^^^ s.mem.readW (V .s0 + BitVec.ofNat 64 344) 64) := by
      rw [u₇.gpr, x₆, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), x₃]
    have g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a0 → s₁₁.gpr r = s.gpr r := fun r a b c d => by
      rw [u₁₁.other _ d, u₁₀.other _ d, u₉.other _ a, u₈.other _ b, u₇.other _ a, u₆.other _ b, u₅.other _ c,
        u₄.other _ b, u₃.other _ a, u₂.other _ b, u₁.other _ a]
    refine ⟨?_, g, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₈.other _ (by decide), x₇]
    · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
    · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  refine WP.mono hrun fun s' ⟨h3, hg, hk⟩ => ⟨?_, hg, hk⟩
  rw [h3, sltu_value]
  have e := words_eq s.mem (V .s0 + BitVec.ofNat 64 0) (V .s0 + BitVec.ofNat 64 336)
  simp only [add_ofNat_assoc, Nat.reduceAdd] at e
  show _ = if bytesAt s.mem (V .s0 + BitVec.ofNat 64 0) 16 = bytesAt s.mem (V .s0 + BitVec.ofNat 64 336) 16
    then _ else _
  by_cases hq : bytesAt s.mem (V .s0 + BitVec.ofNat 64 0) 16 = bytesAt s.mem (V .s0 + BitVec.ofNat 64 336) 16
  · simp only [e.mpr hq, hq, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hq (e.mp h)), ite_eq_right_of_eq_false _ _ (eq_false hq)]

/-- `cmp`: the first `tl` bytes of the tag at `W + t2O`, padded with zeros
at `W + vO`, compared with the received tag at `W`. -/
theorem cmp_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) (hal : (V .s0).toNat % 8 = 0)
    {tl : Nat} (h8 : V .s8 = BitVec.ofNat 64 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa cmp s fun s' => s'.gpr .a0 = (if bytesAt s.mem (V .s0 + BitVec.ofNat 64 tagO) 16 =
        bytesAt s.mem (V .s0 + BitVec.ofNat 64 t2O) tl ++ zeros (16 - tl) then 1 else 0) ∧
      Frame [⟨V .s0 + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ cmpRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := E.perm.w
  have hSd : (⟨V .s0 + BitVec.ofNat 64 t2O, tl⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 vO, 16⟩ :=
    Offset.disjoint _ (.inl (by simp only [t2O, vO]; omega)) (by simp only [t2O]; omega) (by decide)
  have hA : WP isa (.block (zero16 vO ++ [.addi .a0 .s0 (t2O : Int), .addi .a1 .s0 (vO : Int),
      Impl.AesGcm.RISCV64.mov .a2 .s8])) s fun s₂ =>
      bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 vO) 16 = zeros 16 ∧
      Frame [⟨V .s0 + BitVec.ofNat 64 vO, 16⟩] s.mem s₂.mem ∧
      s₂.gpr .a0 = V .s0 + BitVec.ofNat 64 t2O ∧ s₂.gpr .a1 = V .s0 + BitVec.ofNat 64 vO ∧
      s₂.gpr .a2 = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.sp = s.sp :=
    WP.block_append (WP.mono (zero16_ok (s := s) (d := vO) hal (by decide) E.s0 (in_off hw (by decide) (by decide))
      (in_off hw (by decide) (by decide))) fun s₁ B₁ =>
      wp_addi (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ =>
        wp_mv fun t₃ u₃ => WP.block_nil
        ⟨by rw [u₃.mem, u₂.mem, u₁.mem]; exact bytesAt_of_zero B₁.val,
          by rw [u₃.mem, u₂.mem, u₁.mem]; exact B₁.frame,
          by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, B₁.gpr _ (by decide), E.s0],
          by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), B₁.gpr _ (by decide), E.s0],
          by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), E.s8, h8],
          fun r a b c d => by rw [u₃.other _ d, u₂.other _ c, u₁.other _ b, B₁.gpr r (by simp [a])],
          by rw [u₃.rd, u₂.rd, u₁.rd, B₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr, B₁.wr],
          by rw [u₃.sp, u₂.sp, u₁.sp, B₁.sp]⟩)
  unfold cmp
  refine WP.seq (WP.mono hA fun s₂ ⟨hz, fz, a0, a1, a2, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  have hS₂ : bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 t2O) tl = bytesAt s.mem (V .s0 + BitVec.ofNat 64 t2O) tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega)
  have dTV : ∀ r ∈ [(⟨V .s0 + BitVec.ofNat 64 vO, 16⟩ : Region)],
      (⟨V .s0 + BitVec.ofNat 64 tagO, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (padCopy_ok (W := V .s0) (d := vO) (by rw [wr₂]; exact hw) (by decide) h1 h16
    (by rw [rd₂, wr₂]; exact covers_left (covers_prefix (covers_off hw (d := t2O) (n := 16) (by decide) (by decide))
      h16)) hSd hz a0 a1 a2) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  obtain ⟨rd₃, wr₃, sp₃⟩ := lo.keeps
  have g₃ : ∀ r, r ∉ cmpRegs → s₃.gpr r = s.gpr r := fun r hr => by
    rw [lo.other r (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr)
      (ne_of_not_mem hr), g₂ r (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr)]
  have E₃ := E.others g₃ (by rw [sp₃, sp₂]) (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])
  have f₃ : Frame [⟨V .s0 + BitVec.ofNat 64 vO, 16⟩] s.mem s₃.mem := fz.trans hf
  have hT₃ : bytesAt s₃.mem (V .s0 + BitVec.ofNat 64 tagO) 16 = bytesAt s.mem (V .s0 + BitVec.ofNat 64 tagO) 16 :=
    Proof.Cmac.bytesAt_frame f₃ dTV (by omega)
  refine WP.mono (cmpTail_ok E₃ hal) fun s₄ ⟨a0₄, g₄, k₄⟩ => ⟨?_, by rw [k₄.mem]; exact f₃, fun r hr => ?_,
    by rw [k₄.sp, sp₃, sp₂], by rw [k₄.rd, rd₃, rd₂], by rw [k₄.wr, wr₃, wr₂]⟩
  · rw [a0₄, hT₃, hb, hS₂]
  · rw [g₄ r (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr), g₃ r hr]

/-! ## `mask` -/

theorem mask_byte (b : Byte) (c : Bool) :
    (BitVec.setWidth 64 b &&& (BitVec.ofNat 64 0 - (if c then 1 else 0))).setWidth 8 = if c then b else 0 := by
  cases c
  · simp
  · have h : BitVec.ofNat 64 0 - (if true = true then 1 else 0 : BitVec 64) = BitVec.allOnes 64 := by decide
    rw [h, BitVec.and_allOnes]
    simp only [↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := b.isLt
    omega

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- The registers `mask` writes. -/
abbrev maskRegs : List Reg := [.t2, .t5, .s4, .s5]

/-- `mask`: the `n` bytes of the data at `D` (in its slot in `W`, `n` in
`s11`) kept if `c` (`a0 = 1`), zeroed if not. -/
theorem mask_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) (hal : (V .s0).toNat % 8 = 0)
    {A D : Addr} {n : Nat} (hS : Slots (V .s0) A D s.mem) (h11 : V .s11 = BitVec.ofNat 64 n)
    (hD : DBuf (V .s2) (V .s0) s D n) {c : Bool} (h3 : s.gpr .a0 = if c then 1 else 0) :
    WP isa mask s fun t => t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) ∧
      (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hD.lt
  have hA : WP isa (.block [.load .d .s4 .s0 Impl.AesGcm.RISCV64.dataO, Impl.AesGcm.RISCV64.mov .s5 .s11,
      .li .t2 0, .sub .t5 .t2 .a0]) s fun s₁ =>
      s₁.gpr .s4 = D + BitVec.ofNat 64 0 ∧ s₁.gpr .s5 = BitVec.ofNat 64 (n - 0) ∧
      s₁.gpr .t5 = BitVec.ofNat 64 0 - (if c then 1 else 0) ∧
      (∀ r, r ∉ maskRegs → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ :=
    wp_ld (off := 240) (a := V .s0 + BitVec.ofNat 64 240) (by decide) (by rw [E.s0]) (Spill.al8 hal (by decide))
      (E.perm.wR (by decide)) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_li (imm := 0) (by decide) fun t₃ u₃ =>
      wp_sub fun t₄ u₄ => WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hS.data,
          BitVec.add_zero],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s11, h11]; rfl,
        by rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h3],
        fun r hr => by
          rw [u₄.other _ (ne_of_not_mem hr), u₃.other _ (ne_of_not_mem hr), u₂.other _ (ne_of_not_mem hr),
            u₁.other _ (ne_of_not_mem hr)],
        ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩⟩
  unfold mask
  refine WP.seq (WP.mono hA fun s₁ ⟨s4₁, s5₁, t5₁, g₁, k₁⟩ => ?_)
  refine WP.ite _ (eval_zero s5₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hz : n = 0 := by have := of_decide_eq_true h0; omega
    subst hz
    refine ⟨by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], g₁, k₁.sp, k₁.rd, k₁.wr⟩
  · have hpos : 0 < n := by have := of_decide_eq_false h0; omega
    refine WP.loop (M := isa)
      (fun (k : Nat) (u : State) => ∃ j, k = n - j ∧ j < n ∧ u.gpr .s4 = D + BitVec.ofNat 64 j ∧
        u.gpr .s5 = BitVec.ofNat 64 (n - j) ∧ u.gpr .t5 = BitVec.ofNat 64 0 - (if c then 1 else 0) ∧
        u.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
        (∀ r, r ∉ maskRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_
      (n - 0) _ ⟨0, rfl, hpos, by rw [s4₁], s5₁, t5₁,
        by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], g₁, k₁.sp, k₁.rd, k₁.wr⟩
    rintro k u ⟨j, rfl, hj, s4, s5, t5, mem, g, sp, rd, wr⟩
    have rq : InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 j) 1 := by
      rw [rd, wr]; exact in_of_covers hD.rd hj hn
    have wq : InRegions u.wr (D + BitVec.ofNat 64 j) 1 := by rw [wr]; exact in_of_covers hD.wr hj hn
    refine wp_lbu (off := 0) (a := D + BitVec.ofNat 64 j) (by decide) (by rw [s4, BitVec.add_zero]) rq
      fun u₁ v₁ => wp_and fun u₂ v₂ => wp_sb (off := 0) (a := D + BitVec.ofNat 64 j) (by decide)
        (by rw [v₂.other _ (by decide), v₁.other _ (by decide), s4, BitVec.add_zero])
        (by rw [v₂.wr, v₁.wr]; exact wq) fun u₃ v₃ => wp_addi (imm := 1) (by decide) fun u₄ v₄ =>
        wp_subi (imm := 1) (by decide) fun u₅ v₅ => WP.block_nil ?_
    have hl : (if c then bytesAt s.mem D j else zeros j).length = j := length_mask _ _ _ _
    have byte : u.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) := by
      rw [mem]; exact Proof.AesGcm.RISCV64.dst_kept hj hn _ hl
    have m₅ : u₅.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
      rw [v₅.mem, v₄.mem, v₃.mem, v₂.gpr, v₁.gpr, v₁.other _ (by decide), t5, byte,
        mask_byte, v₂.mem, v₁.mem, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl]
    have s5' : u₅.gpr .s5 = BitVec.ofNat 64 (n - (j + 1)) := by
      rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), s5,
        Proof.AesGcm.RISCV64.dec64 hj hn]
    have s4' : u₅.gpr .s4 = D + BitVec.ofNat 64 (j + 1) := by
      rw [v₅.other _ (by decide), v₄.gpr, v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), s4,
        Offset.add_add]
    have t5' : u₅.gpr .t5 = BitVec.ofNat 64 0 - (if c then 1 else 0) := by
      rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), t5]
    have g' : ∀ r, r ∉ maskRegs → u₅.gpr r = s.gpr r := fun r hr => by
      rw [v₅.other _ (ne_of_not_mem hr), v₄.other _ (ne_of_not_mem hr), v₃.gpr, v₂.other _ (ne_of_not_mem hr),
        v₁.other _ (ne_of_not_mem hr), g r hr]
    have ks : u₅.sp = s.sp ∧ u₅.rd = s.rd ∧ u₅.wr = s.wr :=
      ⟨by rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp], by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd],
        by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr]⟩
    have ev := eval_nonzero s5' (by omega)
    by_cases he : j + 1 = n
    · left
      exact ⟨ev.trans (by simp [he]), by rw [m₅, he], g', ks.1, ks.2.1, ks.2.2⟩
    · right
      exact ⟨ev.trans (by simp; omega), n - (j + 1), by omega, j + 1, rfl, by omega, s4', s5', t5', m₅, g',
        ks.1, ks.2.1, ks.2.2⟩

end VG.Proof.AesOcb.RISCV64
