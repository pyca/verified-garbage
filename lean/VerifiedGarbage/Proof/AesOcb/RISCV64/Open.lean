module

-- separate module: its proofs (about 2 s) build in parallel with the constant-time ones, `FrontCT` and `FnCT`
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Entry
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Hash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.AesOcb.RISCV64.RestTag
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Callee
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Args
import VerifiedGarbage.Proof.AesOcb.RISCV64.Offset0
import VerifiedGarbage.Proof.AesOcb.RISCV64.NonceBlock
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.AesOcb.RISCV64.LNtz
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.AesOcb.RISCV64.PadTo
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-! ### `AesOcb.RISCV64.CmpMask`, which this module and modules that import it used -/

section

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
  obtain lp : LoopPre s S (W + BitVec.ofNat 64 d) tl :=
    ⟨ha0, ha1, ha2, h1, by omega_using [h16], hSr, covers_prefix (covers_off hw hd (by decide)) h16,
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
  obtain hTd' : (⟨V .s9, tl⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 tagO, 16⟩ :=
    hTd.sub_right (Lay.wSub (by decide))
  obtain hA : WP isa (.block (zero16 tagO ++ [Impl.AesGcm.RISCV64.mov .a0 .s9, Impl.AesGcm.RISCV64.mov .a1 .s0,
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
  obtain hT₂ : bytesAt s₂.mem (V .s9) tl = bytesAt s.mem (V .s9) tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd') (by omega_using [h16])
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
    obtain hl : BitVec.ofNat 64 0 < x := by rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega_using [hx]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hl), ite_eq_right_of_eq_false _ _ (eq_false h)]; decide

/-- `cmpTail`: `a0` is 1 iff the 16 bytes at `W` and `W + vO` are equal. -/
theorem cmpTail_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) (hal : (V .s0).toNat % 8 = 0) :
    WP isa (.block cmpTail) s fun s' =>
      s'.gpr .a0 = (if bytesAt s.mem (V .s0 + BitVec.ofNat 64 tagO) 16 =
        bytesAt s.mem (V .s0 + BitVec.ofNat 64 vO) 16 then 1 else 0) ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h31 := E.s0
  obtain r₀ := E.perm.wR (show 0 + 8 ≤ 2560 by decide)
  obtain r₁ := E.perm.wR (show 336 + 8 ≤ 2560 by decide)
  obtain r₂ := E.perm.wR (show 8 + 8 ≤ 2560 by decide)
  obtain r₃ := E.perm.wR (show 344 + 8 ≤ 2560 by decide)
  obtain hrun : WP isa (.block cmpTail) s fun s' =>
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
    obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
    obtain x₃ : s₃.gpr .t1 = s.mem.readW (V .s0 + BitVec.ofNat 64 0) 64 ^^^
        s.mem.readW (V .s0 + BitVec.ofNat 64 336) 64 := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, m₁]
    obtain x₆ : s₆.gpr .t2 = s.mem.readW (V .s0 + BitVec.ofNat 64 8) 64 ^^^
        s.mem.readW (V .s0 + BitVec.ofNat 64 344) 64 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₅.gpr, m₃, m₄]
    obtain x₇ : s₇.gpr .t1 = (s.mem.readW (V .s0 + BitVec.ofNat 64 0) 64 ^^^
          s.mem.readW (V .s0 + BitVec.ofNat 64 336) 64) |||
        (s.mem.readW (V .s0 + BitVec.ofNat 64 8) 64 ^^^ s.mem.readW (V .s0 + BitVec.ofNat 64 344) 64) := by
      rw [u₇.gpr, x₆, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), x₃]
    obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a0 → s₁₁.gpr r = s.gpr r := fun r a b c d => by
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
  obtain e := words_eq s.mem (V .s0 + BitVec.ofNat 64 0) (V .s0 + BitVec.ofNat 64 336)
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
  obtain hSd : (⟨V .s0 + BitVec.ofNat 64 t2O, tl⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 vO, 16⟩ :=
    Offset.disjoint _ (.inl (by simp only [t2O, vO]; omega_using [h16])) (by simp only [t2O]; omega_using [h16]) (by decide)
  obtain hA : WP isa (.block (zero16 vO ++ [.addi .a0 .s0 (t2O : Int), .addi .a1 .s0 (vO : Int),
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
  obtain hS₂ : bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 t2O) tl = bytesAt s.mem (V .s0 + BitVec.ofNat 64 t2O) tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega_using [h16])
  obtain dTV : ∀ r ∈ [(⟨V .s0 + BitVec.ofNat 64 vO, 16⟩ : Region)],
      (⟨V .s0 + BitVec.ofNat 64 tagO, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (padCopy_ok (W := V .s0) (d := vO) (by rw [wr₂]; exact hw) (by decide) h1 h16
    (by rw [rd₂, wr₂]; exact covers_left (covers_prefix (covers_off hw (d := t2O) (n := 16) (by decide) (by decide))
      h16)) hSd hz a0 a1 a2) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  obtain ⟨rd₃, wr₃, sp₃⟩ := lo.keeps
  obtain g₃ : ∀ r, r ∉ cmpRegs → s₃.gpr r = s.gpr r := fun r hr => by
    rw [lo.other r (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr)
      (ne_of_not_mem hr), g₂ r (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr) (ne_of_not_mem hr)]
  obtain E₃ := E.others g₃ (by rw [sp₃, sp₂]) (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])
  obtain f₃ : Frame [⟨V .s0 + BitVec.ofNat 64 vO, 16⟩] s.mem s₃.mem := fz.trans hf
  obtain hT₃ : bytesAt s₃.mem (V .s0 + BitVec.ofNat 64 tagO) 16 = bytesAt s.mem (V .s0 + BitVec.ofNat 64 tagO) 16 :=
    Proof.Cmac.bytesAt_frame f₃ dTV (by omega_using [])
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
    omega_using []

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
  obtain hA : WP isa (.block [.load .d .s4 .s0 Impl.AesGcm.RISCV64.dataO, Impl.AesGcm.RISCV64.mov .s5 .s11,
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
  refine WP.ite _ (eval_zero s5₁ (by omega_using [hn])) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hz : n = 0 := by have := of_decide_eq_true h0; omega_using [this]
    subst hz
    refine ⟨by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], g₁, k₁.sp, k₁.rd, k₁.wr⟩
  · have hpos : 0 < n := by have := of_decide_eq_false h0; omega_using [this]
    refine WP.loop (M := isa)
      (fun (k : Nat) (u : State) => ∃ j, k = n - j ∧ j < n ∧ u.gpr .s4 = D + BitVec.ofNat 64 j ∧
        u.gpr .s5 = BitVec.ofNat 64 (n - j) ∧ u.gpr .t5 = BitVec.ofNat 64 0 - (if c then 1 else 0) ∧
        u.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
        (∀ r, r ∉ maskRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_
      (n - 0) _ ⟨0, rfl, hpos, by rw [s4₁], s5₁, t5₁,
        by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], g₁, k₁.sp, k₁.rd, k₁.wr⟩
    rintro k u ⟨j, rfl, hj, s4, s5, t5, mem, g, sp, rd, wr⟩
    obtain rq : InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 j) 1 := by
      rw [rd, wr]; exact in_of_covers hD.rd hj hn
    obtain wq : InRegions u.wr (D + BitVec.ofNat 64 j) 1 := by rw [wr]; exact in_of_covers hD.wr hj hn
    refine wp_lbu (off := 0) (a := D + BitVec.ofNat 64 j) (by decide) (by rw [s4, BitVec.add_zero]) rq
      fun u₁ v₁ => wp_and fun u₂ v₂ => wp_sb (off := 0) (a := D + BitVec.ofNat 64 j) (by decide)
        (by rw [v₂.other _ (by decide), v₁.other _ (by decide), s4, BitVec.add_zero])
        (by rw [v₂.wr, v₁.wr]; exact wq) fun u₃ v₃ => wp_addi (imm := 1) (by decide) fun u₄ v₄ =>
        wp_subi (imm := 1) (by decide) fun u₅ v₅ => WP.block_nil ?_
    obtain hl : (if c then bytesAt s.mem D j else zeros j).length = j := length_mask _ _ _ _
    obtain byte : u.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) := by
      rw [mem]; exact Proof.AesGcm.RISCV64.dst_kept hj hn _ hl
    obtain m₅ : u₅.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
      rw [v₅.mem, v₄.mem, v₃.mem, v₂.gpr, v₁.gpr, v₁.other _ (by decide), t5, byte,
        mask_byte, v₂.mem, v₁.mem, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [hl]; omega_using [hn, hj]), hl]
    obtain s5' : u₅.gpr .s5 = BitVec.ofNat 64 (n - (j + 1)) := by
      rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), s5,
        Proof.AesGcm.RISCV64.dec64 hj hn]
    obtain s4' : u₅.gpr .s4 = D + BitVec.ofNat 64 (j + 1) := by
      rw [v₅.other _ (by decide), v₄.gpr, v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), s4,
        Offset.add_add]
    obtain t5' : u₅.gpr .t5 = BitVec.ofNat 64 0 - (if c then 1 else 0) := by
      rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), t5]
    obtain g' : ∀ r, r ∉ maskRegs → u₅.gpr r = s.gpr r := fun r hr => by
      rw [v₅.other _ (ne_of_not_mem hr), v₄.other _ (ne_of_not_mem hr), v₃.gpr, v₂.other _ (ne_of_not_mem hr),
        v₁.other _ (ne_of_not_mem hr), g r hr]
    obtain ks : u₅.sp = s.sp ∧ u₅.rd = s.rd ∧ u₅.wr = s.wr :=
      ⟨by rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp], by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd],
        by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr]⟩
    obtain ev := eval_nonzero s5' (by omega_using [hn])
    by_cases he : j + 1 = n
    · left
      exact ⟨ev.trans (by simp [he]), by rw [m₅, he], g', ks.1, ks.2.1, ks.2.2⟩
    · right
      exact ⟨ev.trans (by simp; omega_using [hj, he]), n - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], s4', s5', t5', m₅, g',
        ks.1, ks.2.1, ks.2.2⟩

end VG.Proof.AesOcb.RISCV64

end

end

/-! ### `AesOcb.RISCV64.Seal`, which this module and modules that import it used -/

section

/-! ### `AesOcb.RISCV64.Body`, which this module and modules that import it used -/

section

/-! ### `AesOcb.RISCV64.Whole`, which this module and modules that import it used -/

section

/-! ### `AesOcb.RISCV64.Pass`, which this module and modules that import it used -/

section

/-!
# AES-OCB on RISCV64: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. A pass over the `m` whole
blocks of the data computes each block's offset (`lNtz_ok`, `xorB_ok`),
replaces the block with `fB` of it and the offset, and the checksum with
`fC` of them (`BodyOk`: `xorOfs`, `addCk` then `xorOfs`, `xorOfs` then
`addCk`); `pass_ok` gives the blocks and the checksum after all `m`. As on
PPC64LE (`Proof/AesOcb/PPC64LE/Body.lean`), but the data's blocks, which
need not be aligned, are XORed with the offset (`xorLoop`) and copied to
`W + t2O` to be added to the checksum (`copyLoop`) a byte at a time.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz ofBytes)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (in_left in_off covers_off covers_left LoopPre LoopOut copyLoop_ok xorLoop_ok
  xorBytes length_xorBytes bytesAt_writeBytes_self' writeBytes_frame')

/-- The registers a body writes. -/
abbrev bodyRegs : List Reg := [.t0, .t1, .t2, .a0, .a1, .a2, .a3]

/-- What a body leaves: the block at `B` and the checksum, written only
there and at `W + t2O`. -/
structure BodyPost (W B : Addr) (vB vC : Block) (t t' : State) : Prop where
  blk : blockAtMem t'.mem B = vB
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = vC
  frame : Frame [⟨B, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩] t.mem t'.mem
  gpr : ∀ r, r ∉ bodyRegs → t'.gpr r = t.gpr r
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

/-- What a body does to the block at `B` (in `s4`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (W : Addr) (body : Prog isa) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) :
    Prop :=
  ∀ (t : State) (B : Addr), t.gpr .s4 = B → t.gpr .s0 = W →
    Covers [⟨B, 16⟩] (t.rd ++ t.wr) → Covers [⟨B, 16⟩] t.wr →
    Covers [⟨W, 2560⟩] t.wr → (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩ →
    WP isa body t (BodyPost W B (fB (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)))
      (fC (blockAtMem t.mem (W + BitVec.ofNat 64 ckO)) (blockAtMem t.mem B)
        (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO))) t)

/-- The block at `B` after writing 16 bytes there. -/
theorem blockAtMem_write (m : Mem) (B : Addr) {xs : List Byte} (hx : xs.length = 16) :
    blockAtMem (writeBytes m B xs) B = ofBytes xs := by
  rw [blockAtMem, bytesAt_writeBytes_self' m B hx (by decide)]

/-- `xorOfs`: the block at `B` XORed with the offset. -/
theorem xorOfs_ok {W : Addr} : BodyOk W xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B h4 h0 hBr hBw hw hBW
  unfold xorOfs
  refine WP.seq (wp_addi (imm := ofsO) (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ =>
    wp_li (imm := 16) (by decide) fun t₃ u₃ => WP.block_nil ?_)
  obtain m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain rd₃ : t₃.rd = t.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain lp : LoopPre t₃ (W + BitVec.ofNat 64 ofsO) B 16 :=
    ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h0],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4], u₃.gpr, by decide, by decide,
      by rw [rd₃, wr₃]; exact covers_left (covers_off hw (by decide) (by decide)),
      by rw [wr₃]; exact hBw, (hBW.sub_right (Lay.wSub (by decide))).symm⟩
  refine WP.mono (xorLoop_ok t₃ lp) fun t' ⟨hm, lo⟩ => ?_
  rw [m₃] at hm
  obtain hl := length_xorBytes t.mem B (W + BitVec.ofNat 64 ofsO) 16
  obtain fw : Frame [⟨B, 16⟩] t.mem t'.mem := by rw [hm]; exact writeBytes_frame' _ hl
  refine ⟨?_, ?_, fw.mono (by simp), fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hm, blockAtMem_write _ _ hl, xorBytes]
    exact Proof.Ocb.ofBytes_xor (Proof.Ocb.length_bytesAt _ _ _) (Proof.Ocb.length_bytesAt _ _ _)
  · exact blockAtMem_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hBW.sub_right (Lay.wSub (by decide))).symm
  · simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n0, -, -, n3, n4, n5, n6⟩ := hr
    rw [lo.other r n0 n3 n4 n5 n6, u₃.other r n5, u₂.other r n4, u₁.other r n3]
  · rw [lo.keeps.2.2, u₃.sp, u₂.sp, u₁.sp]
  · rw [lo.keeps.1, rd₃]
  · rw [lo.keeps.2.1, wr₃]

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {W : Addr} (hW : W.toNat % 8 = 0) :
    BodyOk W addCk (fun b _ => b) (fun c b _ => c ^^^ b) := by
  intro t B h4 h0 hBr hBw hw hBW
  unfold addCk
  refine WP.seq (wp_mv fun t₁ u₁ => wp_addi (imm := t2O) (by decide) fun t₂ u₂ =>
    wp_li (imm := 16) (by decide) fun t₃ u₃ => WP.block_nil ?_)
  obtain m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain rd₃ : t₃.rd = t.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain lp : LoopPre t₃ B (W + BitVec.ofNat 64 t2O) 16 :=
    ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h4],
      by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h0], u₃.gpr, by decide, by decide,
      by rw [rd₃, wr₃]; exact hBr, by rw [wr₃]; exact covers_off hw (by decide) (by decide),
      hBW.sub_right (Lay.wSub (by decide))⟩
  refine WP.seq (WP.mono (copyLoop_ok t₃ lp) fun t₄ ⟨hm, lo⟩ => ?_)
  rw [m₃] at hm
  obtain hl := Proof.Ocb.length_bytesAt t.mem B 16
  obtain fw : Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩] t.mem t₄.mem := by rw [hm]; exact writeBytes_frame' _ hl
  obtain g₄ : ∀ r, r ∉ bodyRegs → t₄.gpr r = t.gpr r := fun r hr => by
    simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n0, -, -, n3, n4, n5, n6⟩ := hr
    rw [lo.other r n0 n3 n4 n5 n6, u₃.other r n5, u₂.other r n4, u₁.other r n3]
  obtain rd₄ : t₄.rd = t.rd := by rw [lo.keeps.1, rd₃]
  obtain wr₄ : t₄.wr = t.wr := by rw [lo.keeps.2.1, wr₃]
  obtain hw₄ : Covers [⟨W, 2560⟩] t₄.wr := by rw [wr₄]; exact hw
  obtain h0₄ : t₄.gpr .s0 = W := by rw [g₄ _ (by decide), h0]
  refine WP.mono (xorB_ok (s := t₄) (pd := ckO) (qd := t2O) (cd := ckO) hW hW hW (by decide) (by decide)
    (by decide) h0₄ h0₄ h0₄ (by decide) (by decide) (by decide) (in_left (in_off hw₄ (by decide) (by decide)))
    (in_left (in_off hw₄ (by decide) (by decide))) (in_left (in_off hw₄ (by decide) (by decide)))
    (in_left (in_off hw₄ (by decide) (by decide))) (in_off hw₄ (by decide) (by decide))
    (in_off hw₄ (by decide) (by decide)) (Offset.sep _ (.inr (by decide)) (by decide) (by decide))
    (Offset.sep _ (.inr (by decide)) (by decide) (by decide))) fun t' B' => ?_
  obtain dB : ∀ d, d + 16 ≤ 2560 → (⟨B, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩ :=
    fun _ hd => hBW.sub_right (Lay.wSub hd)
  obtain kB : blockAtMem t'.mem B = blockAtMem t.mem B := by
    rw [blockAtMem_frame B'.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dB _ (by decide)),
      blockAtMem_frame fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dB _ (by decide))]
  refine ⟨kB, ?_, (fw.mono (by simp)).trans (B'.frame.mono (by simp)), fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [B'.val, hm, blockAtMem_write _ _ hl, blockAtMem_frame (writeBytes_frame' t.mem hl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))]
    rfl
  · rw [B'.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])), g₄ r hr]
  · rw [B'.sp, lo.keeps.2.2, u₃.sp, u₂.sp, u₁.sp]
  · rw [B'.rd, rd₄]
  · rw [B'.wr, wr₄]

/-- The offset, after a body. -/
theorem BodyPost.ofs {W B : Addr} {vB vC : Block} {t t' : State} (h : BodyPost W B vB vC t t')
    (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) = blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) :=
  blockAtMem_frame h.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hBW.sub_right (Lay.wSub (by decide))).symm
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

/-- Two bodies, one after the other. -/
theorem BodyOk.seq {W : Addr} {p q : Prog isa} {fB₁ fB₂ : Block → Block → Block}
    {fC₁ fC₂ : Block → Block → Block → Block} (h₁ : BodyOk W p fB₁ fC₁) (h₂ : BodyOk W q fB₂ fC₂) :
    BodyOk W (.seq p q) (fun b o => fB₂ (fB₁ b o) o) (fun c b o => fC₂ (fC₁ c b o) (fB₁ b o) o) := by
  intro t B h4 h0 hBr hBw hw hBW
  refine WP.seq (WP.mono (h₁ t B h4 h0 hBr hBw hw hBW) fun t₁ P₁ => ?_)
  refine WP.mono (h₂ t₁ B (by rw [P₁.gpr _ (by decide), h4]) (by rw [P₁.gpr _ (by decide), h0])
    (by rw [P₁.rd, P₁.wr]; exact hBr) (by rw [P₁.wr]; exact hBw) (by rw [P₁.wr]; exact hw) hBW) fun t₂ P₂ => ?_
  rw [P₁.blk, P₁.ck, P₁.ofs hBW] at P₂
  exact ⟨P₂.blk, P₂.ck, P₁.frame.trans P₂.frame, fun r hr => by rw [P₂.gpr r hr, P₁.gpr r hr],
    by rw [P₂.sp, P₁.sp], by rw [P₂.rd, P₁.rd], by rw [P₂.wr, P₁.wr]⟩

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {W : Addr} (hW : W.toNat % 8 = 0) :
    BodyOk W (.seq addCk xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) :=
  (addCk_ok hW).seq xorOfs_ok

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {W : Addr} (hW : W.toNat % 8 = 0) :
    BodyOk W (.seq xorOfs addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) :=
  xorOfs_ok.seq (addCk_ok hW)

/-- The registers the offset and a body write. -/
abbrev stepRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a2, .a3, .a5]

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a2, .a3, .a5, .s4, .s5, .s6]

theorem ntz_step : ∀ r ∈ ntzRegs, r ∈ stepRegs := by decide
theorem body_step : ∀ r ∈ bodyRegs, r ∈ stepRegs := by decide
theorem t12_step : ∀ r ∈ [Reg.t1, Reg.t2], r ∈ stepRegs := by decide
theorem step_pass : ∀ r ∈ stepRegs, r ∈ passRegs := by decide

theorem pass_step_regs {r : Reg} (hr : r ∉ passRegs) : r ∉ stepRegs ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 :=
  ⟨fun h => hr (step_pass r h), by rintro rfl; exact hr (by decide), by rintro rfl; exact hr (by decide),
    by rintro rfl; exact hr (by decide)⟩

theorem frozen_step : ∀ r ∈ Proof.AesGcm.RISCV64.frozen, r ∉ passRegs := by decide

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them. -/
structure PassInv (V : Reg → BitVec 64) (sp D : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block)
    (fB : Block → Block → Block) (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env V sp t
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 lO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩, ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  s4 : t.gpr .s4 = D + BitVec.ofNat 64 (16 * i)
  s6 : t.gpr .s6 = BitVec.ofNat 64 (i + 1)
  s5 : t.gpr .s5 = BitVec.ofNat 64 (m - i)
  ofs : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ∉ passRegs → t.gpr r = t₀.gpr r

theorem pass_step {V : Reg → BitVec 64} {sp D : Addr} (L : Lay (V .s2) (V .s0)) {m : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block}
    {body : Prog isa} (hB : BodyOk (V .s0) body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf (V .s2) (V .s0) t₀ D (16 * m)) {t : State} {i : Nat} (hi : i < m)
    (P : PassInv V sp D m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.seq body (.block nextBlock))) t fun t' =>
      PassInv V sp D m O0 l X fB ckF t₀ t' (i + 1) := by
  obtain hDt : DBuf (V .s2) (V .s0) t D (16 * m) := hD.of_eq P.rd P.wr
  have hm := hD.lt
  obtain hBi := hDt.slice (a := 16 * i) (k := 16) (by omega_arith)
  have E := P.env
  have hw := E.perm.w
  have hW := L.wal
  refine WP.seq (WP.seq (WP.mono (lNtz_ok E.s0 hW hw (by omega_arith) (by omega_arith) P.s6 P.l0)
    fun t₁ P₁ => ?_))
  obtain h0₁ : t₁.gpr .s0 = V .s0 := by rw [P₁.gpr _ (by decide), E.s0]
  obtain hw₁ : Covers [⟨V .s0, 2560⟩] t₁.wr := by rw [P₁.wr]; exact hw
  refine WP.mono (xorB_ok (s := t₁) (pd := ofsO) (qd := lO) (cd := ofsO) hW hW hW (by decide) (by decide)
    (by decide) h0₁ h0₁ h0₁ (by decide) (by decide) (by decide) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_off hw₁ (by decide) (by decide))
    (in_off hw₁ (by decide) (by decide)) (Offset.sep _ (.inr (by decide)) (by decide) (by decide))
    (Offset.sep _ (.inr (by decide)) (by decide) (by decide))) fun t₂ B₂ => ?_
  obtain g₂ : ∀ r, r ∉ stepRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (t12_step r h)), P₁.gpr r (fun h => hr (ntz_step r h))]
  obtain rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  obtain wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  obtain sp₂ : t₂.sp = t.sp := by rw [B₂.sp, P₁.sp]
  obtain h0₂ : t₂.gpr .s0 = V .s0 := by rw [g₂ _ (by decide), E.s0]
  obtain h4₂ : t₂.gpr .s4 = D + BitVec.ofNat 64 (16 * i) := by rw [g₂ _ (by decide), P.s4]
  obtain fW₂ : Frame [⟨V .s0 + BitVec.ofNat 64 lO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  obtain kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ →
      blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  obtain ofs₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  obtain ck₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  obtain Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  obtain l0₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0 := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  refine WP.seq (WP.mono (hB t₂ _ h4₂ h0₂ (by rw [rd₂, wr₂]; exact hBi.rd) (by rw [wr₂]; exact hBi.wr)
    (by rw [wr₂]; exact hw) hBi.w) fun t₃ P₃ => ?_)
  obtain g₃ : ∀ r, r ∉ stepRegs → t₃.gpr r = t.gpr r := fun r hr => by rw [P₃.gpr r (fun h => hr (body_step r h)), g₂ r hr]
  obtain s5₃ : t₃.gpr .s5 = BitVec.ofNat 64 (m - i) := by rw [g₃ _ (by decide), P.s5]
  obtain s6₃ : t₃.gpr .s6 = BitVec.ofNat 64 (i + 1) := by rw [g₃ _ (by decide), P.s6]
  obtain s4₃ : t₃.gpr .s4 = D + BitVec.ofNat 64 (16 * i) := by rw [g₃ _ (by decide), P.s4]
  obtain kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [blockAtMem_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  obtain dWB : ∀ d, d + 16 ≤ 2560 →
      (⟨V .s0 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ :=
    fun _ hd => (hBi.w.sub_right (Lay.wSub hd)).symm
  unfold nextBlock
  refine wp_addi (imm := 16) (by decide) fun t₄ u₄ => wp_addi (imm := 1) (by decide) fun t₅ u₅ =>
    wp_subi (imm := 1) (by decide) fun t₆ u₆ => WP.block_nil ?_
  obtain hmem : t₆.mem = t₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  refine
    { env := E.keep (fun r hr => by
          obtain ⟨h0, h4, h5, h6⟩ := pass_step_regs (frozen_step r hr)
          rw [u₆.other _ h5, u₅.other _ h6, u₄.other _ h4, g₃ r h0])
        (by rw [u₆.sp, u₅.sp, u₄.sp, P₃.sp, sp₂]) (by rw [u₆.rd, u₅.rd, u₄.rd, P₃.rd, rd₂])
        (by rw [u₆.wr, u₅.wr, u₄.wr, P₃.wr, wr₂])
      frame := by
        rw [hmem]
        exact P.frame.trans ((fW₂.mono (by simp)).trans (P₃.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega_arith)⟩
          · exact ⟨_, by simp, fun _ h => h⟩
          · exact ⟨_, by simp, fun _ h => h⟩))
      rd := by rw [u₆.rd, u₅.rd, u₄.rd, P₃.rd, rd₂, P.rd]
      wr := by rw [u₆.wr, u₅.wr, u₄.wr, P₃.wr, wr₂, P.wr]
      s4 := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, s4₃, Offset.add_add,
          show 16 * i + 16 = 16 * (i + 1) by omega_arith]
      s6 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), s6₃, ← BitVec.ofNat_add]
      s5 := by
        rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), s5₃, Offset.ofNat_sub_ofNat (by omega_arith),
          Nat.sub_sub]
      ofs := by
        rw [hmem, blockAtMem_frame P₃.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact dWB _ (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
      ck := by rw [hmem, P₃.ck, ck₂, Bi₂, ofs₂, hckF i hi]
      blk := fun k hk => ?_
      l0 := by
        rw [hmem, blockAtMem_frame P₃.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact dWB _ (by decide)
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), l0₂]
      gpr := fun r hr => by
        obtain ⟨h0, h4, h5, h6⟩ := pass_step_regs hr
        rw [u₆.other _ h5, u₅.other _ h6, u₄.other _ h4, g₃ r h0, P.gpr r hr] }
  rw [hmem]
  by_cases hki : k = i
  · subst hki
    rw [P₃.blk, Bi₂, ofs₂]; simp
  · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega_arith)
    rw [kB₃ (Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)) hBk.w, P.blk k hk]
    by_cases hk' : k < i
    · simp [hk', show k < i + 1 by omega_arith]
    · simp [hk', show ¬ k < i + 1 by omega_arith]

theorem pass_ok {V : Reg → BitVec 64} {sp D : Addr} (L : Lay (V .s2) (V .s0)) {m : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block}
    {body : Prog isa} (hB : BodyOk (V .s0) body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf (V .s2) (V .s0) t₀ D (16 * m)) {j : Nat} (hj : j < m) {t : State}
    (P : PassInv V sp D m O0 l X fB ckF t₀ t j) :
    WP isa (pass body) t (fun t' => PassInv V sp D m O0 l X fB ckF t₀ t' m) := by
  have hm := hD.lt
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv V sp D m O0 l X fB ckF t₀ u i) ?_
    (m - j) _ ⟨j, rfl, hj, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hD hi P) fun u' P' => ?_
  obtain ev := eval_nonzero P'.s5 (by omega_arith)
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨ev.trans (by simp [he]), (show i + 1 = m by omega_arith) ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp [he]), m - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, P'⟩

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISCV64: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs a
pass with `pre` over the `m` whole blocks of the data, calls `f` on all of
them (`callBlocks_ok`), copies `Offset_0` back and runs a pass with `post`
(`whole_ok`): each block becomes `G (X ⊕ Offset_i) ⊕ Offset_i`, and the
checksum is the second pass's. As on PPC64LE
(`Proof/AesOcb/PPC64LE/Body.lean`), but the data's address is loaded from
its slot in `W` (`Slots`), which the passes and the call keep.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (in_left in_off shr4 Keeps)
open VG.Impl.AesGcm.RISCV64 (dataO)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
copy of a block, the working space of the functions called and the data. -/
abbrev wholeR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 256, 16⟩,
    ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem wholeR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wholeR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- The data's address, in its slot, after writes within `wholeR`. -/
theorem slot_kept {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (wholeR W D n) m m') :
    m'.readW (W + BitVec.ofNat 64 dataO) 64 = m.readW (W + BitVec.ofNat 64 dataO) 64 :=
  (wholeR_mut h).readW (r := ⟨W + BitVec.ofNat 64 dataO, 8⟩) (Region.contains_self _ _)
    (kept_mut L hD ⟨by decide, by decide⟩) (by decide)

/-- The first `k` bytes of a buffer, as a buffer at the same place. -/
theorem DBuf.take' {K W : Addr} {s : State} {D : Addr} {n k : Nat} (h : DBuf K W s D n) (hk : k ≤ n) :
    DBuf K W s D k := by
  have := h.slice (a := 0) (k := k) (by omega_using [hk])
  rwa [BitVec.add_zero] at this

/-- The `m` blocks of the data, `len` (in `s11`) bytes at the address in
its slot. -/
theorem dataArgs_ok {W D : Addr} {t : State} (hs0 : t.gpr .s0 = W)
    (hal : (W + BitVec.ofNat 64 dataO).toNat % 8 = 0) (hin : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 dataO) 8)
    (hS : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D) {len : Nat} (hl : len < 2 ^ 64)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 len) :
    ArgsOk [.load .d .a2 .s0 dataO, .shift .srl .d .a3 .s11 4] t D (len / 16) := by
  refine ⟨(t.write .a2 (t.mem.readW (t.gpr .s0 + BitVec.ofNat 64 dataO) 64)).write .a3
      ((t.write .a2 (t.mem.readW (t.gpr .s0 + BitVec.ofNat 64 dataO) 64)).gpr .s11 >>> 4), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, hs0, hS],
    by rw [gpr_write_self, gpr_write_of_ne _ _ (by decide), h11, shr4 hl],
    fun r h5 h6 => by rw [gpr_write_of_ne _ _ h6, gpr_write_of_ne _ _ h5], ⟨rfl, rfl, rfl, rfl⟩⟩
  simp only [runBlock_cons, runStep_some,
    exec_load_d (show dataO < 2048 by decide) (by rw [hs0]; exact hal) (by rw [hs0]; exact hin)]
  rfl

/-- The start of a pass: `s4 ← D`, `s5 ← m`, `s6 ← 1`. -/
theorem passStart_ok {W D : Addr} {t : State} (hs0 : t.gpr .s0 = W)
    (hal : (W + BitVec.ofNat 64 dataO).toNat % 8 = 0) (hin : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 dataO) 8)
    (hS : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D) {len : Nat} (hl : len < 2 ^ 64)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 len) :
    WP isa (.block passStart) t fun t' =>
      t'.gpr .s4 = D + BitVec.ofNat 64 (16 * 0) ∧ t'.gpr .s5 = BitVec.ofNat 64 (len / 16 - 0) ∧
      t'.gpr .s6 = BitVec.ofNat 64 (0 + 1) ∧ (∀ r, r ∉ [.s4, .s5, .s6] → t'.gpr r = t.gpr r) ∧ Keeps t t' := by
  unfold passStart
  refine wp_ld (a := W + BitVec.ofNat 64 dataO) (by decide) (by rw [hs0]) hal hin fun t₁ u₁ =>
    wp_srl (by decide) fun t₂ u₂ => wp_li (imm := 1) (by decide) fun t₃ u₃ => WP.block_nil
    ⟨?_, ?_, ?_, fun r hr => ?_, ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd],
      by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hS]; simp
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h11, shr4 hl]; rfl
  · rw [u₃.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]

/-- What `whole` leaves. -/
structure WholePost (V : Reg → BitVec 64) (sp D : Addr) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block)
    (t t' : State) : Prop where
  env : Env V sp t'
  frame : Frame (wholeR (V .s0) D (16 * m)) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ckO) = ck

/-- A pass's writes, within `wholeR`. -/
theorem pass_sub {W D : Addr} {n : Nat} :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨D, n⟩], ∃ r' ∈ wholeR W D n,
        Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : Prog isa} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    {V : Reg → BitVec 64} {sp : Addr}
    (hB1 : BodyOk (V .s0) pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk (V .s0) post (fun b o => b ^^^ o) fC2)
    (L : Lay (V .s2) (V .s0)) {t : State} (E : Env V sp t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {len : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 len) {D : Addr} (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) t D len) (hm0 : 0 < len / 16)
    {O0 l : Block}
    (hofs : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (len / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt t.mem (V .s2) (16 * (R + 1)))
        (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole (.call name c) pre post) t (WholePost V sp D (len / 16) O0 l
      (fun k => G (bytesAt t.mem (V .s2) (16 * (R + 1)))
        (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 (len / 16)) t) := by
  have hl := hD.lt
  generalize hmd : len / 16 = m at *
  obtain hmn : 16 * m ≤ len := by omega_using [hmd]
  obtain hDm := hD.take' hmn
  obtain hal := L.alW (d := dataO) (by decide)
  -- the first pass
  unfold whole
  refine WP.seq (WP.mono (passStart_ok E.s0 hal (E.perm.wR (by decide)) hS hl (E.s11.trans h11))
    fun s₁ ⟨s4₁, s5₁, s6₁, g₁, k₁⟩ => ?_)
  rw [hmd] at s5₁
  obtain E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  obtain hD₁ : DBuf (V .s2) (V .s0) s₁ D (16 * m) := hDm.of_eq k₁.rd k₁.wr
  obtain P₀ : PassInv V sp D m O0 l (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, s4 := s4₁, s6 := s6₁, s5 := s5₁
      ofs := by rw [k₁.mem, hofs]; rfl
      ck := by rw [k₁.mem, hck]
      blk := fun k _ => by simp
      l0 := by rw [k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i _ => by rw [hckF1, k₁.mem]) hD₁ hm0 P₀) fun s₂ P₂ => ?_)
  obtain hD₂ : DBuf (V .s2) (V .s0) s₂ D (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  obtain F₂ : Frame (wholeR (V .s0) D (16 * m)) t.mem s₂.mem := by rw [← k₁.mem]; exact P₂.frame.sub pass_sub
  obtain S₂ : s₂.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hD₁.w F₂, hS]
  refine WP.assoc (WP.seq (WP.mono (callBlocks_ok (f := f) L ok nf hR hs3 P₂.env
    (fun s₃ g₃ k₃ => by
      have := dataArgs_ok (t := s₃) (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.s0]) hal
        (by rw [k₃.rd, k₃.wr]; exact P₂.env.perm.wR (by decide)) (by rw [k₃.mem, S₂]) hl
        (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.s11, h11])
      rwa [hmd] at this) (dstD hD₂)) fun s₃ P₃ => ?_))
  obtain E₃ := P₃.env P₂.env
  obtain kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂
  obtain kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 256) ∨
      (272 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega_using [hd]))).symm) (L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 256) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega_using [hd]))).symm)]
  obtain o0₃ : blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), k₁.mem, ho0]
  obtain F₃ : Frame (wholeR (V .s0) D (16 * m)) t.mem s₃.mem :=
    F₂.trans (P₃.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  -- `Offset_0` again
  refine WP.seq (WP.block_append (WP.mono (copy16_ok (s := s₃) (a := o0O) (d := ofsO) L.wal (by decide)
    (by decide) E₃.s0 (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide))
    (E₃.perm.wW (by decide))) fun s₄a B₄ => ?_))
  obtain F₄a : Frame (wholeR (V .s0) D (16 * m)) t.mem s₄a.mem :=
    F₃.trans (B₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
        (by decide)⟩)
  refine WP.mono (passStart_ok (t := s₄a) (D := D) (by rw [B₄.gpr _ (by decide), E₃.s0]) hal
    (by rw [B₄.rd, B₄.wr]; exact E₃.perm.wR (by decide)) (by rw [slot_kept L hD₁.w F₄a, hS]) hl
    (by rw [B₄.gpr _ (by decide), E₃.s11, h11])) fun s₄ ⟨s4₄, s5₄, s6₄, g₄, k₄⟩ => ?_
  obtain E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  rw [hmd] at s5₄
  obtain E₄ := E₄a.others g₄ k₄.sp k₄.rd k₄.wr
  obtain hD₄ : DBuf (V .s2) (V .s0) s₄ D (16 * m) :=
    hD₂.of_eq (by rw [k₄.rd, B₄.rd, P₃.rd]) (by rw [k₄.wr, B₄.wr, P₃.wr])
  obtain kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .s0, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [k₄.mem]; exact blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  obtain hK : bytesAt s₂.mem (V .s2) (16 * (R + 1)) = bytesAt t.mem (V .s2) (16 * (R + 1)) := by
    obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.Cmac.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega_using [hR]), k₁.mem]
  obtain X₄ : ∀ k < m, blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem (V .s2) (16 * (R + 1)))
        (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega_using [hk])).w, hcall P₃ k hk, hK, P₂.blk k hk]
      simp only [hk, ↓reduceIte, k₁.mem]
  obtain ck₃ : blockAtMem s₃.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide)),
      P₂.ck, hckF2₀]
  obtain P₀' : PassInv V sp D m O0 l (fun k => blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, s4 := s4₄, s6 := s6₄, s5 := s5₄
      ofs := by rw [k₄.mem, B₄.val, o0₃]; rfl
      ck := by
        rw [k₄.mem, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [k₄.mem, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          kWP (by decide), k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hD₄ hm0 P₀') fun s₅ P₅ => ?_
  refine ⟨P₅.env, ?_, by rw [P₅.rd, k₄.rd, B₄.rd, P₃.rd, P₂.rd, k₁.rd],
    by rw [P₅.wr, k₄.wr, B₄.wr, P₃.wr, P₂.wr, k₁.wr], fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · have F₅ := P₅.frame
    rw [k₄.mem] at F₅
    exact F₄a.trans (F₅.sub pass_sub)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.RISCV64

end

end

/-! ### `AesOcb.RISCV64.Nonce`, which this module and modules that import it used -/

section

/-!
# AES-OCB on RISC-V: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `encOne_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`). As on PPC64LE (`Proof/AesOcb/PPC64LE/Nonce.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxInv ctxLstar)
open VG.Proof.Ocb (blockAtMem_frame)

/-- The key schedule, after a frame within the parts the pieces write. -/
theorem ctxCiph_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [Proof.Cmac.bytesAt_frame h (fun r hr => (k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hR])]

theorem ctxLstar_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') : ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => (k_mut L hD r hr).sub_left (Lay.kSub (by decide))

/-- What `nonce` writes: `[16, 128)` and `[256, 2560)` of `W`. -/
abbrev nonceR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 112⟩, wB W]

theorem nonceR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (nonceR W) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact in_mutA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- A part of `W` within `[16, 128)` or from 256 on, as a part `nonce` writes. -/
theorem in_nonceR {W : Addr} {d k : Nat} (h : (16 ≤ d ∧ d + k ≤ 128) ∨ (256 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r' ∈ nonceR W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W h₁ (by omega_using [h₂])⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB h₁ h₂⟩

/-- What `nonce` leaves. -/
structure NonceOk (V : Reg → BitVec 64) (sp : Addr) (o : Block) (s s' : State) : Prop where
  env : Env V sp s'
  frame : Frame (nonceR (V .s0)) s.mem s'.mem
  ofs : blockAtMem s'.mem (V .s0 + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (V .s0 + BitVec.ofNat 64 o0O) = o
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
    blockAtMem s'.mem (V .s0 + BitVec.ofNat 64 d) = blockAtMem s.mem (V .s0 + BitVec.ofNat 64 d)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {s : State} (E : Env V sp s)
    {N : Addr} {nl t : Nat} (hs4 : s.gpr .s4 = N) (hs5 : s.gpr .s5 = BitVec.ofNat 64 nl)
    (hs8 : V .s8 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64) (hB : Buf (V .s0) s N nl)
    {D : Addr} {n : Nat} (hKD : (⟨V .s2, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa nonce s (NonceOk V sp (Spec.Ocb.offset0 (ctxCiph s.mem (V .s2) R) t (bytesAt s.mem N nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E.s0 E.perm.w hs4 hs5 (E.s8.trans hs8) h1 h15 ht hB) fun s₁ P₁ => ?_)
  have E₁ : Env V sp s₁ := E.others P₁.gpr P₁.sp P₁.rd P₁.wr
  have F₁ : Frame (nonceR (V .s0)) s.mem s₁.mem := P₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  refine WP.seq (WP.mono (encOne_ok L hR hs3 E₁ (d := tmpO) (by decide)) fun s₂ P₂ => ?_)
  have E₂ : Env V sp s₂ := P₂.env E₁
  have F₂ : Frame (nonceR (V .s0)) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  have ktop : blockAtMem s₂.mem (V .s0 + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem (V .s2) R (Proof.Ocb.nonceN t (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    rw [P₂.enc0, P₁.blk]
    exact congrFun (ctxCiph_mut L hKD (nonceR_mut F₁) hR) _
  have hbv : ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  have bot₂ : s₂.mem.readW (V .s0 + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    rw [P₂.frame.readW (r := ⟨V .s0 + BitVec.ofNat 64 botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), P₁.bot]
  refine WP.mono (offset0_ok L E₂.s0 E₂.perm.w hbv bot₂) fun s₃ P₃ => ?_
  refine ⟨E₂.others P₃.gpr P₃.sp P₃.rd P₃.wr,
    F₁.trans (F₂.trans (P₃.frame.sub fun r hr => ?_)), ?_, ?_, fun {d} h₁ h₂ => ?_, by rw [P₃.rd, P₂.rd, P₁.rd],
    by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [ofsO, o0O]; omega_arith) (by omega_using [h₂]) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (by simp only [tmpO]; omega_using [h₂]) (by omega_using [h₂]) (by decide)
        · exact L.w_w (by omega_using [h₂]) (by omega_using [h₂]) (by decide)),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [tmpO, botO]; omega_using [h₂]) (by omega_using [h₂]) (by decide))]

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISC-V: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs the whole blocks,
if any (`wholeIte_ok`), and the rest, if any (`restIte_ok`): for `seal`
`OCB-ENCRYPT`'s ciphertext, offset and checksum (`bodySeal_ok`), for `open`
`OCB-DECRYPT`'s (`bodyOpen_ok`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/Body.lean`), but the data's address is in its slot in
`W` (`Slots`), from which the whole blocks and the rest load it.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (and15 shr4 ofNat_sub64 Keeps)
open VG.Impl.AesGcm.RISCV64 (dataO)

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : Prog isa} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    {V : Reg → BitVec 64} {sp : Addr}
    (hB1 : BodyOk (V .s0) pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk (V .s0) post (fun b o => b ^^^ o) fC2)
    (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 l : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem (V .s2) (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.shift .srl .d .t1 .s11 4]) (.ite (.zero .t1) (.block []) (whole (.call name c) pre post))) s
      (WholePost V sp D (n / 16) O0 l
        (fun k => G (bytesAt s.mem (V .s2) (16 * (R + 1)))
          (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have t1₁ : s₁.gpr .t1 = BitVec.ofNat 64 (n / 16) := by rw [u₁.gpr, E.s11, h11, shr4 hn]
  have E₁ : Env V sp s₁ := E.others (rs := [.t1]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr
  refine WP.ite _ (eval_zero t1₁ (by omega_using [hn])) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [u₁.mem]; exact Frame.refl _ _, u₁.rd, u₁.wr, fun k hk => absurd hk (by omega_using [hm]),
      by rw [u₁.mem, hofs, hm]; rfl, by rw [u₁.mem, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    have hD₁ := hD.of_eq u₁.rd u₁.wr
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nf hcall hB1 hB2 L E₁ hR hs3 h11 (by rw [u₁.mem, hS]) hD₁
      (by omega_using [hm]) (by rw [u₁.mem, hofs]) (by rw [u₁.mem, ho0]) (by rw [u₁.mem, hck]) (by rw [u₁.mem, hl0])
      (fun i => by rw [u₁.mem, hckF1]) hckF2₀ (fun i => by rw [u₁.mem, hckF2])) fun t P => ?_
    refine ⟨P.env, by have f := P.frame; rwa [u₁.mem] at f, by rw [P.rd, u₁.rd], by rw [P.wr, u₁.wr],
      fun k hk => by rw [P.blk k hk, u₁.mem], P.ofs, by rw [P.ck]⟩

theorem andi15 (x : BitVec 64) : x &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 (x.toNat % 16) := and15 x

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {V : Reg → BitVec 64} {sp : Addr} {K : Addr} (L : Lay K (V .s0)) {t : State} (E : Env V sp t)
    {n : Nat} (hn : n < 2 ^ 64) (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) :
    WP isa (.block [.logicImm .and .s5 .s11 15, .sub .s4 .s11 .s5, .load .d .t1 .s0 dataO, .add .s4 .s4 .t1]) t
      fun t₁ => t₁.gpr .s4 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .s5 = BitVec.ofNat 64 (n % 16) ∧
        (∀ r, r ∉ [.t1, .s4, .s5] → t₁.gpr r = t.gpr r) ∧ Keeps t t₁ := by
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega_using []]
  refine wp_andi (by decide) fun t₁ u₁ => wp_sub fun t₂ u₂ => ?_
  have s5₁ : t₁.gpr .s5 = BitVec.ofNat 64 (n % 16) := by
    rw [u₁.gpr, E.s11, h11, andi15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have s4₂ : t₂.gpr .s4 = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [u₂.gpr, u₁.other _ (by decide), E.s11, h11, s5₁, hsub]
  refine wp_ld (a := V .s0 + BitVec.ofNat 64 dataO) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s0]) (L.alW (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun t₃ u₃ => wp_add fun t₄ u₄ =>
    WP.block_nil ⟨?_, ?_, fun r hr => ?_, ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩⟩
  · rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), s4₂, u₂.mem, u₁.mem, hS, BitVec.add_comm]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), s5₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.1, u₁.other _ hr.2.2]

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) :
    Prop where
  env : Env V sp t'
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩,
    ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .s2)
    else blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem (V .s2) R
        (blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .s2))))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ckO) =
    if 0 < r then
      blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (enc : Bool) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {t : State}
    (E : Env V sp t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) t D n) :
    WP isa (.seq (.block [.logicImm .and .s5 .s11 15, .sub .s4 .s11 .s5, .load .d .t1 .s0 dataO, .add .s4 .s4 .t1])
        (.ite (.zero .s5) (.block []) (rest enc))) t
      (TailPost enc V sp R (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  refine WP.seq (WP.mono (bodyTail_ok L E hn h11 hS) fun t₁ ⟨s4₁, s5₁, g₁, k₁⟩ => ?_)
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  refine WP.ite _ (eval_zero s5₁ (by omega_using [])) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega_using [this]
    refine ⟨E₁, by rw [k₁.mem]; exact Frame.refl _ _, k₁.rd, k₁.wr, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, k₁.mem]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega_using [this]
    have hP : DBuf (V .s2) (V .s0) t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_using [])).of_eq k₁.rd k₁.wr
    refine WP.mono (rest_ok enc L E₁ hR hs3 hr (Nat.mod_lt _ (by decide)) s4₁ s5₁ hP) fun t' P => ?_
    refine ⟨P.env, by rw [← k₁.mem]; exact P.frame, by rw [P.rd, k₁.rd], by rw [P.wr, k₁.wr], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, k₁.mem]
    · rw [P.out, k₁.mem]
    · rw [P.ck, k₁.mem]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called and the data. -/
abbrev bodyR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 256, 16⟩,
    ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem bodyR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (bodyR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyOut (V : Reg → BitVec 64) (sp D : Addr) (n : Nat) (out : List Byte) (ofs ck : Block) (s t : State) :
    Prop where
  env : Env V sp t
  frame : Frame (bodyR (V .s0) D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt p i) :
    ckOf X m = Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega_using [hi])), h m (by omega_using [])]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega_using [hi]))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega_using [])]

/-- `ENCIPHER` from the key schedule, whatever its length. -/
def encG (ks : List Byte) : Cipher := Spec.Ocb.aesWith (ks.length / 16 - 1) ks

/-- `DECIPHER` from the key schedule, whatever its length. -/
def decG (ks : List Byte) : Cipher := Spec.Ocb.aesInvWith (ks.length / 16 - 1) ks

theorem encG_eq (m : Mem) (K : Addr) (R : Nat) : encG (bytesAt m K (16 * (R + 1))) = ctxCiph m K R := by
  rw [encG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega_using []]; rfl

theorem decG_eq (m : Mem) (K : Addr) (R : Nat) : decG (bytesAt m K (16 * (R + 1))) = Spec.Ocb.ctxInv m K R := by
  rw [decG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega_using []]; rfl

theorem hcall_enc {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.cipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      encG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.enc hi, encG_eq]; rfl

theorem hcall_dec {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.invCipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      decG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.dec hi, decG_eq]; rfl

/-- A buffer apart from `W` and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

/-- A buffer apart from `W` and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ wholeR W D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

theorem wholeR_sub {W D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W D k, ∃ r' ∈ bodyR W D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR W D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (body true) s (BodyOut V sp D n
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2))))
      else Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)
       else offAt O0 (ctxLstar s.mem (V .s2)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .s2) (V .s0) s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .s2) (V .s0) s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_using [])
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega_using [hn])
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega_using [hi])).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2))
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames hcall_enc (sealPre_ok L.wal) xorOfs_ok L E hR hs3
    h11 hS hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .s0) D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hSt : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm.w Pw.frame, hS]
  refine WP.mono (restIte_ok true L Pw.env hR hs3 h11 hSt (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .s2) R = ctxCiph s.mem (V .s2) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .s2) = ctxLstar s.mem (V .s2) := ctxLstar_mut L hDm.k fW
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega_using [])
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega_using []]
  have ckT : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega_using [hn]), Proof.Ocb.bytesAt_blocks,
      Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_using []))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega_using []] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [↓reduceIte, show n % 16 = 0 by omega_using [hr], b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega_using [hi])), h m (by omega_using [])]

/-- `body` for `open`. -/
theorem bodyOpen_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (body false) s (BodyOut V sp D n
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2))))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)
       else offAt O0 (ctxLstar s.mem (V .s2)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .s2) (V .s0) s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .s2) (V .s0) s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_using [])
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega_using [hn])
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega_using [hi])).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .s2) (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .s2)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .s2)) (i + 1))
    Proof.Aes.RISCV64.decryptBlocks_correct decryptBlocks_noFrames hcall_dec xorOfs_ok (openPost_ok L.wal) L E hR hs3
    h11 hS hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .s0) D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hSt : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm.w Pw.frame, hS]
  refine WP.mono (restIte_ok false L Pw.env hR hs3 h11 hSt (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .s2) R = ctxCiph s.mem (V .s2) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .s2) = ctxLstar s.mem (V .s2) := ctxLstar_mut L hDm.k fW
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega_using [])
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega_using []]
  have ckT : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega_using [hn]), Proof.Ocb.bytesAt_blocks,
      Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega_using []] at e
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_using []))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [↓reduceIte, show n % 16 = 0 by omega_using [hr], b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.RISCV64

end

end

/-! ### `AesOcb.RISCV64.Contract`, which this module and modules that import it used -/

section

/-!
# AES-OCB on RISCV64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, with the working space as a
last argument (`Proof/AesOcb/Scratch.lean`), which imply these
(`Verified.lean`). As on PPC64LE (`Proof/AesOcb/PPC64LE/FnCT.lean`): a
call (`jal`) stores nothing in memory, so no stack is used; `seal` and `open`
read `tag`, `tag_len` and `work` from the stack, at the stack pointer, which
they may only read; the stack pointer is aligned, and so are `ctx` and
`work` (`Abi.alignsU64`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- The key context. -/
abbrev aCtx (s : State) : Region := ⟨s.gpr .a0, 256⟩

/-- The nonce. -/
abbrev aNonce (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩

/-- The associated data. -/
abbrev aAad (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩

/-- The data. -/
abbrev aData (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩

/-- The tag. -/
abbrev aTag (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩

/-- The working space. -/
abbrev aWork (s : State) : Region := ⟨stackArg s 2, 2560⟩

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need of their arguments
`(ctx = a0, rounds = a1, nonce = a2, nonce_len = a3, aad = a4, aad_len = a5,
data = a6, len = a7, tag = [sp], tag_len = [sp + 8], work = [sp + 16])`, but
for what they may access. -/
def oneFacts (s : State) : Prop :=
  (aCtx s).Disjoint (aData s) ∧ (aCtx s).Disjoint (aWork s) ∧ (aNonce s).Disjoint (aData s) ∧
    (aNonce s).Disjoint (aWork s) ∧ (aAad s).Disjoint (aData s) ∧ (aAad s).Disjoint (aWork s) ∧
    (aTag s).Disjoint (aData s) ∧ (aTag s).Disjoint (aWork s) ∧
    (aData s).Disjoint (aWork s) ∧ (aData s).Disjoint (args s 3) ∧ (aWork s).Disjoint (args s 3) ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ (stackArgAddr s 0).toNat + 24 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ (stackArg s 2).toNat % 8 = 0 ∧ rounds (s.gpr .a1) ∧
    lengthsOk (stackArg s 1).toNat (s.gpr .a3).toNat = true

/-- What `vg_aes_ocb_seal` needs: it may write the data, the tag and the
working space. -/
def sealPreA (s : State) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, args s 3] ∧ s.wr = [aData s, aTag s, aWork s] ∧
    (aTag s).Disjoint (args s 3) ∧ (aCtx s).Disjoint (aTag s) ∧ (aNonce s).Disjoint (aTag s) ∧
    (aAad s).Disjoint (aTag s) ∧ oneFacts s

/-- What `vg_aes_ocb_open` needs: it may write the data and the working
space, and read the tag. -/
def openPreA (s : State) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, aTag s, args s 3] ∧ s.wr = [aData s, aWork s] ∧ oneFacts s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ocb_seal`. -/
def sealRISCV64 : Contract isa where
  pre := sealPreA
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxLstar s.mem (s.gpr .a0)) (stackArg s 1).toNat
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
        (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat) =
      (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat, bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := onePub

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxInv s.mem (s.gpr .a0) (s.gpr .a1).toNat)
    (ctxLstar s.mem (s.gpr .a0)) (stackArg s 1).toNat (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds (s.gpr .a1) then [] else [if (openOut s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openRISCV64 : Contract isa where
  pre := openPreA
  post s s' :=
    match openOut s with
    | some pt => (s'.gpr .a0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat = pt
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat = zeros (s.gpr .a7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISC-V: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreA`
and `openPreA` give the facts the proofs use about the arguments (`FnArgs`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, `Offset_0`
(`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W` (`tag`);
then the copy of the tag to `tag` (`tagOut`), and `restore` (`seal_wp`). The
environment after the entry is the state's own registers (`EntryPost`), and
the addresses of the associated data and the data are in their slots in `W`
(`Slots`). As on PPC64LE (`Proof/AesOcb/PPC64LE/FnCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (covers_mem covers_left covers_prefix in_left in_off SavedAt savedR oneR Keeps Keeps')

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`) and the
working space at `W`. -/
structure FnArgs (s : State) (K W N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  lay : Lay K W
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W s N nl
  aad : Buf W s A al
  data : DBuf K W s D n
  tag : Buf W s T tl
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  td : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  args : Covers [⟨stackArgAddr s 0, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨stackArgAddr s 0, 24⟩ : Region).Disjoint ⟨W, 2560⟩
  sa : s.sp.toNat % 16 = 0

/-- `FnArgs` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the arguments on the
stack and the tag, and write the data and `W`. -/
theorem args_of {s : State} (h : oneFacts s)
    (mrd : ∀ r ∈ [aCtx s, aNonce s, aAad s, args s 3, aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [aData s, aWork s], Covers [r] s.wr) :
    FnArgs s (s.gpr .a0) (stackArg s 2) (s.gpr .a2) (s.gpr .a4) (s.gpr .a6) (s.gpr .a1).toNat (s.gpr .a3).toNat
      (s.gpr .a5).toNat (s.gpr .a7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, _, d11, b12, b13, b14, b15, bt, b16, _, hsa, kal, wal, hR, hv⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  exact {
    lay := ⟨b12, b16, d2, kal, wal⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b13, d4⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b14, d6⟩
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b15, d9⟩, mwr _ (by simp), d1⟩
    tag := ⟨mrd _ (by simp), BitVec.isLt _, bt, d8⟩
    nd := d3
    ad := d5
    td := d7
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    args := mrd (args s 3) (by simp)
    argsW := d11.symm
    sa := hsa }

theorem sealArgs_of {s : State} (h : sealPreA s) :
    FnArgs s (s.gpr .a0) (stackArg s 2) (s.gpr .a2) (s.gpr .a4) (s.gpr .a6) (s.gpr .a1).toNat (s.gpr .a3).toNat
      (s.gpr .a5).toNat (s.gpr .a7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_mem (by simp))

theorem openArgs_of {s : State} (h : openPreA s) :
    FnArgs s (s.gpr .a0) (stackArg s 2) (s.gpr .a2) (s.gpr .a4) (s.gpr .a6) (s.gpr .a1).toNat (s.gpr .a3).toNat
      (s.gpr .a5).toNat (s.gpr .a7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-! ## Frames -/

/-- A frame within `W`. -/
theorem frameW {W : Addr} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨W, 2560⟩) : Frame [⟨W, 2560⟩] m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem entryR_W (W : Addr) : ∀ r ∈ [oneR W, ⟨W + BitVec.ofNat 64 32, 64⟩], Region.Sub r ⟨W, 2560⟩ :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem nonceR_W (W : Addr) : ∀ r ∈ nonceR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem hashR_W (W : Addr) : ∀ r ∈ hashR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Lay.wSub (by decide)

/-- A buffer apart from `W`, after a frame within `W`. -/
theorem bytesAt_W {W P : Addr} {k : Nat} (hP : (⟨P, k⟩ : Region).Disjoint ⟨W, 2560⟩) (hk : k < 2 ^ 64)
    {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') : bytesAt m' P k = bytesAt m P k :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP) (by omega_using [hk])

theorem ctxCiph_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega_using [hR]) h]

theorem ctxInv_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : Spec.Ocb.ctxInv m' K R = Spec.Ocb.ctxInv m K R := by
  unfold Spec.Ocb.ctxInv
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega_using [hR]) h]

theorem ctxLstar_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') :
    ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Lay.kSub (by decide))

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {W D : Addr} {n d : Nat} (hd : d + 16 ≤ 128 ∨ (256 ≤ d ∧ d + 16 ≤ 2560)) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩] m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutW hd
  · exact in_mutB (by decide) (by decide)

/-- Our caller's registers saved in `W`, after a frame within the parts the pieces write. -/
theorem saved_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {s₀ : State} {m m' : Mem} (h : SavedAt m W s₀) (hf : Frame (mutR W D n) m m') : SavedAt m' W s₀ :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa using L.w_w (a := 128) (n := 104) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (a := 128) (n := 104) (d := 256) (k := 2304) (.inl (by decide)) (by decide) (by decide)
    · exact (hD.sub_right (Lay.wSub (W := W) (d := 128) (n := 104) (by decide))).symm

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega_using [h],
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-! ## Before the data -/

/-- What the pieces before the data leave, from `s₀` and with `V` the
registers after the entry: the offset, the checksum, `L_$`, `L_0`, `HASH`
and the slots. -/
structure Pre (V : Reg → BitVec 64) (K W N A D : Addr) (R nl al tl : Nat) (s₀ s' : State) : Prop where
  env : Env V s₀.sp s'
  frame : Frame [⟨W, 2560⟩] s₀.mem s'.mem
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  saved : SavedAt s'.mem W s₀
  slots : Slots W A D s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K)
  l0 : blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₀.mem K) 0
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al)

/-- `nonce` and `hash`, after the entry (in `s₁`, whose registers are `V`). -/
theorem preRest_wp {s₀ s₁ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (P₁ : EntryPost W T s₀ s₁) (htl : stackArg s₀ 1 = BitVec.ofNat 64 tl)
    (ha0 : s₀.gpr .a0 = K) (ha1 : s₀.gpr .a1 = BitVec.ofNat 64 R) (ha2 : s₀.gpr .a2 = N)
    (ha3 : s₀.gpr .a3 = BitVec.ofNat 64 nl) (ha4 : s₀.gpr .a4 = A) (ha5 : s₀.gpr .a5 = BitVec.ofNat 64 al)
    (ha6 : s₀.gpr .a6 = D) :
    WP isa (.seq nonce Impl.AesOcb.RISCV64.hash) s₁ (Pre s₁.gpr K W N A D R nl al tl s₀) := by
  obtain L : Lay (s₁.gpr .s2) (s₁.gpr .s0) := by rw [P₁.s2, P₁.s0, ha0]; exact Ar.lay
  have E₁ := P₁.env
  obtain hs3 : s₁.gpr .s3 = BitVec.ofNat 64 R := P₁.s3.trans ha1
  obtain F₁ : Frame [⟨W, 2560⟩] s₀.mem s₁.mem := frameW P₁.frame (entryR_W W)
  have rd₁ := P₁.keeps.rd
  have wr₁ := P₁.keeps.wr
  have hW₁ : s₁.gpr .s0 = W := P₁.s0
  obtain hK₁ : s₁.gpr .s2 = K := P₁.s2.trans ha0
  obtain hKD : (⟨s₁.gpr .s2, 256⟩ : Region).Disjoint ⟨D, n⟩ := by rw [hK₁]; exact Ar.data.k
  obtain S₁ : Slots W A D s₁.mem := by have := P₁.slots; rwa [ha4, ha6] at this
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok L Ar.rounds hs3 E₁ (P₁.s4.trans ha2) (P₁.s5.trans ha3) (P₁.s8.trans htl)
    Ar.n1 Ar.n15 (by have := Ar.t16; omega_using [this]) (by rw [hW₁]; exact Ar.nonce.of_eq rd₁ wr₁) hKD) fun s₂ P₂ => ?_)
  obtain pf₂ : Frame (nonceR W) s₁.mem s₂.mem := by have := P₂.frame; rwa [hW₁] at this
  have ofs₂ := P₂.ofs
  have o0₂ := P₂.o0
  rw [hW₁] at ofs₂ o0₂
  obtain keep₂ : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
      blockAtMem s₂.mem (W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ => by
    have := P₂.keep h₁ h₂; rwa [hW₁] at this
  obtain F₂ : Frame [⟨W, 2560⟩] s₁.mem s₂.mem := frameW pf₂ (nonceR_W W)
  obtain S₂ : Slots W A D s₂.mem := Slots.mut Ar.lay Ar.data.w (nonceR_mut (D := D) (n := n) pf₂) S₁
  -- `HASH`.
  obtain F₁₂ := F₁.trans F₂
  obtain C : HCtx (s₁.gpr .s2) (s₁.gpr .s0) D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al)
      s₂ :=
    { lay := L, rounds := Ar.rounds
      ciph := by rw [hK₁, ctxCiph_W Ar.lay F₁₂ Ar.rounds]
      lstar := by rw [hK₁, ctxLstar_W Ar.lay F₁₂]
      buf := by rw [length_bytesAt, hW₁]; exact Ar.aad.of_eq (P₂.rd.trans rd₁) (P₂.wr.trans wr₁)
      aad := by rw [length_bytesAt, bytesAt_W Ar.aad.w Ar.aad.lt F₁₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := hKD, dw := by rw [hW₁]; exact Ar.data.w }
  refine WP.mono (hash_ok C P₂.env hs3 (by rw [hW₁]; exact S₂.aad) (by rw [P₁.s10, ha5, length_bytesAt])
    (by rw [hW₁, keep₂ (by decide) (by decide), P₁.l0, ha0])) fun s₃ H₃ => ?_
  obtain hf₃ : Frame (hashR W) s₂.mem s₃.mem := by have := H₃.frame; rwa [hW₁] at this
  obtain F₃ : Frame [⟨W, 2560⟩] s₂.mem s₃.mem := frameW hf₃ (hashR_W W)
  obtain k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 272) ∨
      (288 ≤ d ∧ d + 16 ≤ 296) ∨ (312 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    blockAtMem_frame hf₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Ar.lay.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
  obtain sv₂ : SavedAt s₂.mem W s₀ := saved_mut Ar.lay Ar.data.w P₁.saved (nonceR_mut (D := D) (n := n) pf₂)
  obtain sv₃ : SavedAt s₃.mem W s₀ := saved_mut Ar.lay Ar.data.w sv₂ (hashR_mut (D := D) (n := n) hf₃)
  obtain nonce₁ : bytesAt s₁.mem N nl = bytesAt s₀.mem N nl := bytesAt_W Ar.nonce.w Ar.nonce.lt F₁
  refine ⟨H₃.env, F₁₂.trans F₃, by rw [H₃.rd, P₂.rd, rd₁], by rw [H₃.wr, P₂.wr, wr₁], sv₃,
    Slots.mut Ar.lay Ar.data.w (hashR_mut (D := D) (n := n) hf₃) S₂, ?_, ?_, ?_, ?_, ?_,
    by have := H₃.sum; rwa [hW₁] at this⟩
  · rw [k₃ (d := ofsO) (by decide), ofs₂, hK₁, ctxCiph_W Ar.lay F₁ Ar.rounds, nonce₁]
  · rw [k₃ (d := o0O) (by decide), o0₂, hK₁, ctxCiph_W Ar.lay F₁ Ar.rounds, nonce₁]
  · rw [k₃ (d := ckO) (by decide), keep₂ (by decide) (by decide), P₁.ck]
  · rw [k₃ (d := ldO) (by decide), keep₂ (by decide) (by decide), P₁.ld, ha0]
  · rw [k₃ (d := l0O) (by decide), keep₂ (by decide) (by decide), P₁.l0, ha0]

/-- `body`'s frame misses a block of `W` outside the offset, the checksum,
`[96, 128)` and `[256, 272)`. -/
theorem body_keep {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (bodyR W D n) m m') {d : Nat}
    (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (128 ≤ d ∧ d + 16 ≤ 256) ∨ (272 ≤ d ∧ d + 16 ≤ 512)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact L.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact L.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact L.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact (hD.sub_right (Lay.wSub (by omega_using [hd]))).symm

/-- `tag d`'s frame misses the data. -/
theorem tag_data {W D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hd : d + 16 ≤ 512) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 d, 16⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hD.sub_right (Lay.wSub (by first | omega | (simp only [tmpO]; omega_using [])))

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T` (in `s9`),
`tl` in `s8`, which the state may write. -/
theorem tagOut_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {tl : Nat} (h1 : 1 ≤ tl)
    (h16 : tl ≤ 16) (hs8 : V .s8 = BitVec.ofNat 64 tl) (hTw : Covers [⟨V .s9, tl⟩] s.wr)
    (hTW : (⟨V .s9, tl⟩ : Region).Disjoint ⟨V .s0, 2560⟩) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem (V .s9) (bytesAt s.mem (V .s0) tl) ∧
      (∀ r, r ∉ xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold tagOut
  refine WP.seq (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_)
  obtain a0₃ : s₃.gpr .a0 = V .s0 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.s0]
  obtain a1₃ : s₃.gpr .a1 = V .s9 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s9]
  obtain a2₃ : s₃.gpr .a2 = BitVec.ofNat 64 tl := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s8, hs8]
  obtain rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (Proof.AesGcm.RISCV64.copyLoop_ok s₃ ⟨a0₃, a1₃, a2₃, h1, by omega_using [h16],
    by rw [rd₃, wr₃]; exact covers_left (covers_prefix E.perm.w (by omega_using [h16])),
    by rw [wr₃]; exact hTw, (hTW.sub_right (Region.sub_prefix (by omega_using [h16]))).symm⟩) fun t ⟨mt, ot⟩ => ?_
  obtain ⟨rdt, wrt, spt⟩ := ot.keeps
  refine ⟨by rw [mt, m₃], fun q hq => ?_, by rw [spt, u₃.sp, u₂.sp, u₁.sp], by rw [rdt, rd₃], by rw [wrt, wr₃]⟩
  simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  rw [ot.other q hq.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2.1 hq.2.2.2.2.2.2, u₃.other _ hq.2.2.2.2.2.1,
    u₂.other _ hq.2.2.2.2.1, u₁.other _ hq.2.2.2.1]

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' {s₀ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s₀.wr) (hW : stackArg s₀ 2 = W)
    (hT : stackArg s₀ 0 = T) (htl : stackArg s₀ 1 = BitVec.ofNat 64 tl)
    (ha0 : s₀.gpr .a0 = K) (ha1 : s₀.gpr .a1 = BitVec.ofNat 64 R) (ha2 : s₀.gpr .a2 = N)
    (ha3 : s₀.gpr .a3 = BitVec.ofNat 64 nl) (ha4 : s₀.gpr .a4 = A) (ha5 : s₀.gpr .a5 = BitVec.ofNat 64 al)
    (ha6 : s₀.gpr .a6 = D) (ha7 : s₀.gpr .a7 = BitVec.ofNat 64 n) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ocb.encryptWith (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) tl (bytesAt s₀.mem N nl)
        (bytesAt s₀.mem A al) (bytesAt s₀.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  obtain L₀ : Lay (s₀.gpr .a0) W := by rw [ha0]; exact Ar.lay
  obtain hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := by rw [ha0]; exact Ar.perm.k
  unfold «seal» front
  refine WP.seq (WP.seq (WP.mono (entry_ok L₀ Ar.perm.w hC Ar.sa hW hT Ar.args Ar.argsW) fun s₁ P₁ => ?_))
  have hW₁ : s₁.gpr .s0 = W := P₁.s0
  obtain hK₁ : s₁.gpr .s2 = K := P₁.s2.trans ha0
  obtain hs3 : s₁.gpr .s3 = BitVec.ofNat 64 R := P₁.s3.trans ha1
  obtain h11 : s₁.gpr .s11 = BitVec.ofNat 64 n := P₁.s11.trans ha7
  obtain L : Lay (s₁.gpr .s2) (s₁.gpr .s0) := by rw [hK₁, hW₁]; exact Ar.lay
  refine WP.assoc (WP.seq (WP.mono (preRest_wp Ar P₁ htl ha0 ha1 ha2 ha3 ha4 ha5 ha6) fun s₃ P₃ => ?_))
  obtain hD₃ : DBuf (s₁.gpr .s2) (s₁.gpr .s0) s₃ D n := by
    rw [hK₁, hW₁]; exact Ar.data.of_eq P₃.rd P₃.wr
  obtain c₃ : ctxCiph s₃.mem K R = ctxCiph s₀.mem K R := ctxCiph_W Ar.lay P₃.frame Ar.rounds
  obtain l₃ : ctxLstar s₃.mem K = ctxLstar s₀.mem K := ctxLstar_W Ar.lay P₃.frame
  obtain d₃ : bytesAt s₃.mem D n = bytesAt s₀.mem D n := bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (bodySeal_ok L P₃.env Ar.rounds hs3 h11 (by rw [hW₁]; exact P₃.slots.data) hD₃
    (O0 := Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)) (by rw [hW₁]; exact P₃.ofs)
    (by rw [hW₁]; exact P₃.o0) (by rw [hW₁]; exact P₃.ck) (by rw [hW₁, hK₁, P₃.l0, l₃])) fun s₄ B => ?_)
  obtain Bf : Frame (bodyR W D n) s₃.mem s₄.mem := by have := B.frame; rwa [hW₁] at this
  obtain F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut Bf
  obtain cK₄ : ctxCiph s₄.mem K R = ctxCiph s₀.mem K R := (ctxCiph_mut Ar.lay Ar.data.k F₄ Ar.rounds).trans c₃
  obtain ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (tag_ok L B.env Ar.rounds hs3 (.inl rfl)) fun s₅ T₅ => ?_
  obtain Tf : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 tagO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
      s₄.mem s₅.mem := by have := T₅.frame; rwa [hW₁] at this
  obtain F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (.inl (by decide)) Tf
  obtain sv₅ := saved_mut Ar.lay Ar.data.w (saved_mut Ar.lay Ar.data.w P₃.saved F₄) F₅
  -- The copy of the tag.
  have E₅ := T₅.env
  obtain hTd : (⟨s₁.gpr .s9, tl⟩ : Region).Disjoint ⟨s₁.gpr .s0, 2560⟩ := by rw [P₁.s9, hW₁]; exact Ar.tag.w
  refine WP.seq (WP.mono (tagOut_ok E₅ Ar.t1 Ar.t16 (P₁.s8.trans htl)
    (by rw [P₁.s9, T₅.wr, B.wr, P₃.wr]; exact hTw) hTd) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ := E₅.others g₆ sp₆ rd₆ wr₆
  rw [P₁.s9, hW₁] at m₆
  obtain F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  obtain sv₆ : SavedAt s₆.mem W s₀ := sv₅.frame F₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (Ar.tag.w.sub_right (Lay.wSub (W := W) (d := 128) (n := 104) (by decide))).symm
  -- `restore`.
  refine WP.mono (Proof.AesGcm.RISCV64.restore_ok (E₆.s0.trans hW₁) Ar.lay.wal
    (by rw [rd₆, wr₆, T₅.rd, T₅.wr, B.rd, B.wr, P₃.rd, P₃.wr]; exact covers_left Ar.perm.w) sv₆
    (by rw [E₆.sp])) fun s₇ ⟨abi, m₇, _, _, _⟩ => ⟨abi, ?_⟩
  have hout := B.out
  rw [hK₁, c₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [hW₁, hK₁, l₃] at hofs
  have hck := B.ck
  rw [hW₁, d₃] at hck
  have hn := Ar.data.lt
  have ht := Ar.tag.lt
  obtain d₇ : bytesAt s₇.mem D n = bytesAt s₄.mem D n := by
    rw [m₇, Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega_using [hn])]
    exact Proof.Cmac.bytesAt_frame Tf (tag_data Ar.data.w (by decide)) (by omega_using [hn])
  have tv := T₅.val
  rw [hW₁, hK₁, show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  obtain t₇ : bytesAt s₇.mem T tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl := by
    rw [m₇, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, bytesAt_take_block _ _ Ar.t16]
  rw [Proof.Ocb.encryptWith_eq, d₇, hout, t₇, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega_using [hr]
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega_using [hr]
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp {s : State} (h : sealRISCV64.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp' (sealArgs_of h) (covers_mem (by rw [h.2.1]; simp)) rfl rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISC-V: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front` with the
tag at `W + t2O`, then the received tag padded at `W` (`recv`), the
comparison of the padded tags (`cmp`), the mask of the data (`mask`, which
loads the data's address from its slot) and `restore`, which keeps the
result in `a0` (`open_wp`). As on PPC64LE (`Proof/AesOcb/PPC64LE/Open.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (covers_mem covers_left SavedAt)

/-- Two padded tags are equal iff the tags are. -/
theorem padded_eq {xs ys : List Byte} {t : Nat} (hx : xs.length = t) (hy : ys.length = t) :
    xs ++ zeros (16 - t) = ys ++ zeros (16 - t) ↔ xs = ys := by
  constructor
  · intro h; exact (List.append_inj h (by rw [hx, hy])).1
  · intro h; rw [h]

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' {s₀ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (hW : stackArg s₀ 2 = W)
    (hT : stackArg s₀ 0 = T) (htl : stackArg s₀ 1 = BitVec.ofNat 64 tl)
    (ha0 : s₀.gpr .a0 = K) (ha1 : s₀.gpr .a1 = BitVec.ofNat 64 R) (ha2 : s₀.gpr .a2 = N)
    (ha3 : s₀.gpr .a3 = BitVec.ofNat 64 nl) (ha4 : s₀.gpr .a4 = A) (ha5 : s₀.gpr .a5 = BitVec.ofNat 64 al)
    (ha6 : s₀.gpr .a6 = D) (ha7 : s₀.gpr .a7 = BitVec.ofNat 64 n) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s₀.mem K R) (Spec.Ocb.ctxInv s₀.mem K R) (ctxLstar s₀.mem K) tl
          (bytesAt s₀.mem N nl) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n) (bytesAt s₀.mem T tl) with
      | some pt => (s'.gpr .a0).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .a0).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  obtain L₀ : Lay (s₀.gpr .a0) W := by rw [ha0]; exact Ar.lay
  obtain hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := by rw [ha0]; exact Ar.perm.k
  have hn := Ar.data.lt
  unfold «open» front
  refine WP.seq (WP.seq (WP.mono (entry_ok L₀ Ar.perm.w hC Ar.sa hW hT Ar.args Ar.argsW) fun s₁ P₁ => ?_))
  have hW₁ : s₁.gpr .s0 = W := P₁.s0
  obtain hK₁ : s₁.gpr .s2 = K := P₁.s2.trans ha0
  obtain hs3 : s₁.gpr .s3 = BitVec.ofNat 64 R := P₁.s3.trans ha1
  obtain h11 : s₁.gpr .s11 = BitVec.ofNat 64 n := P₁.s11.trans ha7
  obtain L : Lay (s₁.gpr .s2) (s₁.gpr .s0) := by rw [hK₁, hW₁]; exact Ar.lay
  have hal : (s₁.gpr .s0).toNat % 8 = 0 := L.wal
  refine WP.assoc (WP.seq (WP.mono (preRest_wp Ar P₁ htl ha0 ha1 ha2 ha3 ha4 ha5 ha6) fun s₃ P₃ => ?_))
  obtain hD₃ : DBuf (s₁.gpr .s2) (s₁.gpr .s0) s₃ D n := by
    rw [hK₁, hW₁]; exact Ar.data.of_eq P₃.rd P₃.wr
  obtain c₃ : ctxCiph s₃.mem K R = ctxCiph s₀.mem K R := ctxCiph_W Ar.lay P₃.frame Ar.rounds
  obtain i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s₀.mem K R := ctxInv_W Ar.lay P₃.frame Ar.rounds
  obtain l₃ : ctxLstar s₃.mem K = ctxLstar s₀.mem K := ctxLstar_W Ar.lay P₃.frame
  obtain d₃ : bytesAt s₃.mem D n = bytesAt s₀.mem D n := bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (bodyOpen_ok L P₃.env Ar.rounds hs3 h11 (by rw [hW₁]; exact P₃.slots.data) hD₃
    (O0 := Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)) (by rw [hW₁]; exact P₃.ofs)
    (by rw [hW₁]; exact P₃.o0) (by rw [hW₁]; exact P₃.ck) (by rw [hW₁, hK₁, P₃.l0, l₃])) fun s₄ B => ?_)
  obtain Bf : Frame (bodyR W D n) s₃.mem s₄.mem := by have := B.frame; rwa [hW₁] at this
  obtain F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut Bf
  obtain cK₄ : ctxCiph s₄.mem K R = ctxCiph s₀.mem K R := (ctxCiph_mut Ar.lay Ar.data.k F₄ Ar.rounds).trans c₃
  obtain ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.mono (tag_ok L B.env Ar.rounds hs3 (.inr rfl)) fun s₅ T₅ => ?_
  obtain Tf : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
      s₄.mem s₅.mem := by have := T₅.frame; rwa [hW₁] at this
  obtain F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (.inr ⟨by decide, by decide⟩) Tf
  obtain sv₅ := saved_mut Ar.lay Ar.data.w (saved_mut Ar.lay Ar.data.w P₃.saved F₄) F₅
  obtain S₅ : Slots W A D s₅.mem := Slots.mut Ar.lay Ar.data.w F₅ (Slots.mut Ar.lay Ar.data.w F₄ P₃.slots)
  have E₅ := T₅.env
  obtain rd₅ : s₅.rd = s₀.rd := by rw [T₅.rd, B.rd, P₃.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [T₅.wr, B.wr, P₃.wr]
  -- The received tag, to `W`.
  obtain hTd : (⟨s₁.gpr .s9, tl⟩ : Region).Disjoint ⟨s₁.gpr .s0, 2560⟩ := by rw [P₁.s9, hW₁]; exact Ar.tag.w
  refine WP.seq (WP.mono (recv_ok E₅ hal (P₁.s8.trans htl) Ar.t1 Ar.t16
    (by rw [P₁.s9, rd₅, wr₅]; exact Ar.tag.rd) hTd) fun s₆ ⟨b₆, f₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ := E₅.others g₆ sp₆ rd₆ wr₆
  rw [hW₁, P₁.s9] at b₆
  rw [hW₁] at f₆
  obtain F₆ : Frame (mutR W D n) s₅.mem s₆.mem :=
    f₆.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide)
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok E₆ hal (P₁.s8.trans htl) Ar.t1 Ar.t16) fun s₇ ⟨a0₇, f₇, g₇, sp₇, rd₇, wr₇⟩ => ?_)
  obtain E₇ := E₆.others g₇ sp₇ rd₇ wr₇
  rw [hW₁] at a0₇ f₇
  obtain F₇ : Frame (mutR W D n) s₆.mem s₇.mem :=
    f₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutB (by decide) (by decide)
  let c : Bool := decide (bytesAt s₆.mem (W + BitVec.ofNat 64 tagO) 16 =
    bytesAt s₆.mem (W + BitVec.ofNat 64 t2O) tl ++ zeros (16 - tl))
  obtain a0c : s₇.gpr .a0 = if c then 1 else 0 := by
    rw [a0₇]; simp only [c, decide_eq_true_eq]
  obtain hD₇ : DBuf (s₁.gpr .s2) (s₁.gpr .s0) s₇ D n := by
    rw [hK₁, hW₁]; exact Ar.data.of_eq (by rw [rd₇, rd₆, rd₅]) (by rw [wr₇, wr₆, wr₅])
  obtain S₇ : Slots (s₁.gpr .s0) A D s₇.mem := by
    rw [hW₁]; exact Slots.mut Ar.lay Ar.data.w F₇ (Slots.mut Ar.lay Ar.data.w F₆ S₅)
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₇ hal S₇ h11 hD₇ a0c) fun s₈ ⟨m₈, g₈, sp₈, rd₈, wr₈⟩ => ?_)
  obtain E₈ := E₇.others g₈ sp₈ rd₈ wr₈
  obtain F₈ : Frame [⟨D, n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain F₅₈ : Frame (mutR W D n) s₅.mem s₈.mem :=
    (F₆.trans F₇).trans (F₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact in_mutD fun _ h => h)
  obtain sv₈ : SavedAt s₈.mem W s₀ := saved_mut Ar.lay Ar.data.w sv₅ F₅₈
  -- `restore`.
  refine WP.mono (Proof.AesGcm.RISCV64.restore_ok (E₈.s0.trans hW₁) Ar.lay.wal
    (by rw [rd₈, wr₈, rd₇, wr₇, rd₆, wr₆, rd₅, wr₅]; exact covers_left Ar.perm.w) sv₈
    (by rw [E₈.sp])) fun s₉ ⟨abi, m₉, a0₉, _, _⟩ => ⟨abi, ?_⟩
  -- The plaintext and the comparison.
  obtain a0₉' : s₉.gpr .a0 = if c then 1 else 0 := by
    rw [a0₉, g₈ _ (by decide), a0c]
  have hout := B.out
  rw [hK₁, c₃, i₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [hW₁, hK₁, l₃] at hofs
  have hck := B.ck
  rw [hW₁, hK₁, c₃, i₃, l₃, d₃] at hck
  have hTn := Ar.tag.lt
  obtain Ff : Frame [⟨W, 2560⟩, ⟨D, n⟩] s₀.mem s₅.mem :=
    (P₃.frame.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans ((F₄.trans F₅).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  obtain recv : bytesAt s₅.mem T tl = bytesAt s₀.mem T tl :=
    Proof.Cmac.bytesAt_frame Ff (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Ar.tag.w
      · exact Ar.td) (by omega_using [hTn])
  obtain t2₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 t2O) tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inr (by simp only [tagO, t2O]; omega_using []))
        (by have := Ar.t16; simp only [t2O]; omega_using [this]) (by decide)) (by omega_using [hTn])
  have tagv := T₅.val
  rw [hW₁, hK₁, hck, hofs, ld₄, sum₄, cK₄] at tagv
  obtain d₉ : bytesAt s₉.mem D n = if c then bytesAt s₄.mem D n else zeros n := by
    obtain d₇ : bytesAt s₇.mem D n = bytesAt s₄.mem D n := by
      rw [Proof.Cmac.bytesAt_frame f₇ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by omega_using [hn]),
        Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by omega_using [hn]),
        Proof.Cmac.bytesAt_frame Tf (tag_data Ar.data.w (by decide)) (by omega_using [hn])]
    rw [m₉, m₈, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) hn, length_mask,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₇]
  rw [a0₉', d₉, hout, Proof.Ocb.decryptWith_eq]
  simp only [length_bytesAt, List.length_drop]
  obtain hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
      (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s₀.mem T tl) := fun x hx => by
    show decide (_ = _) = true ↔ _
    rw [decide_eq_true_iff, b₆, t2₆, recv, hx,
      padded_eq (length_bytesAt _ _ _) (by rw [List.length_take, Proof.Ocb.toBytes_length]; have := Ar.t16; omega_using [this]),
      eq_comm]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega_using [hr]
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
    obtain hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega_using [hr]
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
    obtain hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp {s : State} (h : openRISCV64.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp' (openArgs_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm
    rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.RISCV64
