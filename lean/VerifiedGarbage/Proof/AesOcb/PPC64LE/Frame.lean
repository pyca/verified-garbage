module

public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Seal
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.AesOcb.PPC64LE.PadTo
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.RestTag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.AesOcb.PPC64LE.FnCT
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `AesOcb.PPC64LE.Verified`, which only this module used -/

section

/-! ### `AesOcb.PPC64LE.Open`, which only this module used -/

section

/-! ### `AesOcb.PPC64LE.CmpMask`, which only this module used -/

section

/-!
# AES-OCB on PPC64LE: checking the tag (`recv`, `cmp`) and the mask (`mask`)

Untrusted: everything here is checked by Lean. `recv` copies the received
tag, padded with zeros, to `W` (`recv_ok`); `cmp` copies the first `tl`
bytes of the tag `open` computes, padded with zeros, to `W + vO`, and sets
`r3` to 1 if the two blocks are equal and 0 if not, without a branch
(`cmp_ok`, as AES-GCM's `Proof.AesGcm.PPC64LE.cmpTail_ok`); `mask` ANDs
every byte of the data with `0 − r3`: the data stays if the tags were equal,
and is zeroed if not (`mask_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros blockAtMem)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.AesGcm.PPC64LE (copyLoop_ok LoopPre in_left in_off covers_off covers_left covers_prefix Keeps
  eval_zero bytesAt_succ in_of_covers words_eq cmp_value)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or, wp_addi → cwp_addi, wp_li → cwp_li,
  wp_sub → cwp_sub, wp_ld → cwp_ld, wp_xor → cwp_xor, wp_lsr → cwp_lsr, wp_lbz → cwp_lbz, wp_and → cwp_and,
  wp_stb → cwp_stb, wp_subi → cwp_subi

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes' {m : Mem} {P : Addr} (hz : bytesAt m P 16 = zeros 16) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes m P xs) P 16 = xs ++ zeros (16 - xs.length) :=
  Proof.AesGcm.PPC64LE.pad_bytes hz xs hx

/-- A copy of `tl` bytes from `S` to `W + d`, which holds 16 zero bytes. -/
theorem padCopy_ok {W : Addr} {s : State} (hw : Covers [⟨W, 2560⟩] s.wr) {S : Addr} {d tl : Nat}
    (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (hSr : Covers [⟨S, tl⟩] (s.rd ++ s.wr))
    (hSd : (⟨S, tl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩)
    (hz : bytesAt s.mem (W + BitVec.ofNat 64 d) 16 = zeros 16) (hr3 : s.gpr .r3 = S)
    (hr4 : s.gpr .r4 = W + BitVec.ofNat 64 d) (hr5 : s.gpr .r5 = BitVec.ofNat 64 tl) :
    WP isa Impl.AesGcm.PPC64LE.copyLoop s fun s' => bytesAt s'.mem (W + BitVec.ofNat 64 d) 16 =
        bytesAt s.mem S tl ++ zeros (16 - tl) ∧
      Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem ∧
      Proof.AesGcm.PPC64LE.LoopOut s S (W + BitVec.ofNat 64 d) tl s' := by
  obtain lp : LoopPre s S (W + BitVec.ofNat 64 d) tl :=
    ⟨hr3, hr4, hr5, h1, by omega_using [h16], hSr, covers_prefix (covers_off hw hd (by decide)) h16,
      hSd.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm, lo⟩ => ⟨?_, ?_, lo⟩
  · rw [hm, pad_bytes' hz _ (by rw [length_bytesAt]; exact h16), length_bytesAt]
  · rw [hm]
    exact (Proof.AesGcm.PPC64LE.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩

/-- `recv`: the received tag (`tl` bytes at `T`, in `r20`), padded with zeros at `W`. -/
theorem recv_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {tl : Nat}
    (h19 : V .r19 = BitVec.ofNat 64 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (hTr : Covers [⟨V .r20, tl⟩] (s.rd ++ s.wr))
    (hTd : (⟨V .r20, tl⟩ : Region).Disjoint ⟨V .r31, 2560⟩) :
    WP isa recv s fun s' => bytesAt s'.mem (V .r31 + BitVec.ofNat 64 tagO) 16 =
        bytesAt s.mem (V .r20) tl ++ zeros (16 - tl) ∧
      Frame [⟨V .r31 + BitVec.ofNat 64 tagO, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ xpRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := E.perm.w
  obtain hTd' : (⟨V .r20, tl⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 tagO, 16⟩ :=
    hTd.sub_right (Lay.wSub (by decide))
  obtain hA : WP isa (.block (zero16 tagO ++ [Impl.AesGcm.PPC64LE.mov .r3 .r20, Impl.AesGcm.PPC64LE.mov .r4 .r31,
      Impl.AesGcm.PPC64LE.mov .r5 .r19])) s fun s₂ =>
      bytesAt s₂.mem (V .r31 + BitVec.ofNat 64 tagO) 16 = zeros 16 ∧
      Frame [⟨V .r31 + BitVec.ofNat 64 tagO, 16⟩] s.mem s₂.mem ∧
      s₂.gpr .r3 = V .r20 ∧ s₂.gpr .r4 = V .r31 + BitVec.ofNat 64 tagO ∧ s₂.gpr .r5 = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s.gpr r) ∧ Keeps s₂ s₂ ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.sp = s.sp ∧ s₂.lr = s.lr :=
    WP.block_append (WP.mono (zero16_ok (s := s) (d := tagO) (by decide) E.r31 (in_off hw (by decide) (by decide))
      (in_off hw (by decide) (by decide))) fun s₁ B₁ =>
      cwp_or fun t₁ u₁ => cwp_or fun t₂ u₂ => cwp_or fun t₃ u₃ => WP.block_nil
        ⟨by rw [u₃.mem, u₂.mem, u₁.mem]; exact bytesAt_of_zero B₁.val,
          by rw [u₃.mem, u₂.mem, u₁.mem]; exact B₁.frame,
          by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, BitVec.or_self, B₁.gpr _ (by decide), E.r20],
          by rw [u₃.other _ (by decide), u₂.gpr, BitVec.or_self, u₁.other _ (by decide), B₁.gpr _ (by decide), E.r31]
             exact (BitVec.add_zero _).symm,
          by rw [u₃.gpr, BitVec.or_self, u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), E.r19,
            h19],
          fun r a b c d => by rw [u₃.other _ d, u₂.other _ c, u₁.other _ b, B₁.gpr r (by simp [a])],
          Keeps.refl _,
          by rw [u₃.rd, u₂.rd, u₁.rd, B₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr, B₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp, B₁.sp],
          by rw [u₃.lr, u₂.lr, u₁.lr, B₁.lr]⟩)
  unfold recv
  refine WP.seq (WP.mono hA fun s₂ ⟨hz, fz, a3, a4, a5, g₂, _, rd₂, wr₂, sp₂, lr₂⟩ => ?_)
  obtain hT₂ : bytesAt s₂.mem (V .r20) tl = bytesAt s.mem (V .r20) tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd') (by omega_using [h16])
  refine WP.mono (padCopy_ok (W := V .r31) (d := tagO) (by rw [wr₂]; exact hw) (by decide) h1 h16
    (by rw [rd₂, wr₂]; exact hTr) hTd' hz a3 a4 a5) fun s' ⟨hb, hf, lo⟩ => ?_
  obtain ⟨rd', wr', sp', lr'⟩ := lo.keeps
  exact ⟨by rw [hb, hT₂], fz.trans hf, fun r hr => by
      simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [lo.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2, g₂ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1],
    by rw [sp', sp₂], by rw [lr', lr₂], by rw [rd', rd₂], by rw [wr', wr₂]⟩

/-- `cmpTail`: `r3` is 1 iff the 16 bytes at `W` and `W + vO` are equal. -/
theorem cmpTail_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) :
    WP isa (.block cmpTail) s fun s' =>
      s'.gpr .r3 = (if bytesAt s.mem (V .r31 + BitVec.ofNat 64 tagO) 16 =
        bytesAt s.mem (V .r31 + BitVec.ofNat 64 vO) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h31 := E.r31
  obtain r₀ := E.perm.wR (show 0 + 8 ≤ 2560 by decide)
  obtain r₁ := E.perm.wR (show 336 + 8 ≤ 2560 by decide)
  obtain r₂ := E.perm.wR (show 8 + 8 ≤ 2560 by decide)
  obtain r₃ := E.perm.wR (show 344 + 8 ≤ 2560 by decide)
  obtain hrun : WP isa (.block cmpTail) s fun s' =>
      s'.gpr .r3 = BitVec.ofNat 64 1 - (((s.mem.readW (V .r31 + BitVec.ofNat 64 0) 64 ^^^
          s.mem.readW (V .r31 + BitVec.ofNat 64 336) 64) |||
        (s.mem.readW (V .r31 + BitVec.ofNat 64 8) 64 ^^^ s.mem.readW (V .r31 + BitVec.ofNat 64 344) 64)) |||
        (BitVec.ofNat 64 0 - ((s.mem.readW (V .r31 + BitVec.ofNat 64 0) 64 ^^^
          s.mem.readW (V .r31 + BitVec.ofNat 64 336) 64) |||
        (s.mem.readW (V .r31 + BitVec.ofNat 64 8) 64 ^^^ s.mem.readW (V .r31 + BitVec.ofNat 64 344) 64)))) >>> 63 ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
    apply WP.of_runBlock
    simp only [cmpTail, vO, tagO, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load,
      State.write, Size.bytes, Size.bits, h31, r₀, r₁, r₂, r₃, Proof.Gcm.PPC64LE.read_8, Option.bind_some,
      Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq, not_false_eq_true,
      Nat.reduceLT, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.reduceAdd, ↓reduceIte, and_self,
      implies_true, BitVec.setWidth_eq]
    exact ⟨rfl, fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono hrun fun s' ⟨h3, hg, hk⟩ => ⟨?_, hg, hk⟩
  rw [h3, cmp_value]
  obtain e := words_eq s.mem (V .r31 + BitVec.ofNat 64 0) (V .r31 + BitVec.ofNat 64 336)
  simp only [Proof.AesGcm.PPC64LE.add_ofNat_assoc, Nat.reduceAdd] at e
  show _ = if bytesAt s.mem (V .r31 + BitVec.ofNat 64 0) 16 = bytesAt s.mem (V .r31 + BitVec.ofNat 64 336) 16
    then _ else _
  by_cases hq : bytesAt s.mem (V .r31 + BitVec.ofNat 64 0) 16 = bytesAt s.mem (V .r31 + BitVec.ofNat 64 336) 16
  · simp only [e.mpr hq, hq, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hq (e.mp h)), ite_eq_right_of_eq_false _ _ (eq_false hq)]

/-- `cmp`: the first `tl` bytes of the tag at `W + t2O`, padded with zeros
at `W + vO`, compared with the received tag at `W`. -/
theorem cmp_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {tl : Nat}
    (h19 : V .r19 = BitVec.ofNat 64 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa cmp s fun s' => s'.gpr .r3 = (if bytesAt s.mem (V .r31 + BitVec.ofNat 64 tagO) 16 =
        bytesAt s.mem (V .r31 + BitVec.ofNat 64 t2O) tl ++ zeros (16 - tl) then 1 else 0) ∧
      Frame [⟨V .r31 + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ xpRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := E.perm.w
  obtain hSd : (⟨V .r31 + BitVec.ofNat 64 t2O, tl⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 vO, 16⟩ :=
    Offset.disjoint _ (.inl (by simp only [t2O, vO]; omega_using [h16])) (by simp only [t2O]; omega_using [h16]) (by decide)
  obtain hA : WP isa (.block (zero16 vO ++ [.addi .r3 .r31 t2O, .addi .r4 .r31 vO,
      Impl.AesGcm.PPC64LE.mov .r5 .r19])) s fun s₂ =>
      bytesAt s₂.mem (V .r31 + BitVec.ofNat 64 vO) 16 = zeros 16 ∧
      Frame [⟨V .r31 + BitVec.ofNat 64 vO, 16⟩] s.mem s₂.mem ∧
      s₂.gpr .r3 = V .r31 + BitVec.ofNat 64 t2O ∧ s₂.gpr .r4 = V .r31 + BitVec.ofNat 64 vO ∧
      s₂.gpr .r5 = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.sp = s.sp ∧ s₂.lr = s.lr :=
    WP.block_append (WP.mono (zero16_ok (s := s) (d := vO) (by decide) E.r31 (in_off hw (by decide) (by decide))
      (in_off hw (by decide) (by decide))) fun s₁ B₁ =>
      cwp_addi (by decide) (by decide) fun t₁ u₁ => cwp_addi (by decide) (by decide) fun t₂ u₂ =>
        cwp_or fun t₃ u₃ => WP.block_nil
        ⟨by rw [u₃.mem, u₂.mem, u₁.mem]; exact bytesAt_of_zero B₁.val,
          by rw [u₃.mem, u₂.mem, u₁.mem]; exact B₁.frame,
          by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, B₁.gpr _ (by decide), E.r31],
          by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), B₁.gpr _ (by decide), E.r31],
          by rw [u₃.gpr, BitVec.or_self, u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), E.r19,
            h19],
          fun r a b c d => by rw [u₃.other _ d, u₂.other _ c, u₁.other _ b, B₁.gpr r (by simp [a])],
          by rw [u₃.rd, u₂.rd, u₁.rd, B₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr, B₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp, B₁.sp],
          by rw [u₃.lr, u₂.lr, u₁.lr, B₁.lr]⟩)
  unfold cmp
  refine WP.seq (WP.mono hA fun s₂ ⟨hz, fz, a3, a4, a5, g₂, rd₂, wr₂, sp₂, lr₂⟩ => ?_)
  obtain hS₂ : bytesAt s₂.mem (V .r31 + BitVec.ofNat 64 t2O) tl = bytesAt s.mem (V .r31 + BitVec.ofNat 64 t2O) tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega_using [h16])
  obtain dTV : ∀ r ∈ [(⟨V .r31 + BitVec.ofNat 64 vO, 16⟩ : Region)],
      (⟨V .r31 + BitVec.ofNat 64 tagO, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (padCopy_ok (W := V .r31) (d := vO) (by rw [wr₂]; exact hw) (by decide) h1 h16
    (by rw [rd₂, wr₂]; exact covers_left (covers_prefix (covers_off hw (d := t2O) (n := 16) (by decide) (by decide))
      h16)) hSd hz a3 a4 a5) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  obtain ⟨rd₃, wr₃, sp₃, lr₃⟩ := lo.keeps
  obtain g₃ : ∀ r, r ∉ xpRegs → s₃.gpr r = s.gpr r := fun r hr => by
    simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [lo.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2, g₂ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1]
  obtain E₃ := E.others g₃ (by rw [sp₃, sp₂]) (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])
  obtain f₃ : Frame [⟨V .r31 + BitVec.ofNat 64 vO, 16⟩] s.mem s₃.mem := fz.trans hf
  obtain hT₃ : bytesAt s₃.mem (V .r31 + BitVec.ofNat 64 tagO) 16 = bytesAt s.mem (V .r31 + BitVec.ofNat 64 tagO) 16 :=
    Proof.Cmac.bytesAt_frame f₃ dTV (by omega_using [])
  refine WP.mono (cmpTail_ok E₃) fun s₄ ⟨r3₄, g₄, k₄⟩ => ⟨?_, by rw [k₄.mem]; exact f₃, fun r hr => ?_,
    by rw [k₄.sp, sp₃, sp₂], by rw [k₄.lr, lr₃, lr₂], by rw [k₄.rd, rd₃, rd₂], by rw [k₄.wr, wr₃, wr₂]⟩
  · rw [r3₄, hT₃, hb, hS₂]
  · simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄ r hr.2.1 hr.2.2.1 hr.2.2.2.1, g₃ r (by simp [xpRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]

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
abbrev maskRegs : List Reg := [.r4, .r7, .r24, .r25]

/-- `mask`: the `n` bytes of the data at `D` (in `r27`, `n` in `r23`) kept if
`c` (`r3 = 1`), zeroed if not. -/
theorem mask_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {D : Addr} {n : Nat}
    (h27 : V .r27 = D) (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s D n) {c : Bool}
    (h3 : s.gpr .r3 = if c then 1 else 0) :
    WP isa mask s fun t => t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) ∧
      (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hD.lt
  obtain hA : WP isa (.block [Impl.AesGcm.PPC64LE.mov .r24 .r27, Impl.AesGcm.PPC64LE.mov .r25 .r23, .li .r4 0,
      .sub .r7 .r4 .r3]) s fun s₁ =>
      s₁.gpr .r24 = D + BitVec.ofNat 64 0 ∧ s₁.gpr .r25 = BitVec.ofNat 64 (n - 0) ∧
      s₁.gpr .r7 = BitVec.ofNat 64 0 - (if c then 1 else 0) ∧
      (∀ r, r ∉ maskRegs → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ :=
    cwp_or fun t₁ u₁ => cwp_or fun t₂ u₂ => cwp_li (by decide) fun t₃ u₃ => cwp_sub fun t₄ u₄ => WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, BitVec.or_self, E.r27,
          h27, BitVec.add_zero],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, BitVec.or_self, u₁.other _ (by decide), E.r23,
          h23]; rfl,
        by rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h3],
        fun r hr => by
          simp only [maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          rw [u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.2.2, u₁.other _ hr.2.2.1],
        ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.lr, u₃.lr, u₂.lr, u₁.lr]⟩⟩
  unfold mask
  refine WP.seq (WP.mono hA fun s₁ ⟨r24₁, r25₁, r7₁, g₁, k₁⟩ => ?_)
  refine WP.ite _ (eval_zero r25₁ (by omega_using [hn])) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hz : n = 0 := by have := of_decide_eq_true h0; omega_using [this]
    subst hz
    refine ⟨by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], g₁, k₁.sp, k₁.lr, k₁.rd, k₁.wr⟩
  · have hpos : 0 < n := by have := of_decide_eq_false h0; omega_using [this]
    refine WP.loop (M := isa)
      (fun (k : Nat) (u : State) => ∃ j, k = n - j ∧ j < n ∧ u.gpr .r24 = D + BitVec.ofNat 64 j ∧
        u.gpr .r25 = BitVec.ofNat 64 (n - j) ∧ u.gpr .r7 = BitVec.ofNat 64 0 - (if c then 1 else 0) ∧
        u.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
        (∀ r, r ∉ maskRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.lr = s.lr ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_
      (n - 0) _ ⟨0, rfl, hpos, by rw [r24₁], r25₁, r7₁,
        by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], g₁, k₁.sp, k₁.lr, k₁.rd, k₁.wr⟩
    rintro k u ⟨j, rfl, hj, r24, r25, r7, mem, g, sp, lr, rd, wr⟩
    obtain rq : InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 j) 1 := by
      rw [rd, wr]; exact in_of_covers hD.rd hj hn
    obtain wq : InRegions u.wr (D + BitVec.ofNat 64 j) 1 := by rw [wr]; exact in_of_covers hD.wr hj hn
    refine cwp_lbz (a := D + BitVec.ofNat 64 j) (by decide) (by decide) (by rw [r24, BitVec.add_zero]) rq
      fun u₁ v₁ => cwp_and fun u₂ v₂ => cwp_stb (a := D + BitVec.ofNat 64 j) (by decide) (by decide)
        (by rw [v₂.other _ (by decide), v₁.other _ (by decide), r24, BitVec.add_zero])
        (by rw [v₂.wr, v₁.wr]; exact wq) fun u₃ v₃ => cwp_addi (by decide) (by decide) fun u₄ v₄ =>
        cwp_subi (by decide) (by decide) fun u₅ v₅ => WP.block_nil ?_
    obtain hl : (if c then bytesAt s.mem D j else zeros j).length = j := length_mask _ _ _ _
    obtain byte : u.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) := by
      rw [mem]; exact Proof.AesGcm.PPC64LE.dst_kept hj hn _ hl
    obtain m₅ : u₅.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
      rw [v₅.mem, v₄.mem, v₃.mem, v₂.gpr, v₁.gpr, v₁.other _ (by decide), r7, byte,
        mask_byte, v₂.mem, v₁.mem, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [hl]; omega_using [hn, hj]), hl]
    obtain r25' : u₅.gpr .r25 = BitVec.ofNat 64 (n - (j + 1)) := by
      rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), r25,
        Proof.AesGcm.PPC64LE.dec64 hj hn]
    obtain r24' : u₅.gpr .r24 = D + BitVec.ofNat 64 (j + 1) := by
      rw [v₅.other _ (by decide), v₄.gpr, v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), r24,
        Offset.add_add]
    obtain r7' : u₅.gpr .r7 = BitVec.ofNat 64 0 - (if c then 1 else 0) := by
      rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), r7]
    obtain g' : ∀ r, r ∉ maskRegs → u₅.gpr r = s.gpr r := fun r hr => by
      simp only [maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [v₅.other _ hr.2.2.2, v₄.other _ hr.2.2.1, v₃.gpr, v₂.other _ hr.1, v₁.other _ hr.1,
        g r (by simp [maskRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
    obtain ks : u₅.sp = s.sp ∧ u₅.lr = s.lr ∧ u₅.rd = s.rd ∧ u₅.wr = s.wr :=
      ⟨by rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp], by rw [v₅.lr, v₄.lr, v₃.lr, v₂.lr, v₁.lr, lr],
        by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd], by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr]⟩
    obtain ev := eval_nonzero r25' (by omega_using [hn])
    by_cases he : j + 1 = n
    · left
      exact ⟨ev.trans (by simp [he]), by rw [m₅, he], g', ks.1, ks.2.1, ks.2.2.1, ks.2.2.2⟩
    · right
      exact ⟨ev.trans (by simp; omega_using [hj, he]), n - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], r24', r25', r7', m₅, g',
        ks.1, ks.2.1, ks.2.2.1, ks.2.2.2⟩

end VG.Proof.AesOcb.PPC64LE

end

end


/-!
# AES-OCB on PPC64LE: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front` with the
tag at `W + t2O`, then the received tag padded at `W` (`recv`), the
comparison of the padded tags (`cmp`), the mask of the data (`mask`) and
`restore`, which keeps the result in `r3` (`open_wp`). As on AArch64
(`Proof/AesOcb/AArch64/Open.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (covers_mem covers_left SavedAt)

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
    (h3 : s₀.gpr .r3 = K) (h4 : s₀.gpr .r4 = BitVec.ofNat 64 R) (h5 : s₀.gpr .r5 = N)
    (h6 : s₀.gpr .r6 = BitVec.ofNat 64 nl) (h7 : s₀.gpr .r7 = A) (h8 : s₀.gpr .r8 = BitVec.ofNat 64 al)
    (h9 : s₀.gpr .r9 = D) (h10 : s₀.gpr .r10 = BitVec.ofNat 64 n) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s₀.mem K R) (Spec.Ocb.ctxInv s₀.mem K R) (ctxLstar s₀.mem K) tl
          (bytesAt s₀.mem N nl) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n) (bytesAt s₀.mem T tl) with
      | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .r3).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  obtain L₀ : Lay (s₀.gpr .r3) W := by rw [h3]; exact Ar.lay
  obtain hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := by rw [h3]; exact Ar.perm.k
  have hn := Ar.data.lt
  unfold «open» front
  refine WP.seq (WP.seq (WP.mono (entry_ok L₀ Ar.perm.w hC hW hT Ar.args Ar.argsW) fun s₁ P₁ => ?_))
  have hW₁ : s₁.gpr .r31 = W := P₁.r31
  obtain hK₁ : s₁.gpr .r29 = K := P₁.r29.trans h3
  obtain hD₁ : s₁.gpr .r27 = D := P₁.r27.trans h9
  obtain h28 : s₁.gpr .r28 = BitVec.ofNat 64 R := P₁.r28.trans h4
  obtain h23 : s₁.gpr .r23 = BitVec.ofNat 64 n := P₁.r23.trans h10
  obtain L : Lay (s₁.gpr .r29) (s₁.gpr .r31) := by rw [hK₁, hW₁]; exact Ar.lay
  refine WP.assoc (WP.seq (WP.mono (preRest_wp Ar P₁ htl h3 h4 h5 h6 h7 h8) fun s₃ P₃ => ?_))
  obtain hD₃ : DBuf (s₁.gpr .r29) (s₁.gpr .r31) s₃ (s₁.gpr .r27) n := by
    rw [hK₁, hW₁, hD₁]; exact Ar.data.of_eq P₃.rd P₃.wr
  obtain c₃ : ctxCiph s₃.mem K R = ctxCiph s₀.mem K R := ctxCiph_W Ar.lay P₃.frame Ar.rounds
  obtain i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s₀.mem K R := ctxInv_W Ar.lay P₃.frame Ar.rounds
  obtain l₃ : ctxLstar s₃.mem K = ctxLstar s₀.mem K := ctxLstar_W Ar.lay P₃.frame
  obtain d₃ : bytesAt s₃.mem D n = bytesAt s₀.mem D n := bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (bodyOpen_ok L P₃.env Ar.rounds h28 h23 hD₃
    (O0 := Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)) (by rw [hW₁]; exact P₃.ofs)
    (by rw [hW₁]; exact P₃.o0) (by rw [hW₁]; exact P₃.ck) (by rw [hW₁, hK₁, P₃.l0, l₃])) fun s₄ B => ?_)
  obtain Bf : Frame (bodyR W D n) s₃.mem s₄.mem := by have := B.frame; rwa [hW₁, hD₁] at this
  obtain F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut Bf
  obtain cK₄ : ctxCiph s₄.mem K R = ctxCiph s₀.mem K R := (ctxCiph_mut Ar.lay Ar.data.k F₄ Ar.rounds).trans c₃
  obtain ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.mono (tag_ok L B.env Ar.rounds h28 (.inr rfl)) fun s₅ T₅ => ?_
  obtain Tf : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
      s₄.mem s₅.mem := by have := T₅.frame; rwa [hW₁] at this
  obtain F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (.inr ⟨by decide, by decide⟩) Tf
  obtain sv₅ := saved_mut Ar.lay Ar.data.w (saved_mut Ar.lay Ar.data.w P₃.saved F₄) F₅
  have E₅ := T₅.env
  obtain rd₅ : s₅.rd = s₀.rd := by rw [T₅.rd, B.rd, P₃.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [T₅.wr, B.wr, P₃.wr]
  -- The received tag, to `W`.
  obtain hTd : (⟨s₁.gpr .r20, tl⟩ : Region).Disjoint ⟨s₁.gpr .r31, 2560⟩ := by rw [P₁.r20, hW₁]; exact Ar.tag.w
  refine WP.seq (WP.mono (recv_ok E₅ (P₁.r19.trans htl) Ar.t1 Ar.t16
    (by rw [P₁.r20, rd₅, wr₅]; exact Ar.tag.rd) hTd) fun s₆ ⟨b₆, f₆, g₆, sp₆, lr₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ := E₅.others g₆ sp₆ rd₆ wr₆
  rw [hW₁, P₁.r20] at b₆
  rw [hW₁] at f₆
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok E₆ (P₁.r19.trans htl) Ar.t1 Ar.t16) fun s₇ ⟨r3₇, f₇, g₇, sp₇, lr₇, rd₇, wr₇⟩ => ?_)
  obtain E₇ := E₆.others g₇ sp₇ rd₇ wr₇
  rw [hW₁] at r3₇ f₇
  let c : Bool := decide (bytesAt s₆.mem (W + BitVec.ofNat 64 tagO) 16 =
    bytesAt s₆.mem (W + BitVec.ofNat 64 t2O) tl ++ zeros (16 - tl))
  obtain r3c : s₇.gpr .r3 = if c then 1 else 0 := by
    rw [r3₇]; simp only [c, decide_eq_true_eq]
  obtain hD₇ : DBuf (s₁.gpr .r29) (s₁.gpr .r31) s₇ D n := by
    rw [hK₁, hW₁]; exact Ar.data.of_eq (by rw [rd₇, rd₆, rd₅]) (by rw [wr₇, wr₆, wr₅])
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₇ hD₁ h23 hD₇ r3c) fun s₈ ⟨m₈, g₈, sp₈, lr₈, rd₈, wr₈⟩ => ?_)
  obtain E₈ := E₇.others g₈ sp₈ rd₈ wr₈
  obtain F₈ : Frame [⟨D, n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain F₅₈ : Frame (mutR W D n) s₅.mem s₈.mem :=
    ((f₆.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide)).trans
      (f₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutB (by decide) (by decide))).trans
      (F₈.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutD fun _ h => h)
  obtain sv₈ : SavedAt s₈.mem W s₀ := saved_mut Ar.lay Ar.data.w sv₅ F₅₈
  -- `restore`.
  refine WP.mono (Proof.AesGcm.PPC64LE.restore_ok (E₈.r31.trans hW₁)
    (by rw [rd₈, wr₈, rd₇, wr₇, rd₆, wr₆, rd₅, wr₅]; exact covers_left Ar.perm.w) sv₈
    (by rw [E₈.sp]) (fun r hr => by
      rw [E₈.fr r (by revert hr; revert r; decide), P₁.low r hr])) fun s₉ ⟨abi, m₉, r3₉, _, _⟩ => ⟨abi, ?_⟩
  -- The plaintext and the comparison.
  obtain r3₉' : s₉.gpr .r3 = if c then 1 else 0 := by
    rw [r3₉, g₈ _ (by decide), r3c]
  have hout := B.out
  rw [hK₁, hD₁, c₃, i₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [hW₁, hK₁, l₃] at hofs
  have hck := B.ck
  rw [hW₁, hD₁, hK₁, c₃, i₃, l₃, d₃] at hck
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
  rw [r3₉', d₉, hout, Proof.Ocb.decryptWith_eq]
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
theorem open_wp {s : State} (h : openPPC64LE.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp' (openArgs_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm
    rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.PPC64LE

end

end


/-!
# AES-OCB on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`; with no stack: a call keeps the return address
in the link register, which each function saves in the working space).
`Frame.lean` allocates the working space; `init` is AES-GCM's
(`Init.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE

theorem seal_correct (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_wp hs

theorem open_correct (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions -/

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0, with
the stack arguments at `0x8060`. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 1 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8068 then 4 else bif Nat.beq a.toNat 0x8061 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified :
    Verified PPC64LE.target «seal» (Proof.AesOcb.sealScratchContract PPC64LE.abi) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealPPC64LE, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop] [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified :
    Verified PPC64LE.target «open» (Proof.AesOcb.openScratchContract PPC64LE.abi) :=
  Verified.of_correct open_correct open_ct
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat, stackArg, stackArgAddr, Mem.readW,
        Mem.read] using openSat }

end VG.Proof.AesOcb.PPC64LE

end

end


/-!
# AES-OCB on PPC64LE, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratchArgs`): `tag` and `tag_len` arrive on the stack, so
the frame of 2688 bytes copies them, then the working space's address, above
its stack pointer. The copies are read only where the pre- and
postconditions read the buffers, and `open`'s leak, whether it succeeds,
reads only its buffers (`Proof/AesOcb/Scratch.lean`). As AES-GCM's `open`
(`Proof/AesGcm/PPC64LE/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8060, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract PPC64LE.abi 2688).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «seal»)
      (Proof.AesOcb.sealRoundsContract PPC64LE.abi 2688) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.sealPre PPC64LE.abi.ptrBits) (post := Proof.AesOcb.sealRoundsPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2688) (m := 2) seal_verified (by decide) (by decide)
    (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _)
    (Proof.AesOcb.sealPostOut_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8060, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract PPC64LE.abi 2688).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «open»)
      (Proof.AesOcb.openRoundsContract PPC64LE.abi 2688) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre PPC64LE.abi.ptrBits) (post := Proof.AesOcb.openRoundsPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2688) (m := 2) (leak := some (Spec.Ocb.openLeak PPC64LE.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesOcb.openPre_local _) (Proof.AesOcb.openPost_local _)
    (Proof.AesOcb.openPostOut_local _)
    openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.PPC64LE
