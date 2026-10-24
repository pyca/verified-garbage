module

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
public import VerifiedGarbage.Impl.AesOcb.PPC64LE

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
  have lp : LoopPre s S (W + BitVec.ofNat 64 d) tl :=
    ⟨hr3, hr4, hr5, h1, by omega, hSr, covers_prefix (covers_off hw hd (by decide)) h16,
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
  have hTd' : (⟨V .r20, tl⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 tagO, 16⟩ :=
    hTd.sub_right (Lay.wSub (by decide))
  have hA : WP isa (.block (zero16 tagO ++ [Impl.AesGcm.PPC64LE.mov .r3 .r20, Impl.AesGcm.PPC64LE.mov .r4 .r31,
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
  have hT₂ : bytesAt s₂.mem (V .r20) tl = bytesAt s.mem (V .r20) tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd') (by omega)
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
  have r₀ := E.perm.wR (show 0 + 8 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 336 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 8 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 344 + 8 ≤ 2560 by decide)
  have hrun : WP isa (.block cmpTail) s fun s' =>
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
  have e := words_eq s.mem (V .r31 + BitVec.ofNat 64 0) (V .r31 + BitVec.ofNat 64 336)
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
  have hSd : (⟨V .r31 + BitVec.ofNat 64 t2O, tl⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 vO, 16⟩ :=
    Offset.disjoint _ (.inl (by simp only [t2O, vO]; omega)) (by simp only [t2O]; omega) (by decide)
  have hA : WP isa (.block (zero16 vO ++ [.addi .r3 .r31 t2O, .addi .r4 .r31 vO,
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
  have hS₂ : bytesAt s₂.mem (V .r31 + BitVec.ofNat 64 t2O) tl = bytesAt s.mem (V .r31 + BitVec.ofNat 64 t2O) tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega)
  have dTV : ∀ r ∈ [(⟨V .r31 + BitVec.ofNat 64 vO, 16⟩ : Region)],
      (⟨V .r31 + BitVec.ofNat 64 tagO, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (padCopy_ok (W := V .r31) (d := vO) (by rw [wr₂]; exact hw) (by decide) h1 h16
    (by rw [rd₂, wr₂]; exact covers_left (covers_prefix (covers_off hw (d := t2O) (n := 16) (by decide) (by decide))
      h16)) hSd hz a3 a4 a5) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  obtain ⟨rd₃, wr₃, sp₃, lr₃⟩ := lo.keeps
  have g₃ : ∀ r, r ∉ xpRegs → s₃.gpr r = s.gpr r := fun r hr => by
    simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [lo.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2, g₂ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1]
  have E₃ := E.others g₃ (by rw [sp₃, sp₂]) (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])
  have f₃ : Frame [⟨V .r31 + BitVec.ofNat 64 vO, 16⟩] s.mem s₃.mem := fz.trans hf
  have hT₃ : bytesAt s₃.mem (V .r31 + BitVec.ofNat 64 tagO) 16 = bytesAt s.mem (V .r31 + BitVec.ofNat 64 tagO) 16 :=
    Proof.Cmac.bytesAt_frame f₃ dTV (by omega)
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
    omega

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
  have hA : WP isa (.block [Impl.AesGcm.PPC64LE.mov .r24 .r27, Impl.AesGcm.PPC64LE.mov .r25 .r23, .li .r4 0,
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
  refine WP.ite _ (eval_zero r25₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hz : n = 0 := by have := of_decide_eq_true h0; omega
    subst hz
    refine ⟨by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], g₁, k₁.sp, k₁.lr, k₁.rd, k₁.wr⟩
  · have hpos : 0 < n := by have := of_decide_eq_false h0; omega
    refine WP.loop (M := isa)
      (fun (k : Nat) (u : State) => ∃ j, k = n - j ∧ j < n ∧ u.gpr .r24 = D + BitVec.ofNat 64 j ∧
        u.gpr .r25 = BitVec.ofNat 64 (n - j) ∧ u.gpr .r7 = BitVec.ofNat 64 0 - (if c then 1 else 0) ∧
        u.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
        (∀ r, r ∉ maskRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.lr = s.lr ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_
      (n - 0) _ ⟨0, rfl, hpos, by rw [r24₁], r25₁, r7₁,
        by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], g₁, k₁.sp, k₁.lr, k₁.rd, k₁.wr⟩
    rintro k u ⟨j, rfl, hj, r24, r25, r7, mem, g, sp, lr, rd, wr⟩
    have rq : InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 j) 1 := by
      rw [rd, wr]; exact in_of_covers hD.rd hj hn
    have wq : InRegions u.wr (D + BitVec.ofNat 64 j) 1 := by rw [wr]; exact in_of_covers hD.wr hj hn
    refine cwp_lbz (a := D + BitVec.ofNat 64 j) (by decide) (by decide) (by rw [r24, BitVec.add_zero]) rq
      fun u₁ v₁ => cwp_and fun u₂ v₂ => cwp_stb (a := D + BitVec.ofNat 64 j) (by decide) (by decide)
        (by rw [v₂.other _ (by decide), v₁.other _ (by decide), r24, BitVec.add_zero])
        (by rw [v₂.wr, v₁.wr]; exact wq) fun u₃ v₃ => cwp_addi (by decide) (by decide) fun u₄ v₄ =>
        cwp_subi (by decide) (by decide) fun u₅ v₅ => WP.block_nil ?_
    have hl : (if c then bytesAt s.mem D j else zeros j).length = j := length_mask _ _ _ _
    have byte : u.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) := by
      rw [mem]; exact Proof.AesGcm.PPC64LE.dst_kept hj hn _ hl
    have m₅ : u₅.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
      rw [v₅.mem, v₄.mem, v₃.mem, v₂.gpr, v₁.gpr, v₁.other _ (by decide), r7, byte,
        mask_byte, v₂.mem, v₁.mem, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl]
    have r25' : u₅.gpr .r25 = BitVec.ofNat 64 (n - (j + 1)) := by
      rw [v₅.gpr, v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), r25,
        Proof.AesGcm.PPC64LE.dec64 hj hn]
    have r24' : u₅.gpr .r24 = D + BitVec.ofNat 64 (j + 1) := by
      rw [v₅.other _ (by decide), v₄.gpr, v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), r24,
        Offset.add_add]
    have r7' : u₅.gpr .r7 = BitVec.ofNat 64 0 - (if c then 1 else 0) := by
      rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), r7]
    have g' : ∀ r, r ∉ maskRegs → u₅.gpr r = s.gpr r := fun r hr => by
      simp only [maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [v₅.other _ hr.2.2.2, v₄.other _ hr.2.2.1, v₃.gpr, v₂.other _ hr.1, v₁.other _ hr.1,
        g r (by simp [maskRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
    have ks : u₅.sp = s.sp ∧ u₅.lr = s.lr ∧ u₅.rd = s.rd ∧ u₅.wr = s.wr :=
      ⟨by rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp], by rw [v₅.lr, v₄.lr, v₃.lr, v₂.lr, v₁.lr, lr],
        by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd], by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr]⟩
    have ev := eval_nonzero r25' (by omega)
    by_cases he : j + 1 = n
    · left
      exact ⟨ev.trans (by simp [he]), by rw [m₅, he], g', ks.1, ks.2.1, ks.2.2.1, ks.2.2.2⟩
    · right
      exact ⟨ev.trans (by simp; omega), n - (j + 1), by omega, j + 1, rfl, by omega, r24', r25', r7', m₅, g',
        ks.1, ks.2.1, ks.2.2.1, ks.2.2.2⟩

end VG.Proof.AesOcb.PPC64LE
