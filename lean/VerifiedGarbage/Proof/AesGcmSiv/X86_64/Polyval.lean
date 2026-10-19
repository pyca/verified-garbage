module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
public import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV on x86-64: POLYVAL and the tag input (`polyval`)

Untrusted: everything here is checked by Lean. `lens` absorbs the lengths
block (`lens_ok`), `tagIn` turns POLYVAL's result into the tag input
(`tagIn_ok`), and `polyvalLong` absorbs the padded additional data, the padded
data and the lengths block from the zero accumulator, leaving the tag input
of RFC 8452 §4 at `W + 96` (`polyvalLong_ok`). `stage` copies the padded
blocks of a string, each reversed, to block `s` of `W + 488` on
(`stage_ok`); `polyvalOne` stages the additional data, the data and the
lengths block so and absorbs all of them with one call of `vg_ghash`
(`polyvalOne_ok`), which `polyval` takes when they fit (`polyval_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall GhPost gh_call ofNat_add_ofNat in_off toNat_ofNat_of_lt)

/-- The arguments of `lens`'s call. -/
theorem lensArgs_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {al n : Nat}
    (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    ∃ t₁ : State,
      runBlock isa (([.mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 bO) .rax,
        .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] :
          List Instr) ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr)) t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 128) (bswap64 (BitVec.ofNat 64 (8 * n)))).writeW
        (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8) (bswap64 (BitVec.ofNat 64 (8 * al))) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 64 ∧ t₁.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 1512 ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 128 ∧
      t₁.gpr .rcx = BitVec.ofNat 64 1 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have r₂ := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 128 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 136 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [ghArgs, h15, r₁, r₂, w₀, w₈, hal, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, add_ofNat_assoc, Proof.AesGcm.X86_64.times8_val,
      toNat_ofNat_of_lt hal', toNat_ofNat_of_lt hn']
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · intro r hr; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_arithFlags, gpr_setReg, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]
  all_goals rfl

theorem lens_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {al n : Nat}
    (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    WP isa (lens v.callees) t
      (AbsPost K W SP [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))] t) := by
  obtain ⟨t₁, run₁, hm₁, rdi₁, rsi₁, r8₁, rdx₁, rcx₁, hg₁, hrd₁, hwr₁⟩ := lensArgs_ok E hal hn hal' hn'
  have E₁ : Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  have fB : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (Nat.le_refl _) (by decide) (by have := L.ww; omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
  have dB : ∀ d, d + 16 ≤ 128 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl hd) (by omega_arith) (by decide)
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (gh_call v.gh (gargs L E₁ (d := 128) (n := 1) (by decide) (by decide) rdi₁ rsi₁ rdx₁ rcx₁ r8₁))
    fun t₂ Q => ?_
  have fr₂ := Q.frame
  rw [E₁.rsp] at fr₂
  refine ⟨E₁.of_saved Q.saved Q.rd Q.wr, by rw [Q.rd, hrd₁], by rw [Q.wr, hwr₁],
    (fB.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans (fr₂.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp), ?_⟩
  rw [Q.out, Proof.AesGcm.X86_64.blockAt_frame fB (dB 64 (by decide)),
    Proof.AesGcm.X86_64.blockAt_frame fB (dB 80 (by decide)),
    show Spec.Gcm.blocksAt t₁.mem (W + BitVec.ofNat 64 128) 1 = [Spec.Gcm.blockAt t₁.mem (W + BitVec.ofNat 64 128)] by
      simp [Spec.Gcm.blocksAt], hm₁, blockAt_two, GcmSiv.le64_le8, GcmSiv.le64_le8, GcmSiv.ofBytes_le8]

theorem tagIn_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {N : Addr}
    (hN : t.mem.readW (W + BitVec.ofNat 64 208) 64 = N) (hNb : Buf K W SP t N 12) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t.mem t'.mem ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 96) 16 =
        GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80))) (bytesAt t.mem N 12) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have hw := L.ww
  have r₀ := E.perm.wR (show 80 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 88 + 8 ≤ 3816 by decide)
  have rn := E.perm.wR (show 208 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3816 by decide)
  have n₀ : InRegions (t.rd ++ t.wr) N 8 := by
    simpa using in_off (d := 0) (n := 8) hNb.rd (by decide) (by decide)
  have n₈ := in_off (d := 8) (n := 4) hNb.rd (by decide) (by decide)
  refine ⟨_, by srun [tagIn, h15, r₀, r₈, rn, w₀, w₈, hN, n₀, n₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (Nat.le_refl _) (by decide) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains W (by decide) (by decide) (by omega_arith))
  · simp only [mem_setReg, mem_arithFlags]
    rw [show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
      Proof.Cmac.bytesAt_store2, ← Proof.Gcm.X86_64.blockAt_bswap, BitVec.add_zero, add_ofNat_assoc,
      GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le8_readW,
      ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words]
    rfl
  · intro r hr; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_arithFlags, gpr_setReg, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]
  all_goals rfl

/-- The slots, after code that writes only what absorbing writes. -/
theorem Slots.absR {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {m m' : Mem}
    (S : Slots W R N A D al n m) (hf : Frame (absR W SP) m m') : Slots W R N A D al n m' := by
  have k (d : Nat) (hd : 200 ≤ d ∧ d + 8 ≤ 248) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    hf.readW (Region.contains_self _ _) (w_absR L (.inr (.inr ⟨by omega_arith, by omega_arith⟩))) (by decide)
  exact ⟨by rw [k 200 (by decide)]; exact S.rounds, by rw [k 208 (by decide)]; exact S.nonce,
    by rw [k 216 (by decide)]; exact S.aad, by rw [k 224 (by decide)]; exact S.alen,
    by rw [k 232 (by decide)]; exact S.data, by rw [k 240 (by decide)]; exact S.len⟩

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W SP : Addr) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: absR W SP

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (K W SP : Addr) (N A D : Addr) (al n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (polyR W SP) t.mem t'.mem
  /-- Given that POLYVAL is GHASH with `mulXG` of the key (`PolyvalEq`, proved
  in `Verified.lean` so that these proofs need not import its algebra). -/
  out : GcmSiv.Polyval.PolyvalEq → bytesAt t'.mem (W + BitVec.ofNat 64 96) 16 =
    Spec.GcmSiv.tagInput (bytesAt t.mem (W + BitVec.ofNat 64 16) 16) (bytesAt t.mem N 12) (bytesAt t.mem D n)
      (bytesAt t.mem A al)

/-- The tag input, from GHASH over the padded additional data, the padded
data and the lengths block. -/
theorem polyPost_ok {K W SP : Addr} (L : Lay K W SP) {t t₅ : State} {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hN : Buf K W SP t N 12)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0)
    (P : AbsPost K W SP (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al)) ++
      Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem D n)) ++
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))]) t t₅) :
    WP isa (.block tagIn) t₅ (PolyPost K W SP N A D al n t) := by
  have S₅ := S.absR L P.frame
  obtain ⟨t₆, run₆, fr₆, out₆, hg₆, hrd₆, hwr₆⟩ := tagIn_ok L P.env S₅.nonce (hN.of_eq P.rd P.wr)
  refine WP.of_runBlock ⟨t₆, run₆, P.env.of_saved hg₆ hrd₆ hwr₆, hrd₆.trans P.rd, hwr₆.trans P.wr,
    (P.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans
      (fr₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self ..), fun hpv => ?_⟩
  have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
    rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega_arith
  rw [out₆, Proof.AesGcm.X86_64.bytesAt_frame P.frame (buf_absR hN) (by decide), GcmSiv.tagInput_eq,
    Proof.AesGcm.X86_64.length_bytesAt, Proof.AesGcm.X86_64.length_bytesAt, P.out, hG, hY, Spec.GcmSiv.polyval,
    hpv, GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
    GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n)) (by simp [Spec.GcmSiv.le64])]

theorem polyvalLong_ok (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat}
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n)
    (hN : Buf K W SP t N 12)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyvalLong v.callees wide) t (PolyPost K W SP N A D al n t) := by
  have h15 := E.r15
  have rA := E.perm.wR (show 216 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have sA := S.aad
  have sL := S.alen
  obtain ⟨t₁, run₁, h12₁, hbp₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] t = some t₁ ∧
      t₁.gpr .r12 = A ∧ t₁.gpr .rbp = BitVec.ofNat 64 al ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rA, rL], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sA]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sL]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  refine WP.mono (absorb_ok v wide L E₁ (hA.of_eq hrd₁ hwr₁) h12₁ hbp₁) fun t₂ P₂ => ?_
  have P₂' := P₂.of_eq hm₁ hrd₁ hwr₁
  rw [hm₁] at P₂'
  have S₂ := S.absR L P₂'.frame
  have h15₂ := P₂'.env.r15
  have rD := P₂'.env.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rN := P₂'.env.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sD := S₂.data
  have sN := S₂.len
  obtain ⟨t₃, run₃, h12₃, hbp₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))] t₂ = some t₃ ∧
      t₃.gpr .r12 = D ∧ t₃.gpr .rbp = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → t₃.gpr r = t₂.gpr r) ∧
      t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [h15₂, rD, rN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sD]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sN]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, WP.seq ?_⟩)
  have E₃ : Env K W SP t₃ := P₂'.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have hD₃ : Buf K W SP t₃ D n := hD.of_eq (hrd₃.trans P₂'.rd) (hwr₃.trans P₂'.wr)
  refine WP.mono (absorb_ok v wide L E₃ hD₃ h12₃ hbp₃) fun t₄ P₄ => ?_
  have P₄' := P₄.of_eq hm₃ hrd₃ hwr₃
  rw [hm₃, Proof.AesGcm.X86_64.bytesAt_frame P₂'.frame (buf_absR hD) (Nat.le_of_lt hD.lt)] at P₄'
  have P₂₄ := P₂'.trans L P₄'
  have S₄ := S.absR L P₂₄.frame
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env S₄.alen S₄.len hA.lt hD.lt) fun t₅ P₅ => ?_)
  exact polyPost_ok L S hN hG hY (P₂₄.trans L P₅)

/-! ## POLYVAL in one call -/

theorem blocksAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Gcm.blocksAt m p (a + b) =
      Spec.Gcm.blocksAt m p a ++ Spec.Gcm.blocksAt m (p + BitVec.ofNat 64 (16 * a)) b := by
  simp only [Spec.Gcm.blocksAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, add_ofNat_assoc, Nat.mul_add]

theorem elemsAt_length (m : Mem) (Q : Addr) (k : Nat) : (elemsAt m Q k).length = k := by
  simp [elemsAt]

/-- What staging from block `s` writes: the block at `W + 128` and the blocks
of `W + 488` from block `s` on. -/
abbrev stR (W : Addr) (s : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 (488 + 16 * s), 1024 - 16 * s⟩]

/-- What staging leaves, from `t`, having staged the elements `xs` from block
`s` of `W + 488` on. -/
structure StPost (K W SP : Addr) (s : Nat) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (stR W s) t.mem t'.mem
  out : Spec.Gcm.blocksAt t'.mem (W + BitVec.ofNat 64 (488 + 16 * s)) xs.length = xs
  rdi : t'.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * (s + xs.length))
  le : s + xs.length ≤ 64

/-- Nothing staged. -/
theorem StPost.nil {K W SP : Addr} {s : Nat} {t : State} (E : Env K W SP t) (hs : s ≤ 64)
    (hdi : t.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * s)) : StPost K W SP s [] t t :=
  ⟨E, rfl, rfl, Frame.refl _ _, by simp [Spec.Gcm.blocksAt], by rw [hdi, List.length_nil, Nat.add_zero], by simpa⟩

theorem StPost.trans {K W SP : Addr} (L : Lay K W SP) {s : Nat} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : StPost K W SP s xs t t₁) (h₂ : StPost K W SP (s + xs.length) ys t₁ t₂) :
    StPost K W SP s (xs ++ ys) t t₂ := by
  have hl₁ := h₁.le
  have hl₂ := h₂.le
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans (h₂.frame.sub fun r hr => ?_), ?_,
    by rw [h₂.rdi, List.length_append, Nat.add_assoc], by rw [List.length_append]; omega_arith⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub W (by omega_arith) (by omega_arith)⟩
  · rw [List.length_append, blocksAt_add, Proof.AesGcm.X86_64.blocksAt_frame h₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith), h₁.out, add_ofNat_assoc,
      show 488 + 16 * s + 16 * xs.length = 488 + 16 * (s + xs.length) by omega_arith, h₂.out]

/-- `stageTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros,
reversed at block `s` of `W + 488`. -/
theorem stageTail_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {P : Addr} {r : Nat} (hr1 : 1 ≤ r) (hr : r < 16) (hP : Buf K W SP t P r)
    (hsi : t.gpr .rsi = P) (hbp : t.gpr .rbp = BitVec.ofNat 64 r) {s : Nat} (hs : s < 64)
    (hdi : t.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * s)) :
    WP isa stageTail t
      (StPost K W SP s [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have h15 := E.r15
  have hw := L.ww
  have w₀ := E.perm.wW (show 128 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 136 + 8 ≤ 3816 by decide)
  -- The destination kept, the block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, hdi₁, hsi₁, hcx₁, hbx₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa ([.mov .rbx (.reg .rdi)] ++ zero16 bO ++ ptr .rdi .r15 bO ++ [.mov .rcx (.reg .rbp)]) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero2 t.mem (W + BitVec.ofNat 64 128) ∧ t₁.gpr .rdi = W + BitVec.ofNat 64 128 ∧
      t₁.gpr .rsi = P ∧ t₁.gpr .rcx = BitVec.ofNat 64 r ∧ t₁.gpr .rbx = W + BitVec.ofNat 64 (488 + 16 * s) ∧
      (∀ q, q ≠ .rax → q ≠ .rdi → q ≠ .rbx → q ≠ .rcx → t₁.gpr q = t.gpr q) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [zero16, h15, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, Proof.Cmac.zero2, add_ofNat_assoc]
      rfl
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hsi]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
    · intro q h₁ h₂ h₃ h₄; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, h₃, h₄, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have lp : Proof.AesGcm.X86_64.LoopPre t₁ P (W + BitVec.ofNat 64 128) r :=
    ⟨hsi₁, hdi₁, hcx₁, hr1, by omega_arith, by rw [hrd₁, hwr₁]; exact hP.rd, by rw [hwr₁]; exact E.perm.wC (by omega_arith),
      hP.w.sub_right (Lay.wSub (by omega_arith))⟩
  refine WP.seq (WP.mono (Proof.AesGcm.X86_64.copyLoop_ok t₁ lp) fun t₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem P r = bytesAt t.mem P r := by
    rw [hm₁, Proof.Cmac.zero2]
    exact Proof.AesGcm.X86_64.bytesAt_frame
      (((Frame.refl [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)] _).writeW (List.mem_singleton_self _) _
        (Offset.contains W (Nat.le_refl _) (by decide) (by omega_arith))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide)))
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by omega_arith)
  have hb₂ : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := Proof.AesGcm.X86_64.length_bytesAt t.mem P r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega_arith), hl]
  have h15₂ : t₂.gpr .r15 = W := by
    rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide), h15]
  have hbx₂ : t₂.gpr .rbx = W + BitVec.ofNat 64 (488 + 16 * s) := by rw [hg₂ _ (by decide) (by decide), hbx₁]
  have r₀ := E.perm.wR (show 128 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 136 + 8 ≤ 3816 by decide)
  have v₀ := E.perm.wW (d := 488 + 16 * s) (n := 8) (by omega_arith)
  have v₈ := E.perm.wW (d := 488 + 16 * s + 8) (n := 8) (by omega_arith)
  rw [← add_ofNat_assoc] at v₈
  rw [← hrd₁, ← hwr₁, ← hrd₂, ← hwr₂] at r₀ r₈
  rw [← hwr₁, ← hwr₂] at v₀ v₈
  -- The block reversed at block `s`.
  obtain ⟨t₃, run₃, hm₃, hdi₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃ : State,
      runBlock isa [.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax, .bswap .rdx,
        .store (at_ .rbx 0) .rdx, .store (at_ .rbx 8) .rax, .mov .rdi (.reg .rbx), .alu .add .rdi (imm 16)] t₂ =
        some t₃ ∧
      t₃.mem = (t₂.mem.writeW (W + BitVec.ofNat 64 (488 + 16 * s))
          (bswap64 (t₂.mem.readW (W + BitVec.ofNat 64 136) 64))).writeW
        (W + BitVec.ofNat 64 (488 + 16 * s) + BitVec.ofNat 64 8) (bswap64 (t₂.mem.readW (W + BitVec.ofNat 64 128) 64)) ∧
      t₃.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * (s + 1)) ∧
      (∀ q ∈ [Reg.r13, .r15, .rsp], t₃.gpr q = t₂.gpr q) ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [h15₂, hbx₂, r₀, r₈, v₀, v₈], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, add_ofNat_assoc, hbx₂, BitVec.add_zero]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbx₂, add_ofNat_assoc]
      rw [show 488 + 16 * s + 16 = 488 + 16 * (s + 1) by omega_arith]
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₃ : Env K W SP t₃ := E.keep (fun q hq => by
      rw [hg₃ q hq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;>
        rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])
  -- What the pieces wrote.
  have mB : (⟨W + BitVec.ofNat 64 128, 16⟩ : Region) ∈ stR W s := by simp
  have mR : (⟨W + BitVec.ofNat 64 (488 + 16 * s), 1024 - 16 * s⟩ : Region) ∈ stR W s := by simp
  have f₁ : Frame (stR W s) t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero2]
    exact ((Frame.refl _ _).writeW mB _ (Offset.contains W (Nat.le_refl _) (by decide) (by omega_arith))).writeW mB _
      (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
  have f₂ : Frame (stR W s) t₁.mem t₂.mem := by
    rw [hm₂]
    exact (Proof.AesGcm.X86_64.writeBytes_frame' _ (Proof.AesGcm.X86_64.length_bytesAt _ _ _)).sub
      fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, mB, Region.sub_prefix (by omega_arith)⟩
  have f₃ : Frame (stR W s) t₂.mem t₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW mR _ (Offset.contains W (Nat.le_refl _) (by omega_arith) (by omega_arith))).writeW mR _
      (Offset.contains_base _ (show 8 + 8 ≤ 1024 - 16 * s by omega_arith) (by decide))
  refine WP.of_runBlock ⟨t₃, run₃, E₃, by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁], (f₁.trans f₂).trans f₃,
    ?_, by rw [hdi₃]; rfl, by simp only [List.length_singleton]; omega_arith⟩
  simp only [List.length_singleton]
  rw [show Spec.Gcm.blocksAt t₃.mem (W + BitVec.ofNat 64 (488 + 16 * s)) 1 =
      [Spec.Gcm.blockAt t₃.mem (W + BitVec.ofNat 64 (488 + 16 * s))] by simp [Spec.Gcm.blocksAt],
    hm₃, blockAt_two, ← hb₂, GcmSiv.ofBytes_bytesAt, add_ofNat_assoc]

/-- `stage wide`: the `n` bytes at `Q`, padded with zeros to whole blocks,
reversed from block `s` of `W + 488` on. -/
theorem stage_ok (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {Q : Addr} {n : Nat} (hQ : Buf K W SP t Q n) (h12 : t.gpr .r12 = Q) (hbp : t.gpr .rbp = BitVec.ofNat 64 n)
    {s : Nat} (hs : s + n / 16 < 64) (hdi : t.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * s)) :
    WP isa (stage wide) t (StPost K W SP s (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q n))) t) := by
  have hn := hQ.lt
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  obtain ⟨t₁, run₁, hbx₁, hbp₁, hsi₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .mov .rsi (.reg .r12),
        .alu .test .rbx (.reg .rbx)] t = some t₁ ∧
      t₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₁.gpr .rsi = Q ∧
      t₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .rsi → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp,
        Proof.AesGcm.X86_64.shr4 _ hn]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp, hand]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h12]
    · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hbp, Proof.AesGcm.X86_64.shr4 _ hn]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]
    · intro r h₁ h₂ h₃; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have hQ₁ := hQ.of_eq hrd₁ hwr₁
  have hdi₁ : t₁.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * s) := by
    rw [hg₁ _ (by decide) (by decide) (by decide), hdi]
  -- The whole blocks.
  have hmid : WP isa (.ite .e (.block []) (.seq (.block [.mov .r14 (.reg .rbx)]) (revSel wide))) t₁ fun t₂ =>
      StPost K W SP s (elemsAt t.mem Q (n / 16)) t₁ t₂ ∧ t₂.gpr .rsi = Q + BitVec.ofNat 64 (16 * (n / 16)) ∧
      t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := by
    refine WP.ite (decide (n / 16 = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 16 = 0 := by simpa using ht
      refine WP.block_nil ⟨?_, by rw [hsi₁, h0, Nat.mul_zero, BitVec.add_zero], hbp₁⟩
      rw [h0]
      exact StPost.nil E₁ (by omega_arith) hdi₁
    · have h0 : n / 16 ≠ 0 := by simpa using hf
      obtain ⟨t₂, run₂, h14₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ t₂ : State, runBlock isa [.mov .r14 (.reg .rbx)] t₁ = some t₂ ∧
          t₂.gpr .r14 = BitVec.ofNat 64 (n / 16) ∧ (∀ r, r ≠ .r14 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧
          t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
        refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
        · simp only [gpr_setReg, ite_true, hbx₁]
        · intro r h; simp only [gpr_setReg, h, ite_false]
        all_goals rfl
      refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
      have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
      have hQ₂ : Buf K W SP t₂ Q (16 * (n / 16)) := (hQ₁.take (by omega_arith)).of_eq hrd₂ hwr₂
      refine WP.mono (revSelAt_ok wide L E₂ (s := s) (c := n / 16) (by omega_arith) (by omega_arith) hQ₂ h14₂
        (by rw [hg₂ _ (by decide), hsi₁]) (by rw [hg₂ _ (by decide), hdi₁])) fun t₃ P => ?_
      have hl := elemsAt_length t.mem Q (n / 16)
      have fP := P.frame
      rw [hm₂] at fP
      refine ⟨⟨E₂.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact P.regs _ (by decide) (by decide) (by decide) (by decide) (by decide))
          P.rd P.wr, P.rd.trans hrd₂, P.wr.trans hwr₂, fP.sub fun r hr => ?_, ?_, ?_, by rw [hl]; omega_arith⟩,
        P.rsi, by rw [P.regs _ (by decide) (by decide) (by decide) (by decide) (by decide), hg₂ _ (by decide), hbp₁]⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub W (Nat.le_refl _) (by omega_arith)⟩
      · rw [hl, P.out, hm₂, hm₁]
      · rw [P.rdi, hl, show 488 + 16 * s + 16 * (n / 16) = 488 + 16 * (s + n / 16) by omega_arith]
  refine WP.seq (WP.mono hmid fun t₂ ⟨P₂, rsi₂, rbp₂⟩ => ?_)
  obtain ⟨t₃, run₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa [.alu .test .rbp (.reg .rbp)] t₂ = some t₃ ∧
      t₃.zf = some (decide (n % 16 = 0)) ∧ (∀ r, t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, rbp₂]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]
    · intro r; rfl
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have P₃ : StPost K W SP s (elemsAt t.mem Q (n / 16)) t t₃ :=
    ⟨P₂.env.keep (fun r _ => hg₃ r) hrd₃ hwr₃, by rw [hrd₃, P₂.rd, hrd₁], by rw [hwr₃, P₂.wr, hwr₁],
      by rw [hm₃, ← hm₁]; exact P₂.frame, by rw [hm₃]; exact P₂.out, by rw [hg₃]; exact P₂.rdi, P₂.le⟩
  have hl := elemsAt_length t.mem Q (n / 16)
  rw [elems_pad16_bytesAt]
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil P₃
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hP : Buf K W SP t₃ (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hQ.slice (by omega_arith)).of_eq P₃.rd P₃.wr
    refine WP.mono (stageTail_ok L P₃.env (by omega_arith) (by omega_arith) hP (by rw [hg₃, rsi₂]) (by rw [hg₃, rbp₂])
      (by rw [hl]; omega_arith) P₃.rdi) fun t₄ T => ?_
    have e := Proof.AesGcm.X86_64.bytesAt_frame P₃.frame (p := Q + BitVec.ofNat 64 (16 * (n / 16)))
      (n := n % 16) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact (hQ.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)).w.sub_right
          (Lay.wSub (by omega_arith))) (by omega_arith)
    rw [e] at T
    exact P₃.trans L T

/-- `lensAt`: the lengths block at block `k` of `W + 488`, and the arguments
of `vg_ghash` for the `k + 1` blocks there. -/
theorem lensAt_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {al n k : Nat} (hk : k < 64)
    (hdi : t.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * k))
    (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa lensAt t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 (488 + 16 * k)) (bswap64 (BitVec.ofNat 64 (8 * n)))).writeW
        (W + BitVec.ofNat 64 (488 + 16 * k) + BitVec.ofNat 64 8) (bswap64 (BitVec.ofNat 64 (8 * al))) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 64 ∧ t₁.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 1512 ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 488 ∧
      t₁.gpr .rcx = BitVec.ofNat 64 (k + 1) ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have r₂ := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (d := 488 + 16 * k) (n := 8) (by omega_arith)
  have w₈ := E.perm.wW (d := 488 + 16 * k + 8) (n := 8) (by omega_arith)
  rw [← add_ofNat_assoc] at w₈
  refine ⟨_, by srun [lensAt, ghArgs, h15, hdi, r₁, r₂, w₀, w₈, hal, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, add_ofNat_assoc, BitVec.add_zero,
      Proof.AesGcm.X86_64.times8_val, toNat_ofNat_of_lt hal', toNat_ofNat_of_lt hn']
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15, hdi]
    rw [BitVec.add_comm W, BitVec.add_sub_cancel, Proof.AesGcm.X86_64.shr4 _ (by omega_arith),
      show 488 / 16 - 1 = 29 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith),
      show (488 + 16 * k) / 16 - 29 = k + 1 by omega_arith]
  · intro r hr; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]
  all_goals rfl

/-- What staging writes, as what absorbing writes. -/
theorem Frame.stR_absR {W SP : Addr} {s : Nat} {m m' : Mem} (hs : s ≤ 64) (h : Frame (stR W s) m m') :
    Frame (absR W SP) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by mem_lit, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 488, 1024⟩, by mem_lit, Offset.sub W (by omega_arith) (by omega_arith)⟩

theorem StPost.of_eq {K W SP : Addr} {s : Nat} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : StPost K W SP s xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    StPost K W SP s xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, h.out, h.rdi, h.le⟩

theorem elems_pad16_length (m : Mem) (Q : Addr) (n : Nat) :
    (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n))).length ≤ n / 16 + 1 := by
  rw [elems_pad16_bytesAt, List.length_append, elemsAt_length]
  split <;> simp

/-- `polyvalOne`: POLYVAL with one call of `vg_ghash`, when the whole blocks of
the additional data and the data number at most 61. -/
theorem polyvalOne_ok (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al)
    (hD : Buf K W SP t D n) (hN : Buf K W SP t N 12) (hsz : al / 16 + n / 16 ≤ 61)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyvalOne v.callees wide) t (PolyPost K W SP N A D al n t) := by
  have h15 := E.r15
  have rA := E.perm.wR (show 216 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have sA := S.aad
  have sL := S.alen
  -- The additional data, staged from block 0.
  obtain ⟨t₁, run₁, hdi₁, h12₁, hbp₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      (ptr .rdi .r15 revO ++ [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))]) t = some t₁ ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * 0) ∧ t₁.gpr .r12 = A ∧ t₁.gpr .rbp = BitVec.ofNat 64 al ∧
      (∀ r, r ≠ .rdi → r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rA, rL], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, sA]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, sL]
    · intro r h₁ h₂ h₃; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, h₃, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have lA := elems_pad16_length t.mem A al
  have lD := elems_pad16_length t.mem D n
  refine WP.seq (WP.mono (stage_ok wide L E₁ (hA.of_eq hrd₁ hwr₁) h12₁ hbp₁ (by omega_arith) hdi₁) fun t₂ P₂ => ?_)
  rw [hm₁] at P₂
  have P₂' := P₂.of_eq hm₁ hrd₁ hwr₁
  have S₂ := S.absR L (Frame.stR_absR (by decide) P₂'.frame)
  -- The data, staged after it.
  have h15₂ := P₂'.env.r15
  have rD := P₂'.env.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rN := P₂'.env.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sD := S₂.data
  have sN := S₂.len
  obtain ⟨t₃, run₃, h12₃, hbp₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))] t₂ = some t₃ ∧
      t₃.gpr .r12 = D ∧ t₃.gpr .rbp = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → t₃.gpr r = t₂.gpr r) ∧
      t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [h15₂, rD, rN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sD]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sN]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : Env K W SP t₃ := P₂'.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have hD₃ : Buf K W SP t₃ D n := hD.of_eq (hrd₃.trans P₂'.rd) (hwr₃.trans P₂'.wr)
  refine WP.seq (WP.mono (stage_ok wide L E₃ hD₃ h12₃ hbp₃
    (s := 0 + (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al))).length) (by omega_arith)
    (by rw [hg₃ _ (by decide) (by decide)]; exact P₂'.rdi)) fun t₄ P₄ => ?_)
  have P₄' := P₄.of_eq hm₃ hrd₃ hwr₃
  rw [hm₃, Proof.AesGcm.X86_64.bytesAt_frame (Frame.stR_absR (SP := SP) (by decide) P₂'.frame) (buf_absR hD)
    (Nat.le_of_lt hD.lt)] at P₄'
  have P₂₄ := P₂'.trans L P₄'
  obtain ⟨k, hk⟩ : ∃ k, (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al)) ++
      Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem D n))).length = k := ⟨_, rfl⟩
  have hk64 : k < 64 := by rw [← hk, List.length_append]; omega_arith
  have out₄ := P₂₄.out
  have rdi₄ := P₂₄.rdi
  rw [hk] at out₄ rdi₄
  have S₄ := S.absR L (Frame.stR_absR (by decide) P₂₄.frame)
  -- The lengths block after them, and one call.
  obtain ⟨t₅, run₅, hm₅, rdi₅, rsi₅, r8₅, rdx₅, rcx₅, hg₅, hrd₅, hwr₅⟩ :=
    lensAt_ok P₂₄.env hk64 (by rw [rdi₄, Nat.zero_add]) S₄.alen S₄.len hA.lt hD.lt
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  have E₅ : Env K W SP t₅ := P₂₄.env.of_saved hg₅ hrd₅ hwr₅
  refine WP.seq (WP.mono (gh_call v.gh (gargs L E₅ (d := 488) (n := k + 1) (by decide) (by omega_arith) rdi₅ rsi₅ rdx₅
    rcx₅ r8₅)) fun t₆ Q => ?_)
  have mR : (⟨W + BitVec.ofNat 64 (488 + 16 * 0), 1024 - 16 * 0⟩ : Region) ∈ stR W 0 := by simp
  have fL : Frame [⟨W + BitVec.ofNat 64 (488 + 16 * k), 16⟩] t₄.mem t₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains W (Nat.le_refl _) (by omega_arith)
      (by omega_arith))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
  have F₅ : Frame (stR W 0) t.mem t₅.mem := P₂₄.frame.trans (fL.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, mR, Offset.sub W (by omega_arith) (by omega_arith)⟩)
  have fr₆ := Q.frame
  rw [E₅.rsp] at fr₆
  have d₀ : ∀ d, d + 16 ≤ 128 → ∀ r ∈ stR W 0, (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun d hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have pre : Spec.Gcm.blocksAt t₅.mem (W + BitVec.ofNat 64 488) k = Spec.Gcm.blocksAt t₄.mem (W + BitVec.ofNat 64 488) k :=
    Proof.AesGcm.X86_64.blocksAt_frame fL (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)
  refine polyPost_ok L S hN hG hY ⟨E₅.of_saved Q.saved Q.rd Q.wr, by rw [Q.rd, hrd₅, P₂₄.rd],
    by rw [Q.wr, hwr₅, P₂₄.wr], (Frame.stR_absR (by decide) F₅).trans (fr₆.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp), ?_⟩
  rw [Q.out, Proof.AesGcm.X86_64.blockAt_frame F₅ (d₀ 64 (by decide)),
    Proof.AesGcm.X86_64.blockAt_frame F₅ (d₀ 80 (by decide)), blocksAt_succ, pre, out₄, add_ofNat_assoc, hm₅,
    blockAt_two, GcmSiv.le64_le8, GcmSiv.le64_le8, GcmSiv.ofBytes_le8]

/-- The lengths of the padded strings, in blocks. -/
theorem elems_pad16_length_eq (m : Mem) (Q : Addr) (n : Nat) :
    (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n))).length = (n + 15) / 16 := by
  rw [elems_pad16_bytesAt, List.length_append, elemsAt_length]
  split <;> simp <;> omega_arith

/-- `polyval`'s test: whether the whole blocks number fewer than 62. -/
theorem polyCond_run {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (ha : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa
      [.mov .rax (.mem (at_ .r15 alenO)), .shift .shr .rax 4, .mov .rdx (.mem (at_ .r15 lenO)), .shift .shr .rdx 4,
        .alu .add .rax (.reg .rdx), .alu .cmp .rax (imm 62)] t = some t₁ ∧
      t₁.cf = some (decide (al / 16 + n / 16 < 62)) ∧ (∀ r, r ≠ .rax → r ≠ .rdx → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have rN := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sL := S.alen
  have sN := S.len
  refine ⟨_, by srun [h15, rL, rN, sL, sN], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, gpr_arithFlags, gpr_setFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq,
      Proof.AesGcm.X86_64.shr4 _ ha, Proof.AesGcm.X86_64.shr4 _ hn, ofNat_add_ofNat,
      toNat_ofNat_of_lt (show al / 16 + n / 16 < 2 ^ 64 by omega_arith)]
    rfl
  · intro r h₁ h₂; simp only [gpr_arithFlags, gpr_setFlags, gpr_setReg, h₁, h₂, ite_false]
  all_goals rfl

/-- `polyval`: POLYVAL of the padded additional data, the padded data and the
lengths block, and the tag input; with one call of `vg_ghash` when they fit. -/
theorem polyval_ok (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al)
    (hD : Buf K W SP t D n) (hN : Buf K W SP t N 12)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees wide) t (PolyPost K W SP N A D al n t) := by
  obtain ⟨t₁, run₁, hcf₁, hg₁, hm₁, hrd₁, hwr₁⟩ := polyCond_run E S hA.lt hD.lt
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  have hS₁ : Slots W R N A D al n t₁.mem := hm₁ ▸ S
  have P : ∀ t' : State, PolyPost K W SP N A D al n t₁ t' → PolyPost K W SP N A D al n t t' := fun t' P =>
    ⟨P.env, P.rd.trans hrd₁, P.wr.trans hwr₁, hm₁ ▸ P.frame, by rw [← hm₁]; exact P.out⟩
  refine WP.ite (!decide (al / 16 + n / 16 < 62)) (show t₁.cf.map (!·) = _ by rw [hcf₁]; rfl) (fun h => ?_) (fun h => ?_)
  · exact WP.mono (polyvalLong_ok v wide L E₁ hS₁ (hA.of_eq hrd₁ hwr₁) (hD.of_eq hrd₁ hwr₁) (hN.of_eq hrd₁ hwr₁)
      (by rw [hm₁]; exact hG) (by rw [hm₁]; exact hY)) P
  · have hsz : al / 16 + n / 16 ≤ 61 := by simp at h; omega_arith
    exact WP.mono (polyvalOne_ok v wide L E₁ hS₁ (hA.of_eq hrd₁ hwr₁) (hD.of_eq hrd₁ hwr₁) (hN.of_eq hrd₁ hwr₁)
      hsz (by rw [hm₁]; exact hG) (by rw [hm₁]; exact hY)) P

end VG.Proof.AesGcmSiv.X86_64
