module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Derive
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
public import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops

/-! ### `AesGcmSiv.X86_64.Polyval`, which this module and modules that import it used -/

section

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
        .alu .add .rax (.reg .rax), .bswap .rax,
        .mov .rdx (.mem (at_ .r15 alenO)), .alu .add .rdx (.reg .rdx),
        .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .bswap .rdx] : List Instr) ++
          store2 (at_ .r15 bO) .rax .rdx ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr)) t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 128) (bswap64 (BitVec.ofNat 64 (8 * n)))).writeW
        (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8) (bswap64 (BitVec.ofNat 64 (8 * al))) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 64 ∧ t₁.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 1512 ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 128 ∧
      t₁.gpr .rcx = BitVec.ofNat 64 1 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  obtain r₁ := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  obtain r₂ := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  obtain w₀ := E.perm.wW (show 128 + 16 ≤ 3816 by decide)
  refine ⟨_, by srun [store2, ghArgs, h15, r₁, r₂, w₀, hal, hn, XOp.exec, State.store128, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, zf_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne, punpck_movq, writeW128_app, gpr_setXmm, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq, add_ofNat_assoc, Proof.AesGcm.X86_64.times8_val, toNat_ofNat_of_lt hal', toNat_ofNat_of_lt hn']
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq]
  · intro r hr; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]
  all_goals rfl

theorem lens_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {al n : Nat}
    (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    WP isa (lens v.callees) t
      (AbsPost K W SP [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))] t) := by
  obtain ⟨t₁, run₁, hm₁, rdi₁, rsi₁, r8₁, rdx₁, rcx₁, hg₁, hrd₁, hwr₁⟩ := lensArgs_ok E hal hn hal' hn'
  obtain E₁ : Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  obtain fB : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (Nat.le_refl _) (by decide) (by have := L.ww; omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
  obtain dB : ∀ d, d + 16 ≤ 128 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)],
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
  obtain r₀ := E.perm.wR (show 80 + 8 ≤ 3816 by decide)
  obtain r₈ := E.perm.wR (show 88 + 8 ≤ 3816 by decide)
  obtain rn := E.perm.wR (show 208 + 8 ≤ 3816 by decide)
  obtain w₀ := E.perm.wW (show 96 + 16 ≤ 3816 by decide)
  obtain n₀ : InRegions (t.rd ++ t.wr) N 8 := by
    simpa using in_off (d := 0) (n := 8) hNb.rd (by decide) (by decide)
  obtain n₈ := in_off (d := 8) (n := 4) hNb.rd (by decide) (by decide)
  refine ⟨_, by srun [tagIn, store2, h15, r₀, r₈, rn, w₀, hN, n₀, n₈, XOp.exec, State.store128, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, zf_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne, punpck_movq, writeW128_app, gpr_setXmm, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq, add_ofNat_assoc]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (Nat.le_refl _) (by decide) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains W (by decide) (by decide) (by omega_arith))
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne, punpck_movq, writeW128_app, gpr_setXmm, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq]
    rw [Proof.Cmac.bytesAt_store2, ← Proof.Gcm.X86_64.blockAt_bswap, BitVec.add_zero, add_ofNat_assoc,
      GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le8_readW,
      ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words]
    rfl
  · intro r hr; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]
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
  obtain S₅ := S.absR L P.frame
  obtain ⟨t₆, run₆, fr₆, out₆, hg₆, hrd₆, hwr₆⟩ := tagIn_ok L P.env S₅.nonce (hN.of_eq P.rd P.wr)
  refine WP.of_runBlock ⟨t₆, run₆, P.env.of_saved hg₆ hrd₆ hwr₆, hrd₆.trans P.rd, hwr₆.trans P.wr,
    (P.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans
      (fr₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self ..), fun hpv => ?_⟩
  obtain hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
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
  obtain rA := E.perm.wR (show 216 + 8 ≤ 3816 by decide)
  obtain rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
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
  obtain E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  refine WP.mono (absorb_ok v wide L E₁ (hA.of_eq hrd₁ hwr₁) h12₁ hbp₁) fun t₂ P₂ => ?_
  obtain P₂' := P₂.of_eq hm₁ hrd₁ hwr₁
  rw [hm₁] at P₂'
  obtain S₂ := S.absR L P₂'.frame
  have h15₂ := P₂'.env.r15
  obtain rD := P₂'.env.perm.wR (show 232 + 8 ≤ 3816 by decide)
  obtain rN := P₂'.env.perm.wR (show 240 + 8 ≤ 3816 by decide)
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
  obtain E₃ : Env K W SP t₃ := P₂'.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  obtain hD₃ : Buf K W SP t₃ D n := hD.of_eq (hrd₃.trans P₂'.rd) (hwr₃.trans P₂'.wr)
  refine WP.mono (absorb_ok v wide L E₃ hD₃ h12₃ hbp₃) fun t₄ P₄ => ?_
  obtain P₄' := P₄.of_eq hm₃ hrd₃ hwr₃
  rw [hm₃, Proof.AesGcm.X86_64.bytesAt_frame P₂'.frame (buf_absR hD) (Nat.le_of_lt hD.lt)] at P₄'
  obtain P₂₄ := P₂'.trans L P₄'
  obtain S₄ := S.absR L P₂₄.frame
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
  obtain w₀ := E.perm.wW (show 128 + 16 ≤ 3816 by decide)
  -- The destination kept, the block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, hdi₁, hsi₁, hcx₁, hbx₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa ([.mov .rbx (.reg .rdi)] ++ zero16 bO ++ ptr .rdi .r15 bO ++ [.mov .rcx (.reg .rbp)]) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero2 t.mem (W + BitVec.ofNat 64 128) ∧ t₁.gpr .rdi = W + BitVec.ofNat 64 128 ∧
      t₁.gpr .rsi = P ∧ t₁.gpr .rcx = BitVec.ofNat 64 r ∧ t₁.gpr .rbx = W + BitVec.ofNat 64 (488 + 16 * s) ∧
      (∀ q, q ≠ .rax → q ≠ .rdi → q ≠ .rbx → q ≠ .rcx → t₁.gpr q = t.gpr q) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [zero16, h15, w₀, pxor_self, XOp.exec, State.store128, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, zf_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setXmm, writeW128_app, Proof.Cmac.zero2, add_ofNat_assoc]
      rfl
    · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, hsi]
    · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, hbp]
    · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, hdi]
    · intro q h₁ h₂ h₃ h₄; simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, h₁, h₂, h₃, h₄, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain lp : Proof.AesGcm.X86_64.LoopPre t₁ P (W + BitVec.ofNat 64 128) r :=
    ⟨hsi₁, hdi₁, hcx₁, hr1, by omega_arith, by rw [hrd₁, hwr₁]; exact hP.rd, by rw [hwr₁]; exact E.perm.wC (by omega_arith),
      hP.w.sub_right (Lay.wSub (by omega_arith))⟩
  refine WP.seq (WP.mono (Proof.AesGcm.X86_64.copyLoop_ok t₁ lp) fun t₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  -- The data is outside the zeroed block.
  obtain hd₁ : bytesAt t₁.mem P r = bytesAt t.mem P r := by
    rw [hm₁, Proof.Cmac.zero2]
    exact Proof.AesGcm.X86_64.bytesAt_frame
      (((Frame.refl [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)] _).writeW (List.mem_singleton_self _) _
        (Offset.contains W (Nat.le_refl _) (by decide) (by omega_arith))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide)))
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by omega_arith)
  obtain hb₂ : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    obtain hl := Proof.AesGcm.X86_64.length_bytesAt t.mem P r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega_arith), hl]
  obtain h15₂ : t₂.gpr .r15 = W := by
    rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide), h15]
  obtain hbx₂ : t₂.gpr .rbx = W + BitVec.ofNat 64 (488 + 16 * s) := by rw [hg₂ _ (by decide) (by decide), hbx₁]
  obtain r₀ := E.perm.wR (show 128 + 8 ≤ 3816 by decide)
  obtain r₈ := E.perm.wR (show 136 + 8 ≤ 3816 by decide)
  obtain v₀ := E.perm.wW (d := 488 + 16 * s) (n := 16) (by omega_arith)
  rw [← hrd₁, ← hwr₁, ← hrd₂, ← hwr₂] at r₀ r₈
  rw [← hwr₁, ← hwr₂] at v₀
  -- The block reversed at block `s`.
  obtain ⟨t₃, run₃, hm₃, hdi₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃ : State,
      runBlock isa (([.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax, .bswap .rdx] :
        List Instr) ++ store2 (at_ .rbx 0) .rdx .rax ++ ([.mov .rdi (.reg .rbx), .alu .add .rdi (imm 16)] : List Instr)) t₂ =
        some t₃ ∧
      t₃.mem = (t₂.mem.writeW (W + BitVec.ofNat 64 (488 + 16 * s))
          (bswap64 (t₂.mem.readW (W + BitVec.ofNat 64 136) 64))).writeW
        (W + BitVec.ofNat 64 (488 + 16 * s) + BitVec.ofNat 64 8) (bswap64 (t₂.mem.readW (W + BitVec.ofNat 64 128) 64)) ∧
      t₃.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * (s + 1)) ∧
      (∀ q ∈ [Reg.r13, .r15, .rsp], t₃.gpr q = t₂.gpr q) ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [store2, h15₂, hbx₂, r₀, r₈, v₀, XOp.exec, State.store128, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, zf_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne, punpck_movq, writeW128_app, gpr_setXmm, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
        reduceCtorEq, add_ofNat_assoc, hbx₂, BitVec.add_zero]
    · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, hbx₂, add_ofNat_assoc]
      rw [show 488 + 16 * s + 16 = 488 + 16 * (s + 1) by omega_arith]
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  obtain E₃ : Env K W SP t₃ := E.keep (fun q hq => by
      rw [hg₃ q hq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;>
        rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])
  -- What the pieces wrote.
  obtain mB : (⟨W + BitVec.ofNat 64 128, 16⟩ : Region) ∈ stR W s := by simp
  obtain mR : (⟨W + BitVec.ofNat 64 (488 + 16 * s), 1024 - 16 * s⟩ : Region) ∈ stR W s := by simp
  obtain f₁ : Frame (stR W s) t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero2]
    exact ((Frame.refl _ _).writeW mB _ (Offset.contains W (Nat.le_refl _) (by decide) (by omega_arith))).writeW mB _
      (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
  obtain f₂ : Frame (stR W s) t₁.mem t₂.mem := by
    rw [hm₂]
    exact (Proof.AesGcm.X86_64.writeBytes_frame' _ (Proof.AesGcm.X86_64.length_bytesAt _ _ _)).sub
      fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, mB, Region.sub_prefix (by omega_arith)⟩
  obtain f₃ : Frame (stR W s) t₂.mem t₃.mem := by
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
  obtain hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
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
  obtain E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  obtain hQ₁ := hQ.of_eq hrd₁ hwr₁
  obtain hdi₁ : t₁.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * s) := by
    rw [hg₁ _ (by decide) (by decide) (by decide), hdi]
  -- The whole blocks.
  obtain hmid : WP isa (.ite .e (.block []) (.seq (.block [.mov .r14 (.reg .rbx)]) (revSel wide))) t₁ fun t₂ =>
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
      obtain E₂ : Env K W SP t₂ := E₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
      obtain hQ₂ : Buf K W SP t₂ Q (16 * (n / 16)) := (hQ₁.take (by omega_arith)).of_eq hrd₂ hwr₂
      refine WP.mono (revSelAt_ok wide L E₂ (s := s) (c := n / 16) (by omega_arith) (by omega_arith) hQ₂ h14₂
        (by rw [hg₂ _ (by decide), hsi₁]) (by rw [hg₂ _ (by decide), hdi₁])) fun t₃ P => ?_
      obtain hl := elemsAt_length t.mem Q (n / 16)
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
  obtain P₃ : StPost K W SP s (elemsAt t.mem Q (n / 16)) t t₃ :=
    ⟨P₂.env.keep (fun r _ => hg₃ r) hrd₃ hwr₃, by rw [hrd₃, P₂.rd, hrd₁], by rw [hwr₃, P₂.wr, hwr₁],
      by rw [hm₃, ← hm₁]; exact P₂.frame, by rw [hm₃]; exact P₂.out, by rw [hg₃]; exact P₂.rdi, P₂.le⟩
  obtain hl := elemsAt_length t.mem Q (n / 16)
  rw [elems_pad16_bytesAt]
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil P₃
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    obtain hP : Buf K W SP t₃ (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hQ.slice (by omega_arith)).of_eq P₃.rd P₃.wr
    refine WP.mono (stageTail_ok L P₃.env (by omega_arith) (by omega_arith) hP (by rw [hg₃, rsi₂]) (by rw [hg₃, rbp₂])
      (by rw [hl]; omega_arith) P₃.rdi) fun t₄ T => ?_
    obtain e := Proof.AesGcm.X86_64.bytesAt_frame P₃.frame (p := Q + BitVec.ofNat 64 (16 * (n / 16)))
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
  obtain r₁ := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  obtain r₂ := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  obtain w₀ := E.perm.wW (d := 488 + 16 * k) (n := 16) (by omega_arith)
  refine ⟨_, by srun [lensAt, store2, ghArgs, h15, hdi, r₁, r₂, w₀, hal, hn, XOp.exec, State.store128, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, zf_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, mem_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne, punpck_movq, writeW128_app, gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags,
      ite_true, ite_false, reduceCtorEq, hdi, add_ofNat_assoc, BitVec.add_zero,
      Proof.AesGcm.X86_64.times8_val, toNat_ofNat_of_lt hal', toNat_ofNat_of_lt hn']
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15, hdi]
    rw [BitVec.add_comm W, BitVec.add_sub_cancel, Proof.AesGcm.X86_64.shr4 _ (by omega_arith),
      show 488 / 16 - 1 = 29 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith),
      show (488 + 16 * k) / 16 - 29 = k + 1 by omega_arith]
  · intro r hr; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_arithFlags, gpr_setReg, gpr_setFlags, gpr_setXmm, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]
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
  obtain rA := E.perm.wR (show 216 + 8 ≤ 3816 by decide)
  obtain rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
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
  obtain E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  obtain lA := elems_pad16_length t.mem A al
  obtain lD := elems_pad16_length t.mem D n
  refine WP.seq (WP.mono (stage_ok wide L E₁ (hA.of_eq hrd₁ hwr₁) h12₁ hbp₁ (by omega_arith) hdi₁) fun t₂ P₂ => ?_)
  rw [hm₁] at P₂
  obtain P₂' := P₂.of_eq hm₁ hrd₁ hwr₁
  obtain S₂ := S.absR L (Frame.stR_absR (by decide) P₂'.frame)
  -- The data, staged after it.
  have h15₂ := P₂'.env.r15
  obtain rD := P₂'.env.perm.wR (show 232 + 8 ≤ 3816 by decide)
  obtain rN := P₂'.env.perm.wR (show 240 + 8 ≤ 3816 by decide)
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
  obtain E₃ : Env K W SP t₃ := P₂'.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  obtain hD₃ : Buf K W SP t₃ D n := hD.of_eq (hrd₃.trans P₂'.rd) (hwr₃.trans P₂'.wr)
  refine WP.seq (WP.mono (stage_ok wide L E₃ hD₃ h12₃ hbp₃
    (s := 0 + (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al))).length) (by omega_arith)
    (by rw [hg₃ _ (by decide) (by decide)]; exact P₂'.rdi)) fun t₄ P₄ => ?_)
  obtain P₄' := P₄.of_eq hm₃ hrd₃ hwr₃
  rw [hm₃, Proof.AesGcm.X86_64.bytesAt_frame (Frame.stR_absR (SP := SP) (by decide) P₂'.frame) (buf_absR hD)
    (Nat.le_of_lt hD.lt)] at P₄'
  obtain P₂₄ := P₂'.trans L P₄'
  obtain ⟨k, hk⟩ : ∃ k, (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al)) ++
      Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem D n))).length = k := ⟨_, rfl⟩
  obtain hk64 : k < 64 := by rw [← hk, List.length_append]; omega_arith
  have out₄ := P₂₄.out
  have rdi₄ := P₂₄.rdi
  rw [hk] at out₄ rdi₄
  obtain S₄ := S.absR L (Frame.stR_absR (by decide) P₂₄.frame)
  -- The lengths block after them, and one call.
  obtain ⟨t₅, run₅, hm₅, rdi₅, rsi₅, r8₅, rdx₅, rcx₅, hg₅, hrd₅, hwr₅⟩ :=
    lensAt_ok P₂₄.env hk64 (by rw [rdi₄, Nat.zero_add]) S₄.alen S₄.len hA.lt hD.lt
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  obtain E₅ : Env K W SP t₅ := P₂₄.env.of_saved hg₅ hrd₅ hwr₅
  refine WP.seq (WP.mono (gh_call v.gh (gargs L E₅ (d := 488) (n := k + 1) (by decide) (by omega_arith) rdi₅ rsi₅ rdx₅
    rcx₅ r8₅)) fun t₆ Q => ?_)
  obtain mR : (⟨W + BitVec.ofNat 64 (488 + 16 * 0), 1024 - 16 * 0⟩ : Region) ∈ stR W 0 := by simp
  obtain fL : Frame [⟨W + BitVec.ofNat 64 (488 + 16 * k), 16⟩] t₄.mem t₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains W (Nat.le_refl _) (by omega_arith)
      (by omega_arith))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
  obtain F₅ : Frame (stR W 0) t.mem t₅.mem := P₂₄.frame.trans (fL.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, mR, Offset.sub W (by omega_arith) (by omega_arith)⟩)
  have fr₆ := Q.frame
  rw [E₅.rsp] at fr₆
  obtain d₀ : ∀ d, d + 16 ≤ 128 → ∀ r ∈ stR W 0, (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun d hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain pre : Spec.Gcm.blocksAt t₅.mem (W + BitVec.ofNat 64 488) k = Spec.Gcm.blocksAt t₄.mem (W + BitVec.ofNat 64 488) k :=
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
  obtain rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  obtain rN := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
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
  obtain E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  obtain hS₁ : Slots W R N A D al n t₁.mem := hm₁ ▸ S
  obtain P : ∀ t' : State, PolyPost K W SP N A D al n t₁ t' → PolyPost K W SP N A D al n t t' := fun t' P =>
    ⟨P.env, P.rd.trans hrd₁, P.wr.trans hwr₁, hm₁ ▸ P.frame, by rw [← hm₁]; exact P.out⟩
  refine WP.ite (!decide (al / 16 + n / 16 < 62)) (show t₁.cf.map (!·) = _ by rw [hcf₁]; rfl) (fun h => ?_) (fun h => ?_)
  · exact WP.mono (polyvalLong_ok v wide L E₁ hS₁ (hA.of_eq hrd₁ hwr₁) (hD.of_eq hrd₁ hwr₁) (hN.of_eq hrd₁ hwr₁)
      (by rw [hm₁]; exact hG) (by rw [hm₁]; exact hY)) P
  · have hsz : al / 16 + n / 16 ≤ 61 := by simp at h; omega_arith
    exact WP.mono (polyvalOne_ok v wide L E₁ hS₁ (hA.of_eq hrd₁ hwr₁) (hD.of_eq hrd₁ hwr₁) (hN.of_eq hrd₁ hwr₁)
      hsz (by rw [hm₁]; exact hG) (by rw [hm₁]; exact hY)) P

end VG.Proof.AesGcmSiv.X86_64

end

end

/-!
# AES-GCM-SIV on x86-64: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `cmp` stores at `W + 192`
whether the received tag at `W` equals the computed one at `W + 128`,
without a branch (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − ok`, leaving it if the tags are equal and zeroing it if not
(`mask_ok`). `recv` copies the received tag to `W` (`recv_ok`), and
`tagOut` the computed one from `W` to `tag` (`tagOut_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG.Proof.Aes.X86_64 (BlocksImpl)

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt in_off)

/-- `ok` from the XOR of the tags' words: 1 if both are equal, 0 if not. -/
theorem ok_val (a b c d : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 0#64 + BitVec.setWidth 32
      (BitVec.ofBool (decide ((a ^^^ b ||| c ^^^ d).toNat < (1#64).toNat)))) =
      if a = b ∧ c = d then 1#64 else 0#64 := by
  by_cases h : a = b ∧ c = d
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
    have : decide ((a ^^^ b ||| c ^^^ d).toNat < (1#64).toNat) = false := decide_eq_false fun hl => h (by
      obtain e : (a ^^^ b ||| c ^^^ d) = 0#64 := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ofNat]; rw [BitVec.toNat_ofNat] at hl; omega_arith)
      rw [BitVec.or_eq_zero_iff] at e
      exact ⟨BitVec.xor_eq_zero_iff.mp e.1, BitVec.xor_eq_zero_iff.mp e.2⟩)
    rw [this]
    decide

theorem le8_inj {a b : BitVec 64} (h : Proof.Cmac.le8 a = Proof.Cmac.le8 b) : a = b :=
  BitVec.eq_of_toNat_eq (by rw [← GcmSiv.leNat_le8, h, GcmSiv.leNat_le8])

/-- Two blocks in memory are equal when their words are. -/
theorem bytes16_eq (m : Mem) (p q : Addr) :
    bytesAt m p 16 = bytesAt m q 16 ↔
      m.readW p 64 = m.readW q 64 ∧ m.readW (p + BitVec.ofNat 64 8) 64 = m.readW (q + BitVec.ofNat 64 8) 64 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    exact ⟨le8_inj h₁, le8_inj h₂⟩
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]

theorem cmp_ok {K W SP : Addr} {t : State} (E : Env K W SP t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.mem = t.mem.writeW (W + BitVec.ofNat 64 192)
        (if bytesAt t.mem W 16 = bytesAt t.mem (W + BitVec.ofNat 64 128) 16 then 1#64 else 0#64) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  obtain r₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  obtain r₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  obtain u₀ := E.perm.wR (show 128 + 8 ≤ 3816 by decide)
  obtain u₈ := E.perm.wR (show 136 + 8 ≤ 3816 by decide)
  obtain wo := E.perm.wW (show 192 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [Impl.AesGcmSiv.X86_64.cmp, h15, r₀, r₈, u₀, u₈, wo], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, cf_arithFlags, cf_setReg,
      ite_true, ite_false, reduceCtorEq]
    obtain hb := bytes16_eq t.mem W (W + BitVec.ofNat 64 128)
    rw [add_ofNat_assoc] at hb
    simp only [ok_val, hb]
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- What `mask` leaves, from `t`, when `ok` is whether `c` holds. -/
structure MaskPost (K W SP : Addr) (D : Addr) (n : Nat) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [⟨D, n⟩] t.mem t'.mem
  data : bytesAt t'.mem D n = if c then bytesAt t.mem D n else Spec.GcmSiv.zeros n

theorem mask_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) {c : Prop} [Decidable c]
    (hok : t.mem.readW (W + BitVec.ofNat 64 192) 64 = if c then 1#64 else 0#64) :
    WP isa mask t (MaskPost K W SP D n c t) := by
  have h15 := E.r15
  have hn := hD.lt
  obtain rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  obtain rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  obtain rO := E.perm.wR (show 192 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  obtain hok' : t.mem.readW (W + BitVec.ofNat 64 192) 64 = if decide c then 1 else 0 := by
    rw [hok]; by_cases hc : c <;> simp [hc]
  obtain ⟨t₁, run₁, h12₁, hbp₁, h11₁, h10₁, rcx₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .mov .rcx (.reg .rbp),
        .shift .shr .rcx 4, .alu .test .rcx (.reg .rcx)] t = some t₁ ∧
      t₁.gpr .r12 = D ∧ t₁.gpr .rbp = BitVec.ofNat 64 n ∧
      t₁.gpr .r11 = 0 - (if decide c then 1 else 0) ∧ t₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      t₁.gpr .rcx = BitVec.ofNat 64 (n / 16) ∧ t₁.zf = some (decide (n / 16 = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rD, rL, rO], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sD]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hok']; rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL,
        Proof.AesGcm.X86_64.ofNat_shr4 hn]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL,
        Proof.AesGcm.X86_64.ofNat_shr4 hn, Proof.AesGcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega_arith)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP t₁ := E.keep hg₁ hrd₁ hwr₁
  refine WP.mono (Proof.AesGcm.X86_64.maskTail_wp hn (by rw [hrd₁, hwr₁]; exact hD.rd) (by rw [hwr₁]; exact hDw)
    h12₁ h11₁ hbp₁ h10₁ rcx₁ hzf₁) fun t₂ M => ?_
  obtain hl : (Proof.AesGcm.X86_64.masked t₁.mem D (decide c) n).length = n :=
    Proof.AesGcm.X86_64.length_masked _ _ _ _
  refine ⟨E₁.keep (fun r hr => M.keep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    M.rd M.wr, M.rd.trans hrd₁, M.wr.trans hwr₁, by rw [M.mem, ← hm₁]; exact Proof.AesGcm.X86_64.writeBytes_frame' _ hl,
    ?_⟩
  obtain e := Proof.AesGcm.X86_64.bytesAt_writeBytes_self t₁.mem D (Proof.AesGcm.X86_64.masked t₁.mem D (decide c) n)
    (by omega_arith)
  rw [hl] at e
  rw [M.mem, e, hm₁]
  by_cases hc : c <;> simp [Proof.AesGcm.X86_64.masked, hc, Spec.GcmSiv.zeros]

/-! ## The tag's copies -/

/-- A 16-byte block copied from `S` to `T`, by words. -/
theorem bytesAt_copy2 (m : Mem) (S T : Addr) (hs : Mem.Sep (S + BitVec.ofNat 64 8) (64 / 8) T (64 / 8)) :
    bytesAt ((m.writeW T (m.readW S 64)).writeW (T + BitVec.ofNat 64 8)
      ((m.writeW T (m.readW S 64)).readW (S + BitVec.ofNat 64 8) 64)) T 16 = bytesAt m S 16 := by
  rw [Mem.readW_writeW_sep hs (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

/-- `recv`: the received tag, at `T`, whose address is at `SP + 16`, copied
to `W`. -/
theorem recv_ok {K W SP T : Addr} {s : State} (E : Env K W SP s)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T) (hTa : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hB : Buf K W SP s T 16) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem W 16 = bytesAt s.mem T 16 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  obtain t₀ : InRegions (s.rd ++ s.wr) T 8 := by simpa using in_off (d := 0) (n := 8) hB.rd (by decide) (by decide)
  obtain t₈ := in_off (d := 8) (n := 8) hB.rd (by decide) (by decide)
  obtain w₀ : InRegions s.wr W 8 := by simpa using E.perm.wW (show 0 + 8 ≤ 3816 by decide)
  obtain w₈ := E.perm.wW (show 8 + 8 ≤ 3816 by decide)
  obtain hs : Mem.Sep (T + BitVec.ofNat 64 8) (64 / 8) W (64 / 8) :=
    hB.w.sep (Offset.contains_base T (d := 8) (n := 8) (k := 16) (by decide) (by decide))
      (by simpa using Offset.contains_base W (d := 0) (n := 8) (k := 3816) (by decide) (by decide))
  refine ⟨_, by srun [recv, h15, hsp, hT, hTa, t₀, t₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg]; exact bytesAt_copy2 _ _ _ hs
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- `tagOut`: the tag at `W` copied to `T`, whose address is at `SP + 16`. -/
theorem tagOut_ok {K W SP T : Addr} {s : State} (E : Env K W SP s)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T) (hTa : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hTw : Covers [⟨T, 16⟩] s.wr) (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 3816⟩) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem T 16 = bytesAt s.mem W 16 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  obtain t₀ : InRegions s.wr T 8 := by simpa using in_off (d := 0) (n := 8) hTw (by decide) (by decide)
  obtain t₈ := in_off (d := 8) (n := 8) hTw (by decide) (by decide)
  obtain w₀ : InRegions (s.rd ++ s.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  obtain w₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  obtain hs : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
    hTW.symm.sep (Offset.contains_base W (d := 8) (n := 8) (k := 3816) (by decide) (by decide))
      (by simpa using Offset.contains_base T (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  refine ⟨_, by srun [tagOut, h15, hsp, hT, hTa, t₀, t₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg]; exact bytesAt_copy2 _ _ _ hs
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

end VG.Proof.AesGcmSiv.X86_64

/-!
## The keys, and what the pieces write

Untrusted: everything here is checked by Lean. `keys` derives the message
keys, expands the encryption key and sets up GHASH's key and accumulator
(`keys_ok`). Every piece but counter mode and the mask writes only parts of
`W` and the stack below `SP` (`mutW`), which miss the buffers, the key
schedule and what the entry keeps in `W`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- What the pieces before counter mode write. -/
abbrev mutW (W SP : Addr) : List Region := [wA W, wO W, wC W, below SP 8]

theorem mutW_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ mutW W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' :=
  fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp, fun _ h => h⟩

/-- `⟨W + d, k⟩` within `[0, 144)` of `W`. -/
theorem sub_wA {W SP : Addr} {d k : Nat} (h : d + k ≤ 144) :
    ∃ r' ∈ mutW W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨wA W, by mem_lit, Offset.sub_base W h⟩

/-- `⟨W + d, k⟩` within `[248, 3816)` of `W`. -/
theorem sub_wC {W SP : Addr} {d k : Nat} (h₁ : 248 ≤ d) (h₂ : d + k ≤ 3816) :
    ∃ r' ∈ mutW W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨wC W, by mem_lit, Offset.sub W h₁ (by omega_arith)⟩

theorem sub_stk {W SP : Addr} : ∃ r' ∈ mutW W SP, Region.Sub (below SP 8) r' := ⟨_, by mem_lit, fun _ h => h⟩

theorem buf_mutW {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) {m m' : Mem}
    (hf : Frame (mutW W SP) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega_arith)

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule and the working spaces. -/
abbrev keyR (W SP : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 128⟩, wC W, below SP 8]

theorem keyR_mutW (W SP : Addr) : ∀ r ∈ keyR W SP, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact ⟨_, by mem_lit, fun _ h => h⟩
  · exact sub_stk

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (K W SP : Addr) (R : Nat) (N : Addr) (σ t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame (keyR W SP) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).1 =
    bytesAt t.mem (W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).2
  hkey : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
    GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keys_ok (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (E : Env K W SP σ) (S : Slots W R N A D al n σ.mem)
    (hN : Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    WP isa (keys v.callees ⟨eb.enc.name, eb.enc.code⟩) σ (KeysPost K W SP R N σ) := by
  refine WP.seq (WP.mono (derive_ok eb L hR E S hN hDW) fun t₂ I => ?_)
  obtain f₂ : Frame (keyR W SP) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by mem_lit, fun _ h => h⟩
  obtain S₂ := slots_mut L hDW ((f₂.sub (keyR_mutW W SP)).sub (mutW_mut W SP D n)) S
  refine WP.seq (WP.mono (expand_ok v L hR I.env S₂) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hG, hY, f₄, hg₄, hrd₄, hwr₄⟩ := hkey_ok X.env
  refine WP.of_runBlock ⟨t₄, run₄, ?_⟩
  have fX := X.frame
  obtain f₃ : Frame (keyR W SP) t₂.mem t₃.mem := fX.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by mem_lit, fun _ h => h⟩
  obtain dA : ∀ q ∈ [(⟨W + BitVec.ofNat 64 248, 240⟩ : Region), ⟨W + BitVec.ofNat 64 1768, 512⟩, below SP 8],
      (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  obtain d64 : ∀ q ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region)], (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain hA₄ : bytesAt t₄.mem (W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (W + BitVec.ofNat 64 16) 16 := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₄ d64 (by decide), Proof.AesGcm.X86_64.bytesAt_frame fX dA (by decide)]
  obtain hK := I.keys hR
  refine ⟨X.env.keep (fun r hr => ?_) hrd₄ hwr₄, by rw [hrd₄, X.rd, I.rd], by rw [hwr₄, X.wr, I.wr],
    (f₂.trans f₃).trans (f₄.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by mem_lit, Offset.sub W (by decide) (by decide)⟩),
    ?_, ?_,
    by rw [hG, hA₄, ← Proof.AesGcm.X86_64.bytesAt_frame fX dA (by decide)], hY⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by simp)
  · rw [hK, hA₄]
  · rw [ctxCiph_frame f₄ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by rcases hR with h | h <;> subst h <;> decide), X.ciph, hK]

/-- What `keysS` leaves, from `σ`: as `keys`, with the encryption key itself
at `W + 32` in place of its schedule. -/
structure KeysSPost (K W SP : Addr) (R : Nat) (N : Addr) (σ t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame (keyR W SP) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).1 =
    bytesAt t.mem (W + BitVec.ofNat 64 16) 16
  ekey : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).2 =
    bytesAt t.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R)
  hkey : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
    GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keysS_ok (eb : Proof.Aes.X86_64.BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat} {σ : State} (E : Env K W SP σ)
    (S : Slots W R N A D al n σ.mem) (hN : Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    WP isa (keysS ⟨eb.enc.name, eb.enc.code⟩) σ (KeysSPost K W SP R N σ) := by
  refine WP.seq (WP.mono (derive_ok eb L hR E S hN hDW) fun t₂ I => ?_)
  obtain f₂ : Frame (keyR W SP) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by mem_lit, fun _ h => h⟩
  obtain ⟨t₄, run₄, hG, hY, f₄, hg₄, hrd₄, hwr₄⟩ := hkey_ok I.env
  refine WP.of_runBlock ⟨t₄, run₄, ?_⟩
  obtain hkl : Spec.GcmSiv.keyLen R ≤ 32 := by unfold Spec.GcmSiv.keyLen; omega_arith
  obtain d64 : ∀ {a k : Nat}, a + k ≤ 64 → ∀ q ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨W + BitVec.ofNat 64 a, k⟩ : Region).Disjoint q := fun h q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl h) (by omega_arith) (by decide)
  obtain hA₄ : bytesAt t₄.mem (W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86_64.bytesAt_frame f₄ (d64 (by decide)) (by decide)
  obtain hE₄ : bytesAt t₄.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R) =
      bytesAt t₂.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R) :=
    Proof.AesGcm.X86_64.bytesAt_frame f₄ (d64 (by omega_arith)) (by omega_arith)
  obtain hK := I.keys hR
  refine ⟨I.env.keep (fun r hr => ?_) hrd₄ hwr₄, by rw [hrd₄, I.rd], by rw [hwr₄, I.wr],
    f₂.trans (f₄.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by mem_lit, Offset.sub W (by decide) (by decide)⟩),
    by rw [hK, hA₄], by rw [hK, hE₄], by rw [hG, hA₄], hY⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by simp)

end VG.Proof.AesGcmSiv.X86_64

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the
copy of the tag to `tag` and the restore compute `encryptWith` (RFC 8452
§4) of the arguments (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- The return address misses everything the code writes. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega_arith)
  · exact hD

theorem cryR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ cryR W SP D n, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨wA W, by mem_lit, Offset.sub_base W (by decide)⟩
  · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨wC W, by mem_lit, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by mem_lit, fun _ h => h⟩
  · exact ⟨_, by mem_lit, fun _ h => h⟩

theorem polyR_mutW (W SP : Addr) : ∀ r ∈ polyR W SP, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact sub_wA (by decide)
  · exact sub_wA (by decide)
  · exact sub_wC (by decide) (by decide)
  · exact sub_wC (by decide) (by decide)
  · exact sub_stk

theorem tagR_mutW (W SP : Addr) {o : Nat} (ho : o + 16 ≤ 144) : ∀ r ∈ tagR W SP o, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact sub_wA ho
  · exact sub_wC (by decide) (by decide)
  · exact sub_stk

theorem key_polyR {K W SP : Addr} (L : Lay K W SP) :
    ∀ r ∈ polyR W SP, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem key_tagR {K W SP : Addr} (L : Lay K W SP) {o : Nat} (ho : o + 16 ≤ 248) :
    ∀ r ∈ tagR W SP o, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr ho) (by decide) (by omega_arith)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- `vg_aes_gcm_siv_seal`, for its arguments. -/
theorem seal_wp' (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTw : Covers [⟨T, 16⟩] s.wr)
    (hrT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s fun s' => gprPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T 16) := by
  have L := Ar.lay
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  obtain bN₁ := Ar.nonce.of_eq rd₁ wr₁
  obtain bA₁ := Ar.aad.of_eq rd₁ wr₁
  obtain bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys but the expansion.
  refine WP.seq (WP.mono (keysS_ok eb L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  obtain fK : Frame (mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (keyR_mutW W SP)
  obtain S₂ := slots_mut L Ar.data.w (fK.sub (mutW_mut W SP D n)) S₁
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v wide L Ky.env S₂ (bA₁.of_eq Ky.rd Ky.wr) (bD₁.of_eq Ky.rd Ky.wr)
    (bN₁.of_eq Ky.rd Ky.wr) Ky.hkey Ky.acc) fun s₃ Po => ?_)
  obtain f₃ : Frame (mutW W SP) s₂.mem s₃.mem := Po.frame.sub (polyR_mutW W SP)
  obtain S₃ := slots_mut L Ar.data.w (f₃.sub (mutW_mut W SP D n)) S₂
  -- The expansion of the encryption key.
  refine WP.seq (WP.mono (expand_ok v L Ar.rounds Po.env S₃) fun s₃' X => ?_)
  obtain f₃' : Frame (mutW W SP) s₃.mem s₃'.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_wC (by decide) (by decide)
    · exact sub_wC (by decide) (by decide)
    · exact sub_stk
  obtain S₃' := slots_mut L Ar.data.w (f₃'.sub (mutW_mut W SP D n)) S₃
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Ar.rounds X.env S₃' (o := 0) (by decide)) fun s₄ Tg => ?_)
  obtain f₄ : Frame (mutW W SP) s₃'.mem s₄.mem := Tg.frame.sub (tagR_mutW W SP (by decide))
  obtain S₄ := slots_mut L Ar.data.w (f₄.sub (mutW_mut W SP D n)) S₃'
  obtain f₁₄ : Frame (mutW W SP) s₁.mem s₄.mem := ((fK.trans f₃).trans f₃').trans f₄
  -- Counter mode.
  obtain bD₄ : Buf K W SP s₄ D n := bD₁.of_eq (by rw [Tg.rd, X.rd, Po.rd, Ky.rd]) (by rw [Tg.wr, X.wr, Po.wr, Ky.wr])
  refine WP.seq (WP.mono (crypt_ok v eb wide L Ar.rounds Tg.env S₄ bD₄
    (by rw [Tg.wr, X.wr, Po.wr, Ky.wr, wr₁]; exact Ar.dw)) fun s₅ Cr => ?_)
  obtain f₁₅ : Frame (mutR W SP D n) s₁.mem s₅.mem := (f₁₄.sub (mutW_mut W SP D n)).trans (Cr.frame.sub (cryR_mut W SP D n))
  obtain fall : Frame (entryR W :: mutR W SP D n) s.mem s₅.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₅.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  obtain r₅ : s₅.rd = s.rd := by rw [Cr.rd, Tg.rd, X.rd, Po.rd, Ky.rd, rd₁]
  obtain w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, X.wr, Po.wr, Ky.wr, wr₁]
  -- The copy of the tag, and `restore`.
  obtain hTa : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 16) 8 := by
    obtain h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [r₅, w₅]; exact h
  obtain ⟨s₆, run₆, fT, hT₆, hg₆, rd₆, wr₆⟩ := tagOut_ok Cr.env (by rw [argT_kept fall Ar.argsW Ar.argsD, hT]) hTa
    (by rw [w₅]; exact hTw) Tb.w
  obtain E₆ : Env K W SP s₆ := Cr.env.of_saved hg₆ rd₆ wr₆
  obtain dT : ∀ q ∈ [(⟨T, 16⟩ : Region)], ∀ p ∈ saved, (⟨W + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint q := by
    intro q hq p hp
    simp only [List.mem_singleton] at hq; subst hq
    obtain hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (Tb.w.sub_right (Lay.wSub (by omega_arith))).symm
  obtain sv₆ : Saved s₆.mem W s.gpr := fun p hp => by
    rw [← saved_mut L Ar.data.w f₁₅ sv₁ p hp]
    exact fT.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun q hq => dT q hq p hp) (by decide)
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := restore_ok E₆ sv₆
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_append, run₆]; exact run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, 144) (by decide)
    · exact hg₇ (.rbp, 152) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, 160) (by decide)
    · exact hg₇ (.r13, 168) (by decide)
    · exact hg₇ (.r14, 176) (by decide)
    · exact hg₇ (.r15, 184) (by decide)
  · rw [hm₇, hsp, fT.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hrT) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₃'.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame Tg.frame (key_tagR L (by decide)) hRb
    obtain hkl : Spec.GcmSiv.keyLen R ≤ 32 := by unfold Spec.GcmSiv.keyLen; omega_arith
    obtain ek₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R) =
        bytesAt s₂.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R) :=
      Proof.AesGcm.X86_64.bytesAt_frame Po.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact (L.stk_w' (by omega_arith)).symm) (by omega_arith)
    obtain ti₃ : bytesAt s₃'.mem (W + BitVec.ofNat 64 96) 16 = bytesAt s₃.mem (W + BitVec.ofNat 64 96) 16 :=
      Proof.AesGcm.X86_64.bytesAt_frame X.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm) (by decide)
    obtain n₂ : bytesAt s₂.mem N 12 = bytesAt s.mem N 12 := by rw [buf_mutW bN₁ fK, hent Ar.nonce]
    obtain a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by rw [buf_mutW bA₁ fK, hent Ar.aad]
    obtain d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ fK, hent Ar.data]
    obtain d₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ f₁₄, hent Ar.data]
    obtain t₅ : bytesAt s₅.mem W 16 = bytesAt s₄.mem W 16 := Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide)
    obtain d₇ : bytesAt s₇.mem D n = bytesAt s₅.mem D n := by
      rw [hm₇]; exact Proof.AesGcm.X86_64.bytesAt_frame fT (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact Tb.d.symm) (by have := Ar.data.lt; omega_arith)
    have tg := Tg.out
    rw [BitVec.add_zero] at tg
    have au := Ky.auth
    have ek := Ky.ekey
    rw [hK₁, hent Ar.nonce] at au ek
    have ci := X.ciph
    rw [ek₃, ← ek] at ci
    obtain po := Po.out hpv
    rw [n₂, a₂, d₂] at po
    rw [d₇, hm₇, hT₆, Cr.data, t₅, d₄, key₄, ci, tg, ci, ti₃, po, ← au]
    unfold Spec.GcmSiv.encryptWith
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
    obtain ⟨a, e⟩ := dk
    rfl

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} (h : sealPre s) :
    WP isa («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTw, hrT⟩ := args_of_seal h
  exact seal_wp' v eb wide hpv Ar Tb hTw hrT rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 128`, the comparison, the mask
and the restore compute `decryptWith` (RFC 8452 §5) of the arguments
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

theorem w0_keyR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ keyR W SP, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 16) (k := 128) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 248) (k := 3568) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_cryR {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    ∀ r ∈ cryR W SP D n, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · exact (hD.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_polyR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ polyR W SP, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 80) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 128) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1512) (k := 256) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_tagR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ tagR W SP 128, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 112) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 128) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

/-- `vg_aes_gcm_siv_open`, for its arguments. -/
theorem open_wp' (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s fun s' => gprPreserved s s' ∧
      openPost (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16)) s' D n := by
  have L := Ar.lay
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₀, run₀, E₀, S₀, sv₀, f₀, rd₀, wr₀⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  obtain f₀' : Frame (entryR W :: mutR W SP D n) s.mem s₀.mem :=
    f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  -- The received tag, copied to `W`.
  obtain hTa : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 16) 8 := by
    obtain h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₀, wr₀]; exact h
  obtain ⟨s₁, run₁, fR, hR₁, hgR, rdR, wrR⟩ := recv_ok E₀ (by rw [argT_kept f₀' Ar.argsW Ar.argsD, hT]) hTa
    ((Tb.buf (s := s) hTr).of_eq rd₀ wr₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP s₁ := E₀.of_saved hgR rdR wrR
  obtain fR' : Frame (mutR W SP D n) s₀.mem s₁.mem := fR.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨wA W, by mem_lit, Region.sub_prefix (by decide)⟩
  obtain S₁ := slots_mut L Ar.data.w fR' S₀
  obtain rd₁ : s₁.rd = s.rd := by rw [rdR, rd₀]
  obtain wr₁ : s₁.wr = s.wr := by rw [wrR, wr₀]
  obtain f₁ : Frame (entryR W :: mutR W SP D n) s.mem s₁.mem :=
    f₀'.trans (fR'.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  obtain f₀₁ : Frame [entryR W, ⟨W, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨W, 16⟩, by mem_lit, fun _ h => h⟩)
  obtain hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Region.sub_prefix (by decide)))
      (by have := hP.lt; omega_arith)
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Region.sub_prefix (by decide))) hRb
  obtain hT₁ : bytesAt s₁.mem W 16 = bytesAt s.mem T 16 := by
    rw [hR₁]; exact tag_kept Tb f₀'
  obtain bN₁ := Ar.nonce.of_eq rd₁ wr₁
  obtain bA₁ := Ar.aad.of_eq rd₁ wr₁
  obtain bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v eb L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  obtain fK : Frame (mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (keyR_mutW W SP)
  obtain S₂ := slots_mut L Ar.data.w (fK.sub (mutW_mut W SP D n)) S₁
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok v eb wide L Ar.rounds Ky.env S₂ (bD₁.of_eq Ky.rd Ky.wr)
    (by rw [Ky.wr, wr₁]; exact Ar.dw)) fun s₃ Cr => ?_)
  obtain S₃ := S₂.of_frame Cr.frame (slots_cryR L Ar.data)
  obtain dK : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 96 → ∀ q ∈ cryR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (L.stk_w' (by omega_arith)).symm
      · exact (Ar.data.w.sub_right (Lay.wSub (by omega_arith))).symm
  obtain hA₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (dK (by decide) (by decide)) (by decide)
  obtain hG₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), Ky.hkey, hA₃]
  obtain hY₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), Ky.acc]
  obtain nA : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩ →
      bytesAt s₃.mem P len = bytesAt s.mem P len := fun hP hPD => by
    rw [Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.stk.symm
        · exact hPD) (by have := hP.lt; omega_arith),
      buf_mutW (hP.of_eq rd₁ wr₁) fK, hent hP]
  -- POLYVAL of the plaintext and the tag input.
  obtain r₃ : s₃.rd = s₁.rd := by rw [Cr.rd, Ky.rd]
  obtain w₃ : s₃.wr = s₁.wr := by rw [Cr.wr, Ky.wr]
  refine WP.seq (WP.mono (polyval_ok v wide L Cr.env S₃ (bA₁.of_eq r₃ w₃) (bD₁.of_eq r₃ w₃) (bN₁.of_eq r₃ w₃) hG₃ hY₃)
    fun s₄ Po => ?_)
  obtain S₄ := slots_mut L Ar.data.w ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n)) S₃
  -- Its tag at `W + 128`.
  refine WP.seq (WP.mono (tag_ok v L Ar.rounds Po.env S₄ (o := 128) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, hm₆, hg₆, hrd₆, hwr₆⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env K W SP s₆ := Tg.env.of_saved hg₆ hrd₆ hwr₆
  obtain fO : Frame [wO W] s₅.mem s₆.mem := by
    rw [hm₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain S₅ := slots_mut L Ar.data.w ((Tg.frame.sub (tagR_mutW W SP (by decide))).sub (mutW_mut W SP D n)) S₄
  obtain S₆ := S₅.of_frame fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
  obtain r₅ : s₅.rd = s₁.rd := by rw [Tg.rd, Po.rd, r₃]
  obtain w₅ : s₅.wr = s₁.wr := by rw [Tg.wr, Po.wr, w₃]
  obtain hok : s₆.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16 = bytesAt s₅.mem W 16 then 1#64 else 0#64 := by
    rw [hm₆, Mem.readW_writeW_self64]
    by_cases hc : bytesAt s₅.mem W 16 = bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Ne.symm hc, ↓reduceIte]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ S₆ (bD₁.of_eq (by rw [hrd₆, r₅]) (by rw [hwr₆, w₅]))
    (by rw [hwr₆, w₅, wr₁]; exact Ar.dw) hok) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  have h15₇ := Mk.env.r15
  obtain rO := Mk.env.perm.wR (show 192 + 8 ≤ 3816 by decide)
  obtain ⟨s₈, run₈, hax₈, hm₈, hg₈, hrd₈, hwr₈⟩ : ∃ s₈ : State, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₇ =
      some s₈ ∧ s₈.gpr .rax = s₇.mem.readW (W + BitVec.ofNat 64 192) 64 ∧ s₈.mem = s₇.mem ∧
      (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by srun [h15₇, rO], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  obtain E₈ : Env K W SP s₈ := Mk.env.keep (fun r hr => hg₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₈ hwr₈
  obtain fall : Frame (mutR W SP D n) s₁.mem s₇.mem :=
    ((((fK.sub (mutW_mut W SP D n)).trans (Cr.frame.sub (cryR_mut W SP D n))).trans
      ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n))).trans
      (((Tg.frame.sub (tagR_mutW W SP (by decide))).sub (mutW_mut W SP D n)).trans
        (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩))).trans
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ :=
    restore_ok E₈ (by rw [hm₈]; exact saved_mut L Ar.data.w (fR'.trans fall) sv₀)
  refine WP.of_runBlock ⟨s₉, by rw [runBlock_append, run₈]; exact run₉, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, 144) (by decide)
    · exact hg₉ (.rbp, 152) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, 160) (by decide)
    · exact hg₉ (.r13, 168) (by decide)
    · exact hg₉ (.r14, 176) (by decide)
    · exact hg₉ (.r15, 184) (by decide)
  · have fall' : Frame (entryR W :: mutR W SP D n) s.mem s₇.mem :=
      f₁.trans (fall.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₉, hm₈, hsp]
    exact fall'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    obtain tag₂ : bytesAt s₂.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Ky.frame (w0_keyR L) (by decide), hT₁]
    obtain tag₅ : bytesAt s₅.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Tg.frame (w0_tagR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Po.frame (w0_polyR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (w0_cryR L Ar.data.w) (by decide), tag₂]
    obtain ct₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ fK, hent Ar.data]
    obtain ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := by
      rw [ctxCiph_frame Po.frame (key_polyR L) hRb, ctxCiph_frame Cr.frame (key_cryR L Ar.data) hRb]
    have pt₃ := Cr.data
    rw [tag₂, ct₂, ci] at pt₃
    obtain po := Po.out hpv
    rw [hA₃, ← au, nA Ar.nonce Ar.nd, nA Ar.aad Ar.ad, pt₃] at po
    have tg := Tg.out
    rw [ci₄, ci, po] at tg
    obtain dD : ∀ q ∈ tagR W SP 128, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    obtain dP : ∀ q ∈ polyR W SP, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    obtain d₆ : bytesAt s₆.mem D n = bytesAt s₃.mem D n := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame fO (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by have := Ar.data.lt; omega_arith),
        Proof.AesGcm.X86_64.bytesAt_frame Tg.frame dD (by have := Ar.data.lt; omega_arith),
        Proof.AesGcm.X86_64.bytesAt_frame Po.frame dP (by have := Ar.data.lt; omega_arith)]
    obtain ax : s₉.gpr .rax = s₆.mem.readW (W + BitVec.ofNat 64 192) 64 := by
      rw [hax₉, hax₈, Mk.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm)
        (by decide)]
    have md := Mk.data
    obtain ax' := ax.trans hok
    rw [tg, tag₅] at ax'
    rw [tg, tag₅, d₆, pt₃] at md
    obtain hdec : Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16) =
        let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        if Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
            (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
            (bytesAt s.mem A al)) = bytesAt s.mem T 16 then
          some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
        else none := by
      unfold Spec.GcmSiv.decryptWith
      rw [← Prod.eta (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R)
        (bytesAt s.mem N 12))]
    simp only at hdec
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
      at md ax' hdec
    rw [hdec]
    refine Or.elim (Classical.em (Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
      (bytesAt s.mem A al)) = bytesAt s.mem T 16)) (fun hc => ?_) (fun hc => ?_)
    · refine openPost_some (by rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]
    · refine openPost_none (by rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} (h : openPre s) :
    WP isa («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := args_of_open h
  exact open_wp' v eb wide hpv Ar Tb hTr rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64
