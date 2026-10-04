import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb

/-!
# AES-GCM-SIV on x86-64: POLYVAL and the tag input (`polyval`)

Untrusted: everything here is checked by Lean. `lens` absorbs the lengths
block (`lens_ok`), `tagIn` turns POLYVAL's result into the tag input
(`tagIn_ok`), and `polyval` absorbs the padded additional data, the padded
data and the lengths block from the zero accumulator, leaving the tag input
of RFC 8452 §4 at `W + 96` (`polyval_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall GhPost gh_call ofNat_add_ofNat in_off toNat_ofNat_of_lt)

theorem lens_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {al n : Nat}
    (hal : t.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 312) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    WP isa (lens v.callees) t
      (AbsPost K W SP [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))] t) := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 312 + 8 ≤ 4096 by decide)
  have r₂ := E.perm.wR (show 296 + 8 ≤ 4096 by decide)
  have w₀ := E.perm.wW (show 128 + 8 ≤ 4096 by decide)
  have w₈ := E.perm.wW (show 136 + 8 ≤ 4096 by decide)
  obtain ⟨t₁, run₁, hm₁, rdi₁, rsi₁, r8₁, rdx₁, rcx₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa (([.mov .rax (.mem (at_ .r15 lenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 bO) .rax,
        .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] :
          List Instr) ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr)) t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 128) (bswap64 (BitVec.ofNat 64 (8 * n)))).writeW
        (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8) (bswap64 (BitVec.ofNat 64 (8 * al))) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 64 ∧ t₁.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 1792 ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 128 ∧
      t₁.gpr .rcx = BitVec.ofNat 64 1 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [ghArgs, h15, r₁, r₂, w₀, w₈, hal, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, add_ofNat_assoc, Proof.AesGcm.X86_64.times8_val,
        toNat_ofNat_of_lt hal', toNat_ofNat_of_lt hn']
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  have fB : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (Nat.le_refl _) (by decide) (by have := L.ww; omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
  have dB : ∀ d, d + 16 ≤ 128 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl hd) (by omega) (by decide)
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
    (hN : t.mem.readW (W + BitVec.ofNat 64 280) 64 = N) (hNb : Buf K W SP t N 12) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t.mem t'.mem ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 96) 16 =
        GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80))) (bytesAt t.mem N 12) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have hw := L.ww
  have r₀ := E.perm.wR (show 80 + 8 ≤ 4096 by decide)
  have r₈ := E.perm.wR (show 88 + 8 ≤ 4096 by decide)
  have rn := E.perm.wR (show 280 + 8 ≤ 4096 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 4096 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 4096 by decide)
  have n₀ : InRegions (t.rd ++ t.wr) N 8 := by
    simpa using in_off (d := 0) (n := 8) hNb.rd (by decide) (by decide)
  have n₈ := in_off (d := 8) (n := 4) hNb.rd (by decide) (by decide)
  refine ⟨_, by srun [tagIn, h15, r₀, r₈, rn, w₀, w₈, hN, n₀, n₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (Nat.le_refl _) (by decide) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains W (by decide) (by decide) (by omega))
  · simp only [mem_setReg, mem_arithFlags]
    rw [show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
      Proof.Cmac.bytesAt_store2, ← Proof.Gcm.X86_64.blockAt_bswap, BitVec.add_zero, add_ofNat_assoc,
      GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le8_readW,
      ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words]
    rfl
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- The slots, after code that writes only what absorbing writes. -/
theorem Slots.absR {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {m m' : Mem}
    (S : Slots W R N A D al n m) (hf : Frame (absR W SP) m m') : Slots W R N A D al n m' := by
  have k (d : Nat) (hd : 272 ≤ d ∧ d + 8 ≤ 320) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    hf.readW (Region.contains_self _ _) (w_absR L (.inr (.inr ⟨by omega, by omega⟩))) (by decide)
  exact ⟨by rw [k 272 (by decide)]; exact S.rounds, by rw [k 280 (by decide)]; exact S.nonce,
    by rw [k 288 (by decide)]; exact S.aad, by rw [k 296 (by decide)]; exact S.alen,
    by rw [k 304 (by decide)]; exact S.data, by rw [k 312 (by decide)]; exact S.len⟩

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W SP : Addr) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: absR W SP

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (K W SP : Addr) (N A D : Addr) (al n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (polyR W SP) t.mem t'.mem
  out : bytesAt t'.mem (W + BitVec.ofNat 64 96) 16 =
    Spec.GcmSiv.tagInput (bytesAt t.mem (W + BitVec.ofNat 64 16) 16) (bytesAt t.mem N 12) (bytesAt t.mem D n)
      (bytesAt t.mem A al)

theorem polyval_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat}
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n)
    (hN : Buf K W SP t N 12)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees) t (PolyPost K W SP N A D al n t) := by
  have h15 := E.r15
  have rA := E.perm.wR (show 288 + 8 ≤ 4096 by decide)
  have rL := E.perm.wR (show 296 + 8 ≤ 4096 by decide)
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
  refine WP.mono (absorb_ok v L E₁ (hA.of_eq hrd₁ hwr₁) h12₁ hbp₁) fun t₂ P₂ => ?_
  have P₂' := P₂.of_eq hm₁ hrd₁ hwr₁
  rw [hm₁] at P₂'
  have S₂ := S.absR L P₂'.frame
  have h15₂ := P₂'.env.r15
  have rD := P₂'.env.perm.wR (show 304 + 8 ≤ 4096 by decide)
  have rN := P₂'.env.perm.wR (show 312 + 8 ≤ 4096 by decide)
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
  refine WP.mono (absorb_ok v L E₃ hD₃ h12₃ hbp₃) fun t₄ P₄ => ?_
  have P₄' := P₄.of_eq hm₃ hrd₃ hwr₃
  rw [hm₃, Proof.AesGcm.X86_64.bytesAt_frame P₂'.frame (buf_absR hD) hD.lt.le] at P₄'
  have P₂₄ := P₂'.trans L P₄'
  have S₄ := S.absR L P₂₄.frame
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env S₄.alen S₄.len hA.lt hD.lt) fun t₅ P₅ => ?_)
  have P₂₅ := P₂₄.trans L P₅
  have S₅ := S.absR L P₂₅.frame
  obtain ⟨t₆, run₆, fr₆, out₆, hg₆, hrd₆, hwr₆⟩ := tagIn_ok L P₂₅.env S₅.nonce (hN.of_eq P₂₅.rd P₂₅.wr)
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.of_saved hg₆ hrd₆ hwr₆, hrd₆.trans P₂₅.rd, hwr₆.trans P₂₅.wr,
    (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans
      (fr₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self ..), ?_⟩
  have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
    rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
  rw [out₆, Proof.AesGcm.X86_64.bytesAt_frame P₂₅.frame (buf_absR hN) (by decide), GcmSiv.tagInput_eq,
    Proof.AesGcm.X86_64.length_bytesAt, Proof.AesGcm.X86_64.length_bytesAt, P₂₅.out, hG, hY, Spec.GcmSiv.polyval,
    GcmSiv.Polyval.polyvalFrom_eq, GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
    GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n)) (by simp [Spec.GcmSiv.le64])]

end VG.Proof.AesGcmSiv.X86_64
