import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Tag
import VerifiedGarbage.Proof.GcmSiv.Ctr
import VerifiedGarbage.Proof.AesOcb.X86_64.Callee

/-!
# AES-GCM-SIV on x86-64: a chunk of counter mode's whole blocks

Untrusted: everything here is checked by Lean. A chunk of `c` (1 to 64)
whole blocks from block `j`: `ctrGen` writes the counter blocks
`CB_j, …, CB_{j + c − 1}` from `W + 488` (`ctrGen_ok`), `vg_aes_encrypt_blocks`
encrypts them in place, and `ksXor` XORs them into the data, a word at a
time (`ksXor_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt)
open VG.Proof.AesOcb.X86_64 (frame_store2)

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega) (by omega)) hc

/-- A counter block at `p`, as two words and the bytes after them: block `i`
from `icb`. -/
theorem counterBlock_at {m : Mem} {p : Addr} {icb : List Byte} {i : Nat}
    (hw : m.readW p 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + i))
    (hr : bytesAt m (p + BitVec.ofNat 64 4) 12 = icb.drop 4) :
    bytesAt m p 16 = Spec.GcmSiv.counterBlock icb i := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    hw, hr]

/-- One counter block stored at `rdi`: its first word from `r8`, the next
from `r9` and the last two from `rdx`; then `r8` and `rdi` on, and `rcx`
down. -/
theorem genStep_ok (s : State) {P : Addr} {k : Nat}
    (hdi : s.gpr .rdi = P) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (w₀ : InRegions s.wr P 4) (w₄ : InRegions s.wr (P + BitVec.ofNat 64 4) 4)
    (w₈ : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa [.store32 (at_ .rdi 0) .r8, .store32 (at_ .rdi 4) .r9, .store (at_ .rdi 8) .rdx,
        .alu32 .add .r8 (imm 1), .alu .add .rdi (imm 16), .alu .sub .rcx (imm 1)] s = some s' ∧
      s'.mem = ((s.mem.writeW P ((s.gpr .r8).setWidth 32)).writeW (P + BitVec.ofNat 64 4) ((s.gpr .r9).setWidth 32)).writeW
        (P + BitVec.ofNat 64 8) (s.gpr .rdx) ∧
      s'.gpr .r8 = (((s.gpr .r8).setWidth 32 + 1 : BitVec 32)).setWidth 64 ∧
      s'.gpr .rdi = P + BitVec.ofNat 64 16 ∧ s'.gpr .rcx = BitVec.ofNat 64 k - 1 ∧
      s'.zf = some (BitVec.ofNat 64 k - 1 == 0) ∧
      (∀ r, r ≠ .r8 → r ≠ .rdi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₀' : InRegions s.wr (P + BitVec.ofNat 64 0) 4 := by simpa using w₀
  refine ⟨_, by srun [hdi, hcx, w₀, w₀', w₄, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.add_zero]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx]; rfl
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx]; rfl
  · intro r h₁ h₂ h₃; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, ite_false]
  all_goals rfl

/-- What `ctrGen` leaves: the counter blocks `CB_j, …, CB_{j + c − 1}` from
`W + 488`, and the counter block at `W + 96` on by `c`. -/
structure GenPost (W : Addr) (icb : List Byte) (j c : Nat) (t t' : State) : Prop where
  blocks : ∀ k < c, bytesAt t'.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 = Spec.GcmSiv.counterBlock icb (j + k)
  ctr : CtrSt W icb (j + c) t'.mem
  frame : Frame [⟨W + BitVec.ofNat 64 96, 4⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩] t.mem t'.mem
  gpr : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .rdx → r ≠ .rcx → r ≠ .rdi → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem setWidth_32_64 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- The loop of `ctrGen`, before block `k`. -/
structure GenInv (W : Addr) (icb : List Byte) (j c : Nat) (t₁ u : State) (k : Nat) : Prop where
  rdi : u.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * k)
  rcx : u.gpr .rcx = BitVec.ofNat 64 (c - k)
  r8 : u.gpr .r8 = (BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + (j + k))).setWidth 64
  blocks : ∀ k' < k, bytesAt u.mem (W + BitVec.ofNat 64 (488 + 16 * k')) 16 = Spec.GcmSiv.counterBlock icb (j + k')
  frame : Frame [⟨W + BitVec.ofNat 64 488, 16 * k⟩] t₁.mem u.mem
  gpr : ∀ r, r ≠ .r8 → r ≠ .rcx → r ≠ .rdi → u.gpr r = t₁.gpr r
  rd : u.rd = t₁.rd
  wr : u.wr = t₁.wr

theorem genLoop_ok {K W SP : Addr} (L : Lay K W SP) {t t₁ : State} (E : Env K W SP t) {icb : List Byte} {j c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hwr : t₁.wr = t.wr)
    (hrest : Proof.Cmac.le4 ((t₁.gpr .r9).setWidth 32) ++ Proof.Cmac.le8 (t₁.gpr .rdx) = icb.drop 4)
    (I₀ : GenInv W icb j c t₁ t₁ 0) :
    WP isa (.loop (.block [.store32 (at_ .rdi 0) .r8, .store32 (at_ .rdi 4) .r9, .store (at_ .rdi 8) .rdx,
        .alu32 .add .r8 (imm 1), .alu .add .rdi (imm 16), .alu .sub .rcx (imm 1)]) .ne) t₁
      fun u => GenInv W icb j c t₁ u c := by
  have hw := L.ww
  refine WP.loop (M := isa) (c := .ne)
    (fun (m : Nat) (u : State) => ∃ k, m = c - k ∧ k < c ∧ GenInv W icb j c t₁ u k) ?_ (c - 0) t₁
    ⟨0, rfl, hc1, I₀⟩
  rintro m u ⟨k, rfl, hk, I⟩
  have wu : ∀ {d n : Nat}, d + n ≤ 3816 → InRegions u.wr (W + BitVec.ofNat 64 d) n := fun h => by
    rw [I.wr, hwr]; exact E.perm.wW h
  have e4 : W + BitVec.ofNat 64 (488 + 16 * k) + BitVec.ofNat 64 4 = W + BitVec.ofNat 64 (488 + 16 * k + 4) :=
    add_ofNat_assoc _ _ _
  have e8 : W + BitVec.ofNat 64 (488 + 16 * k) + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (488 + 16 * k + 8) :=
    add_ofNat_assoc _ _ _
  obtain ⟨u', run', m', r8', rdi', rcx', zf', g', rd', wr'⟩ := genStep_ok u (P := W + BitVec.ofNat 64 (488 + 16 * k))
    (k := c - k) I.rdi I.rcx (wu (by omega)) (by rw [e4]; exact wu (by omega)) (by rw [e8]; exact wu (by omega))
  refine WP.of_runBlock ⟨u', run', ?_⟩
  rw [e4, e8] at m'
  have fB : Frame [⟨W + BitVec.ofNat 64 (488 + 16 * k), 16⟩] u.mem u'.mem := by
    rw [m']
    have c₀ : Region.Contains ⟨W + BitVec.ofNat 64 (488 + 16 * k), 16⟩ (W + BitVec.ofNat 64 (488 + 16 * k)) (32 / 8) := by
      simpa using Offset.contains_base (W + BitVec.ofNat 64 (488 + 16 * k)) (d := 0) (n := 4) (k := 16) (by decide)
        (by decide)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))
  have I' : GenInv W icb j c t₁ u' (k + 1) := by
    refine ⟨?_, ?_, ?_, fun k' hk' => ?_, ?_, fun r h₁ h₂ h₃ => ?_, by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · rw [rdi', add_ofNat_assoc, show 488 + 16 * k + 16 = 488 + 16 * (k + 1) by omega]
    · rw [rcx', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega),
        Nat.sub_sub]
    · rw [r8', I.r8, setWidth_32_64, show Spec.GcmSiv.leNat (icb.take 4) + (j + (k + 1)) =
        Spec.GcmSiv.leNat (icb.take 4) + (j + k) + 1 by omega, BitVec.ofNat_add (Spec.GcmSiv.leNat (icb.take 4) + (j + k)) 1]
      rfl
    · by_cases hkk : k' = k
      · subst hkk
        rw [m']
        refine counterBlock_at ?_ ?_
        · simp (disch := omega) only [readW_writeW_W, Mem.readW_writeW_self32]
          rw [I.r8, setWidth_32_64]
        · rw [add_ofNat_assoc, Proof.Cmac.bytesAt_add _ _ 4 8, add_ofNat_assoc, ← Proof.Cmac.le4_readW,
            ← Proof.Cmac.le8_readW]
          simp (disch := omega) only [readW_writeW_W, Mem.readW_writeW_self32, Mem.readW_writeW_self64]
          rw [I.gpr _ (by decide) (by decide) (by decide), I.gpr _ (by decide) (by decide) (by decide), hrest]
      · rw [Proof.AesGcm.X86_64.bytesAt_frame fB (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact L.w_w (by omega) (by omega) (by omega)) (by decide), I.blocks k' (by omega)]
    · exact (I.frame.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Offset.sub W (by omega) (by omega)⟩).trans (fB.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Offset.sub W (by omega) (by omega)⟩)
    · rw [g' r h₁ h₃ h₂, I.gpr r h₁ h₂ h₃]
  by_cases he : k + 1 = c
  · left
    refine ⟨(eval_ne zf').trans ?_, he ▸ I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    simp [show c - k - 1 = 0 by omega]
  · right
    refine ⟨(eval_ne zf').trans ?_, c - (k + 1), by omega, k + 1, rfl, by omega, I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    have : BitVec.ofNat 64 (c - k - 1) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
    rw [beq_eq_false_iff_ne.mpr this]; rfl

theorem ctrGen_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {icb : List Byte} {j c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (h14 : t.gpr .r14 = BitVec.ofNat 64 c) (C : CtrSt W icb j t.mem) :
    WP isa ctrGen t (GenPost W icb j c t) := by
  have h15 := E.r15
  have hw := L.ww
  have r₀ := E.perm.wR (show 96 + 4 ≤ 3816 by decide)
  have r₄ := E.perm.wR (show 100 + 4 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 3816 by decide)
  obtain ⟨t₁, run₁, rdi₁, rcx₁, r8₁, r9₁, rdx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      ([.mov32 .r8 (.mem (at_ .r15 cmO)), .mov32 .r9 (.mem (at_ .r15 (cmO + 4))),
        .mov .rdx (.mem (at_ .r15 (cmO + 8))), .mov .rcx (.reg .r14)] ++ ptr .rdi .r15 revO) t = some t₁ ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 488 ∧ t₁.gpr .rcx = BitVec.ofNat 64 c ∧
      t₁.gpr .r8 = (t.mem.readW (W + BitVec.ofNat 64 96) 32).setWidth 64 ∧
      t₁.gpr .r9 = (t.mem.readW (W + BitVec.ofNat 64 100) 32).setWidth 64 ∧
      t₁.gpr .rdx = t.mem.readW (W + BitVec.ofNat 64 104) 64 ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .rdx → r ≠ .rcx → r ≠ .rdi → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, r₀, r₄, r₈, h14], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, h14]; done)
    · intro r h₁ h₂ h₃ h₄ h₅; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, h₄, h₅, ite_false]
    all_goals rfl
  have hL : t₁.gpr .r8 = (BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + (j + 0))).setWidth 64 := by
    rw [r8₁, C.word, Nat.add_zero]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have hrest : Proof.Cmac.le4 ((t₁.gpr .r9).setWidth 32) ++ Proof.Cmac.le8 (t₁.gpr .rdx) = icb.drop 4 := by
    rw [r9₁, rdx₁, setWidth_32_64, Proof.Cmac.le4_readW, Proof.Cmac.le8_readW, ← C.rest,
      show (12 : Nat) = 4 + 8 from rfl, Proof.Cmac.bytesAt_add, add_ofNat_assoc]
  refine WP.seq (WP.mono (genLoop_ok L E hc1 hc wr₁ hrest
    ⟨by rw [rdi₁, Nat.mul_zero, Nat.add_zero], by rw [rcx₁, Nat.sub_zero], hL, fun _ h => absurd h (Nat.not_lt_zero _),
      by rw [Nat.mul_zero]; exact fun x _ => rfl, fun r h₁ h₂ h₃ => rfl, rfl, rfl⟩) fun u I => ?_)
  have h15u : u.gpr .r15 = W := by
    rw [I.gpr _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h15]
  have wC := E.perm.wW (show 96 + 4 ≤ 3816 by decide)
  rw [← wr₁, ← I.wr] at wC
  refine WP.of_runBlock ⟨_, by srun [h15u, wC], ?_⟩
  have fW : Frame [⟨W + BitVec.ofNat 64 96, 4⟩] u.mem (u.mem.writeW (W + BitVec.ofNat 64 96) ((u.gpr .r8).setWidth 32)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd96 : ∀ q ∈ [(⟨W + BitVec.ofNat 64 96, 4⟩ : Region)], ∀ {d k : Nat}, 100 ≤ d → d + k ≤ 3816 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q := fun q hq d k h₁ h₂ => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by omega)) h₂ (by decide)
  refine ⟨fun k hk => ?_, ⟨?_, ?_⟩, ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, by simp only [rd_setReg]; rw [I.rd, rd₁],
    by simp only [wr_setReg]; rw [I.wr, wr₁]⟩
  all_goals simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · rw [Proof.AesGcm.X86_64.bytesAt_frame fW (fun q hq => hd96 q hq (by omega) (by omega)) (by decide),
      I.blocks k hk]
  · rw [Mem.readW_writeW_self32, I.r8, setWidth_32_64]
  · rw [Proof.AesGcm.X86_64.bytesAt_frame fW (fun q hq => hd96 q hq (by omega) (by omega)) (by decide),
      Proof.AesGcm.X86_64.bytesAt_frame I.frame (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by omega)) (by omega) (by omega))
        (by decide), m₁, C.rest]
  · rw [← m₁]
    exact ((I.frame.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W + BitVec.ofNat 64 488, 1024⟩, by simp, Offset.sub W (by omega) (by omega)⟩).trans
      (fW.mono (by simp)))
  · rw [I.gpr r h₁ h₄ h₅, g₁ r h₁ h₂ h₃ h₄ h₅]

/-- One block of `ksXor`: the block at `r12` XORed with the one at `rsi`;
both pointers on, and `rcx` down. -/
theorem xorStep_ok (s : State) {Q S : Addr} {k : Nat} (h12 : s.gpr .r12 = Q) (hsi : s.gpr .rsi = S)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (rQ₀ : InRegions (s.rd ++ s.wr) Q 8) (rQ₈ : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (rS₀ : InRegions (s.rd ++ s.wr) S 8) (rS₈ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 8) 8)
    (wQ₀ : InRegions s.wr Q 8) (wQ₈ : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r12 0)), .mov .rdx (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .rsi 0)),
        .alu .xor .rdx (.mem (at_ .rsi 8)), .store (at_ .r12 0) .rax, .store (at_ .r12 8) .rdx,
        .alu .add .r12 (imm 16), .alu .add .rsi (imm 16), .alu .sub .rcx (imm 1)] s = some s' ∧
      bytesAt s'.mem Q 16 = Spec.Cmac.xor (bytesAt s.mem Q 16) (bytesAt s.mem S 16) ∧
      Frame [⟨Q, 16⟩] s.mem s'.mem ∧
      s'.gpr .r12 = Q + BitVec.ofNat 64 16 ∧ s'.gpr .rsi = S + BitVec.ofNat 64 16 ∧
      s'.gpr .rcx = BitVec.ofNat 64 k - 1 ∧ s'.zf = some (BitVec.ofNat 64 k - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r12 → r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₀ : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  have rQ₀' : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 0) 8 := by rw [e₀]; exact rQ₀
  have rS₀' : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 0) 8 := by rw [e₀]; exact rS₀
  have wQ₀' : InRegions s.wr (Q + BitVec.ofNat 64 0) 8 := by rw [e₀]; exact wQ₀
  refine ⟨_, by srun [h12, hsi, hcx, rQ₀, rQ₈, rS₀, rS₈, wQ₀, wQ₈, rQ₀', rS₀', wQ₀'], ?_, ?_, ?_, ?_, ?_, ?_,
    fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    rw [Proof.Cmac.bytesAt_store2, Proof.Cmac.xor_words]
  · simp only [mem_setReg, mem_arithFlags]
    exact frame_store2 _ _ _ _
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hsi]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx]; rfl
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, h₄, h₅, ite_false]
  all_goals rfl

/-- What `ksXor`'s loop keeps, before block `k` of the chunk. -/
structure XorInv (D W : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j c : Nat) (t₁ u : State)
    (k : Nat) : Prop where
  r12 : u.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + k))
  rsi : u.gpr .rsi = W + BitVec.ofNat 64 (488 + 16 * k)
  rcx : u.gpr .rcx = BitVec.ofNat 64 (c - k)
  data : bytesAt u.mem D n = GcmSiv.ctrPart ciph icb x (16 * (j + k))
  frame : Frame [⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩] t₁.mem u.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r12 → r ≠ .rsi → r ≠ .rcx → u.gpr r = t₁.gpr r
  rd : u.rd = t₁.rd
  wr : u.wr = t₁.wr

theorem xorLoop_ok {K W SP : Addr} (L : Lay K W SP) {t₁ : State} (E : Env K W SP t₁) {D : Addr} {n : Nat}
    (hD : Buf K W SP t₁ D n) (hDw : Covers [⟨D, n⟩] t₁.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte}
    (hxl : x.length = n) (hk16 : ∀ i, (GcmSiv.ksBlock ciph icb i).length = 16) {j c : Nat} (hc1 : 1 ≤ c)
    (hc : c ≤ 64) (hjc : 16 * (j + c) ≤ n)
    (hks : ∀ k < c, bytesAt t₁.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 = GcmSiv.ksBlock ciph icb (j + k))
    (I₀ : XorInv D W n ciph icb x j c t₁ t₁ 0) :
    WP isa (.loop (.block [.mov .rax (.mem (at_ .r12 0)), .mov .rdx (.mem (at_ .r12 8)),
        .alu .xor .rax (.mem (at_ .rsi 0)), .alu .xor .rdx (.mem (at_ .rsi 8)), .store (at_ .r12 0) .rax,
        .store (at_ .r12 8) .rdx, .alu .add .r12 (imm 16), .alu .add .rsi (imm 16), .alu .sub .rcx (imm 1)]) .ne) t₁
      fun u => XorInv D W n ciph icb x j c t₁ u c := by
  have hw := L.ww
  have hn := hD.lt
  refine WP.loop (M := isa) (c := .ne)
    (fun (m : Nat) (u : State) => ∃ k, m = c - k ∧ k < c ∧ XorInv D W n ciph icb x j c t₁ u k) ?_ (c - 0) t₁
    ⟨0, rfl, hc1, I₀⟩
  rintro m u ⟨k, rfl, hk, I⟩
  have eQ : D + BitVec.ofNat 64 (16 * (j + k)) + BitVec.ofNat 64 8 = D + BitVec.ofNat 64 (16 * (j + k) + 8) :=
    add_ofNat_assoc _ _ _
  have eS : W + BitVec.ofNat 64 (488 + 16 * k) + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (488 + 16 * k + 8) :=
    add_ofNat_assoc _ _ _
  have dR : ∀ {a : Nat}, a + 8 ≤ n → InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 a) 8 := fun h => by
    rw [I.rd, I.wr]; exact Proof.AesGcm.X86_64.in_off hD.rd h hn
  have dW : ∀ {a : Nat}, a + 8 ≤ n → InRegions u.wr (D + BitVec.ofNat 64 a) 8 := fun h => by
    rw [I.wr]; exact Proof.AesGcm.X86_64.in_off hDw h hn
  have wR : ∀ {a : Nat}, a + 8 ≤ 3816 → InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 a) 8 := fun h => by
    rw [I.rd, I.wr]; exact E.perm.wR h
  obtain ⟨u', run', hb', fB, r12', rsi', rcx', zf', g', rd', wr'⟩ := xorStep_ok u (k := c - k) I.r12 I.rsi I.rcx
    (dR (by omega)) (by rw [eQ]; exact dR (by omega)) (wR (by omega)) (by rw [eS]; exact wR (by omega))
    (dW (by omega)) (by rw [eQ]; exact dW (by omega))
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have hDQ : (⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (488 + 16 * k), 16⟩ :=
    (hD.w.sub_left (Offset.sub_base D (by omega))).sub_right (Lay.wSub (by omega))
  have hks' : bytesAt u.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 = GcmSiv.ksBlock ciph icb (j + k) := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame I.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ((hD.w.sub_left (Offset.sub_base D (by omega))).sub_right (Lay.wSub (by omega))).symm) (by decide),
      hks k hk]
  have hx' : bytesAt u'.mem D n = GcmSiv.ctrPart ciph icb x (16 * (j + (k + 1))) := by
    rw [← hxl] at I ⊢
    have := GcmSiv.ctrPart_step ciph icb x D (i := j + k) (n := 16) (Nat.le_refl _) (hk16 _) I.data
      (frame_outside fB (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq) (by rw [hxl]; exact hn)
        (by omega))
      (by rw [hb', hks', List.take_of_length_le (by rw [hk16])])
    rwa [show 16 * (j + k) + 16 = 16 * (j + (k + 1)) by omega] at this
  have I' : XorInv D W n ciph icb x j c t₁ u' (k + 1) := by
    refine ⟨?_, ?_, ?_, hx', ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · rw [r12', add_ofNat_assoc, show 16 * (j + k) + 16 = 16 * (j + (k + 1)) by omega]
    · rw [rsi', add_ofNat_assoc, show 488 + 16 * k + 16 = 488 + 16 * (k + 1) by omega]
    · rw [rcx', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega),
        Nat.sub_sub]
    · have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ ⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩ :=
        Offset.sub D (d := 16 * (j + k)) (n := 16) (e := 16 * j) (k := 16 * c) (by omega) (by omega)
      exact I.frame.trans (fB.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, hsub⟩)
    · rw [g' r h₁ h₂ h₃ h₄ h₅, I.gpr r h₁ h₂ h₃ h₄ h₅]
  by_cases he : k + 1 = c
  · left
    refine ⟨(eval_ne zf').trans ?_, he ▸ I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    simp [show c - k - 1 = 0 by omega]
  · right
    refine ⟨(eval_ne zf').trans ?_, c - (k + 1), by omega, k + 1, rfl, by omega, I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    have : BitVec.ofNat 64 (c - k - 1) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
    rw [beq_eq_false_iff_ne.mpr this]; rfl

/-- What `ksXor`'s loop keeps of the registers and memory, before block `k`
of the chunk (for the constant-time proofs, which need no data). -/
structure XorRegs (D W : Addr) (j c : Nat) (t₁ u : State) (k : Nat) : Prop where
  r12 : u.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + k))
  rsi : u.gpr .rsi = W + BitVec.ofNat 64 (488 + 16 * k)
  rcx : u.gpr .rcx = BitVec.ofNat 64 (c - k)
  frame : Frame [⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩] t₁.mem u.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r12 → r ≠ .rsi → r ≠ .rcx → u.gpr r = t₁.gpr r
  rd : u.rd = t₁.rd
  wr : u.wr = t₁.wr

theorem xorLoop_regs {K W SP : Addr} (L : Lay K W SP) {t₁ : State} (E : Env K W SP t₁) {D : Addr} {n : Nat}
    (hD : Buf K W SP t₁ D n) (hDw : Covers [⟨D, n⟩] t₁.wr) {j c : Nat} (hc1 : 1 ≤ c) (hc : c ≤ 64)
    (hjc : 16 * (j + c) ≤ n) (I₀ : XorRegs D W j c t₁ t₁ 0) :
    WP isa (.loop (.block [.mov .rax (.mem (at_ .r12 0)), .mov .rdx (.mem (at_ .r12 8)),
        .alu .xor .rax (.mem (at_ .rsi 0)), .alu .xor .rdx (.mem (at_ .rsi 8)), .store (at_ .r12 0) .rax,
        .store (at_ .r12 8) .rdx, .alu .add .r12 (imm 16), .alu .add .rsi (imm 16), .alu .sub .rcx (imm 1)]) .ne) t₁
      fun u => XorRegs D W j c t₁ u c := by
  have hw := L.ww
  have hn := hD.lt
  refine WP.loop (M := isa) (c := .ne)
    (fun (m : Nat) (u : State) => ∃ k, m = c - k ∧ k < c ∧ XorRegs D W j c t₁ u k) ?_ (c - 0) t₁
    ⟨0, rfl, hc1, I₀⟩
  rintro m u ⟨k, rfl, hk, I⟩
  have eQ : D + BitVec.ofNat 64 (16 * (j + k)) + BitVec.ofNat 64 8 = D + BitVec.ofNat 64 (16 * (j + k) + 8) :=
    add_ofNat_assoc _ _ _
  have eS : W + BitVec.ofNat 64 (488 + 16 * k) + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (488 + 16 * k + 8) :=
    add_ofNat_assoc _ _ _
  have dR : ∀ {a : Nat}, a + 8 ≤ n → InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 a) 8 := fun h => by
    rw [I.rd, I.wr]; exact Proof.AesGcm.X86_64.in_off hD.rd h hn
  have dW : ∀ {a : Nat}, a + 8 ≤ n → InRegions u.wr (D + BitVec.ofNat 64 a) 8 := fun h => by
    rw [I.wr]; exact Proof.AesGcm.X86_64.in_off hDw h hn
  have wR : ∀ {a : Nat}, a + 8 ≤ 3816 → InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 a) 8 := fun h => by
    rw [I.rd, I.wr]; exact E.perm.wR h
  obtain ⟨u', run', -, fB, r12', rsi', rcx', zf', g', rd', wr'⟩ := xorStep_ok u (k := c - k) I.r12 I.rsi I.rcx
    (dR (by omega)) (by rw [eQ]; exact dR (by omega)) (wR (by omega)) (by rw [eS]; exact wR (by omega))
    (dW (by omega)) (by rw [eQ]; exact dW (by omega))
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (j + k)), 16⟩ ⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩ :=
    Offset.sub D (d := 16 * (j + k)) (n := 16) (e := 16 * j) (k := 16 * c) (by omega) (by omega)
  have I' : XorRegs D W j c t₁ u' (k + 1) := by
    refine ⟨?_, ?_, ?_, I.frame.trans (fB.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, hsub⟩), fun r h₁ h₂ h₃ h₄ h₅ => ?_, by rw [rd', I.rd],
      by rw [wr', I.wr]⟩
    · rw [r12', add_ofNat_assoc, show 16 * (j + k) + 16 = 16 * (j + (k + 1)) by omega]
    · rw [rsi', add_ofNat_assoc, show 488 + 16 * k + 16 = 488 + 16 * (k + 1) by omega]
    · rw [rcx', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega),
        Nat.sub_sub]
    · rw [g' r h₁ h₂ h₃ h₄ h₅, I.gpr r h₁ h₂ h₃ h₄ h₅]
  by_cases he : k + 1 = c
  · left
    refine ⟨(eval_ne zf').trans ?_, he ▸ I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    simp [show c - k - 1 = 0 by omega]
  · right
    refine ⟨(eval_ne zf').trans ?_, c - (k + 1), by omega, k + 1, rfl, by omega, I'⟩
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]
    have : BitVec.ofNat 64 (c - k - 1) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
    rw [beq_eq_false_iff_ne.mpr this]; rfl

/-- Any memory holds the counter block it holds, from block 0. -/
theorem CtrSt.self (W : Addr) (m : Mem) : CtrSt W (bytesAt m (W + BitVec.ofNat 64 96) 16) 0 m := by
  have h4 := Proof.Cmac.bytesAt_add m (W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, add_ofNat_assoc] at h4
  refine ⟨?_, ?_⟩
  · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
  · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

/-! ## The pieces around them -/

/-- A chunk's size: `min(64, b − j)` blocks into `r14`. -/
theorem chunkHead_wp {t : State} {b j : Nat} (hb : b < 2 ^ 60) (hbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)) :
    WP isa (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))) t fun t' =>
      t'.gpr .r14 = BitVec.ofNat 64 (min 64 (b - j)) ∧ (∀ r, r ≠ .r14 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, r14₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)] t
      = some t₁ ∧ t₁.gpr .r14 = BitVec.ofNat 64 64 ∧ t₁.cf = some (decide (b - j < 64)) ∧
      (∀ r, r ≠ .r14 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · rw [cf_arithFlags]
      simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        toNat_ofNat_of_lt (show b - j < 2 ^ 64 by omega)]
      rfl
    · intro r hr; simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (b - j < 64)) (eval_b cf₁) (fun hb' => ?_) (fun hb' => WP.block_nil ?_)
  · have hlt : b - j < 64 := of_decide_eq_true hb'
    refine WP.of_runBlock ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, g₁ _ (by decide : Reg.rbx ≠ .r14), hbx, Nat.min_eq_right (by omega : b - j ≤ 64)]
    · intro r hr; simp only [gpr_setReg, hr, ite_false, g₁ r hr]
    · exact m₁
    · exact rd₁
    · exact wr₁
  · have hge : ¬ b - j < 64 := of_decide_eq_false hb'
    exact ⟨by rw [r14₁, Nat.min_eq_left (by omega)], g₁, m₁, rd₁, wr₁⟩

/-- The arguments of `vg_aes_encrypt_blocks`: the encryption key's schedule
at `W + 248`, the `c` counter blocks at `W + 488` and the working space at
`W + 1768`. -/
theorem bargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 14)
    {c : Nat} (hc : c ≤ 64)
    (rdi : s.gpr .rdi = W + BitVec.ofNat 64 248) (rsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 488) (rcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (r8 : s.gpr .r8 = W + BitVec.ofNat 64 1768) :
    Proof.AesOcb.X86_64.BCall s (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1768) R c where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := by omega
  wrap := by rw [toNat_W L.ww (by decide)]; have := L.ww; omega
  kd := L.w_w (.inl (by omega)) (by decide) (by omega)
  ks := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := L.w_w (.inl (by omega)) (by omega) (by decide)
  stkK := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkD := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := Proof.AesGcm.X86_64.covers_append (Proof.AesGcm.X86_64.covers_cons (E.perm.wCR (by decide))
      Proof.AesGcm.X86_64.covers_nil)
    (Proof.AesGcm.X86_64.covers_cons (E.perm.wCR (by omega)) (Proof.AesGcm.X86_64.covers_cons (E.perm.wCR (by decide))
      Proof.AesGcm.X86_64.covers_nil))
  writes := Proof.AesGcm.X86_64.covers_cons (E.perm.wC (by omega))
    (Proof.AesGcm.X86_64.covers_cons (E.perm.wC (by decide)) Proof.AesGcm.X86_64.covers_nil)

theorem ecbArgs_ok {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) {c : Nat} (h14 : t.gpr .r14 = BitVec.ofNat 64 c) :
    ∃ t₁ : State, runBlock isa ecbArgs t = some t₁ ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .rdx = W + BitVec.ofNat 64 488 ∧ t₁.gpr .rcx = BitVec.ofNat 64 c ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 1768 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rR := S.rounds
  have rR' := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [ecbArgs, h15, rR, rR', h14], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, rR, h14]; done)
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

theorem stateAt_eq_ofFn (m : Mem) (p : Addr) :
    Spec.Aes.stateAt m p = Vector.ofFn fun i => (bytesAt m p 16).getD i.1 0 := by
  apply Vector.ext
  intro i hi
  simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD, hi]

/-- A block `vg_aes_encrypt_blocks` replaced: the cipher of the old one. -/
theorem bytesAt_cipher {m m' : Mem} {D : Addr} {c : Nat} {R : Nat} {w : List Byte}
    (h : Spec.Aes.statesAt m' D c = (Spec.Aes.statesAt m D c).map (Spec.Aes.cipher R w)) {k : Nat} (hk : k < c) :
    bytesAt m' (D + BitVec.ofNat 64 (16 * k)) 16 = Spec.GcmSiv.aesWith R w (bytesAt m (D + BitVec.ofNat 64 (16 * k)) 16) := by
  rw [Proof.AesOcb.X86_64.bytesAt_toList, Proof.AesOcb.X86_64.stateAt_of_statesAt h hk, stateAt_eq_ofFn]
  rfl

end VG.Proof.AesGcmSiv.X86_64
