module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTCall
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.FixedCT
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Calls
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTCall
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
meta import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.FixedCT
meta import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Calls
meta import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Absorb
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Parameters
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTBase
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Parameters

/-!
# Argon2 on RISC-V: H₀, in two runs

`code_rel`: H₀'s hash leaks the same trace in two runs with the same public
data. The BLAKE2b calls are related by H′'s (`HPrime.init_rel`,
`update_rel`, `finalize_rel`), from the same arguments: `scratch`, the
inputs' places and lengths, and the byte count, which only the inputs'
lengths fix; the code between them by `frameTaint`.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.Impl.Argon2.RISCV64.Derive (countOff ld st lda)

theorem li64_ok {s₀ s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa (.block [.li .a1 64]) s fun t => Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .a1 = BitVec.ofNat 64 64 :=
  wp_li (by decide) fun _ u₁ => WP.block_nil ⟨h.upd u₁, Prm.of_lw pr fun d _ _ => lw_mem u₁.mem d, u₁.gpr⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem finReady {s : State} (h : Inv s₀ s) : HPrime.FinalizeReady s :=
  ⟨h.scr_in hp⟩

theorem initReady {s : State} (h : Inv s₀ s) (r4 : s.gpr .a1 = BitVec.ofNat 64 64) : HPrime.InitReady s :=
  ⟨by rw [r4]; decide, h.scr_in hp⟩

/-- `update`'s readiness, for data readable and outside `scratch`'s state. -/
theorem updReady {s : State} (h : Inv s₀ s)
    (hdata : Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨scrP s₀, 768⟩) :
    HPrime.UpdateReady s :=
  ⟨h.scr_in hp, hdata, by rw [h.s4]; exact dataState.sub_right (Region.sub_prefix (by decide)),
    by rw [h.s4]; exact dataState.sub_right (Offset.sub_base _ (by decide))⟩

theorem init_step {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) (r4 : s.gpr .a1 = BitVec.ofNat 64 64) :
    WP isa Impl.Argon2.RISCV64.HPrime.init s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (scrP s₀) [] :=
  (HPrime.init_ok s (by rw [r4]; decide) (h.scr_in hp)).mono fun t ⟨rp, g, rd, wr, sp, f⟩ => by
    obtain ⟨i, p, -⟩ := h.keepsP hp pr ⟨g, rd, wr, sp, HPrime.init_frame _ f⟩
    rw [r4, h.s4] at rp
    exact ⟨i, p, by simpa using rp⟩

theorem fixed_step {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) (offset size : Nat) (ho : offset < 2048)
    (hn : size < 2048) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    WP isa (Impl.Argon2.RISCV64.HPrime.absorbFixed offset size) s fun t => Inv s₀ t ∧ Prm s₀ t :=
  (HPrime.absorbFixed_keeps s offset size (finReady hp h) ho hn lo hi).mono fun _ k =>
    let ⟨i, p, _⟩ := h.keepsP hp pr k
    ⟨i, p⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- Absorbing `size` bytes of `scratch` at `offset` leaks the same trace in two runs. -/
theorem fixed_rel (offset size : Nat) (ho : offset < 2048) (hn : size < 2048) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384)
    (hc : ∃ hc, (VG.Taint.check frameTaint (τF [] []) (.block (Impl.Argon2.RISCV64.HPrime.fixedArgs offset size))
      hc).isSome = true)
    {F₁ F₂ : State → Prop} (hF₁ : ∀ s, F₁ s → Inv s₀₁ s) (hF₂ : ∀ s, F₂ s → Inv s₀₂ s) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (Impl.Argon2.RISCV64.HPrime.absorbFixed offset size)
      fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.HPrime.absorbFixed
  have args := (T.leaf (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) [] []
    (fun s₁ s₂ h => ⟨hF₁ _ h.1, hF₂ _ h.2, by simp, by simp⟩) hc).wpDep
    (F := fun s t => HPrime.FixedArgs s t offset size)
    fun s₁ s₂ _ => ⟨HPrime.fixedArgs_ok s₁ offset size ho hn,
      HPrime.fixedArgs_ok s₂ offset size ho hn⟩
  refine args.seq (HPrime.update_rel fun s₁ s₂ ⟨_, σ₁, σ₂, hσ, h₁, h₂⟩ => ?_)
  have i₁ := hF₁ _ hσ.1
  have i₂ := hF₂ _ hσ.2
  have base : σ₁.gpr .s4 = σ₂.gpr .s4 := by rw [i₁.s4, i₂.s4, T.pb.scrP_eq]
  exact ⟨HPrime.fixed_ready (finReady T.hp₁ i₁) h₁ lo hi, HPrime.fixed_ready (finReady T.hp₂ i₂) h₂ lo hi,
    by rw [h₁.keeps.s4, h₂.keeps.s4, base], by rw [h₁.count, h₂.count],
    by rw [h₁.data, h₂.data, base], by rw [h₁.size, h₂.size],
    by rw [h₁.keeps.sp, h₂.keeps.sp, i₁.sp, i₂.sp, T.pb.E_eq]⟩

/-- `start` leaks the same trace in two runs. -/
theorem start_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.RISCV64.Derive.start fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.Derive.start
  refine RelCT.seqW (T.leaf [] [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => li64_ok h.1 h.2) (fun s h => li64_ok h.1 h.2) ?_
  refine RelCT.seqW (HPrime.init_rel fun s₁ s₂ h => ⟨initReady T.hp₁ h.1.1 h.1.2.2,
      initReady T.hp₂ h.2.1 h.2.2.2, by rw [h.1.1.s4, h.2.1.s4, T.pb.scrP_eq], by rw [h.1.2.2, h.2.2.2],
      by rw [h.1.1.sp, h.2.1.sp, T.pb.E_eq]⟩)
    (fun s h => init_step T.hp₁ h.1 h.2.1 h.2.2) (fun s h => init_step T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW (T.leaf [] [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp, by simp⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t) (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t)
    (fun s h => (header_ok T.hp₁ h.1 h.2.1 h.2.2).mono fun t ⟨i, p, _⟩ => ⟨i, p⟩)
    (fun s h => (header_ok T.hp₂ h.1 h.2.1 h.2.2).mono fun t ⟨i, p, _⟩ => ⟨i, p⟩) ?_
  refine RelCT.seqW (T.fixed_rel 896 24 (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩
      (fun s h => h.1) (fun s h => h.1))
    (fun s h => fixed_step T.hp₁ h.1 h.2 896 24 (by decide) (by decide) (by decide) (by decide))
    (fun s h => fixed_step T.hp₂ h.1 h.2 896 24 (by decide) (by decide) (by decide) (by decide)) ?_
  exact T.leaf [] [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp, by simp⟩) ⟨_, by taint_decide⟩

/-- `absorb ptr len` leaks the same trace in two runs whose absorbed data have
the same length. -/
theorem absorb_rel {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18) (hnp : ptr ∉ intArgs)
    (hnl : len ∉ intArgs)
    (hR₁ : (⟨arg s₀₁ ptr, (arg s₀₁ len).toNat⟩ : Region) ∈ [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁])
    (hR₂ : (⟨arg s₀₂ ptr, (arg s₀₂ len).toNat⟩ : Region) ∈ [pwR s₀₂, saltR s₀₂, secR s₀₂, adR s₀₂])
    (hl₁ : (arg s₀₁ len).toNat < 2 ^ 32) (hl₂ : (arg s₀₂ len).toNat < 2 ^ 32)
    {data₁ data₂ : List Byte} (heq : data₁.length = data₂.length)
    (hd₁ : data₁.length + 4 + 2 ^ 32 < 2 ^ 36) (hd₂ : data₂.length + 4 + 2 ^ 32 < 2 ^ 36)
    (hcA : ∃ hc, (VG.Taint.check frameTaint (τF [countOff] [])
      (.block [lda .a0 len, .store .w .a0 .s4 920, ld .a1 countOff, .addi .a2 .s4 920, .li .a3 4])
      hc).isSome = true)
    (hcB : ∃ hc, (VG.Taint.check frameTaint (τF [countOff] [])
      (.block [ld .a1 countOff, .addi .a1 .a1 4, st countOff .a1, lda .a2 ptr, lda .a3 len]) hc).isSome = true)
    (hcC : ∃ hc, (VG.Taint.check frameTaint (τF [countOff] [])
      (.block [ld .a1 countOff, lda .a0 len, .add .a1 .a1 .a0, st countOff .a1]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) (Impl.Argon2.RISCV64.Derive.absorb ptr len)
      fun _ _ => True := by
  have ep := T.pb.arg_eq hptr hnp
  have el := T.pb.arg_eq hlen hnl
  -- What a run satisfies after each part.
  let GA (s₀ : State) (data : List Byte) (t : State) : Prop :=
    HI s₀ data t ∧ t.gpr .a1 = BitVec.ofNat 64 data.length ∧
      t.gpr .a2 = scrP s₀ + BitVec.ofNat 64 920 ∧ t.gpr .a3 = BitVec.ofNat 64 4 ∧
      bytesAt t.mem (scrP s₀ + BitVec.ofNat 64 920) 4 = Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32)
  let GU (s₀ : State) (data : List Byte) (t : State) : Prop :=
    Inv s₀ t ∧ Prm s₀ t ∧ lw s₀ t countOff = BitVec.ofNat 64 data.length ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (scrP s₀) (data ++ Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32))
  let GB (s₀ : State) (data : List Byte) (t : State) : Prop :=
    Inv s₀ t ∧ Prm s₀ t ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (scrP s₀) (data ++ Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32)) ∧
      lw s₀ t countOff = BitVec.ofNat 64 (data.length + 4) ∧ t.gpr .a1 = BitVec.ofNat 64 (data.length + 4) ∧
      t.gpr .a2 = arg s₀ ptr ∧ t.gpr .a3 = arg s₀ len
  let GC (s₀ : State) (data : List Byte) (t : State) : Prop :=
    Inv s₀ t ∧ lw s₀ t countOff = BitVec.ofNat 64 (data.length + 4)
  have wl : ∀ s₀ : State, (Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32)).length = 4 := fun _ => by
    simp [Spec.Blake2.wordBytes]
  -- The first `update`'s readiness and effect.
  have rdyU : ∀ {s₀ s : State} {data : List Byte}, DPre s₀ → GA s₀ data s → HPrime.UpdateReady s :=
    fun {s₀ s data} hp ⟨h, _, r5, r6, _⟩ => updReady hp h.inv
      (by rw [r5, r6, h.inv.wr]
          exact Covers.right (Covers.one ⟨scrR s₀, scr_mem hp, Offset.contains_base _ (by decide) (by decide)⟩))
      (by rw [r5, r6]; exact Offset.disjoint_base _ (by decide) (by decide))
  have wU : ∀ {s₀ : State} {data : List Byte}, DPre s₀ → ∀ s, GA s₀ data s →
      WP isa Impl.Argon2.RISCV64.HPrime.update s (GU s₀ data) :=
    fun {s₀ data} hp s ⟨h, r4, r5, r6, w⟩ => (absU_ok hp h r4 (by rw [r6]; decide)
      (by rw [r5, r6, h.inv.wr]
          exact Covers.right (Covers.one ⟨scrR s₀, scr_mem hp, Offset.contains_base _ (by decide) (by decide)⟩))
      (by rw [r5, r6]; exact Offset.disjoint_base _ (by decide) (by decide))).mono
      fun t ⟨i, p, c, rp⟩ => ⟨i, p, c.trans h.cnt, by
        rw [r5, r6, show (BitVec.ofNat 64 4).toNat = 4 from rfl, w] at rp; exact rp⟩
  -- The second `update`'s readiness and effect.
  have hR' : ∀ {s₀ : State}, (⟨arg s₀ ptr, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] →
      (⟨arg s₀ ptr, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] :=
    fun {s₀} hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
      rcases hR with h | h | h | h <;> simp [h]
  have cov₂ : ∀ {s₀ s : State} {data : List Byte}, DPre s₀ → GB s₀ data s →
      (⟨arg s₀ ptr, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] →
      Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] (s.rd ++ s.wr) := fun {s₀ s data} hp h hR => by
    rw [h.2.2.2.2.2.1, h.2.2.2.2.2.2, h.1.rd, hp.rd]
    exact Covers.left (Covers.one ⟨_, hR' hR, Region.contains_self _ _⟩)
  have ds₂ : ∀ {s₀ s : State} {data : List Byte}, DPre s₀ → GB s₀ data s →
      (⟨arg s₀ ptr, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] →
      (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨scrP s₀, 768⟩ := fun {s₀ s data} hp h hR => by
    rw [h.2.2.2.2.2.1, h.2.2.2.2.2.2]
    exact (hp.ro_w _ (hR' hR) (scrR s₀) (by simp)).sub_right (Region.sub_prefix (by decide))
  have wU2 : ∀ {s₀ : State} {data : List Byte}, DPre s₀ → (arg s₀ len).toNat < 2 ^ 32 →
      data.length + 4 + 2 ^ 32 < 2 ^ 36 →
      (⟨arg s₀ ptr, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] → ∀ s, GB s₀ data s →
      WP isa Impl.Argon2.RISCV64.HPrime.update s (GC s₀ data) :=
    fun {s₀ data} hp hl hd hR s h => by
      obtain ⟨i, p, rp, c, r4, r5, r6⟩ := h
      have dl : (data ++ Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32)).length = data.length + 4 := by
        rw [List.length_append, wl]
      exact (absU_ok hp ⟨i, p, rp, by rw [c, dl], by rw [dl]; omega_arith⟩ (by rw [r4, dl]) (by rw [r6]; exact hl)
        (cov₂ hp ⟨i, p, rp, c, r4, r5, r6⟩ hR) (ds₂ hp ⟨i, p, rp, c, r4, r5, r6⟩ hR)).mono fun t ⟨i', _, c', _⟩ => ⟨i', c'.trans c⟩
  unfold Impl.Argon2.RISCV64.Derive.absorb
  refine RelCT.seqW (G₁ := GA s₀₁ data₁) (G₂ := GA s₀₂ data₂)
    (T.leaf [countOff] [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.cnt, h.2.cnt, heq], by simp⟩) hcA)
    (fun s h => absA_ok T.hp₁ hlen h) (fun s h => absA_ok T.hp₂ hlen h) ?_
  refine RelCT.seqW (G₁ := GU s₀₁ data₁) (G₂ := GU s₀₂ data₂)
    (HPrime.update_rel fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨rdyU T.hp₁ h₁, rdyU T.hp₂ h₂,
      by rw [h₁.1.inv.s4, h₂.1.inv.s4, T.pb.scrP_eq], by rw [h₁.2.1, h₂.2.1, heq],
      by rw [h₁.2.2.1, h₂.2.2.1, T.pb.scrP_eq], by rw [h₁.2.2.2.1, h₂.2.2.2.1],
      by rw [h₁.1.inv.sp, h₂.1.inv.sp, T.pb.E_eq]⟩)
    (wU T.hp₁) (wU T.hp₂) ?_
  refine RelCT.seqW (G₁ := GB s₀₁ data₁) (G₂ := GB s₀₂ data₂)
    (T.leaf [countOff] [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, heq], by simp⟩) hcB)
    (fun s h => absB_ok T.hp₁ hptr hlen h.1 h.2.1 h.2.2.2 h.2.2.1)
    (fun s h => absB_ok T.hp₂ hptr hlen h.1 h.2.1 h.2.2.2 h.2.2.1) ?_
  refine RelCT.seqW (G₁ := GC s₀₁ data₁) (G₂ := GC s₀₂ data₂)
    (HPrime.update_rel fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨updReady T.hp₁ h₁.1 (cov₂ T.hp₁ h₁ hR₁) (ds₂ T.hp₁ h₁ hR₁),
      updReady T.hp₂ h₂.1 (cov₂ T.hp₂ h₂ hR₂) (ds₂ T.hp₂ h₂ hR₂),
      by rw [h₁.1.s4, h₂.1.s4, T.pb.scrP_eq], by rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1, heq],
      by rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1, ep], by rw [h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2, el],
      by rw [h₁.1.sp, h₂.1.sp, T.pb.E_eq]⟩)
    (wU2 T.hp₁ hl₁ hd₁ hR₁) (wU2 T.hp₂ hl₂ hd₂ hR₂) ?_
  exact T.leaf [countOff] [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, heq], by simp⟩) hcC

/-- `finish` leaks the same trace in two runs whose hashed data have the same
length. -/
theorem finish_rel {data₁ data₂ : List Byte} (heq : data₁.length = data₂.length) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) Impl.Argon2.RISCV64.Derive.finish
      fun _ _ => True := by
  have ld : ∀ {s₀ : State} {data : List Byte} (s : State), HI s₀ data s →
      WP isa (.block [ld .a1 countOff]) s fun t =>
        Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .a1 = BitVec.ofNat 64 data.length :=
    fun {s₀ data} s h => wp_ldloc h.inv (d := countOff) (by decide) fun t u => WP.block_nil
      ⟨h.inv.upd u, Prm.of_lw h.prm fun d _ _ => lw_mem u.mem d, by rw [u.gpr, h.cnt]⟩
  unfold Impl.Argon2.RISCV64.Derive.finish
  refine RelCT.seqW (T.leaf [countOff] [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.cnt, h.2.cnt, heq], by simp⟩) ⟨_, by taint_decide⟩)
    (ld (data := data₁)) (ld (data := data₂)) ?_
  refine RelCT.seqW (G₁ := fun t => Inv s₀₁ t) (G₂ := fun t => Inv s₀₂ t)
    (HPrime.finalize_rel fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨finReady T.hp₁ h₁.1, finReady T.hp₂ h₂.1,
      by rw [h₁.1.s4, h₂.1.s4, T.pb.scrP_eq], by rw [h₁.2.2, h₂.2.2, heq],
      by rw [h₁.1.sp, h₂.1.sp, T.pb.E_eq]⟩)
    (fun s h => (HPrime.finalize_keeps s (finReady T.hp₁ h.1)).mono fun _ k => (h.1.keeps T.hp₁ k).1)
    (fun s h => (HPrime.finalize_keeps s (finReady T.hp₂ h.1)).mono fun _ k => (h.1.keeps T.hp₂ k).1) ?_
  exact T.leaf [] [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp, by simp⟩) ⟨_, by taint_decide⟩

/-- H₀'s hash leaks the same trace in two runs. -/
theorem code_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.RISCV64.Derive.code fun _ _ => True := by
  have l : ∀ {s₀ : State}, DPre s₀ → (arg s₀ 2).toNat < 2 ^ 32 ∧ (arg s₀ 4).toNat < 2 ^ 32 ∧
      (arg s₀ 10).toNat < 2 ^ 32 ∧ (arg s₀ 12).toNat < 2 ^ 32 := fun {s₀} hp =>
    ⟨hp.valid.2.2.2.2.2.2.2.2.1, hp.valid.2.2.2.2.2.2.2.2.2.1, hp.valid.2.2.2.2.2.2.2.2.2.2.1,
      hp.valid.2.2.2.2.2.2.2.2.2.2.2⟩
  obtain ⟨l1, l2, l3, l4⟩ := l T.hp₁
  obtain ⟨m1, m2, m3, m4⟩ := l T.hp₂
  have e2 : (arg s₀₁ 2).toNat = (arg s₀₂ 2).toNat := by rw [T.pb.arg_eq (by decide)]
  have e4 : (arg s₀₁ 4).toNat = (arg s₀₂ 4).toNat := by rw [T.pb.arg_eq (by decide)]
  have e10 : (arg s₀₁ 10).toNat = (arg s₀₂ 10).toNat := by rw [T.pb.arg_eq (by decide)]
  have len : ∀ (d : List Byte) (m : Mem) (p : Addr) (n : Nat),
      (Proof.Argon2.appendInput d (bytesAt m p n)).length = d.length + 4 + n := fun d m p n => by
    simp only [Proof.Argon2.appendInput_length, bytesAt, List.length_map, List.length_range]
  have h24 := Proof.Argon2.initialHeader_length (prm s₀₁)
  have h24' := Proof.Argon2.initialHeader_length (prm s₀₂)
  unfold Impl.Argon2.RISCV64.Derive.code
  refine RelCT.seqW T.start_rel (fun s h => start_ok T.hp₁ h.1 h.2) (fun s h => start_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 1) (len := 2) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp) l1 m1
      (by rw [h24, h24']) (by rw [h24]; omega_arith) (by rw [h24']; omega_arith)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) l1
      (by rw [h24]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) m1
      (by rw [h24']; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 3) (len := 4) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp) l2 m2
      (by rw [len, len, h24, h24', e2]) (by rw [len, h24]; omega_arith) (by rw [len, h24']; omega_arith)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) l2
      (by rw [len, h24]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) m2
      (by rw [len, h24']; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 9) (len := 10) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp) l3 m3
      (by rw [len, len, len, len, h24, h24', e2, e4]) (by rw [len, len, h24]; omega_arith)
      (by rw [len, len, h24']; omega_arith)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) l3
      (by rw [len, len, h24]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) m3
      (by rw [len, len, h24']; omega_arith) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 11) (len := 12) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp) l4 m4
      (by rw [len, len, len, len, len, len, h24, h24', e2, e4, e10]) (by rw [len, len, len, h24]; omega_arith)
      (by rw [len, len, len, h24']; omega_arith)
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) l4
      (by rw [len, len, len, h24]; omega_arith) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) m4
      (by rw [len, len, len, h24']; omega_arith) h) ?_
  exact T.finish_rel (by rw [len, len, len, len, len, len, len, len, h24, h24', e2, e4, e10,
    T.pb.arg_eq (i := 12) (by decide)])

end Two

end VG.Proof.Argon2.RISCV64.Derive
