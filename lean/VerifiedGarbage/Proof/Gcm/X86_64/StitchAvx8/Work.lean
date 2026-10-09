import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Prepared
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Flow

/-! # One hash product in the interleaved pipeline -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.StitchAvx8 (gh8 prepare)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast)

theorem hashStep_ok {s₀ s : State} {P X Y : Nat → Block} {y : Block}
    (hp : SPre s₀) (hE : Env s₀ P s) (n : Nat) (hn : n < 8)
    (hB : Prepared s₀ X Y n s.mem) (hy : s.lane .xmm2 0 = y)
    (ha : n ≠ 0 → prod (s.proj 0) = accN X P y n) :
    WP isa (.block (gh8 ((n + 1) % 8))) s fun t =>
      Env s₀ P t ∧ prod (t.proj 0) = accN X P y (n + 1) ∧
      t.lane .xmm2 0 = y ∧ YFrame ghRegs s t := by
  have hk : (n + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hpow : power s ((n + 1) % 8) = P ((n + 1) % 8) := by
    simp only [power, ea_at, ofInt_natCast, hE.r11, Nat.mod_mod]
    rw [show 16 * (8 + (n + 1) % 8) = 128 + 16 * ((n + 1) % 8) by omega]
    exact hE.powers _ hk
  have hin : input s ((n + 1) % 8) = hashInput X y ((n + 1) % 8) := by
    simp only [input, hashInput, ea_at, ofInt_natCast, hE.r11, Nat.mod_mod, hy]
    exact congrArg (fun v => v ^^^ (if (n + 1) % 8 = 0 then y else 0)) (hB.current hn)
  refine WP.mono (gh8_ok s ((n + 1) % 8) (by
    simp only [ea_at, ofInt_natCast, hE.rd, hE.wr, hE.r11, Nat.mod_mod]
    exact in_rdwr (in_sub hp.p_in (by omega))) (by
    simp only [ea_at, ofInt_natCast, hE.rd, hE.wr, hE.r11, Nat.mod_mod]
    exact in_rdwr (in_sub hp.p_in (by omega)))) fun t ⟨hv, hf⟩ => ?_
  refine ⟨hE.yframe hf, ?_, (hf.lane .xmm2 (by decide) 0 (by decide)).trans hy, hf⟩
  rw [hv, hin, hpow, Nat.mod_mod, accN_succ]
  by_cases hz : n = 0
  · subst n
    simp only [Nat.zero_add, Nat.reduceMod, ite_true, accN, List.range_zero, List.foldl_nil]
  · rw [ite_eq_right (by omega : (n + 1) % 8 ≠ 1), ha hz]

/-- Replace the just-consumed hash slot with the next batch's block. -/
theorem prepareNext_ok {s₀ s : State} {P X Y : Nat → Block}
    (hp : SPre s₀) (hE : Env s₀ P s) (n : Nat) (hn : n < 8)
    (hB : Prepared s₀ X Y n s.mem)
    (hR : InRegions (s.rd ++ s.wr)
      (s.gpr .rdx + BitVec.ofNat 64 (16 * (8 + (n + 1) % 8))) 16)
    (hS : Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (8 + (n + 1) % 8)), 16⟩ (pR s₀))
    (hX : Spec.Gcm.blockAt s.mem
      (s.gpr .rdx + BitVec.ofNat 64 (16 * (8 + (n + 1) % 8))) = Y ((n + 1) % 8)) :
    WP isa (.block (prepare (8 + (n + 1) % 8))) s fun t =>
      Env s₀ P t ∧ Prepared s₀ X Y (n + 1) t.mem ∧ BufferFrame s t ∧
      Frame [hashR s₀] s.mem t.mem := by
  have hk : (n + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hmod : (8 + (n + 1) % 8) % 8 = (n + 1) % 8 := by omega
  refine WP.mono (prepare_ok s (8 + (n + 1) % 8)
    (by simpa only [BitVec.add_zero] using in_sub hR (off := 0) (n := 8) (by decide)) (by
      simpa only [Offset.add_add] using in_sub hR (off := 8) (n := 8) (by decide))
    (by rw [hE.wr, hE.r11, hmod]; exact in_sub hp.p_in (by omega))
    (by rw [hE.wr, hE.r11, hmod]; exact in_sub hp.p_in (by omega)) (by
      rw [hE.r11, hmod]
      exact (hS.sub_left (Region.sub_prefix (by decide))).sub_right
        (Offset.sub_base (pp s₀) (by omega)) |>.sep
        (Region.contains_self _ _) (Region.contains_self _ _))) fun t ⟨hm, hf⟩ => ?_
  rw [hE.r11, hmod] at hm
  have hF : Frame [⟨hashAddr s₀ ((n + 1) % 8), 16⟩] s.mem t.mem := by
    rw [hm]
    exact prepareMem_frame _ _ _
  have hW : Frame [workR s₀] s.mem t.mem := hF.sub fun r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨workR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 512 + 16 * ((n + 1) % 8)) (e := 512) (n := 16) (k := 256)
        (by omega) (by omega)⟩
  refine ⟨hE.buffer hf hW, hB.next hn ?_ hF, hf, hF.sub fun r hr => ?_⟩
  · rw [hm]
    exact (prepareMem_read _ _ _).trans hX
  · simp only [List.mem_singleton] at hr
    subst r
    exact ⟨hashR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 512 + 16 * ((n + 1) % 8)) (e := 512) (n := 16) (k := 128)
        (by omega) (by omega)⟩

theorem hashPrepared_ok {s₀ s : State} {P X Y : Nat → Block} {y : Block}
    (hp : SPre s₀) (hE : Env s₀ P s) (n : Nat) (hn : n < 8)
    (hB : Prepared s₀ X Y n s.mem) (hy : s.lane .xmm2 0 = y)
    (ha : n ≠ 0 → prod (s.proj 0) = accN X P y n) (more : Bool)
    (hR : more = true → InRegions (s.rd ++ s.wr)
      (s.gpr .rdx + BitVec.ofNat 64 (16 * (8 + (n + 1) % 8))) 16)
    (hS : more = true → Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (8 + (n + 1) % 8)), 16⟩ (pR s₀))
    (hX : more = true → Spec.Gcm.blockAt s.mem
      (s.gpr .rdx + BitVec.ofNat 64 (16 * (8 + (n + 1) % 8))) = Y ((n + 1) % 8))
    (hNo : more = false → ∀ i < 8, Y i = X i) :
    WP isa (.block (gh8 ((n + 1) % 8) ++ (if more then prepare (8 + (n + 1) % 8) else []))) s fun t =>
      Env s₀ P t ∧ Prepared s₀ X Y (n + 1) t.mem ∧
      prod (t.proj 0) = accN X P y (n + 1) ∧ t.lane .xmm2 0 = y ∧
      FlowFrame ghRegs s t ∧ Frame [hashR s₀] s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (hashStep_ok hp hE n hn hB hy ha) fun t ⟨hEt, hat, hyt, hf⟩ => ?_
  have hBt : Prepared s₀ X Y n t.mem := by rw [hf.mem]; exact hB
  cases more with
  | false =>
    exact WP.block_nil ⟨hEt, hBt.same_next (hNo rfl), hat, hyt, .of_yframe hf,
      hf.mem ▸ Frame.refl _ _⟩
  | true =>
    refine WP.mono (prepareNext_ok hp hEt n hn hBt (by
      simpa only [hf.rd, hf.wr, hf.gpr] using hR rfl) (by
      simpa only [hf.gpr] using hS rfl) (by
      simpa only [hf.gpr, hf.mem] using hX rfl)) fun u ⟨hEu, hBu, hu, hm⟩ => ?_
    refine ⟨hEu, hBu, ?_, (hu.lane .xmm2 0).trans hyt,
      (FlowFrame.of_yframe hf).trans (.of_buffer _ hu), ?_⟩
    · simpa only [prod, State.proj_xmm, hu.lane] using hat
    · rw [hf.mem] at hm
      exact hm

end VG.Proof.Gcm.X86_64.StitchAvx8
