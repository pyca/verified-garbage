import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Stages

/-! # Seeding the first eight counter templates -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepCounter)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)

def Seeded (s₀ : State) (n : Nat) (m : Mem) : Prop :=
  ∀ i < 8, blockAt m (templateAddr s₀ i) = Nat.repeat inc32 (if i < n then i else 0) (cb s₀)

theorem Seeded.done {s₀ : State} {m : Mem} (h : Seeded s₀ 8 m) : Templates s₀ 0 0 m := by
  intro i hi
  simpa only [hi, ite_true, Nat.zero_add, Nat.not_lt_zero, ite_false, Nat.add_zero] using h i hi

theorem copyTemplate_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (hE : Env s₀ P s) (i : Nat) (hi : i < 8)
    (hC : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀) :
    WP isa (.block [.vmovdquStore .l128 (at_ .r11 (640 + 16 * i)) .xmm7]) s fun t =>
      Env s₀ P t ∧ blockAt t.mem (templateAddr s₀ i) = cb s₀ ∧ BufferFrame s t ∧
      Frame [⟨templateAddr s₀ i, 16⟩] s.mem t.mem := by
  have hw : InRegions s.wr (s.ea (at_ .r11 (640 + 16 * i))) 16 := by
    rw [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, hE.wr, hE.r11]
    exact in_sub hp.p_in (by omega)
  have hw' : InRegions s.wr (pp s₀ + BitVec.ofNat 64 (640 + 16 * i)) 16 := by
    simpa only [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, hE.r11] using hw
  rw [WP.block_cons_iff]
  refine ⟨s.setMem (s.mem.writeW (templateAddr s₀ i) (s.lane .xmm7 0)), ?_, ?_⟩
  · simp only [exec, isa, State.store128_eq,
      VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, hE.r11, hw', ite_true]
    rfl
  have hf : BufferFrame s (s.setMem (s.mem.writeW (templateAddr s₀ i) (s.lane .xmm7 0))) :=
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have hm : Frame [⟨templateAddr s₀ i, 16⟩] s.mem
      (s.mem.writeW (templateAddr s₀ i) (s.lane .xmm7 0)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  refine WP.block_nil ⟨hE.buffer hf (hm.sub fun r hr => ?_), ?_, hf, hm⟩
  · simp only [List.mem_singleton] at hr
    subst r
    exact ⟨workR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 640 + 16 * i) (e := 512) (n := 16) (k := 256) (by omega) (by omega)⟩
  · rw [State.setMem_mem, blockAt_eq, Mem.readW_writeW_self s.mem _ 16 _ (by decide)]
    exact hC

theorem copyTemplates_ok {s₀ : State} {P : Nat → Block} (hp : SPre s₀)
    (s : State) (hE : Env s₀ P s)
    (hC : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀)
    (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).map fun i =>
      .vmovdquStore .l128 (at_ .r11 (640 + 16 * i)) .xmm7)) s fun t =>
      Env s₀ P t ∧ (∀ i < n, blockAt t.mem (templateAddr s₀ i) = cb s₀) ∧
      BufferFrame s t ∧ Frame [counterR s₀] s.mem t.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨hE, fun _ h => (Nat.not_lt_zero _ h).elim, .refl _, .refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hEt, hTt, hf, hm⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    refine WP.mono (copyTemplate_ok hp hEt n (by omega) (by rw [hf.lane]; exact hC))
      fun u ⟨hEu, hTu, hf', hm'⟩ => ?_
    refine ⟨hEu, fun i hi => ?_, hf.trans hf', hm.trans (hm'.sub fun r hr => ?_)⟩
    · by_cases he : i = n
      · subst i; exact hTu
      · exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame hm' (by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint (pp s₀) (d := 640 + 16 * i) (e := 640 + 16 * n)
            (n := 16) (k := 16) (by omega) (by omega) (by omega))).trans (hTt i (by omega))
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨counterR s₀, List.mem_singleton_self _,
        Offset.sub (pp s₀) (d := 640 + 16 * n) (e := 640) (n := 16) (k := 128) (by omega) (by omega)⟩

theorem seedTemplate_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (hE : Env s₀ P s) (n : Nat) (hn : n < 8) (hT : Seeded s₀ n s.mem)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32) :
    WP isa (.block (prepCounter n)) s fun t =>
      Env s₀ P t ∧ Seeded s₀ (n + 1) t.mem ∧ BufferFrame s t ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 (652 + 16 * n), 4⟩] s.mem t.mem := by
  refine WP.mono (prepCounter_ok s n (by
    rw [hE.wr, hE.r11]; exact in_sub hp.p_in (by omega))) fun t ⟨hm, hf⟩ => ?_
  rw [hE.r11, hv] at hm
  have hF : Frame [⟨pp s₀ + BitVec.ofNat 64 (652 + 16 * n), 4⟩] s.mem t.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  refine ⟨hE.buffer hf (hF.sub fun r hr => ?_), ?_, hf, hF⟩
  · simp only [List.mem_singleton] at hr; subst r
    exact ⟨workR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 652 + 16 * n) (e := 512) (n := 4) (k := 256) (by omega) (by omega)⟩
  · intro i hi
    by_cases he : i = n
    · subst i
      have htn : blockAt s.mem (templateAddr s₀ n) = Nat.repeat inc32 0 (cb s₀) := by
        simpa only [Nat.lt_irrefl, ite_false] using hT n hn
      rw [hm, ← templateWord]
      simpa only [Nat.zero_add, Nat.lt_add_one, Nat.le_refl, ite_true] using
        refreshCounter_ok s.mem (templateAddr s₀ n) (cb s₀) 0 n htn
    · have hk : (if i < n + 1 then i else 0) = (if i < n then i else 0) := by
        split_ifs <;> omega
      rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact Offset.disjoint (pp s₀) (by omega) (by omega) (by omega)), hk]
      exact hT i hi

theorem seedTemplates_ok {s₀ : State} {P : Nat → Block} (hp : SPre s₀)
    (s : State) (hE : Env s₀ P s) (hT : Seeded s₀ 0 s.mem)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32) (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap prepCounter)) s fun t =>
      Env s₀ P t ∧ Seeded s₀ n t.mem ∧ BufferFrame s t ∧ Frame [counterR s₀] s.mem t.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨hE, hT, .refl _, .refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hEt, hTt, hf, hm⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (seedTemplate_ok hp hEt n (by omega) hTt (by
      rw [hf.gpr .r8 (by decide)]; exact hv)) fun u ⟨hEu, hTu, hf', hm'⟩ => ?_
    refine ⟨hEu, hTu, hf.trans hf', hm.trans (hm'.sub fun r hr => ?_)⟩
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨counterR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 652 + 16 * n) (e := 640) (n := 4) (k := 128) (by omega) (by omega)⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
