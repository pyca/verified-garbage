import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Stages

/-! # Filling eight hash-buffer slots before and after the main loop -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepare)

theorem prepareBlock_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (hE : Env s₀ P s) (k : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : Region.Disjoint ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀)) :
    WP isa (.block (prepare k)) s fun t => Env s₀ P t ∧
      t.mem.readW (hashAddr s₀ (k % 8)) 128 = blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) ∧
      BufferFrame s t ∧ Frame [⟨hashAddr s₀ (k % 8), 16⟩] s.mem t.mem := by
  have hk : k % 8 < 8 := Nat.mod_lt _ (by decide)
  refine WP.mono (prepare_ok s k
    (by simpa only [BitVec.add_zero] using in_sub hr (off := 0) (n := 8) (by decide))
    (by simpa only [Offset.add_add] using in_sub hr (off := 8) (n := 8) (by decide))
    (by rw [hE.wr, hE.r11]; exact in_sub hp.p_in (by omega))
    (by rw [hE.wr, hE.r11]; exact in_sub hp.p_in (by omega)) (by
      rw [hE.r11]
      exact (hs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Offset.sub_base (pp s₀) (by omega)))) fun t ⟨hm, hf⟩ => ?_
  rw [hE.r11] at hm
  have hF : Frame [⟨hashAddr s₀ (k % 8), 16⟩] s.mem t.mem := by
    rw [hm]; exact prepareMem_frame _ _ _
  refine ⟨hE.buffer hf (hF.sub fun r hr => ?_), ?_, hf, hF⟩
  · simp only [List.mem_singleton] at hr; subst r
    exact ⟨workR s₀, List.mem_singleton_self _,
      Offset.sub (pp s₀) (d := 512 + 16 * (k % 8)) (e := 512) (n := 16) (k := 256) (by omega) (by omega)⟩
  · rw [hm]; exact prepareMem_read _ _ _

theorem prepareRun_ok {s₀ : State} {P : Nat → Block} (hp : SPre s₀)
    (s : State) (hE : Env s₀ P s) (j : Nat) (hj : j % 8 = 0)
    (hr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hs : ∀ k < 8, Region.Disjoint ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k)), 16⟩ (pR s₀))
    (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap fun i => prepare (j + i))) s fun t =>
      Env s₀ P t ∧ (∀ k < n, t.mem.readW (hashAddr s₀ k) 128 =
        blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k)))) ∧
      BufferFrame s t ∧ Frame [hashR s₀] s.mem t.mem := by
  induction n with
  | zero => exact WP.block_nil ⟨hE, fun _ h => (Nat.not_lt_zero _ h).elim, .refl _, .refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hEt, hBt, hf, hm⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (prepareBlock_ok hp hEt (j + n)
      (by rw [hEt.rd, hEt.wr, hf.gpr .rdx (by decide)]; exact hr n (by omega))
      (by rw [hf.gpr .rdx (by decide)]; exact hs n (by omega)))
      fun u ⟨hEu, hBu, hf', hm'⟩ => ?_
    have hmod : (j + n) % 8 = n := by omega
    rw [hmod] at hBu hm'
    refine ⟨hEu, fun k hk => ?_, hf.trans hf', hm.trans (hm'.sub fun r hr' => ?_)⟩
    · by_cases he : k = n
      · subst k
        rw [hBu, hf.gpr .rdx (by decide)]
        exact VG.Proof.Aes.X86_64.AesNi.blockAt_frame hm (by
          intro r hr'; simp only [List.mem_singleton] at hr'; subst r
          exact (hs n (by omega)).sub_right
            (Offset.sub_base (pp s₀) (d := 512) (n := 128) (k := 1024) (by decide)))
      · have hmread : u.mem.readW (hashAddr s₀ k) 128 = t.mem.readW (hashAddr s₀ k) 128 :=
          hm'.readW (r := ⟨hashAddr s₀ k, 16⟩)
            (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
            (by intro r hr'; simp only [List.mem_singleton] at hr'; subst r
                exact Offset.disjoint (pp s₀) (d := 512 + 16 * k) (e := 512 + 16 * n)
                  (n := 16) (k := 16) (by omega) (by omega) (by omega)) (by decide)
        exact hmread.trans (hBt k (by omega))
    · simp only [List.mem_singleton] at hr'; subst r
      exact ⟨hashR s₀, List.mem_singleton_self _,
        Offset.sub (pp s₀) (d := 512 + 16 * n) (e := 512) (n := 16) (k := 128) (by omega) (by omega)⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
