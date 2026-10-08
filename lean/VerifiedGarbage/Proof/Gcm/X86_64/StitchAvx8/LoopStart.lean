import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.LoopStep

/-! # Filling the pipeline and preparing its first hash batch -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepare batch)

theorem CoreInv.yframe {s₀ s t : State} {P : Nat → Block} {dec : Bool} {c g : Nat} {rs : List XReg}
    (h : CoreInv s₀ P dec c g s) (hf : YFrame rs s t) (hy : .xmm2 ∉ rs) : CoreInv s₀ P dec c g t := by
  refine ⟨h.env.yframe hf, hf.mem ▸ h.data, hf.mem ▸ h.templates, ?_, ?_, ?_, ?_, h.c_le, h.g_le⟩
  · rw [hf.gpr]; exact h.counter
  · rw [hf.gpr]; exact h.cursor
  · rw [hf.gpr]; exact h.remaining
  · rw [hf.lane _ hy 0 (by decide)]; exact h.hash

theorem CoreInv.prepare {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ P dec c g s) (hn : g + 8 ≤ nb s₀)
    (hx : ∀ i < 8, blockAt s.mem (bAddr s₀ (g + i)) = window s₀ dec g i) :
    WP isa (.block ((List.range 8).flatMap prepare)) s fun t =>
      CoreInv s₀ P dec c g t ∧ Buffered s₀ dec g t.mem := by
  have hw := prepareRun_ok hp s h.env 0 (by decide)
    (fun k hk => by rw [Nat.zero_add, h.addr]; exact in_rdwr (in_sub hp.d_in (by omega)))
    (fun k hk => by
      rw [Nat.zero_add, h.addr]
      exact hp.d_p.sub_left
        (Offset.sub_base (dp s₀) (d := 16 * (g + k)) (n := 16) (k := 16 * nb s₀) (by omega))) 8 (by decide)
  simp only [Nat.zero_add] at hw
  refine WP.mono hw fun t ⟨htE, htB, hf, hm⟩ => ?_
  refine ⟨⟨htE, h.data.frame hm ?_, h.templates.frame hm ?_, ?_, ?_, ?_, ?_, h.c_le, h.g_le⟩, ?_⟩
  · intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact hp.d_p.sub_right (Offset.sub_base (pp s₀) (d := 512) (n := 128) (k := 1024) (by decide))
  · intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact (hash_counter_disjoint s₀).symm
  · rw [hf.gpr .r8 (by decide)]; exact h.counter
  · rw [hf.gpr .rdx (by decide)]; exact h.cursor
  · rw [hf.gpr .r9 (by decide)]; exact h.remaining
  · rw [hf.lane]; exact h.hash
  · intro i hi; rw [htB i hi, h.addr]; exact hx i hi

theorem firstEnc_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (h : Ready s₀ P s) :
    WP isa (.seq (batch (nr s₀) 8 0 (fun _ => []))
      (.seq (batch (nr s₀) 8 8 (fun _ => [])) (.block ((List.range 8).flatMap prepare)))) s
      (LoopInv s₀ P false 0) := by
  refine WP.seq (WP.mono ((CoreInv.initial hp h false).bareBatch hp 0 rfl (by have := hp.nb16; omega))
    fun u hu => ?_)
  refine WP.seq (WP.mono (hu.bareBatch hp 8 rfl (by have := hp.nb16; omega)) fun t ht => ?_)
  refine WP.mono (ht.prepare hp (by have := hp.nb16; omega) (fun i hi => ?_)) fun v ⟨hv, hb⟩ => ?_
  · simp only [Nat.zero_add]
    rw [ht.data i (by have := hp.nb16; omega), ite_eq_left (by omega : i < 0 + 8 + 8)]
    simp [window, hashBlock]
  · exact ⟨hv, hb, rfl, hp.nb16⟩

theorem firstDec_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (h : Ready s₀ P s) :
    WP isa (.block ((List.range 8).flatMap prepare)) s (LoopInv s₀ P true 0) := by
  have hc := CoreInv.initial hp h true
  refine WP.mono (hc.prepare hp (by have := hp.nb16; omega) (fun i hi => ?_)) fun t ⟨ht, hb⟩ => ?_
  · simpa only [Nat.zero_add, window, hashBlock, Bool.true_eq, ite_true, Nat.not_lt_zero, ite_false] using
      hc.data i (by have := hp.nb16; omega)
  · exact ⟨ht, hb, rfl, by have := hp.nb16; change 0 + 8 ≤ nb s₀; omega⟩

theorem LoopInv.compare {s₀ s : State} {P : Nat → Block} {dec : Bool} {g : Nat}
    (h : LoopInv s₀ P dec g s) :
    WP isa (.block [.alu .cmp .r9 (.imm (if dec then 16 else 24))]) s fun t =>
      LoopInv s₀ P dec g t ∧ t.cf = some (decide (nb s₀ - g < threshold dec)) := by
  refine WP.mono (cmp8_ok s (if dec then 16 else 24)) fun t ⟨hcf, hf⟩ => ?_
  refine ⟨⟨h.core.yframe hf (by decide), hf.mem ▸ h.buffered, h.multiple, h.tail_le⟩, ?_⟩
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have he : ((if dec then 16 else 24 : BitVec 32).signExtend 64).toNat = threshold dec := by
    cases dec <;> rfl
  rw [hcf, h.core.remaining, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), he]

end VG.Proof.Gcm.X86_64.StitchAvx8
