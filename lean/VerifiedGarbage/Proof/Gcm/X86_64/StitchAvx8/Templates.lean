import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Env
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Counter

/-! # Refreshing the next batch's eight counter templates -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepCounter)

def templateAddr (s₀ : State) (i : Nat) : Addr := pp s₀ + BitVec.ofNat 64 (640 + 16 * i)

/-- Slots below `n` have advanced to the next batch; the others retain this batch. -/
def Templates (s₀ : State) (c n : Nat) (m : Mem) : Prop :=
  ∀ i < 8, blockAt m (templateAddr s₀ i) =
    Nat.repeat inc32 (c + i + if i < n then 8 else 0) (cb s₀)

def counterR (s₀ : State) : Region := ⟨pp s₀ + 640, 128⟩

theorem Templates.frame {s₀ : State} {c n : Nat} {m m' : Mem} {rs : List Region}
    (h : Templates s₀ c n m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (counterR s₀).Disjoint r) : Templates s₀ c n m' := by
  intro i hi
  exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf (fun r hr =>
    (hd r hr).sub_left (Offset.sub (pp s₀) (d := 640 + 16 * i) (e := 640)
      (n := 16) (k := 128) (by omega) (by omega)))).trans (h i hi)

theorem Templates.next {s₀ : State} {c : Nat} {m : Mem} (h : Templates s₀ c 8 m) :
    Templates s₀ (c + 8) 0 m := by
  intro i hi
  have ht := h i hi
  simp only [hi, ite_true] at ht
  simp only [Nat.not_lt_zero, ite_false, Nat.add_zero]
  rw [show c + 8 + i = c + i + 8 by omega]
  exact ht

theorem templateWord (s₀ : State) (i : Nat) :
    templateAddr s₀ i + BitVec.ofNat 64 12 = pp s₀ + BitVec.ofNat 64 (652 + 16 * i) := by
  rw [templateAddr, Offset.add_add]
  congr 2
  omega

theorem prepTemplate_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (hE : Env s₀ P s) (c n : Nat) (hn : n < 8) (hT : Templates s₀ c n s.mem)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)) :
    WP isa (.block (prepCounter n)) s fun t =>
      Env s₀ P t ∧ Templates s₀ c (n + 1) t.mem ∧ BufferFrame s t ∧
      Frame [⟨pp s₀ + BitVec.ofNat 64 (652 + 16 * n), 4⟩] s.mem t.mem := by
  refine WP.mono (prepCounter_ok s n (by
    rw [hE.wr, hE.r11]; exact in_sub hp.p_in (by omega))) fun t ⟨hm, hf⟩ => ?_
  rw [hE.r11, hv, BitVec.add_assoc, ← BitVec.ofNat_add] at hm
  have hm' : t.mem = s.mem.writeW (templateAddr s₀ n + BitVec.ofNat 64 12)
      (bswap32 ((cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + n + 8))) := by
    rw [templateWord, show c + n + 8 = c + 8 + n by omega]
    exact hm
  have hF : Frame [⟨pp s₀ + BitVec.ofNat 64 (652 + 16 * n), 4⟩] s.mem t.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  have hW : Frame [workR s₀] s.mem t.mem := hF.sub fun r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨workR s₀, List.mem_singleton_self _, Offset.sub (pp s₀) (d := 652 + 16 * n) (e := 512) (n := 4) (k := 256) (by omega) (by omega)⟩
  refine ⟨hE.buffer hf hW, ?_, hf, hF⟩
  intro i hi
  by_cases he : i = n
  · subst i
    have ht := hT n hn
    simp only [Nat.lt_irrefl, ite_false, Nat.add_zero] at ht
    simpa only [Templates, Nat.lt_add_one, Nat.le_refl, ite_true] using
      (hm' ▸ refreshCounter_ok s.mem (templateAddr s₀ n) (cb s₀) (c + n) 8 ht)
  · have hk : (if i < n + 1 then 8 else 0) = (if i < n then 8 else 0) := by
      split_ifs <;> omega
    rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint (pp s₀) (by omega) (by omega) (by omega)), hk]
    exact hT i hi

/-- Prepare a consecutive portion of the next batch. The AES rounds use
the two instances starting at slots zero and four. -/
theorem prepTemplates_ok {s₀ : State} {P : Nat → Block} (hp : SPre s₀)
    (c n k : Nat) (hk : n + k ≤ 8) (s : State) (hE : Env s₀ P s)
    (hT : Templates s₀ c n s.mem)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)) :
    WP isa (.block ((List.range k).flatMap fun i => prepCounter (n + i))) s fun t =>
      Env s₀ P t ∧ Templates s₀ c (n + k) t.mem ∧ BufferFrame s t ∧
      Frame [counterR s₀] s.mem t.mem := by
  induction k with
  | zero => exact WP.block_nil ⟨hE, hT, BufferFrame.refl _, Frame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hEt, hTt, hf, hm⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (prepTemplate_ok hp hEt c (n + k) (by omega) hTt (by
      rw [hf.gpr .r8 (by decide)]; exact hv)) fun u ⟨hEu, hTu, hf', hm'⟩ => ?_
    refine ⟨hEu, ?_, hf.trans hf', hm.trans (hm'.sub fun r hr => ?_)⟩
    · simpa only [Nat.add_assoc] using hTu
    · simp only [List.mem_singleton] at hr
      subst r
      exact ⟨counterR s₀, List.mem_singleton_self _,
        Offset.sub (pp s₀) (d := 652 + 16 * (n + k)) (e := 640) (n := 4) (k := 128)
          (by omega) (by omega)⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
