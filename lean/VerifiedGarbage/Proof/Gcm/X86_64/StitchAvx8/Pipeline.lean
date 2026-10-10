import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffers
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ops
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.AesHash
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec

/-! ## Counter -/
section

/-!
# Counter templates and 32-bit wraparound

Only the final four bytes of each copied counter are rewritten. Their
arithmetic is modulo 2^32, including batches that cross the wrap boundary.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Spec.Gcm (blockAt inc32)

def advanceCounter (m : Mem) (p : Addr) (n : Nat) : Mem :=
  m.writeW (p + BitVec.ofNat 64 12)
    (bswap32 (bswap32 (m.readW (p + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 n))

theorem advanceCounter_ok (m : Mem) (p : Addr) (n : Nat) :
    blockAt (advanceCounter m p n) p = Nat.repeat inc32 n (blockAt m p) := by
  apply VG.Proof.Aes.X86_64.ctr_after
  intro k hk
  simp only [advanceCounter, VG.Proof.Aes.X86_64.writeW_apply,
    VG.Proof.Aes.X86_64.off_toNat p (i := k) (j := 12) (by omega) (by omega)]
  by_cases h : k < 12
  · simp only [ite_eq_right (show ¬ 12 ≤ k by omega),
      ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega), ite_eq_left h]
  · simp only [ite_eq_left (show 12 ≤ k by omega),
      ite_eq_left (show k - 12 < 32 / 8 by omega), ite_eq_right h, BitVec.setWidth_eq]
    rw [BitVec.setWidth_ofNat_of_le (by decide)]

/-- Copying all sixteen bytes keeps the counter's big-endian value. -/
theorem copyCounter_ok (m : Mem) (src dst : Addr) :
    blockAt (m.writeW dst (m.readW src 128)) dst = blockAt m src := by
  rw [VG.Proof.Gcm.X86_64.blockAt_eq, Mem.readW_writeW_self m dst 16 _ (by decide),
    VG.Proof.Gcm.X86_64.blockAt_eq]

/-- The native low-counter word can be read from a copied template. -/
theorem copyCounter_low (m : Mem) (src dst : Addr) :
    (m.writeW dst (m.readW src 128)).readW (dst + BitVec.ofNat 64 12) 32 =
      m.readW (src + BitVec.ofNat 64 12) 32 := by
  rw [readW_writeW_inside m dst (m.readW src 128) (k := 12) (n := 4) (by decide) (by decide),
    readW_extract m src (k := 12) (n := 4) (by decide)]

/-- One template, filled directly from the original numeric counter. -/
theorem counterTemplate_ok (m : Mem) (src dst : Addr) (n : Nat) :
    blockAt ((m.writeW dst (m.readW src 128)).writeW (dst + BitVec.ofNat 64 12)
      (bswap32 (bswap32 (m.readW (src + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 n))) dst =
        Nat.repeat inc32 n (blockAt m src) := by
  have h := advanceCounter_ok (m.writeW dst (m.readW src 128)) dst n
  simpa only [advanceCounter, copyCounter_low, copyCounter_ok] using h

theorem inc32_add (C : Spec.Gcm.Block) (n d : Nat) :
    Nat.repeat inc32 d (Nat.repeat inc32 n C) = Nat.repeat inc32 (n + d) C := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change inc32 (Nat.repeat inc32 d (Nat.repeat inc32 n C)) = inc32 (Nat.repeat inc32 (n + d) C)
    exact congrArg inc32 ih

/-- Refresh a template from the numeric counter while retaining its prefix. -/
theorem refreshCounter_ok (m : Mem) (p : Addr) (C : Spec.Gcm.Block) (n d : Nat)
    (h : blockAt m p = Nat.repeat inc32 n C) :
    blockAt (m.writeW (p + BitVec.ofNat 64 12)
      (bswap32 (C.extractLsb' 0 32 + BitVec.ofNat 32 (n + d)))) p =
        Nat.repeat inc32 (n + d) C := by
  have hc := advanceCounter_ok m p d
  rw [advanceCounter, VG.Proof.Aes.X86_64.icb_lo, h,
    VG.Proof.Aes.repeat_inc32_lo, BitVec.add_assoc, ← BitVec.ofNat_add] at hc
  exact hc.trans (inc32_add C n d)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Templates -/
section

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

end

/-! ## Prepared -/
section

/-! # Reusing each GHASH input slot after its product has been consumed -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

def hashAddr (s₀ : State) (i : Nat) : Addr := pp s₀ + BitVec.ofNat 64 (512 + 16 * i)
def hashR (s₀ : State) : Region := ⟨pp s₀ + 512, 128⟩

/-- GHASH consumes slots 1,…,7,0, replacing consumed slots with `Y`. -/
def Prepared (s₀ : State) (X Y : Nat → Block) (n : Nat) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (hashAddr s₀ i) 128 = if (i + 7) % 8 < n then Y i else X i

theorem slot_position (n : Nat) (hn : n < 8) : (((n + 1) % 8) + 7) % 8 = n := by omega

theorem Prepared.current {s₀ : State} {X Y : Nat → Block} {n : Nat} {m : Mem}
    (h : Prepared s₀ X Y n m) (hn : n < 8) :
    m.readW (hashAddr s₀ ((n + 1) % 8)) 128 = X ((n + 1) % 8) := by
  have hi := h ((n + 1) % 8) (Nat.mod_lt _ (by decide))
  rw [slot_position n hn, ite_eq_right (Nat.lt_irrefl n)] at hi
  exact hi

theorem Prepared.next {s₀ : State} {X Y : Nat → Block} {n : Nat} {m m' : Mem}
    (h : Prepared s₀ X Y n m) (hn : n < 8)
    (hv : m'.readW (hashAddr s₀ ((n + 1) % 8)) 128 = Y ((n + 1) % 8))
    (hf : Frame [⟨hashAddr s₀ ((n + 1) % 8), 16⟩] m m') :
    Prepared s₀ X Y (n + 1) m' := by
  intro i hi
  by_cases he : i = (n + 1) % 8
  · subst i
    rw [slot_position n hn, ite_eq_left (by omega : n < n + 1)]
    exact hv
  · have hp : (i + 7) % 8 ≠ n := by omega
    have hv' : m'.readW (hashAddr s₀ i) 128 = m.readW (hashAddr s₀ i) 128 := by
      apply hf.readW (r := ⟨hashAddr s₀ i, 16⟩)
      · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact Offset.disjoint (pp s₀) (by omega) (by omega) (by omega)
      · decide
    have hc : (if (i + 7) % 8 < n + 1 then Y i else X i) =
        (if (i + 7) % 8 < n then Y i else X i) := by split_ifs <;> first | rfl | omega
    exact hv'.trans ((h i hi).trans hc.symm)

theorem Prepared.frame {s₀ : State} {X Y : Nat → Block} {n : Nat} {m m' : Mem}
    {rs : List Region} (h : Prepared s₀ X Y n m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (hashR s₀).Disjoint r) : Prepared s₀ X Y n m' := by
  intro i hi
  refine (hf.readW (r := ⟨hashAddr s₀ i, 16⟩) ?_ ?_ (by decide)).trans (h i hi)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  · intro r hr
    exact (hd r hr).sub_left (Offset.sub (pp s₀) (d := 512 + 16 * i) (e := 512)
      (n := 16) (k := 128) (by omega) (by omega))

theorem Prepared.done {s₀ : State} {X Y : Nat → Block} {m : Mem}
    (h : Prepared s₀ X Y 8 m) : ∀ i < 8, m.readW (hashAddr s₀ i) 128 = Y i := by
  intro i hi
  have hv := h i hi
  rw [ite_eq_left (Nat.mod_lt _ (by decide))] at hv
  exact hv

theorem Prepared.same_next {s₀ : State} {X Y : Nat → Block} {n : Nat} {m : Mem}
    (h : Prepared s₀ X Y n m) (he : ∀ i < 8, Y i = X i) : Prepared s₀ X Y (n + 1) m := by
  intro i hi
  have hv := h i hi
  simpa only [he i hi, ite_self] using hv

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Work -/
section

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

end

/-! ## Stages -/
section

/-!
# The invariant between AES rounds

`nc` counter slots and `nh` hash inputs have been consumed. Only the two
scratch buffers and `rax` may change between rounds. AES's state registers
and round-key register are absent from the invariant.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs prepCounter gh8 prepare reduceFinal)
open VG.Spec.Gcm (Block)

structure StageInv (s₀ start : State) (P X Y : Nat → Block) (y : Block)
    (c nc nh : Nat) (finished : Bool) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ c nc s.mem
  prepared : Prepared s₀ X Y nh s.mem
  hash : s.lane .xmm2 0 = if finished then reduceB (accN X P y 8) else y
  product : finished = false → nh ≠ 0 → prod (s.proj 0) = accN X P y nh
  regs : ∀ r, r ≠ .rax → s.gpr r = start.gpr r
  frame : Frame [workR s₀] start.mem s.mem

theorem StageInv.yframe {s₀ start s t : State} {P X Y : Nat → Block} {y : Block}
    {c nc nh : Nat} {finished : Bool} (h : StageInv s₀ start P X Y y c nc nh finished s)
    (hf : YFrame (.xmm1 :: aregs) s t) : StageInv s₀ start P X Y y c nc nh finished t := by
  refine ⟨h.env.yframe hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.mem]; exact h.templates
  · rw [hf.mem]; exact h.prepared
  · rw [hf.lane .xmm2 (by decide) 0 (by decide)]; exact h.hash
  · intro hfin hn
    have hp := h.product hfin hn
    simpa only [prod, State.proj_xmm,
      hf.lane .xmm8 (by decide) 0 (by decide), hf.lane .xmm9 (by decide) 0 (by decide),
      hf.lane .xmm10 (by decide) 0 (by decide)] using hp
  · intro r hr; rw [hf.gpr]; exact h.regs r hr
  · rw [hf.mem]; exact h.frame

theorem counter_sub_work (s₀ : State) : Region.Sub (counterR s₀) (workR s₀) :=
  Offset.sub (pp s₀) (d := 640) (e := 512) (n := 128) (k := 256) (by decide) (by decide)

theorem hash_sub_work (s₀ : State) : Region.Sub (hashR s₀) (workR s₀) :=
  Offset.sub (pp s₀) (d := 512) (e := 512) (n := 128) (k := 256) (by decide) (by decide)

theorem hash_counter_disjoint (s₀ : State) : (hashR s₀).Disjoint (counterR s₀) :=
  Offset.disjoint (pp s₀) (d := 512) (e := 640) (n := 128) (k := 128)
    (by decide) (by decide) (by decide)

theorem work_sub_p (s₀ : State) : Region.Sub (workR s₀) (pR s₀) :=
  Offset.sub_base (pp s₀) (d := 512) (n := 256) (k := 1024) (by decide)

theorem StageInv.counters {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nc nh : Nat} {finished : Bool} (hp : SPre s₀)
    (h : StageInv s₀ start P X Y y c nc nh finished s) (k : Nat) (hk : nc + k ≤ 8)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)) :
    WP isa (.block ((List.range k).flatMap fun i => prepCounter (nc + i))) s fun t =>
      StageInv s₀ start P X Y y c (nc + k) nh finished t ∧ FlowFrame ghRegs s t := by
  refine WP.mono (prepTemplates_ok hp c nc k hk s h.env h.templates (by
    rw [h.regs .r8 (by decide)]; exact hv)) fun t ⟨hEt, hTt, hf, hm⟩ => ?_
  refine ⟨⟨hEt, hTt, h.prepared.frame hm ?_, ?_, ?_, ?_, ?_⟩, .of_buffer _ hf⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hash_counter_disjoint s₀
  · rw [hf.lane]; exact h.hash
  · intro hfin hn
    have ha := h.product hfin hn
    simpa only [prod, State.proj_xmm, hf.lane] using ha
  · intro r hr; rw [hf.gpr r hr]; exact h.regs r hr
  · refine h.frame.trans (hm.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨workR s₀, List.mem_singleton_self _, counter_sub_work s₀⟩

theorem StageInv.hashStep {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nc nh : Nat} (hp : SPre s₀) (h : StageInv s₀ start P X Y y c nc nh false s)
    (hn : nh < 8) (more : Bool)
    (hr : more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : more = true → ∀ k < 16, Region.Disjoint
      ⟨start.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : more = true → ∀ k < 16, Spec.Gcm.blockAt start.mem
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (.block (gh8 ((nh + 1) % 8) ++ (if more then prepare (8 + (nh + 1) % 8) else []))) s fun t =>
      StageInv s₀ start P X Y y c nc (nh + 1) false t ∧ FlowFrame ghRegs s t := by
  have hk : (nh + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
  refine WP.mono (hashPrepared_ok hp h.env nh hn h.prepared h.hash (h.product rfl) more
    (fun hm => by rw [h.env.rd, h.env.wr, h.regs .rdx (by decide)]; exact hr hm _ (by omega))
    (fun hm => by rw [h.regs .rdx (by decide)]; exact hs hm _ (by omega))
    (fun hm => ?_) (fun hm i hi => by rw [hY i hi, hm]; rfl))
    fun t ⟨hEt, hBt, hat, hyt, hf, hF⟩ => ?_
  · rw [h.regs .rdx (by decide), hY _ hk, hm]
    exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame h.frame (fun r hr' => by
      simp only [List.mem_singleton] at hr'
      subst r
      exact (hs hm _ (by omega)).sub_right (work_sub_p s₀))).trans (hx hm _ (by omega))
  · refine ⟨⟨hEt, h.templates.frame hF ?_, hBt, hyt, fun _ _ => hat,
      fun r hr' => (hf.gpr r hr').trans (h.regs r hr'), ?_⟩, hf⟩
    · intro r hr'
      simp only [List.mem_singleton] at hr'
      subst r
      exact (hash_counter_disjoint s₀).symm
    · refine h.frame.trans (hF.sub fun r hr' => ?_)
      simp only [List.mem_singleton] at hr'
      subst r
      exact ⟨workR s₀, List.mem_singleton_self _, hash_sub_work s₀⟩

theorem StageInv.finishHash {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nc : Nat} (hp : SPre s₀) (h : StageInv s₀ start P X Y y c nc 8 false s) :
    WP isa (.block reduceFinal) s fun t =>
      StageInv s₀ start P X Y y c nc 8 true t ∧ FlowFrame (.xmm1 :: .xmm2 :: ghRegs) s t := by
  refine WP.mono (reduceFinal_ok s (by
    simp only [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, h.env.rd, h.env.wr, h.env.r11]
    exact in_rdwr (in_sub hp.p_in (off := 784) (by decide))) (by
    simp only [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast, h.env.r11]
    exact h.env.poly)) fun t ⟨hv, hf⟩ => ?_
  refine ⟨⟨h.env.yframe hf, ?_, ?_, ?_, fun he => Bool.noConfusion he, ?_, ?_⟩,
    (FlowFrame.of_yframe hf).mono (by decide)⟩
  · rw [hf.mem]; exact h.templates
  · rw [hf.mem]; exact h.prepared
  · rw [hv, h.product rfl (by decide)]; rfl
  · intro r hr; rw [hf.gpr]; exact h.regs r hr
  · rw [hf.mem]; exact h.frame

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Memory -/
section

/-! # Preserving scratch constants while writing encrypted data -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

theorem data_read {s₀ : State} {m m' : Mem} (hp : SPre s₀)
    (h : Frame [dR s₀] m m') (d n : Nat) (hn : d + n ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) =
      m.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) := by
  apply h.readW (r := pR s₀)
  · exact Offset.contains_base _ (by omega) (by omega)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hp.d_p.symm
  · omega

theorem Env.writeData {s₀ s t : State} {P : Nat → Block} (hp : SPre s₀)
    (h : Env s₀ P s) (hg : t.gpr = s.gpr) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hm : Frame [dR s₀] s.mem t.mem) : Env s₀ P t := by
  constructor
  · rw [hg]; exact h.rdi
  · rw [hg]; exact h.rsi
  · rw [hg]; exact h.rcx
  · rw [hg]; exact h.r11
  · rw [hg]; exact h.r10
  · intro r h1 h2 h3 h4 h5 h6; rw [hg]; exact h.other r h1 h2 h3 h4 h5 h6
  · exact h.frame.trans (hm.mono (by simp))
  · intro k hk
    exact (data_read hp hm (128 + 16 * k) 16 (by omega)).trans (h.powers k hk)
  · exact (data_read hp hm 768 16 (by decide)).trans h.mask
  · exact (data_read hp hm 784 16 (by decide)).trans h.poly
  · exact (data_read hp hm 800 8 (by decide)).trans h.rounds
  · exact (data_read hp hm 808 8 (by decide)).trans h.data
  · exact hr.trans h.rd
  · exact hw.trans h.wr

/-- Changing loop counters and cursors does not change the environment. -/
theorem Env.move {s₀ s t : State} {P : Nat → Block} (h : Env s₀ P s)
    (hg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Env s₀ P t := by
  constructor
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rdi
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rsi
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rcx
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.r11
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.r10
  · intro r h1 h2 h3 h4 h5 h6; rw [hg r h1 h2 h3 h4]; exact h.other r h1 h2 h3 h4 h5 h6
  · rw [hm]; exact h.frame
  · rw [hm]; exact h.powers
  · rw [hm]; exact h.mask
  · rw [hm]; exact h.poly
  · rw [hm]; exact h.rounds
  · rw [hm]; exact h.data
  · exact hr.trans h.rd
  · exact hw.trans h.wr

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Ready -/
section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

/-- The state after setup and before the first AES or hash batch. -/
structure Ready (s₀ : State) (P : Nat → Block) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ 0 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + 8
  cursor : s.gpr .rdx = dp s₀
  remaining : s.gpr .r9 = s₀.gpr .r9
  hash : s.lane .xmm2 0 = y₀ s₀
  frame : Frame [pR s₀] s₀.mem s.mem

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Prepare -/
section

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

end

/-! ## Cursor -/
section

/-! # Public cursor updates and loop conditions -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64

theorem next8_ok (s : State) (n : BitVec 32) :
    WP isa (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8), .alu .cmp .r9 (.imm n)]) s
      fun t => t.gpr .rdx = s.gpr .rdx + 128 ∧ t.gpr .r9 = s.gpr .r9 - 8 ∧
        t.cf = some (decide ((s.gpr .r9 - 8).toNat < (n.signExtend 64).toNat)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ (∀ r l, t.lane r l = s.lane r l) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

theorem cmp8_ok (s : State) (n : BitVec 32) :
    WP isa (.block [.alu .cmp .r9 (.imm n)]) s fun t =>
      t.cf = some (decide ((s.gpr .r9).toNat < (n.signExtend 64).toNat)) ∧ YFrame [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, isa, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Dispatch -/
section

/-! # Selecting a fixed schedule from the public round count -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch

private theorem cmpRound_ok (s : State) (n : Nat) (hn : n = 10 ∨ n = 12) :
    WP isa (.block [.alu .cmp .rsi (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.zf = some (decide (nr s = n)) ∧ YFrame [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, isa, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  change some ((s.gpr .rsi - (BitVec.ofNat 32 n).signExtend 64) == 0) = _
  congr 1
  unfold nr
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rcases hn with rfl | rfl
  · change s.gpr .rsi - (10 : BitVec 64) = 0 ↔ _
    bv_omega
  · change s.gpr .rsi - (12 : BitVec 64) = 0 ↔ _
    bv_omega

theorem pre_same {s t : State} (h : SPre s) (hf : YFrame [] s t) : SPre t := by
  rcases hf with ⟨hg, hm, hr, hw, _⟩
  cases s; cases t
  dsimp at hg hm hr hw
  cases hg; cases hm; cases hr; cases hw
  cases h
  constructor <;> with_reducible assumption

theorem epost_same {s t u : State} (hf : YFrame [] s t) (h : EPost t u) : EPost s u := by
  rcases hf with ⟨hg, hm, hr, hw, _⟩
  cases s; cases t
  dsimp at hg hm hr hw
  cases hg; cases hm; cases hr; cases hw
  cases h
  constructor <;> with_reducible assumption

theorem dpost_same {s t u : State} (hf : YFrame [] s t) (h : DPost t u) : DPost s u := by
  rcases hf with ⟨hg, hm, hr, hw, _⟩
  cases s; cases t
  dsimp at hg hm hr hw
  cases hg; cases hm; cases hr; cases hw
  cases h
  constructor <;> with_reducible assumption

theorem dispatch_ok {s : State} {a b c : Prog isa} {Q : State → Prop} (hp : SPre s)
    (ha : ∀ t, YFrame [] s t → nr s = 10 → WP isa a t Q)
    (hb : ∀ t, YFrame [] s t → nr s = 12 → WP isa b t Q)
    (hc : ∀ t, YFrame [] s t → nr s = 14 → WP isa c t Q) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.dispatch a b c) s Q := by
  refine WP.seq (WP.mono (cmpRound_ok s 10 (by decide)) fun t ⟨hz, hf⟩ => ?_)
  refine WP.ite (decide (nr s = 10)) (by simp only [eval, hz])
    (fun he => ha t hf (by simpa using he)) (fun he => ?_)
  have h10 : nr s ≠ 10 := by simpa using he
  refine WP.seq (WP.mono (cmpRound_ok t 12 (by decide)) fun u ⟨hz', hf'⟩ => ?_)
  have ht : nr t = nr s := by simp only [nr, hf.gpr]
  rw [ht] at hz'
  refine WP.ite (decide (nr s = 12)) (by simp only [eval, hz'])
    (fun he => hb u (hf.trans hf') (by simpa using he)) (fun he => ?_)
  have h12 : nr s ≠ 12 := by simpa using he
  exact hc u (hf.trans hf') (by rcases hp.rounds with he | he | he <;> omega)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Finish -/
section

/-! # Writing the final counter and hash and restoring the entry registers -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32)

structure FinishPost (s₀ start : State) (n : Nat) (y : Block) (s : State) : Prop where
  counter : blockAt s.mem (cp s₀) = Nat.repeat inc32 n (cb s₀)
  hash : blockAt s.mem (yp s₀) = y
  frame : Frame [cR s₀, yR s₀] start.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finish_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (hE : Env s₀ P s)
    (n : Nat) (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (n + 8)) :
    WP isa (.block finish) s (FinishPost s₀ s n (s.lane .xmm2 0)) := by
  have hcode : finish = finishHead ++
      ([.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
        .vmovdquStore .l128 (at_ .rcx 0) .xmm2] : List Instr) ++
      [.vop .vzeroupper] ++ restoreEntry := rfl
  rw [hcode, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (finishHead_ok s (by
    rw [hE.wr, hE.rsi]; exact in_sub hp.c_in (off := 12) (by decide)) (by
    rw [hE.rd, hE.wr, hE.r11]; exact in_rdwr (in_sub hp.p_in (off := 768) (by decide))) (by
    rw [hE.r11, hE.rsi]
    exact (hp.p_c.sub_left (Offset.sub_base (pp s₀) (d := 768) (n := 16) (k := 1024) (by decide))).sub_right
      (Offset.sub_base (cp s₀) (d := 12) (n := 4) (k := 16) (by decide)) |>.sep
      (Region.contains_self _ _) (Region.contains_self _ _)))
    fun t ⟨htM, ht0, htG, htX, htR, htW⟩ => ?_
  have hnum : (s.gpr .r8).setWidth 32 - 8 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 n := by
    rw [hv, BitVec.ofNat_add]
    change ((cb s₀).extractLsb' 0 32 + (BitVec.ofNat 32 n + 8)) - 8 = _
    rw [← BitVec.add_assoc, BitVec.add_sub_cancel]
  rw [hE.rsi, hnum] at htM
  have fct : Frame [cR s₀] s.mem t.mem := by
    rw [htM]
    exact (Frame.refl _ _).writeW List.mem_cons_self _
      (Offset.contains_base (cp s₀) (d := 12) (n := 4) (k := 16) (by decide) (by decide))
  have hcb : blockAt s.mem (cp s₀) = cb s₀ := blockAt_frame hE.frame (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_c.symm
    · exact hp.p_c.symm)
  have ct : blockAt t.mem (cp s₀) = Nat.repeat inc32 n (cb s₀) := by
    rw [htM]
    have hc := refreshCounter_ok s.mem (cp s₀) (cb s₀) 0 n hcb
    simpa only [Nat.zero_add] using hc
  rw [WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx t (by
    rw [ht0, hE.r11]; exact hE.mask) (by
    rw [htW, hE.wr, htG _ (by decide) (by decide), hE.rcx]; exact hp.y_in))
    fun u ⟨huM, huG, huR, huW, _⟩ => ?_
  rw [htG _ (by decide) (by decide), hE.rcx, htX _ (by decide) 0 (by decide)] at huM
  have fyu : Frame [yR s₀] t.mem u.mem := by
    rw [huM]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have fu : Frame [cR s₀, yR s₀] s.mem u.mem :=
    (fct.mono (by simp)).trans (fyu.mono (by simp))
  have py : ∀ r ∈ [cR s₀, yR s₀], (pR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.p_c
    · exact hp.p_y
  have saved : ∀ d, d + 8 ≤ 1024 → u.mem.readW (pp s₀ + BitVec.ofNat 64 d) 64 =
      s.mem.readW (pp s₀ + BitVec.ofNat 64 d) 64 := fun d hd =>
    fu.readW (r := pR s₀) (Offset.contains_base _ hd (by omega)) py (by decide)
  have ur11 : u.gpr .r11 = pp s₀ := by rw [huG, htG _ (by decide) (by decide), hE.r11]
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨VOp.exec .vzeroupper u, rfl, ?_⟩
  rw [WP.block_nil_iff]
  refine WP.mono (restoreEntry_ok (VOp.exec .vzeroupper u)
    (by change InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 808) 8
        rw [huR, huW, htR, htW, hE.rd, hE.wr, ur11]
        exact in_rdwr (in_sub hp.p_in (off := 808) (by decide)))
    (by change InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 800) 8
        rw [huR, huW, htR, htW, hE.rd, hE.wr, ur11]
        exact in_rdwr (in_sub hp.p_in (off := 800) (by decide))))
    fun v ⟨hv8, hvi, hvG, hvM, hvR, hvW⟩ => ?_
  change v.gpr .r8 = u.mem.readW (u.gpr .r11 + BitVec.ofNat 64 808) 64 at hv8
  change v.gpr .rsi = u.mem.readW (u.gpr .r11 + BitVec.ofNat 64 800) 64 at hvi
  change v.mem = u.mem at hvM
  refine ⟨?_, ?_, hvM ▸ fu, ?_, ?_, ?_⟩
  · rw [hvM]
    exact (blockAt_frame fyu (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.c_y)).trans ct
  · rw [hvM, huM, VG.Proof.Gcm.X86_64.blockAt_store]
  · intro r hax hdx h9 h10
    by_cases h8 : r = .r8
    · subst r
      rw [hv8, ur11, saved 808 (by decide)]; exact hE.data
    by_cases hi : r = .rsi
    · subst r
      rw [hvi, ur11, saved 800 (by decide)]; exact hE.rounds
    · rw [hvG r h8 hi]
      change u.gpr r = s₀.gpr r
      rw [huG, htG r hax h8]
      exact hE.other r hax hdx h8 h9 h10 hi
  · exact hvR.trans (huR.trans (htR.trans hE.rd))
  · exact hvW.trans (huW.trans (htW.trans hE.wr))

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## SetupPrefix -/
section

/-! # Establishing the batch environment from the saved entry state -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (setupC)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt)

theorem setupPrefix_ok {s₀ : State} (hp : SPre s₀) (s : State) (P : Nat → Block)
    (hg : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r)
    (hm : Frame [pR s₀] s₀.mem s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h0 : s.lane .xmm0 0 = revMask) (h1 : s.lane .xmm1 0 = poly)
    (hP : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 = P k) :
    WP isa (.block (setupC ++ metaCode ++ counterHead)) s fun t =>
      Env s₀ P t ∧ Frame [pR s₀] s₀.mem t.mem ∧
      t.gpr .rdx = dp s₀ ∧ t.gpr .r9 = s₀.gpr .r9 ∧
      (t.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 ∧
      XBinOp.eval .pshufb (t.lane .xmm7 0) revMask = cb s₀ ∧ t.lane .xmm2 0 = y₀ s₀ := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupC_ok s h0 (by rw [hwr, hg _ (by decide)]; exact hp.y_in))
    fun u ⟨hyu, hu10, hax, hdx, hgu, hxu, hmu, hrdu, hwru⟩ => ?_
  have gu : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → u.gpr r = s₀.gpr r :=
    fun r hax hdx h10 => (hgu r hax hdx h10).trans (hg r hax)
  have gu11 : u.gpr .r11 = pp s₀ := gu _ (by decide) (by decide) (by decide)
  have gu10 : u.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀) := by
    rw [hu10, hg _ (by decide), hg _ (by decide)]
  have guax : u.gpr .rax = cp s₀ := hax.trans (hg _ (by decide))
  have gudx : u.gpr .rdx = dp s₀ := hdx.trans (hg _ (by decide))
  have hmu0 : Frame [pR s₀] s₀.mem u.mem := hmu ▸ hm
  rw [WP.block_append_iff]
  refine WP.mono (meta_ok u
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 768) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 784) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 808) (by decide))
    (by rw [hwru, hwr, gu11]; exact in_sub hp.p_in (off := 800) (by decide)))
    fun v ⟨hmv, hgv, hxv, hrdv, hwrv⟩ => ?_
  have fm : Frame [metaR u] u.mem v.mem := hmv ▸ meta_frame u
  have fmv : Frame [pR s₀] s₀.mem v.mem := hmu0.trans (fm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨pR s₀, List.mem_singleton_self _, by
      simpa only [metaR, gu11] using (Offset.sub_base (pp s₀) (d := 768) (n := 48) (k := 1024) (by decide))⟩)
  have gvax : v.gpr .rax = cp s₀ := by rw [hgv]; exact guax
  have vcb : blockAt v.mem (cp s₀) = cb s₀ := blockAt_frame fmv (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.p_c.symm)
  refine WP.mono (counterHead_ok v (by
    rw [hrdv, hwrv, hrdu, hwru, hrd, hwr, gvax, BitVec.add_zero]
    exact in_rdwr hp.c_in) (by
    rw [hrdv, hwrv, hrdu, hwru, hrd, hwr, gvax]
    exact in_rdwr (in_sub hp.c_in (off := 12) (by decide))))
    fun t ⟨hti, ht8, ht7, hgt, hxt, hmt, hrdt, hwrt⟩ => ?_
  have gt : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → r ≠ .rsi → r ≠ .r8 →
      t.gpr r = s₀.gpr r := by
    intro r hax hdx h10 hsi h8
    rw [hgt r hsi h8, hgv]; exact gu r hax hdx h10
  have ft : Frame [pR s₀] s₀.mem t.mem := hmt ▸ fmv
  have ep : Env s₀ P t := by
    constructor
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [hti, gvax]
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [hgt _ (by decide) (by decide), hgv]; exact gu10
    · intro r hax hdx h8 h9 h10 hsi; exact gt r hax hdx h10 hsi h8
    · exact ft.mono (by simp)
    · intro k hk
      rw [hmt]
      have he : v.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 =
          u.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 :=
        fm.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (128 + 16 * k), 16⟩)
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
          (by intro r hr; simp only [List.mem_singleton] at hr; subst r
              rw [metaR, gu11]
              exact Offset.disjoint (pp s₀) (by omega) (by omega) (by decide)) (by decide)
      rw [he, hmu]; exact hP k hk
    · rw [hmt, hmv, ← gu11]
      exact (meta_mask u).trans ((hxu _ (by decide) 0 (by decide)).trans h0)
    · rw [hmt, hmv, ← gu11]
      exact (meta_poly u).trans ((hxu _ (by decide) 0 (by decide)).trans h1)
    · rw [hmt, hmv, ← gu11]
      exact (meta_rounds u).trans (gu _ (by decide) (by decide) (by decide))
    · rw [hmt, hmv, ← gu11]
      exact (meta_data u).trans gudx
    · exact hrdt.trans (hrdv.trans (hrdu.trans hrd))
    · exact hwrt.trans (hwrv.trans (hwru.trans hwr))
  refine ⟨ep, ft, ?_, gt _ (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_⟩
  · rw [hgt _ (by decide) (by decide), hgv]; exact gudx
  · rw [ht8, gvax, VG.Proof.Aes.X86_64.icb_lo, vcb]
  · rw [ht7, gvax, BitVec.add_zero, ← blockAt_eq]; exact vcb
  · rw [hxt _ (by decide), hxv, hyu, hg _ (by decide)]
    exact blockAt_frame hm (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.p_y.symm)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Seeds -/
section

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

end

/-! ## SetupTail -/
section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepCounter)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block)

def counterTail : List Instr :=
  (List.range 8).map (fun i => .vmovdquStore .l128 (at_ .r11 (640 + 16 * i)) .xmm7) ++
  (List.range 8).flatMap prepCounter ++ [.alu32 .add .r8 (.imm 8)]

theorem counterTail_ok {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (hE : Env s₀ P s) (hC : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32) :
    WP isa (.block counterTail) s fun t => Env s₀ P t ∧ Templates s₀ 0 0 t.mem ∧
      (t.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + 8 ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      (∀ r l, t.lane r l = s.lane r l) ∧ Frame [counterR s₀] s.mem t.mem := by
  rw [counterTail, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyTemplates_ok hp s hE hC 8 (by decide)) fun u ⟨hu, hc, hf, hm⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (seedTemplates_ok hp u hu (by
    intro i hi; simpa only [Nat.not_lt_zero, ite_false, Nat.repeat] using hc i hi)
    (by rw [hf.gpr .r8 (by decide)]; exact hv) 8 (by decide)) fun v ⟨hvE, hvT, hvF, hvM⟩ => ?_
  refine WP.mono (bump_ok v) fun t ⟨ht8, htG, htM, htX, htR, htW⟩ => ?_
  refine ⟨hvE.move (fun r _ _ h8 _ => htG r h8) htM htR htW,
    htM ▸ hvT.done, ?_, ?_, ?_, htM ▸ hm.trans hvM⟩
  · rw [ht8, hvF.gpr .r8 (by decide), hf.gpr .r8 (by decide), hv]
  · intro r hax h8; rw [htG r h8, hvF.gpr r hax, hf.gpr r hax]
  · intro r l; rw [htX, hvF.lane, hf.lane]

end VG.Proof.Gcm.X86_64.StitchAvx8

end
