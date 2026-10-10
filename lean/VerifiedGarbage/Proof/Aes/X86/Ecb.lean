import VerifiedGarbage.Proof.Aes.X86.Decrypt
import VerifiedGarbage.Proof.Aes.X86.Group
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES on whole blocks on x86 (32-bit): the groups

A group of `blocks` loads two blocks of the data (or the last one, into
both halves) into slots `0 … 7`, runs a transformation of two blocks
(`encrypt2` or `decrypt2`, whose proofs give `CryptOk`), and stores the
results back in place. The data pointer and the count stay in the scratch
buffer between the phases, as in `vg_aes_ctr32` (`Group.lean`). The data's
invariant (`EcbInv`) says that the first `k` blocks hold the transformation
of the original ones, and the others are still the original ones.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.X86.Wp (Upd Fupd wp_mov wp_addi wp_sub wp_subi wp_cmpi wp_test wp_ldm wp_stm toNat_ofNat_lt
  ofNat_beq_zero)

/-- What a transformation of two blocks does: `f R w` to each, with the
round keys as `EncPre` has them. -/
def CryptOk (crypt2 : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}, EncPre s₀ R w →
    InRel (Q s₀) S → WP isa crypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => f R w (S b))

theorem encrypt2_cryptOk : CryptOk encrypt2 Spec.Aes.cipher := fun hp hin => encrypt2_ok hp hin
theorem decrypt2_cryptOk : CryptOk decrypt2 Spec.Aes.invCipher := fun hp hin => decrypt2_ok hp hin

/-! ## The data -/

/-- The data after `k` blocks: the first `k` of the `n` blocks at `D` are
`F`'s, the others are still `m₀`'s. -/
def EcbInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem ecbInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) (hk : n ≤ k) (hk' : n ≤ k') : EcbInv m₀ m D n k' F := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * k' by omega_arith)]

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : EcbInv m₀ m D n k F) : EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi

/-- Before `k` blocks are stored, a block not yet stored is still `m₀`'s. -/
theorem ecbInv_orig {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) {j : Nat} (hj : k ≤ j) (hjn : j < n) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_right (show ¬ 16 * j + i < 16 * k by omega_arith)]

/-- `c` more blocks stored. -/
theorem ecbInv_store {m₀ m m' : Mem} {D : Addr} {n k c : Nat} {F : Nat → Spec.Aes.State}
    (hn : 16 * n < 2 ^ 64) (hkc : k + c ≤ n) (h : EcbInv m₀ m D n k F)
    (hfr : Frame [⟨D + BitVec.ofNat 64 (16 * k), 16 * c⟩] m m')
    (hv : ∀ i < 16 * c, m' (D + BitVec.ofNat 64 (16 * k + i)) = (F (k + i / 16)).getD (i % 16) 0) :
    EcbInv m₀ m' D n (k + c) F := by
  intro i hi
  by_cases h1 : 16 * k ≤ i ∧ i < 16 * (k + c)
  · rw [ite_eq_left (by omega_arith)]
    have := hv (i - 16 * k) (by omega_arith)
    rwa [show 16 * k + (i - 16 * k) = i by omega_arith, show k + (i - 16 * k) / 16 = i / 16 by omega_arith,
      show (i - 16 * k) % 16 = i % 16 by omega_arith] at this
  · rw [hfr _ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains]
      rw [off_toNat D (by omega_arith) (by omega_arith)]
      split <;> omega_arith), h i hi]
    by_cases h2 : i < 16 * k
    · rw [ite_eq_left h2, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h2, ite_eq_right (by omega_arith)]

/-- The slots holding the words of two blocks, at `a 0` and `a 1`. -/
theorem inRel_of_words {Q' : Nat → BitVec 32} {m : Mem} {a : Nat → Addr}
    (h : ∀ b < 2, ∀ v < 4, Q' (2 * v + b) = m.readW (a b + BitVec.ofNat 64 (4 * v)) 32) :
    InRel Q' (fun b => Spec.Aes.stateAt m (a b)) := by
  intro b hb i hi j hj
  rw [show b + 2 * (i / 4) = 2 * (i / 4) + b by omega_arith, h b hb (i / 4) (by omega_arith),
    readW_bit _ _ (by omega_arith) hj, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * (i / 4) + i % 4 = i by omega_arith, getD_eq _ hi]
  simp [Spec.Aes.stateAt]

/-- The bytes of the words of block `b`, when the slots hold `T`. -/
theorem byte_of_inRel {Q' : Nat → BitVec 32} {T : Nat → Spec.Aes.State} (h : InRel Q' T) {b t : Nat}
    (hb : b < 2) (ht : t < 16) :
    (Q' (2 * (t / 4) + b)).extractLsb' (8 * (t % 4)) 8 = (T b).getD t 0 :=
  byte_ext fun j hj => by
    rw [BitVec.getLsbD_extractLsb', show 2 * (t / 4) + b = b + 2 * (t / 4) by omega_arith, h b hb t ht j hj]
    simp [hj]

/-! ## Where the data is -/

theorem addr_off {Dp : BitVec 32} {a o : Nat} (h : Dp.toNat + a + o < 2 ^ 32) :
    addr (Dp + BitVec.ofNat 32 a) o = Dp.setWidth 64 + BitVec.ofNat 64 (a + o) := by
  rw [addr_add, addr_eq (by omega_arith)]

/-- The blocks a group loads: two, or the last one twice. -/
def blk (n g b : Nat) : Nat := 2 * g + min b (n - 2 * g - 1)

theorem blk_lt {n g b : Nat} (hg : 2 * g < n) : 2 * g ≤ blk n g b ∧ blk n g b < n := by
  simp only [blk]; omega_arith

/-! ## The load phase -/

def loadCfg2 : Cfg := { base := sb, slots := 8, ext := .esi, exts := 8 }
def loadCfg1 : Cfg := { base := sb, slots := 8, ext := .esi, exts := 4 }

def load2Post (e : Env Nat) : Bool :=
  (List.range 2).all fun b => (List.range 4).all fun v => e.slot (2 * v + b) == some (4 * b + v)

def load1Post (e : Env Nat) : Bool :=
  (List.range 4).all fun v => e.slot (2 * v) == some v && e.slot (2 * v + 1) == some v

theorem load2_check :
    check (names 32) loadCfg2 (fun k => some k) (loadBlock 0 ++ loadBlock 1)
      { reg := fun _ => none, slot := fun _ => none } load2Post = true := by
  decide +kernel

theorem load1_check :
    check (names 32) loadCfg1 (fun k => some k) loadOne
      { reg := fun _ => none, slot := fun _ => none } load1Post = true := by
  decide +kernel

theorem names_run {c : Cfg} {is : List Instr} {post : Env Nat → Bool} {s : State}
    (hchk : check (names 32) c (fun k => some k) is { reg := fun _ => none, slot := fun _ => none } post = true)
    (hok : Ok c s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (NameRel (fun k => s.mem.readW (wordAddr (s.gpr c.ext) k) 32)) c (fun k => some k) e' s s'
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (NameRel fun k => s.mem.readW (wordAddr (s.gpr c.ext) k) 32) c (fun k => some k)
      { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound _) hok hrel he
  exact ⟨e', s', hpost, hs', p⟩

/-- The loads of a group: slot `2v + b` gets word `v` of block `blk n g b`. -/
theorem loads_ok {s : State} {B Dp : BitVec 32} {n g : Nat} (hc : 2 * g < n)
    (hb : s.gpr sb = B) (hesi : s.gpr .esi = Dp + BitVec.ofNat 32 (32 * g))
    (hfitD : Dp.toNat + 16 * n ≤ 2 ^ 32) (hdat : reg32 Dp (16 * n) ∈ s.wr)
    (hfitB : B.toNat + 2048 ≤ 2 ^ 32) (hscr : reg32 B 2048 ∈ s.wr)
    (hsep : (reg32 Dp (16 * n)).Disjoint (reg32 B 2048))
    (hcf : s.cf = some (decide (n - 2 * g < 2))) {P : State → Prop}
    (h : ∀ s', (∀ b < 2, ∀ v < 4, Q s' (2 * v + b) =
        s.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 (16 * blk n g b + 4 * v)) 32) →
      Frame [reg32 B 32] s.mem s'.mem → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.ite .ae (.block (loadBlock 0 ++ loadBlock 1)) (.block loadOne)) s P := by
  have hslots : ∀ (c : Cfg), c.base = sb → c.slots = 8 → c.ext = .esi → c.exts ≤ 8 →
      16 * (2 * g) + 4 * c.exts ≤ 16 * n → Ok c s := fun c h1 h2 h3 h4 h5 =>
    Ok.of_off (r := reg32 B 2048) (r' := reg32 Dp (16 * n)) (b := B) (b' := Dp) (off := 0)
      (off' := 32 * g) (n := 2048) (n' := 16 * n) hscr rfl hfitB (Nat.le_refl _)
      (by rw [h1, hb]; simp) (by rw [h2]; omega_arith) (List.mem_append_right _ hdat) rfl hfitD (Nat.le_refl _)
      (by rw [h3, hesi]) (by omega_arith) (.inr (.inr (.inl hsep.symm)))
  have hfr : ∀ (c : Cfg), c.base = sb → c.slots = 8 → slotRegion c s = reg32 B 32 := fun c h1 h2 => by
    simp only [slotRegion, h1, h2, hb]
  have ea : ∀ k, 32 * g + 4 * k + 4 ≤ 16 * n →
      wordAddr (s.gpr .esi) k = Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 4 * k) := by
    intro k hk
    simp only [wordAddr, hesi]
    exact addr_off (by omega_arith)
  refine WP.ite (!decide (n - 2 * g < 2)) (by simp [X86.eval, hcf]) (fun hb2 => ?_) (fun hb2 => ?_)
  · have h2 : 2 ≤ n - 2 * g := by simpa using hb2
    obtain ⟨e', s', hpost, hs', p⟩ := names_run load2_check (hslots loadCfg2 rfl rfl rfl (by decide)
      (by simp [loadCfg2]; omega_arith))
    refine WP.of_runBlock ⟨s', hs', h s' (fun b hb' v hv => ?_) (hfr loadCfg2 rfl rfl ▸ p.frame)
      (fun r hr => p.other r ?_) p.rd p.wr⟩
    · have := List.all_eq_true.mp hpost b (List.mem_range.mpr hb')
      have := List.all_eq_true.mp this v (List.mem_range.mpr hv)
      simp only [beq_iff_eq] at this
      have e := p.rel.slot _ _ (by simp [loadCfg2]; omega_arith) this
      simp only [NameRel, loadCfg2] at e
      rw [Q, e, ea _ (by omega_arith)]
      simp only [blk, show min b (n - 2 * g - 1) = b by omega_arith]
      exact congrArg (fun x => s.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 x) 32) (by omega_arith)
    · have : ((loadBlock 0 ++ loadBlock 1).all fun i => i.dst != some r) = true := by
        revert hr; cases r <;> decide
      simp [this]
  · have h1 : n - 2 * g = 1 := by simp at hb2; omega_arith
    obtain ⟨e', s', hpost, hs', p⟩ := names_run load1_check (hslots loadCfg1 rfl rfl rfl (by decide)
      (by simp [loadCfg1]; omega_arith))
    refine WP.of_runBlock ⟨s', hs', h s' (fun b hb' v hv => ?_) (hfr loadCfg1 rfl rfl ▸ p.frame)
      (fun r hr => p.other r ?_) p.rd p.wr⟩
    · have := List.all_eq_true.mp hpost v (List.mem_range.mpr hv)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      have e := p.rel.slot (2 * v + b) _ (by simp [loadCfg1]; omega_arith)
        (by rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl; exacts [this.1, this.2])
      simp only [NameRel, loadCfg1] at e
      rw [Q, e, ea _ (by omega_arith)]
      simp only [blk, show min b (n - 2 * g - 1) = 0 by omega_arith]
      exact congrArg (fun x => s.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 x) 32) (by omega_arith)
    · have : (loadOne.all fun i => i.dst != some r) = true := by
        revert hr; cases r <;> decide
      simp [this]

/-! ## The store phase -/

def storeCfg2 : Cfg := { base := .esi, slots := 8, ext := sb, exts := 8 }
def storeCfg1 : Cfg := { base := .esi, slots := 4, ext := sb, exts := 8 }

def store2Post (e : Env Nat) : Bool :=
  (List.range 2).all fun b => (List.range 4).all fun v => e.slot (4 * b + v) == some (2 * v + b)

def store1Post (e : Env Nat) : Bool := (List.range 4).all fun v => e.slot v == some (2 * v)

theorem store2_check :
    check (names 32) storeCfg2 (fun k => some k) (storeBlock 0 ++ storeBlock 1)
      { reg := fun _ => none, slot := fun _ => none } store2Post = true := by
  decide +kernel

theorem store1_check :
    check (names 32) storeCfg1 (fun k => some k) (storeBlock 0)
      { reg := fun _ => none, slot := fun _ => none } store1Post = true := by
  decide +kernel

/-- What the stores of `c` blocks leave: the words of the slots at the data,
and nothing else changed. -/
theorem stores_bytes {m' : Mem} {Dp : BitVec 32} {g c : Nat} {T : Nat → Spec.Aes.State}
    {Q' : Nat → BitVec 32} (hin : InRel Q' T) (hc : c ≤ 2)
    (hw : ∀ b < c, ∀ v < 4, m'.readW (Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 16 * b + 4 * v)) 32 =
      Q' (2 * v + b)) :
    ∀ i < 16 * c, m' (Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g) + i)) = (T (i / 16)).getD (i % 16) 0 := by
  intro i hi
  have hb : i / 16 < 2 := by omega_arith
  rw [← byte_of_inRel hin hb (Nat.mod_lt _ (by decide)), ← hw (i / 16) (by omega_arith) (i % 16 / 4) (by omega_arith),
    ← Mem.readW_byte _ _ (by omega_arith : i % 16 % 4 < 4), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 3; omega_arith

/-- The stores of a group: `c` blocks (two, or the last one) from the
slots to the data, then on to the next blocks. -/
theorem stores_ok {s : State} {B Dp : BitVec 32} {n g : Nat} {T : Nat → Spec.Aes.State}
    (hc : 2 * g < n) (hb : s.gpr sb = B) (hesi : s.gpr .esi = Dp + BitVec.ofNat 32 (32 * g))
    (hebp : s.gpr .ebp = BitVec.ofNat 32 (n - 2 * g))
    (hfitD : Dp.toNat + 16 * n ≤ 2 ^ 32) (hdat : reg32 Dp (16 * n) ∈ s.wr)
    (hfitB : B.toNat + 2048 ≤ 2 ^ 32) (hscr : reg32 B 2048 ∈ s.wr)
    (hsep : (reg32 Dp (16 * n)).Disjoint (reg32 B 2048))
    (hcf : s.cf = some (decide (n - 2 * g < 2))) (hin : InRel (Q s) T) {P : State → Prop}
    (h : ∀ s', (∀ i < 16 * min 2 (n - 2 * g),
        s'.mem (Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g) + i)) = (T (i / 16)).getD (i % 16) 0) →
      Frame [⟨Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g)), 16 * min 2 (n - 2 * g)⟩] s.mem s'.mem →
      (∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.gpr .ebp = BitVec.ofNat 32 (n - 2 * g - min 2 (n - 2 * g)) →
      s'.gpr .esi = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∨ n - 2 * g - min 2 (n - 2 * g) = 0 →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.ite .ae (.block storeTwo) (.block storeOne)) s P := by
  have hslots : ∀ (c : Cfg), c.base = .esi → c.ext = sb → c.exts = 8 →
      32 * g + 4 * c.slots ≤ 16 * n → Ok c s := fun c h1 h2 h3 h5 =>
    Ok.of_off (r := reg32 Dp (16 * n)) (r' := reg32 B 2048) (b := Dp) (b' := B) (off := 32 * g)
      (off' := 0) (n := 16 * n) (n' := 2048) hdat rfl hfitD (Nat.le_refl _)
      (by rw [h1, hesi]) h5 (List.mem_append_right _ hscr) rfl hfitB (Nat.le_refl _)
      (by rw [h2, hb]; simp) (by rw [h3]; omega_arith) (.inr (.inr (.inl hsep)))
  have ea : ∀ k, 32 * g + 4 * k + 4 ≤ 16 * n →
      wordAddr (s.gpr .esi) k = Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 4 * k) := by
    intro k hk
    simp only [wordAddr, hesi]
    exact addr_off (by omega_arith)
  have hreg : ∀ (c : Cfg), c.base = .esi → 32 * g + 4 * c.slots ≤ 16 * n →
      slotRegion c s = ⟨Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g)), 4 * c.slots⟩ := by
    intro c h1 h2
    simp only [slotRegion, h1, hesi]
    rw [← addr_zero, addr_off (by omega_arith), Nat.add_zero, show 16 * (2 * g) = 32 * g by omega_arith]
  refine WP.ite (!decide (n - 2 * g < 2)) (by simp [X86.eval, hcf]) (fun hb2 => ?_) (fun hb2 => ?_)
  · have h2 : 2 ≤ n - 2 * g := by simpa using hb2
    rw [storeTwo, WP.block_append_iff (M := isa)]
    obtain ⟨e', s₁, hpost, hs₁, p⟩ := names_run store2_check (hslots storeCfg2 rfl rfl rfl
      (by simp [storeCfg2]; omega_arith))
    refine WP.of_runBlock ⟨s₁, hs₁, wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ _ _ => WP.block_nil ?_⟩
    have hw : ∀ b < 2, ∀ v < 4, s₁.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 16 * b + 4 * v)) 32 =
        Q s (2 * v + b) := by
      intro b hb' v hv
      have := List.all_eq_true.mp hpost b (List.mem_range.mpr hb')
      have := List.all_eq_true.mp this v (List.mem_range.mpr hv)
      simp only [beq_iff_eq] at this
      have e := p.rel.slot _ _ (by simp [storeCfg2]; omega_arith) this
      simp only [NameRel, storeCfg2] at e
      rw [show s₁.gpr .esi = s.gpr .esi from p.base] at e
      rw [show 32 * g + 16 * b + 4 * v = 32 * g + 4 * (4 * b + v) by omega_arith, ← ea _ (by omega_arith), e]
    have hmin : min 2 (n - 2 * g) = 2 := by omega_arith
    refine h s₃ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ ?_ (by rw [u₃.rd, u₂.rd, p.rd]) (by rw [u₃.wr, u₂.wr, p.wr])
    · rw [hmin, u₃.mem, u₂.mem]
      exact stores_bytes hin (by decide) hw
    · rw [hmin, u₃.mem, u₂.mem, show 16 * 2 = 4 * storeCfg2.slots from rfl, ← hreg storeCfg2 rfl (by simp [storeCfg2]; omega_arith)]; exact p.frame
    · rw [u₃.other r h3, u₂.other r h2, p.other r (by
        have : ((storeBlock 0 ++ storeBlock 1).all fun i => i.dst != some r) = true := by
          revert h1; cases r <;> decide
        simp [this])]
    · rw [hmin, u₃.gpr, u₂.other _ (by decide), p.other _ (by decide), hebp]
      have : n ≤ 2 ^ 28 := by omega_arith
      bv_omega
    · refine .inl ?_
      rw [u₃.other _ (by decide), u₂.gpr, p.other _ (by decide), hesi, BitVec.add_assoc,
        show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
  · have h1 : n - 2 * g = 1 := by simp at hb2; omega_arith
    rw [storeOne, WP.block_append_iff (M := isa)]
    obtain ⟨e', s₁, hpost, hs₁, p⟩ := names_run store1_check (hslots storeCfg1 rfl rfl rfl
      (by simp [storeCfg1]; omega_arith))
    refine WP.of_runBlock ⟨s₁, hs₁, wp_sub fun s₂ u₂ _ => WP.block_nil ?_⟩
    have hw : ∀ b < 1, ∀ v < 4, s₁.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 16 * b + 4 * v)) 32 =
        Q s (2 * v + b) := by
      intro b hb' v hv
      have := List.all_eq_true.mp hpost v (List.mem_range.mpr hv)
      simp only [beq_iff_eq] at this
      have e := p.rel.slot _ _ (by simp [storeCfg1]; omega_arith) this
      simp only [NameRel, storeCfg1] at e
      rw [show s₁.gpr .esi = s.gpr .esi from p.base] at e
      rw [show b = 0 by omega_arith, show 32 * g + 16 * 0 + 4 * v = 32 * g + 4 * v by omega_arith, ← ea _ (by omega_arith), e]
      rfl
    have hmin : min 2 (n - 2 * g) = 1 := by omega_arith
    refine h s₂ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ (.inr (by omega_arith)) (by rw [u₂.rd, p.rd]) (by rw [u₂.wr, p.wr])
    · rw [hmin, u₂.mem]
      exact stores_bytes hin (by decide) hw
    · rw [hmin, u₂.mem, show 16 * 1 = 4 * storeCfg1.slots from rfl, ← hreg storeCfg1 rfl (by simp [storeCfg1]; omega_arith)]; exact p.frame
    · rw [u₂.other r h3, p.other r (by
        have : ((storeBlock 0).all fun i => i.dst != some r) = true := by
          revert h1; cases r <;> decide
        simp [this])]
    · rw [hmin, u₂.gpr, BitVec.sub_self, h1]

/-- `groupLoad`: the data pointer to `esi`, the count to `ebp`, and CF set
if fewer than two blocks are left. -/
theorem groupLoad_wp {s : State} {B Dp : BitVec 32} {n g : Nat} (hb : s.gpr .edi = B)
    (hfitB : B.toNat + 2048 ≤ 2 ^ 32) (hscr : reg32 B 2048 ∈ s.wr)
    (hd : s.mem.readW (addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * g))
    (hn : s.mem.readW (addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * g)) (hn32 : n < 2 ^ 32) {P : State → Prop}
    (h : ∀ s', s'.gpr .esi = Dp + BitVec.ofNat 32 (32 * g) → s'.gpr .ebp = BitVec.ofNat 32 (n - 2 * g) →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.cf = some (decide (n - 2 * g < 2)) → P s') :
    WP isa (.block groupLoad) s P := by
  have hin : InRegions (s.rd ++ s.wr) (addr B dOff) 4 := in_rd (in_reg hscr hfitB (by decide) (by decide))
  have hin' : InRegions (s.rd ++ s.wr) (addr B nOff) 4 := in_rd (in_reg hscr hfitB (by decide) (by decide))
  refine wp_ldm (B := B) (o := dOff) hb hin fun s₁ u₁ => ?_
  refine wp_ldm (B := B) (o := nOff) (by rw [u₁.other _ (by decide)]; exact hb)
    (by rw [u₁.rd, u₁.wr]; exact hin') fun s₂ u₂ => ?_
  refine wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ?_
  refine h s₃ (by rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, hd])
    (by rw [u₃.gpr, u₂.gpr, u₁.mem, hn]) (fun r h1 h2 => by rw [u₃.gpr, u₂.other r h2, u₁.other r h1])
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) ?_
  rw [hcf, u₂.gpr, u₁.mem, hn, toNat_ofNat_lt (by omega_arith)]
  rfl

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `B` the scratch buffer, `Dp` the data (`n` blocks). -/
structure ESetup (s₂ : State) (B Dp : BitVec 32) (n R : Nat) (w : List Byte) : Prop where
  scr : reg32 B 2048 ∈ s₂.wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  dat : reg32 Dp (16 * n) ∈ s₂.wr
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  sep : (reg32 Dp (16 * n)).Disjoint (reg32 B 2048)
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  argIn : InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .esp) 8) 4
  argR : s₂.mem.readW (addr (s₂.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  argSep : Region.Disjoint ⟨addr (s₂.gpr .esp) 8, 4⟩ (reg32 B 2048)
  argSepD : Region.Disjoint ⟨addr (s₂.gpr .esp) 8, 4⟩ (reg32 Dp (16 * n))
  keys : KeysAt s₂.mem B R w

/-- The memory the groups write: the layers' slots, the data pointer and
the count, and the data. -/
abbrev eRegions (B Dp : BitVec 32) (n : Nat) : List Region :=
  [reg32 B 256, ⟨addr B dOff, 8⟩, reg32 Dp (16 * n)]

/-- The results: `f R w` of each block of `m₀`'s data. -/
def ecbOut (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr) (R : Nat)
    (w : List Byte) (j : Nat) : Spec.Aes.State :=
  f R w (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

/-- Before group `g`. -/
structure EInv (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (B Dp : BitVec 32) (n R : Nat) (w : List Byte) (g : Nat) (s : State) : Prop where
  hg : 2 * g < n
  base : s.gpr sb = B
  esp : s.gpr .esp = s₂.gpr .esp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (eRegions B Dp n) s₂.mem s.mem
  dslot : s.mem.readW (addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * g)
  nslot : s.mem.readW (addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * g)
  data : EcbInv m₀ s.mem (Dp.setWidth 64) n (2 * g) (ecbOut f m₀ (Dp.setWidth 64) R w)

/-- After the last group. -/
structure EDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (B Dp : BitVec 32) (n R : Nat) (w : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  esp : s.gpr .esp = s₂.gpr .esp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (eRegions B Dp n) s₂.mem s.mem
  data : EcbInv m₀ s.mem (Dp.setWidth 64) n n (ecbOut f m₀ (Dp.setWidth 64) R w)

section
variable {s₂ : State} {B Dp : BitVec 32} {n R : Nat} {w : List Byte}
  (hs : ESetup s₂ B Dp n R w)
include hs

/-- A part of the scratch buffer at offset `o` is apart from the regions the
groups write if it is beyond the slots and the data pointer and count. -/
theorem ESetup.edisj {o l : Nat} (h1 : 256 ≤ o) (h2 : o + l ≤ dOff ∨ dOff + 8 ≤ o) (h3 : o + l ≤ 2048) :
    ∀ r ∈ eRegions B Dp n, Region.Disjoint ⟨addr B o, l⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
    rw [← addr_zero]; exact part_disj hs.fitB h3 (by omega_arith) (.inr h1)
  · exact part_disj hs.fitB h3 (by simp only [dOff]; omega_arith) h2
  · exact (hs.sep.sub_right (part_sub_reg hs.fitB h3)).symm

theorem ESetup.argDisj : ∀ r ∈ eRegions B Dp n, Region.Disjoint ⟨addr (s₂.gpr .esp) 8, 4⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.argSep.sub_right (Region.sub_prefix (by omega_arith))
  · exact hs.argSep.sub_right (part_sub_reg hs.fitB (by simp only [dOff]; omega_arith))
  · exact hs.argSepD

/-- One group: from before group `g`, to after the last group (ZF set) or
before group `g + 1`. -/
theorem ecbGroup_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {m₀ : Mem} {g : Nat} {s : State} (hi : EInv f m₀ s₂ B Dp n R w g s) :
    WP isa (blockGroup crypt2) s fun s' => (s'.zf = some true ∧ EDone f m₀ s₂ B Dp n R w s') ∨
      (s'.zf = some false ∧ EInv f m₀ s₂ B Dp n R w (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hfitB := hs.fitB
  have hfitD := hs.fitD
  have hg := hi.hg
  have hn32 : n < 2 ^ 32 := by omega_arith
  have hscr : reg32 B 2048 ∈ s.wr := hi.wr ▸ hs.scr
  have hdat : reg32 Dp (16 * n) ∈ s.wr := hi.wr ▸ hs.dat
  let D := Dp.setWidth 64
  let F := ecbOut f m₀ D R w
  have d32 : ∀ r ∈ [reg32 B 32], Region.Disjoint (reg32 Dp (16 * n)) r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  have d256 : ∀ r ∈ [reg32 B 256], Region.Disjoint (reg32 Dp (16 * n)) r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  have hn64 : 16 * n < 2 ^ 64 := by omega_arith
  -- Reads of the scratch buffer beyond the slots, through the writes of the slots.
  have slotFar : ∀ {m m' : Mem} {N : Nat}, N ≤ 256 → Frame [reg32 B N] m m' → ∀ o, 256 ≤ o → o + 4 ≤ 2048 →
      m'.readW (addr B o) 32 = m.readW (addr B o) 32 := fun hN hf o h1 h2 =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint _ ⟨B.setWidth 64, _⟩
      rw [← addr_zero]; exact part_disj hfitB h2 (by omega_arith) (.inr (by omega_arith))) (by decide)
  unfold blockGroup loadGroup
  refine WP.seq (WP.seq (groupLoad_wp hi.base hfitB hscr hi.dslot hi.nslot hn32
    fun s₁ esi₁ ebp₁ g₁ m₁ rd₁ wr₁ cf₁ => ?_))
  have hb₁ : s₁.gpr sb = B := (g₁ sb (by decide) (by decide)).trans hi.base
  refine loads_ok hg hb₁ esi₁ hfitD (wr₁ ▸ hdat) hfitB (wr₁ ▸ hscr) hs.sep cf₁
    fun s₃ q₃ f₃ g₃ rd₃ wr₃ => ?_
  rw [m₁] at q₃ f₃
  have keep₃ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 =>
    (g₃ r h1).trans (g₁ r h2 h3)
  have hb₃ : s₃.gpr sb = B := (keep₃ sb (by decide) (by decide) (by decide)).trans hi.base
  have hesp₃ : s₃.gpr .esp = s₂.gpr .esp := (keep₃ _ (by decide) (by decide) (by decide)).trans hi.esp
  have hf₃ : Frame (eRegions B Dp n) s₂.mem s₃.mem :=
    hi.frame.trans (f₃.sub fun r hr => ⟨reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩)
  have hp : EncPre s₃ R w :=
    { scr := by rw [hb₃, wr₃, wr₁]; exact hscr
      fit := by rw [hb₃]; exact hfitB
      rounds := hs.rounds
      argIn := by rw [rd₃, wr₃, rd₁, wr₁, hi.rd, hi.wr, hesp₃]; exact hs.argIn
      argR := by
        rw [hesp₃, ← hs.argR]
        exact hf₃.readW (Region.contains_self _ _) hs.argDisj (by decide)
      argSep := by rw [hesp₃, hb₃]; exact hs.argSep.sub_right (Region.sub_prefix (by omega_arith))
      keys := by
        rw [hb₃]
        intro j hj
        refine keyRel_congr (hs.keys j hj) fun k hk => ?_
        have := keyOff_le (j := j) hR
        exact hf₃.readW (Region.contains_self _ _)
          (hs.edisj (by simp only [lastKey] at this; omega_arith) (.inr (by simp only [dOff, lastKey] at this ⊢; omega_arith))
            (by simp only [lastKey] at this; omega_arith)) (by decide) }
  let S : Nat → Spec.Aes.State := fun b => Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * blk n g b))
  have hin : InRel (Q s₃) S := by
    have h := inRel_of_words (Q' := Q s₃) (m := s.mem) (a := fun b => D + BitVec.ofNat 64 (16 * blk n g b))
      (fun b hb v hv => by rw [q₃ b hb v hv, BitVec.add_assoc, ← BitVec.ofNat_add])
    have e : (fun b => Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16 * blk n g b))) = S := by
      funext b
      have := blk_lt (b := b) hg
      exact ecbInv_orig hi.data this.1 this.2
    rwa [e] at h
  refine WP.seq (WP.mono (hcr hp hin) fun s₄ ⟨hc₄, hin₄⟩ => ?_)
  have fr₄ := hc₄.frame
  rw [hb₃] at fr₄
  have hb₄ : s₄.gpr .edi = B := hc₄.base.trans hb₃
  have hesp₄ : s₄.gpr .esp = s₂.gpr .esp := hc₄.esp.trans hesp₃
  have far₄ : ∀ o, 256 ≤ o → o + 4 ≤ 2048 → s₄.mem.readW (addr B o) 32 = s.mem.readW (addr B o) 32 :=
    fun o h1 h2 => (slotFar (Nat.le_refl _) fr₄ o h1 h2).trans (slotFar (by omega_arith) f₃ o h1 h2)
  have data₄ : EcbInv m₀ s₄.mem D n (2 * g) F :=
    ecbInv_frame fr₄ d256 hn64 (ecbInv_frame f₃ d32 hn64 hi.data)
  -- The store phase.
  unfold storeGroup
  refine WP.seq (groupLoad_wp hb₄ hfitB (by rw [hc₄.wr, wr₃, wr₁]; exact hscr)
    (by rw [far₄ _ (by decide) (by decide)]; exact hi.dslot)
    (by rw [far₄ _ (by decide) (by decide)]; exact hi.nslot) hn32
    fun s₅ esi₅ ebp₅ g₅ m₅ rd₅ wr₅ cf₅ => ?_)
  have hb₅ : s₅.gpr sb = B := (g₅ sb (by decide) (by decide)).trans hb₄
  have hq₅ : Q s₅ = Q s₄ := Q_congr (g₅ sb (by decide) (by decide)) m₅
  have wr₅' : s₅.wr = s₂.wr := by rw [wr₅, hc₄.wr, wr₃, wr₁, hi.wr]
  refine WP.seq (stores_ok (T := fun b => f R w (S b)) hg hb₅ esi₅ ebp₅ hfitD (wr₅' ▸ hs.dat) hfitB
    (wr₅' ▸ hs.scr) hs.sep cf₅ (by rw [hq₅]; exact hin₄)
    fun s₆ v₆ f₆ g₆ ebp₆ esi₆ rd₆ wr₆ => ?_)
  rw [m₅] at f₆
  have hc : min 2 (n - 2 * g) ≤ 2 ∧ 2 * g + min 2 (n - 2 * g) ≤ n := by omega_arith
  have hsub : (⟨D + BitVec.ofNat 64 (16 * (2 * g)), 16 * min 2 (n - 2 * g)⟩ : Region).Sub
      (reg32 Dp (16 * n)) := Offset.sub_base _ (by omega_arith)
  have data₆ : EcbInv m₀ s₆.mem D n (2 * g + min 2 (n - 2 * g)) F := by
    refine ecbInv_store hn64 hc.2 data₄ f₆ fun i hi' => ?_
    refine (v₆ i hi').trans ?_
    have e : blk n g (i / 16) = 2 * g + i / 16 := by simp only [blk]; omega_arith
    simp only [F, ecbOut, S, e]
  have hesi₆ : s₆.gpr .edi = B := by rw [g₆ _ (by decide) (by decide) (by decide)]; exact hb₅
  have hin₆ : ∀ o, o + 4 ≤ 2048 → InRegions s₆.wr (addr B o) 4 := fun o ho => by
    rw [wr₆, wr₅']; exact in_reg hs.scr hfitB ho (by decide)
  refine wp_stm hesi₆ (hin₆ dOff (by decide)) fun s₇ u₇ => ?_
  refine wp_stm ((congrFun u₇.gpr .edi).trans hesi₆) (u₇.wr ▸ hin₆ nOff (by decide))
    fun s₈ u₈ => wp_test fun s₉ u₉ hz => WP.block_nil ?_
  have fr : Frame [⟨addr B dOff, 8⟩] s₆.mem s₉.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem]
    have hm : (⟨addr B dOff, 8⟩ : Region) ∈ [⟨addr B dOff, 8⟩] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (part_contains hfitB (by decide) (by decide) (by decide) (by decide))).writeW
      hm _ (part_contains hfitB (by decide) (by decide) (by decide) (by decide))
  have dsj : ∀ r ∈ [(⟨addr B dOff, 8⟩ : Region)], Region.Disjoint (reg32 Dp (16 * n)) r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (part_sub_reg hfitB (by decide))
  have data₉ := ecbInv_frame fr dsj hn64 data₆
  have hds : s₉.mem.readW (addr B dOff) 32 = s₆.gpr .esi := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₇.gpr, rd_wr_ne hfitB _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), Mem.readW_writeW_self32]
  have hns : s₉.mem.readW (addr B nOff) 32 = s₆.gpr .ebp := by
    rw [u₉.mem, u₈.mem, u₇.gpr, u₇.mem, Mem.readW_writeW_self32]
  have keep₉ : ∀ r, r ∉ tmpRegs → r ≠ .esi → s₉.gpr r = s.gpr r := fun r h1 h2 => by
    have h3 : r ≠ .eax := fun h => h1 (h ▸ by decide)
    have h4 : r ≠ .ebp := fun h => h1 (h ▸ by decide)
    rw [u₉.gpr, u₈.gpr, u₇.gpr, g₆ r h3 h2 h4, g₅ r h2 h4, hc₄.keep r h1 h2, keep₃ r h3 h2 h4]
  have base' : s₉.gpr sb = B := (keep₉ sb (by decide) (by decide)).trans hi.base
  have esp' : s₉.gpr .esp = s₂.gpr .esp := (keep₉ .esp (by decide) (by decide)).trans hi.esp
  have rd' : s₉.rd = s₂.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, hc₄.rd, rd₃, rd₁, hi.rd]
  have wr' : s₉.wr = s₂.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅']
  have frame' : Frame (eRegions B Dp n) s₂.mem s₉.mem := by
    refine hf₃.trans ((fr₄.sub fun r hr => ⟨reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩).trans
      (?_ : Frame _ s₄.mem s₉.mem))
    refine (f₆.sub fun r hr => ⟨reg32 Dp (16 * n),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), by
      simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩).trans
      (fr.sub fun r hr => ⟨⟨addr B dOff, 8⟩, List.mem_cons_of_mem _ (List.mem_cons_self ..), by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  rw [hz, u₈.gpr, u₇.gpr, ebp₆, BitVec.and_self, ofNat_beq_zero (by omega_arith)]
  by_cases hl : n - 2 * g - min 2 (n - 2 * g) = 0
  · refine .inl ⟨by rw [hl]; rfl, base', esp', rd', wr', frame', ecbInv_mono data₉ (by omega_arith) (Nat.le_refl _)⟩
  · have hm2 : min 2 (n - 2 * g) = 2 := by omega_arith
    refine .inr ⟨by simp [hl], ⟨by omega_arith, base', esp', rd', wr', frame', ?_, ?_, ?_⟩⟩
    · rw [hds]; rcases esi₆ with e | e
      · exact e
      · exact absurd e hl
    · rw [hns, ebp₆, hm2, show n - 2 * g - 2 = n - 2 * (g + 1) by omega_arith]
    · rw [hm2] at data₉; rwa [show 2 * g + 2 = 2 * (g + 1) by omega_arith] at data₉

/-- The loop over the groups. -/
theorem ecbGroups_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {m₀ : Mem} {s : State} (hi : EInv f m₀ s₂ B Dp n R w 0 s) :
    WP isa (.loop (blockGroup crypt2) .ne) s (EDone f m₀ s₂ B Dp n R w) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ EInv f m₀ s₂ B Dp n R w g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (ecbGroup_ok hs hcr hg) fun s' h => ?_) n s ⟨0, by omega_arith, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86.eval, z], d⟩
  · exact .inr ⟨by simp [X86.eval, z], n - 2 * (g + 1), by have := hg.hg; omega_arith, g + 1, rfl, d⟩

end

end VG.Proof.Aes.X86
