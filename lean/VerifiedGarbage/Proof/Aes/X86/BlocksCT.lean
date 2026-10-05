import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Taint

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Ecb`. -/
section

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
    InRel (Q s₀) S → WP isa crypt2 s₀ fun s => VG.Proof.Aes.X86.Ctx s₀ s ∧ InRel (Q s) (fun b => f R w (S b))

theorem encrypt2_cryptOk : VG.Proof.Aes.X86.CryptOk encrypt2 Spec.Aes.cipher := fun hp hin => encrypt2_ok hp hin
theorem decrypt2_cryptOk : VG.Proof.Aes.X86.CryptOk decrypt2 Spec.Aes.invCipher := fun hp hin => decrypt2_ok hp hin

/-! ## The data -/

/-- The data after `k` blocks: the first `k` of the `n` blocks at `D` are
`F`'s, the others are still `m₀`'s. -/
def EcbInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem ecbInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {F : Nat → Spec.Aes.State}
    (h : VG.Proof.Aes.X86.EcbInv m₀ m D n k F) (hk : n ≤ k) (hk' : n ≤ k') : VG.Proof.Aes.X86.EcbInv m₀ m D n k' F := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * k' by omega)]

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : VG.Proof.Aes.X86.EcbInv m₀ m D n k F) : VG.Proof.Aes.X86.EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

/-- Before `k` blocks are stored, a block not yet stored is still `m₀`'s. -/
theorem ecbInv_orig {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    (h : VG.Proof.Aes.X86.EcbInv m₀ m D n k F) {j : Nat} (hj : k ≤ j) (hjn : j < n) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_right (show ¬ 16 * j + i < 16 * k by omega)]

/-- `c` more blocks stored. -/
theorem ecbInv_store {m₀ m m' : Mem} {D : Addr} {n k c : Nat} {F : Nat → Spec.Aes.State}
    (hn : 16 * n < 2 ^ 64) (hkc : k + c ≤ n) (h : VG.Proof.Aes.X86.EcbInv m₀ m D n k F)
    (hfr : Frame [⟨D + BitVec.ofNat 64 (16 * k), 16 * c⟩] m m')
    (hv : ∀ i < 16 * c, m' (D + BitVec.ofNat 64 (16 * k + i)) = (F (k + i / 16)).getD (i % 16) 0) :
    VG.Proof.Aes.X86.EcbInv m₀ m' D n (k + c) F := by
  intro i hi
  by_cases h1 : 16 * k ≤ i ∧ i < 16 * (k + c)
  · rw [ite_eq_left (by omega)]
    have := hv (i - 16 * k) (by omega)
    rwa [show 16 * k + (i - 16 * k) = i by omega, show k + (i - 16 * k) / 16 = i / 16 by omega,
      show (i - 16 * k) % 16 = i % 16 by omega] at this
  · rw [hfr _ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains]
      rw [off_toNat D (by omega) (by omega)]
      split <;> omega), h i hi]
    by_cases h2 : i < 16 * k
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The slots holding the words of two blocks, at `a 0` and `a 1`. -/
theorem inRel_of_words {Q' : Nat → BitVec 32} {m : Mem} {a : Nat → Addr}
    (h : ∀ b < 2, ∀ v < 4, Q' (2 * v + b) = m.readW (a b + BitVec.ofNat 64 (4 * v)) 32) :
    InRel Q' (fun b => Spec.Aes.stateAt m (a b)) := by
  intro b hb i hi j hj
  rw [show b + 2 * (i / 4) = 2 * (i / 4) + b by omega, h b hb (i / 4) (by omega),
    readW_bit _ _ (by omega) hj, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * (i / 4) + i % 4 = i by omega, getD_eq _ hi]
  simp [Spec.Aes.stateAt]

/-- The bytes of the words of block `b`, when the slots hold `T`. -/
theorem byte_of_inRel {Q' : Nat → BitVec 32} {T : Nat → Spec.Aes.State} (h : InRel Q' T) {b t : Nat}
    (hb : b < 2) (ht : t < 16) :
    (Q' (2 * (t / 4) + b)).extractLsb' (8 * (t % 4)) 8 = (T b).getD t 0 :=
  byte_ext fun j hj => by
    rw [BitVec.getLsbD_extractLsb', show 2 * (t / 4) + b = b + 2 * (t / 4) by omega, h b hb t ht j hj]
    simp [hj]

/-! ## Where the data is -/

theorem addr_off {Dp : BitVec 32} {a o : Nat} (h : Dp.toNat + a + o < 2 ^ 32) :
    VG.X86.addr (Dp + BitVec.ofNat 32 a) o = Dp.setWidth 64 + BitVec.ofNat 64 (a + o) := by
  rw [addr_add, addr_eq (by omega)]

/-- The blocks a group loads: two, or the last one twice. -/
def blk (n g b : Nat) : Nat := 2 * g + min b (n - 2 * g - 1)

theorem blk_lt {n g b : Nat} (hg : 2 * g < n) : 2 * g ≤ VG.Proof.Aes.X86.blk n g b ∧ VG.Proof.Aes.X86.blk n g b < n := by
  simp only [VG.Proof.Aes.X86.blk]; omega

/-! ## The load phase -/

def loadCfg2 : Cfg := { base := sb, slots := 8, ext := .esi, exts := 8 }
def loadCfg1 : Cfg := { base := sb, slots := 8, ext := .esi, exts := 4 }

def load2Post (e : Env Nat) : Bool :=
  (List.range 2).all fun b => (List.range 4).all fun v => e.slot (2 * v + b) == some (4 * b + v)

def load1Post (e : Env Nat) : Bool :=
  (List.range 4).all fun v => e.slot (2 * v) == some v && e.slot (2 * v + 1) == some v

theorem load2_check :
    VG.X86.Straight.check (names 32) VG.Proof.Aes.X86.loadCfg2 (fun k => some k) (loadBlock 0 ++ loadBlock 1)
      { reg := fun _ => none, slot := fun _ => none } VG.Proof.Aes.X86.load2Post = true := by
  decide +kernel

theorem load1_check :
    VG.X86.Straight.check (names 32) VG.Proof.Aes.X86.loadCfg1 (fun k => some k) loadOne
      { reg := fun _ => none, slot := fun _ => none } VG.Proof.Aes.X86.load1Post = true := by
  decide +kernel

theorem names_run {c : Cfg} {is : List Instr} {post : Env Nat → Bool} {s : State}
    (hchk : VG.X86.Straight.check (names 32) c (fun k => some k) is { reg := fun _ => none, slot := fun _ => none } post = true)
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
        s.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 (16 * VG.Proof.Aes.X86.blk n g b + 4 * v)) 32) →
      Frame [reg32 B 32] s.mem s'.mem → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.ite .ae (.block (loadBlock 0 ++ loadBlock 1)) (.block loadOne)) s P := by
  have hslots : ∀ (c : Cfg), c.base = sb → c.slots = 8 → c.ext = .esi → c.exts ≤ 8 →
      16 * (2 * g) + 4 * c.exts ≤ 16 * n → Ok c s := fun c h1 h2 h3 h4 h5 =>
    Ok.of_off (r := reg32 B 2048) (r' := reg32 Dp (16 * n)) (b := B) (b' := Dp) (off := 0)
      (off' := 32 * g) (n := 2048) (n' := 16 * n) hscr rfl hfitB (Nat.le_refl _)
      (by rw [h1, hb]; simp) (by rw [h2]; omega) (List.mem_append_right _ hdat) rfl hfitD (Nat.le_refl _)
      (by rw [h3, hesi]) (by omega) (.inr (.inr (.inl hsep.symm)))
  have hfr : ∀ (c : Cfg), c.base = sb → c.slots = 8 → slotRegion c s = reg32 B 32 := fun c h1 h2 => by
    simp only [slotRegion, h1, h2, hb]
  have ea : ∀ k, 32 * g + 4 * k + 4 ≤ 16 * n →
      wordAddr (s.gpr .esi) k = Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 4 * k) := by
    intro k hk
    simp only [wordAddr, hesi]
    exact VG.Proof.Aes.X86.addr_off (by omega)
  refine WP.ite (!decide (n - 2 * g < 2)) (by simp [X86.eval, hcf]) (fun hb2 => ?_) (fun hb2 => ?_)
  · have h2 : 2 ≤ n - 2 * g := by simpa using hb2
    obtain ⟨e', s', hpost, hs', p⟩ := VG.Proof.Aes.X86.names_run VG.Proof.Aes.X86.load2_check (hslots VG.Proof.Aes.X86.loadCfg2 rfl rfl rfl (by decide)
      (by simp [VG.Proof.Aes.X86.loadCfg2]; omega))
    refine WP.of_runBlock ⟨s', hs', h s' (fun b hb' v hv => ?_) (hfr VG.Proof.Aes.X86.loadCfg2 rfl rfl ▸ p.frame)
      (fun r hr => p.other r ?_) p.rd p.wr⟩
    · have := List.all_eq_true.mp hpost b (List.mem_range.mpr hb')
      have := List.all_eq_true.mp this v (List.mem_range.mpr hv)
      simp only [beq_iff_eq] at this
      have e := p.rel.slot _ _ (by simp [VG.Proof.Aes.X86.loadCfg2]; omega) this
      simp only [NameRel, VG.Proof.Aes.X86.loadCfg2] at e
      rw [Q, e, ea _ (by omega)]
      simp only [VG.Proof.Aes.X86.blk, show min b (n - 2 * g - 1) = b by omega]
      exact congrArg (fun x => s.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 x) 32) (by omega)
    · have : ((loadBlock 0 ++ loadBlock 1).all fun i => i.dst != some r) = true := by
        revert hr; cases r <;> decide
      simp [this]
  · have h1 : n - 2 * g = 1 := by simp at hb2; omega
    obtain ⟨e', s', hpost, hs', p⟩ := VG.Proof.Aes.X86.names_run VG.Proof.Aes.X86.load1_check (hslots VG.Proof.Aes.X86.loadCfg1 rfl rfl rfl (by decide)
      (by simp [VG.Proof.Aes.X86.loadCfg1]; omega))
    refine WP.of_runBlock ⟨s', hs', h s' (fun b hb' v hv => ?_) (hfr VG.Proof.Aes.X86.loadCfg1 rfl rfl ▸ p.frame)
      (fun r hr => p.other r ?_) p.rd p.wr⟩
    · have := List.all_eq_true.mp hpost v (List.mem_range.mpr hv)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      have e := p.rel.slot (2 * v + b) _ (by simp [VG.Proof.Aes.X86.loadCfg1]; omega)
        (by rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl; exacts [this.1, this.2])
      simp only [NameRel, VG.Proof.Aes.X86.loadCfg1] at e
      rw [Q, e, ea _ (by omega)]
      simp only [VG.Proof.Aes.X86.blk, show min b (n - 2 * g - 1) = 0 by omega]
      exact congrArg (fun x => s.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 x) 32) (by omega)
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
    VG.X86.Straight.check (names 32) VG.Proof.Aes.X86.storeCfg2 (fun k => some k) (storeBlock 0 ++ storeBlock 1)
      { reg := fun _ => none, slot := fun _ => none } VG.Proof.Aes.X86.store2Post = true := by
  decide +kernel

theorem store1_check :
    VG.X86.Straight.check (names 32) VG.Proof.Aes.X86.storeCfg1 (fun k => some k) (storeBlock 0)
      { reg := fun _ => none, slot := fun _ => none } VG.Proof.Aes.X86.store1Post = true := by
  decide +kernel

/-- What the stores of `c` blocks leave: the words of the slots at the data,
and nothing else changed. -/
theorem stores_bytes {m' : Mem} {Dp : BitVec 32} {g c : Nat} {T : Nat → Spec.Aes.State}
    {Q' : Nat → BitVec 32} (hin : InRel Q' T) (hc : c ≤ 2)
    (hw : ∀ b < c, ∀ v < 4, m'.readW (Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 16 * b + 4 * v)) 32 =
      Q' (2 * v + b)) :
    ∀ i < 16 * c, m' (Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g) + i)) = (T (i / 16)).getD (i % 16) 0 := by
  intro i hi
  have hb : i / 16 < 2 := by omega
  rw [← VG.Proof.Aes.X86.byte_of_inRel hin hb (Nat.mod_lt _ (by decide)), ← hw (i / 16) (by omega) (i % 16 / 4) (by omega),
    ← Mem.readW_byte _ _ (by omega : i % 16 % 4 < 4), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 3; omega

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
      (by rw [h2, hb]; simp) (by rw [h3]; omega) (.inr (.inr (.inl hsep)))
  have ea : ∀ k, 32 * g + 4 * k + 4 ≤ 16 * n →
      wordAddr (s.gpr .esi) k = Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 4 * k) := by
    intro k hk
    simp only [wordAddr, hesi]
    exact VG.Proof.Aes.X86.addr_off (by omega)
  have hreg : ∀ (c : Cfg), c.base = .esi → 32 * g + 4 * c.slots ≤ 16 * n →
      slotRegion c s = ⟨Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g)), 4 * c.slots⟩ := by
    intro c h1 h2
    simp only [slotRegion, h1, hesi]
    rw [← addr_zero, VG.Proof.Aes.X86.addr_off (by omega), Nat.add_zero, show 16 * (2 * g) = 32 * g by omega]
  refine WP.ite (!decide (n - 2 * g < 2)) (by simp [X86.eval, hcf]) (fun hb2 => ?_) (fun hb2 => ?_)
  · have h2 : 2 ≤ n - 2 * g := by simpa using hb2
    rw [storeTwo, WP.block_append_iff (M := isa)]
    obtain ⟨e', s₁, hpost, hs₁, p⟩ := VG.Proof.Aes.X86.names_run VG.Proof.Aes.X86.store2_check (hslots VG.Proof.Aes.X86.storeCfg2 rfl rfl rfl
      (by simp [VG.Proof.Aes.X86.storeCfg2]; omega))
    refine WP.of_runBlock ⟨s₁, hs₁, wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ _ _ => WP.block_nil ?_⟩
    have hw : ∀ b < 2, ∀ v < 4, s₁.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 16 * b + 4 * v)) 32 =
        Q s (2 * v + b) := by
      intro b hb' v hv
      have := List.all_eq_true.mp hpost b (List.mem_range.mpr hb')
      have := List.all_eq_true.mp this v (List.mem_range.mpr hv)
      simp only [beq_iff_eq] at this
      have e := p.rel.slot _ _ (by simp [VG.Proof.Aes.X86.storeCfg2]; omega) this
      simp only [NameRel, VG.Proof.Aes.X86.storeCfg2] at e
      rw [show s₁.gpr .esi = s.gpr .esi from p.base] at e
      rw [show 32 * g + 16 * b + 4 * v = 32 * g + 4 * (4 * b + v) by omega, ← ea _ (by omega), e]
    have hmin : min 2 (n - 2 * g) = 2 := by omega
    refine h s₃ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ ?_ (by rw [u₃.rd, u₂.rd, p.rd]) (by rw [u₃.wr, u₂.wr, p.wr])
    · rw [hmin, u₃.mem, u₂.mem]
      exact VG.Proof.Aes.X86.stores_bytes hin (by decide) hw
    · rw [hmin, u₃.mem, u₂.mem, show 16 * 2 = 4 * storeCfg2.slots from rfl, ← hreg VG.Proof.Aes.X86.storeCfg2 rfl (by simp [VG.Proof.Aes.X86.storeCfg2]; omega)]; exact p.frame
    · rw [u₃.other r h3, u₂.other r h2, p.other r (by
        have : ((storeBlock 0 ++ storeBlock 1).all fun i => i.dst != some r) = true := by
          revert h1; cases r <;> decide
        simp [this])]
    · rw [hmin, u₃.gpr, u₂.other _ (by decide), p.other _ (by decide), hebp]
      have : n ≤ 2 ^ 28 := by omega
      bv_omega
    · refine .inl ?_
      rw [u₃.other _ (by decide), u₂.gpr, p.other _ (by decide), hesi, BitVec.add_assoc,
        show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
  · have h1 : n - 2 * g = 1 := by simp at hb2; omega
    rw [storeOne, WP.block_append_iff (M := isa)]
    obtain ⟨e', s₁, hpost, hs₁, p⟩ := VG.Proof.Aes.X86.names_run VG.Proof.Aes.X86.store1_check (hslots VG.Proof.Aes.X86.storeCfg1 rfl rfl rfl
      (by simp [VG.Proof.Aes.X86.storeCfg1]; omega))
    refine WP.of_runBlock ⟨s₁, hs₁, wp_sub fun s₂ u₂ _ => WP.block_nil ?_⟩
    have hw : ∀ b < 1, ∀ v < 4, s₁.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 16 * b + 4 * v)) 32 =
        Q s (2 * v + b) := by
      intro b hb' v hv
      have := List.all_eq_true.mp hpost v (List.mem_range.mpr hv)
      simp only [beq_iff_eq] at this
      have e := p.rel.slot _ _ (by simp [VG.Proof.Aes.X86.storeCfg1]; omega) this
      simp only [NameRel, VG.Proof.Aes.X86.storeCfg1] at e
      rw [show s₁.gpr .esi = s.gpr .esi from p.base] at e
      rw [show b = 0 by omega, show 32 * g + 16 * 0 + 4 * v = 32 * g + 4 * v by omega, ← ea _ (by omega), e]
      rfl
    have hmin : min 2 (n - 2 * g) = 1 := by omega
    refine h s₂ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ (.inr (by omega)) (by rw [u₂.rd, p.rd]) (by rw [u₂.wr, p.wr])
    · rw [hmin, u₂.mem]
      exact VG.Proof.Aes.X86.stores_bytes hin (by decide) hw
    · rw [hmin, u₂.mem, show 16 * 1 = 4 * storeCfg1.slots from rfl, ← hreg VG.Proof.Aes.X86.storeCfg1 rfl (by simp [VG.Proof.Aes.X86.storeCfg1]; omega)]; exact p.frame
    · rw [u₂.other r h3, p.other r (by
        have : ((storeBlock 0).all fun i => i.dst != some r) = true := by
          revert h1; cases r <;> decide
        simp [this])]
    · rw [hmin, u₂.gpr, BitVec.sub_self, h1]

/-- `groupLoad`: the data pointer to `esi`, the count to `ebp`, and CF set
if fewer than two blocks are left. -/
theorem groupLoad_wp {s : State} {B Dp : BitVec 32} {n g : Nat} (hb : s.gpr .edi = B)
    (hfitB : B.toNat + 2048 ≤ 2 ^ 32) (hscr : reg32 B 2048 ∈ s.wr)
    (hd : s.mem.readW (VG.X86.addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * g))
    (hn : s.mem.readW (VG.X86.addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * g)) (hn32 : n < 2 ^ 32) {P : State → Prop}
    (h : ∀ s', s'.gpr .esi = Dp + BitVec.ofNat 32 (32 * g) → s'.gpr .ebp = BitVec.ofNat 32 (n - 2 * g) →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.cf = some (decide (n - 2 * g < 2)) → P s') :
    WP isa (.block groupLoad) s P := by
  have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr B dOff) 4 := in_rd (in_reg hscr hfitB (by decide) (by decide))
  have hin' : InRegions (s.rd ++ s.wr) (VG.X86.addr B nOff) 4 := in_rd (in_reg hscr hfitB (by decide) (by decide))
  refine wp_ldm (B := B) (o := dOff) hb hin fun s₁ u₁ => ?_
  refine wp_ldm (B := B) (o := nOff) (by rw [u₁.other _ (by decide)]; exact hb)
    (by rw [u₁.rd, u₁.wr]; exact hin') fun s₂ u₂ => ?_
  refine wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ?_
  refine h s₃ (by rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, hd])
    (by rw [u₃.gpr, u₂.gpr, u₁.mem, hn]) (fun r h1 h2 => by rw [u₃.gpr, u₂.other r h2, u₁.other r h1])
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) ?_
  rw [hcf, u₂.gpr, u₁.mem, hn, toNat_ofNat_lt (by omega)]
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
  argIn : InRegions (s₂.rd ++ s₂.wr) (VG.X86.addr (s₂.gpr .esp) 8) 4
  argR : s₂.mem.readW (VG.X86.addr (s₂.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  argSep : Region.Disjoint ⟨VG.X86.addr (s₂.gpr .esp) 8, 4⟩ (reg32 B 2048)
  argSepD : Region.Disjoint ⟨VG.X86.addr (s₂.gpr .esp) 8, 4⟩ (reg32 Dp (16 * n))
  keys : KeysAt s₂.mem B R w

/-- The memory the groups write: the layers' slots, the data pointer and
the count, and the data. -/
abbrev eRegions (B Dp : BitVec 32) (n : Nat) : List Region :=
  [reg32 B 256, ⟨VG.X86.addr B dOff, 8⟩, reg32 Dp (16 * n)]

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
  frame : Frame (VG.Proof.Aes.X86.eRegions B Dp n) s₂.mem s.mem
  dslot : s.mem.readW (VG.X86.addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * g)
  nslot : s.mem.readW (VG.X86.addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * g)
  data : VG.Proof.Aes.X86.EcbInv m₀ s.mem (Dp.setWidth 64) n (2 * g) (VG.Proof.Aes.X86.ecbOut f m₀ (Dp.setWidth 64) R w)

/-- After the last group. -/
structure EDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (s₂ : State)
    (B Dp : BitVec 32) (n R : Nat) (w : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  esp : s.gpr .esp = s₂.gpr .esp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (VG.Proof.Aes.X86.eRegions B Dp n) s₂.mem s.mem
  data : VG.Proof.Aes.X86.EcbInv m₀ s.mem (Dp.setWidth 64) n n (VG.Proof.Aes.X86.ecbOut f m₀ (Dp.setWidth 64) R w)

section
variable {s₂ : State} {B Dp : BitVec 32} {n R : Nat} {w : List Byte}
  (hs : VG.Proof.Aes.X86.ESetup s₂ B Dp n R w)
include hs

/-- A part of the scratch buffer at offset `o` is apart from the regions the
groups write if it is beyond the slots and the data pointer and count. -/
theorem ESetup.edisj {o l : Nat} (h1 : 256 ≤ o) (h2 : o + l ≤ dOff ∨ dOff + 8 ≤ o) (h3 : o + l ≤ 2048) :
    ∀ r ∈ VG.Proof.Aes.X86.eRegions B Dp n, Region.Disjoint ⟨VG.X86.addr B o, l⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
    rw [← addr_zero]; exact part_disj hs.fitB h3 (by omega) (.inr h1)
  · exact part_disj hs.fitB h3 (by simp only [dOff]; omega) h2
  · exact (hs.sep.sub_right (part_sub_reg hs.fitB h3)).symm

theorem ESetup.argDisj : ∀ r ∈ VG.Proof.Aes.X86.eRegions B Dp n, Region.Disjoint ⟨VG.X86.addr (s₂.gpr .esp) 8, 4⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.argSep.sub_right (Region.sub_prefix (by omega))
  · exact hs.argSep.sub_right (part_sub_reg hs.fitB (by simp only [dOff]; omega))
  · exact hs.argSepD

/-- One group: from before group `g`, to after the last group (ZF set) or
before group `g + 1`. -/
theorem ecbGroup_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : VG.Proof.Aes.X86.CryptOk crypt2 f) {m₀ : Mem} {g : Nat} {s : State} (hi : VG.Proof.Aes.X86.EInv f m₀ s₂ B Dp n R w g s) :
    WP isa (blockGroup crypt2) s fun s' => (s'.zf = some true ∧ VG.Proof.Aes.X86.EDone f m₀ s₂ B Dp n R w s') ∨
      (s'.zf = some false ∧ VG.Proof.Aes.X86.EInv f m₀ s₂ B Dp n R w (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hfitB := hs.fitB
  have hfitD := hs.fitD
  have hg := hi.hg
  have hn32 : n < 2 ^ 32 := by omega
  have hscr : reg32 B 2048 ∈ s.wr := hi.wr ▸ hs.scr
  have hdat : reg32 Dp (16 * n) ∈ s.wr := hi.wr ▸ hs.dat
  let D := Dp.setWidth 64
  let F := VG.Proof.Aes.X86.ecbOut f m₀ D R w
  have d32 : ∀ r ∈ [reg32 B 32], Region.Disjoint (reg32 Dp (16 * n)) r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (Region.sub_prefix (by omega))
  have d256 : ∀ r ∈ [reg32 B 256], Region.Disjoint (reg32 Dp (16 * n)) r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (Region.sub_prefix (by omega))
  have hn64 : 16 * n < 2 ^ 64 := by omega
  -- Reads of the scratch buffer beyond the slots, through the writes of the slots.
  have slotFar : ∀ {m m' : Mem} {N : Nat}, N ≤ 256 → Frame [reg32 B N] m m' → ∀ o, 256 ≤ o → o + 4 ≤ 2048 →
      m'.readW (VG.X86.addr B o) 32 = m.readW (VG.X86.addr B o) 32 := fun hN hf o h1 h2 =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint _ ⟨B.setWidth 64, _⟩
      rw [← addr_zero]; exact part_disj hfitB h2 (by omega) (.inr (by omega))) (by decide)
  unfold blockGroup loadGroup
  refine WP.seq (WP.seq (VG.Proof.Aes.X86.groupLoad_wp hi.base hfitB hscr hi.dslot hi.nslot hn32
    fun s₁ esi₁ ebp₁ g₁ m₁ rd₁ wr₁ cf₁ => ?_))
  have hb₁ : s₁.gpr sb = B := (g₁ sb (by decide) (by decide)).trans hi.base
  refine VG.Proof.Aes.X86.loads_ok hg hb₁ esi₁ hfitD (wr₁ ▸ hdat) hfitB (wr₁ ▸ hscr) hs.sep cf₁
    fun s₃ q₃ f₃ g₃ rd₃ wr₃ => ?_
  rw [m₁] at q₃ f₃
  have keep₃ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 =>
    (g₃ r h1).trans (g₁ r h2 h3)
  have hb₃ : s₃.gpr sb = B := (keep₃ sb (by decide) (by decide) (by decide)).trans hi.base
  have hesp₃ : s₃.gpr .esp = s₂.gpr .esp := (keep₃ _ (by decide) (by decide) (by decide)).trans hi.esp
  have hf₃ : Frame (VG.Proof.Aes.X86.eRegions B Dp n) s₂.mem s₃.mem :=
    hi.frame.trans (f₃.sub fun r hr => ⟨reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)
  have hp : EncPre s₃ R w :=
    { scr := by rw [hb₃, wr₃, wr₁]; exact hscr
      fit := by rw [hb₃]; exact hfitB
      rounds := hs.rounds
      argIn := by rw [rd₃, wr₃, rd₁, wr₁, hi.rd, hi.wr, hesp₃]; exact hs.argIn
      argR := by
        rw [hesp₃, ← hs.argR]
        exact hf₃.readW (Region.contains_self _ _) hs.argDisj (by decide)
      argSep := by rw [hesp₃, hb₃]; exact hs.argSep.sub_right (Region.sub_prefix (by omega))
      keys := by
        rw [hb₃]
        intro j hj
        refine keyRel_congr (hs.keys j hj) fun k hk => ?_
        have := keyOff_le (j := j) hR
        exact hf₃.readW (Region.contains_self _ _)
          (hs.edisj (by simp only [lastKey] at this; omega) (.inr (by simp only [dOff, lastKey] at this ⊢; omega))
            (by simp only [lastKey] at this; omega)) (by decide) }
  let S : Nat → Spec.Aes.State := fun b => Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * VG.Proof.Aes.X86.blk n g b))
  have hin : InRel (Q s₃) S := by
    have h := VG.Proof.Aes.X86.inRel_of_words (Q' := Q s₃) (m := s.mem) (a := fun b => D + BitVec.ofNat 64 (16 * VG.Proof.Aes.X86.blk n g b))
      (fun b hb v hv => by rw [q₃ b hb v hv, BitVec.add_assoc, ← BitVec.ofNat_add])
    have e : (fun b => Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16 * VG.Proof.Aes.X86.blk n g b))) = S := by
      funext b
      have := VG.Proof.Aes.X86.blk_lt (b := b) hg
      exact VG.Proof.Aes.X86.ecbInv_orig hi.data this.1 this.2
    rwa [e] at h
  refine WP.seq (WP.mono (hcr hp hin) fun s₄ ⟨hc₄, hin₄⟩ => ?_)
  have fr₄ := hc₄.frame
  rw [hb₃] at fr₄
  have hb₄ : s₄.gpr .edi = B := hc₄.base.trans hb₃
  have hesp₄ : s₄.gpr .esp = s₂.gpr .esp := hc₄.esp.trans hesp₃
  have far₄ : ∀ o, 256 ≤ o → o + 4 ≤ 2048 → s₄.mem.readW (VG.X86.addr B o) 32 = s.mem.readW (VG.X86.addr B o) 32 :=
    fun o h1 h2 => (slotFar (Nat.le_refl _) fr₄ o h1 h2).trans (slotFar (by omega) f₃ o h1 h2)
  have data₄ : VG.Proof.Aes.X86.EcbInv m₀ s₄.mem D n (2 * g) F :=
    VG.Proof.Aes.X86.ecbInv_frame fr₄ d256 hn64 (VG.Proof.Aes.X86.ecbInv_frame f₃ d32 hn64 hi.data)
  -- The store phase.
  unfold storeGroup
  refine WP.seq (VG.Proof.Aes.X86.groupLoad_wp hb₄ hfitB (by rw [hc₄.wr, wr₃, wr₁]; exact hscr)
    (by rw [far₄ _ (by decide) (by decide)]; exact hi.dslot)
    (by rw [far₄ _ (by decide) (by decide)]; exact hi.nslot) hn32
    fun s₅ esi₅ ebp₅ g₅ m₅ rd₅ wr₅ cf₅ => ?_)
  have hb₅ : s₅.gpr sb = B := (g₅ sb (by decide) (by decide)).trans hb₄
  have hq₅ : Q s₅ = Q s₄ := Q_congr (g₅ sb (by decide) (by decide)) m₅
  have wr₅' : s₅.wr = s₂.wr := by rw [wr₅, hc₄.wr, wr₃, wr₁, hi.wr]
  refine WP.seq (VG.Proof.Aes.X86.stores_ok (T := fun b => f R w (S b)) hg hb₅ esi₅ ebp₅ hfitD (wr₅' ▸ hs.dat) hfitB
    (wr₅' ▸ hs.scr) hs.sep cf₅ (by rw [hq₅]; exact hin₄)
    fun s₆ v₆ f₆ g₆ ebp₆ esi₆ rd₆ wr₆ => ?_)
  rw [m₅] at f₆
  have hc : min 2 (n - 2 * g) ≤ 2 ∧ 2 * g + min 2 (n - 2 * g) ≤ n := by omega
  have hsub : (⟨D + BitVec.ofNat 64 (16 * (2 * g)), 16 * min 2 (n - 2 * g)⟩ : Region).Sub
      (reg32 Dp (16 * n)) := Offset.sub_base _ (by omega)
  have data₆ : VG.Proof.Aes.X86.EcbInv m₀ s₆.mem D n (2 * g + min 2 (n - 2 * g)) F := by
    refine VG.Proof.Aes.X86.ecbInv_store hn64 hc.2 data₄ f₆ fun i hi' => ?_
    refine (v₆ i hi').trans ?_
    have e : VG.Proof.Aes.X86.blk n g (i / 16) = 2 * g + i / 16 := by simp only [VG.Proof.Aes.X86.blk]; omega
    simp only [F, VG.Proof.Aes.X86.ecbOut, S, e]
  have hesi₆ : s₆.gpr .edi = B := by rw [g₆ _ (by decide) (by decide) (by decide)]; exact hb₅
  have hin₆ : ∀ o, o + 4 ≤ 2048 → InRegions s₆.wr (VG.X86.addr B o) 4 := fun o ho => by
    rw [wr₆, wr₅']; exact in_reg hs.scr hfitB ho (by decide)
  refine wp_stm hesi₆ (hin₆ dOff (by decide)) fun s₇ u₇ => ?_
  refine wp_stm ((congrFun u₇.gpr .edi).trans hesi₆) (u₇.wr ▸ hin₆ nOff (by decide))
    fun s₈ u₈ => wp_test fun s₉ u₉ hz => WP.block_nil ?_
  have fr : Frame [⟨VG.X86.addr B dOff, 8⟩] s₆.mem s₉.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem]
    have hm : (⟨VG.X86.addr B dOff, 8⟩ : Region) ∈ [⟨VG.X86.addr B dOff, 8⟩] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (part_contains hfitB (by decide) (by decide) (by decide) (by decide))).writeW
      hm _ (part_contains hfitB (by decide) (by decide) (by decide) (by decide))
  have dsj : ∀ r ∈ [(⟨VG.X86.addr B dOff, 8⟩ : Region)], Region.Disjoint (reg32 Dp (16 * n)) r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (part_sub_reg hfitB (by decide))
  have data₉ := VG.Proof.Aes.X86.ecbInv_frame fr dsj hn64 data₆
  have hds : s₉.mem.readW (VG.X86.addr B dOff) 32 = s₆.gpr .esi := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₇.gpr, rd_wr_ne hfitB _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), Mem.readW_writeW_self32]
  have hns : s₉.mem.readW (VG.X86.addr B nOff) 32 = s₆.gpr .ebp := by
    rw [u₉.mem, u₈.mem, u₇.gpr, u₇.mem, Mem.readW_writeW_self32]
  have keep₉ : ∀ r, r ∉ tmpRegs → r ≠ .esi → s₉.gpr r = s.gpr r := fun r h1 h2 => by
    have h3 : r ≠ .eax := fun h => h1 (h ▸ by decide)
    have h4 : r ≠ .ebp := fun h => h1 (h ▸ by decide)
    rw [u₉.gpr, u₈.gpr, u₇.gpr, g₆ r h3 h2 h4, g₅ r h2 h4, hc₄.keep r h1 h2, keep₃ r h3 h2 h4]
  have base' : s₉.gpr sb = B := (keep₉ sb (by decide) (by decide)).trans hi.base
  have esp' : s₉.gpr .esp = s₂.gpr .esp := (keep₉ .esp (by decide) (by decide)).trans hi.esp
  have rd' : s₉.rd = s₂.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, hc₄.rd, rd₃, rd₁, hi.rd]
  have wr' : s₉.wr = s₂.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅']
  have frame' : Frame (VG.Proof.Aes.X86.eRegions B Dp n) s₂.mem s₉.mem := by
    refine hf₃.trans ((fr₄.sub fun r hr => ⟨reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩).trans
      (?_ : Frame _ s₄.mem s₉.mem))
    refine (f₆.sub fun r hr => ⟨reg32 Dp (16 * n),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), by
      simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩).trans
      (fr.sub fun r hr => ⟨⟨VG.X86.addr B dOff, 8⟩, List.mem_cons_of_mem _ (List.mem_cons_self ..), by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  rw [hz, u₈.gpr, u₇.gpr, ebp₆, BitVec.and_self, ofNat_beq_zero (by omega)]
  by_cases hl : n - 2 * g - min 2 (n - 2 * g) = 0
  · refine .inl ⟨by rw [hl]; rfl, base', esp', rd', wr', frame', VG.Proof.Aes.X86.ecbInv_mono data₉ (by omega) (Nat.le_refl _)⟩
  · have hm2 : min 2 (n - 2 * g) = 2 := by omega
    refine .inr ⟨by simp [hl], ⟨by omega, base', esp', rd', wr', frame', ?_, ?_, ?_⟩⟩
    · rw [hds]; rcases esi₆ with e | e
      · exact e
      · exact absurd e hl
    · rw [hns, ebp₆, hm2, show n - 2 * g - 2 = n - 2 * (g + 1) by omega]
    · rw [hm2] at data₉; rwa [show 2 * g + 2 = 2 * (g + 1) by omega] at data₉

/-- The loop over the groups. -/
theorem ecbGroups_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : VG.Proof.Aes.X86.CryptOk crypt2 f) {m₀ : Mem} {s : State} (hi : VG.Proof.Aes.X86.EInv f m₀ s₂ B Dp n R w 0 s) :
    WP isa (.loop (blockGroup crypt2) .ne) s (VG.Proof.Aes.X86.EDone f m₀ s₂ B Dp n R w) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ VG.Proof.Aes.X86.EInv f m₀ s₂ B Dp n R w g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (VG.Proof.Aes.X86.ecbGroup_ok hs hcr hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86.eval, z], d⟩
  · exact .inr ⟨by simp [X86.eval, z], n - 2 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.BlocksContract`. -/
section

/-!
# AES on whole blocks on x86 (32-bit): the contract

The per-target contract both implementations of `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` on x86 are proven against (`blocksX86`), and its
precondition by name (`BPre`).
-/

namespace VG.Proof.Aes

open _root_.VG.X86 in
/-- X86 (32-bit) contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher), whose arguments are on
the stack: replaces each of the `n` blocks at `data` with `f rounds w` of it,
for the key schedule `w`.

The code may read `schedule` (240 bytes) and the arguments (20 bytes above
the return address), and read and write `data` (`16 n` bytes) and `scratch`
(2048 bytes, whose contents on exit are unspecified). The writable buffers
may not overlap each other, `schedule`, the arguments or the return address;
nothing may wrap around the end of the (32-bit) address space. `rounds` is
10, 12 or 14. `esp` and the arguments are public; the key schedule and the
data are secret. -/
def blocksX86 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(VG.X86.arg s 0).setWidth 64, 240⟩
    let data : Region := ⟨(VG.X86.arg s 2).setWidth 64, 16 * (VG.X86.arg s 3).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, 2048⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 16 * (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 4).toNat + 2048 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat =
      (Spec.Aes.statesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat).map
        (f (VG.X86.arg s 1).toNat (Spec.Aes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (16 * ((VG.X86.arg s 1).toNat + 1))))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

end VG.Proof.Aes

namespace VG.Proof.Aes.X86

open VG VG.X86

section
variable (s : State)

abbrev bSchP : BitVec 32 := VG.X86.arg s 0
abbrev bRounds : Nat := (VG.X86.arg s 1).toNat
abbrev bDatP : BitVec 32 := VG.X86.arg s 2
abbrev bN : Nat := (VG.X86.arg s 3).toNat
abbrev bScrP : BitVec 32 := VG.X86.arg s 4
abbrev bSchR : Region := reg32 (VG.Proof.Aes.X86.bSchP s) 240
abbrev bDatR : Region := reg32 (VG.Proof.Aes.X86.bDatP s) (16 * VG.Proof.Aes.X86.bN s)
abbrev bScrR : Region := reg32 (VG.Proof.Aes.X86.bScrP s) 2048
abbrev bArgR : Region := ⟨argAddr s 0, 20⟩
abbrev bRetR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `blocksX86.pre`, by name. -/
structure BPre (s : State) : Prop where
  rd : s.rd = [VG.Proof.Aes.X86.bSchR s, VG.Proof.Aes.X86.bArgR s]
  wr : s.wr = [VG.Proof.Aes.X86.bDatR s, VG.Proof.Aes.X86.bScrR s]
  dSD : (VG.Proof.Aes.X86.bSchR s).Disjoint (VG.Proof.Aes.X86.bDatR s)
  dSB : (VG.Proof.Aes.X86.bSchR s).Disjoint (VG.Proof.Aes.X86.bScrR s)
  dDB : (VG.Proof.Aes.X86.bDatR s).Disjoint (VG.Proof.Aes.X86.bScrR s)
  aD : (VG.Proof.Aes.X86.bArgR s).Disjoint (VG.Proof.Aes.X86.bDatR s)
  aB : (VG.Proof.Aes.X86.bArgR s).Disjoint (VG.Proof.Aes.X86.bScrR s)
  rD : (VG.Proof.Aes.X86.bRetR s).Disjoint (VG.Proof.Aes.X86.bDatR s)
  rB : (VG.Proof.Aes.X86.bRetR s).Disjoint (VG.Proof.Aes.X86.bScrR s)
  fS : (VG.Proof.Aes.X86.bSchP s).toNat + 240 ≤ 2 ^ 32
  fD : (VG.Proof.Aes.X86.bDatP s).toNat + 16 * VG.Proof.Aes.X86.bN s ≤ 2 ^ 32
  fB : (VG.Proof.Aes.X86.bScrP s).toNat + 2048 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  rounds : VG.Proof.Aes.X86.bRounds s = 10 ∨ VG.Proof.Aes.X86.bRounds s = 12 ∨ VG.Proof.Aes.X86.bRounds s = 14

theorem BPre.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State}
    (h : (Proof.Aes.blocksX86 f).pre s) : VG.Proof.Aes.X86.BPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-! ## Where constant time starts -/

/-- The taint analysis starts with `esp` public, and the words holding
`data` and `scratch` known to be the base addresses of the writable regions. -/
def blocksτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 2048], argLen := 24,
    argBases := [(12, 0), (20, 1)] }

theorem blocks_wf₀ {s : State} (hp : VG.Proof.Aes.X86.BPre s) : VG.X86.Taint.Wf VG.Proof.Aes.X86.blocksτ₀ s := by
  have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.Aes.X86.blocksτ₀]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [VG.Proof.Aes.X86.toNat_setWidth32] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [VG.Proof.Aes.X86.blocksτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]

theorem blocks_agree₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₁ s₂ : State}
    (h₁ : (Proof.Aes.blocksX86 f).pre s₁) (h₂ : (Proof.Aes.blocksX86 f).pre s₂)
    (hpub : (Proof.Aes.blocksX86 f).pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.Aes.X86.blocksτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := BPre.of h₁; have hp₂ := BPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Aes.X86.blocks_wf₀ hp₁, VG.Proof.Aes.X86.blocks_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Aes.X86.blocksτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [VG.Proof.Aes.X86.bDatR, VG.Proof.Aes.X86.bScrR, VG.Proof.Aes.X86.bDatP, VG.Proof.Aes.X86.bN, VG.Proof.Aes.X86.bScrP, ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)]
  · simp only [VG.Proof.Aes.X86.blocksτ₀] at hk
    rw [show VG.X86.Taint.depth blocksτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 24) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 10, 0x3000, 0, 0x4000` at `0x8004`. -/
def blocksSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800D then 0x30
  else if a = 0x8015 then 0x40 else 0

/-- A state satisfying the precondition (with no data). -/
def blocksSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Aes.X86.blocksSatMem
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 20⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Blocks`. -/
section

/-!
# AES on whole blocks on x86 (32-bit): the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt2` and `decrypt2`, and are proven at once, for any transformation
of two blocks with `CryptOk`: the prologue saves the callee-saved registers
in the scratch buffer and bitslices the round keys as `vg_aes_ctr32`'s does
(`Ctr32.lean`, `Keys.lean`); the groups (`Ecb.lean`) do the rest; the
epilogue restores the registers.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.X86.Wp (wp_mov wp_ldm wp_stm wp_test)

/-! ## The prologue -/

/-- After the prologue. -/
structure BP1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  edi : s.gpr .edi = VG.Proof.Aes.X86.bScrP s₀
  esi : s.gpr .esi = arg s₀ 1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (VG.Proof.Aes.X86.bScrP s₀) 256, 16⟩] s₀.mem s.mem
  saved : ∀ p ∈ savedRegs, s.mem.readW (addr (VG.Proof.Aes.X86.bScrP s₀) p.2) 32 = s₀.gpr p.1

theorem bPrologue_eq : saveRegs 4 ++ keySetup = ([
    .mov .eax (.mem (at_ .esp 20)), .store (at_ .eax 256) .ebx, .store (at_ .eax 260) .esi,
    .store (at_ .eax 264) .edi, .store (at_ .eax 268) .ebp, .mov .edi (.reg .eax),
    .mov .esi (.mem (at_ .esp 8))] : List Instr) := rfl

theorem bPrologue_ok {s₀ : State} (hp : VG.Proof.Aes.X86.BPre s₀) :
    WP isa (.block (saveRegs 4 ++ keySetup)) s₀ (VG.Proof.Aes.X86.BP1 s₀) := by
  have fB := hp.fB; have fSp := hp.fSp
  let B := VG.Proof.Aes.X86.bScrP s₀
  let E := s₀.gpr .esp
  have hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hrA : VG.Proof.Aes.X86.bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argC : ∀ i < 5, (VG.Proof.Aes.X86.bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨VG.Proof.Aes.X86.bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have bIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  have cB : ∀ o, 256 ≤ o → o + 4 ≤ 272 → (⟨addr B 256, 16⟩ : Region).Contains (addr B o) (32 / 8) :=
    fun o h1 h2 => part_contains fB (by omega) h1 (by omega) (by decide)
  have hmB : (⟨addr B 256, 16⟩ : Region) ∈ [⟨addr B 256, 16⟩] := List.mem_singleton_self _
  rw [VG.Proof.Aes.X86.bPrologue_eq]
  refine wp_ldm (B := E) (o := 20) rfl (argIn _ rfl 4 (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = B := by rw [u₁.gpr]; rfl
  refine wp_stm e₁ (bIn _ u₁.wr 256 (by omega)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (bIn _ (by rw [u₂.wr, u₁.wr]) 260 (by omega)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁) (bIn _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 264 (by omega))
    fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    (bIn _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 268 (by omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .edi → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₆.other r h2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h1]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  let M₄ := (((s₀.mem.writeW (addr B 256) (s₀.gpr .ebx)).writeW (addr B 260) (s₀.gpr .esi)).writeW
    (addr B 264) (s₀.gpr .edi)).writeW (addr B 268) (s₀.gpr .ebp)
  have m₆ : s₆.mem = M₄ := by
    simp only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr]
    rw [u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.mem]
  have f₆ : Frame [⟨addr B 256, 16⟩] s₀.mem s₆.mem := by
    rw [m₆]
    exact ((((Frame.refl _ _).writeW hmB _ (cB 256 (by omega) (by omega))).writeW hmB _
      (cB 260 (by omega) (by omega))).writeW hmB _ (cB 264 (by omega) (by omega))).writeW hmB _
      (cB 268 (by omega) (by omega))
  have esp₆ : s₆.gpr .esp = E := g₆ _ (by decide) (by decide)
  refine wp_ldm (B := E) (o := 8) esp₆ (argIn _ rd₆ 1 (by omega)) fun s₇ u₇ => WP.block_nil ?_
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  refine ⟨by rw [u₇.other _ (by decide)]; exact esp₆, ?_, ?_, by rw [u₇.rd, rd₆],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₇.mem]; exact f₆, fun p hp' => ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁
  · rw [u₇.gpr, arg_eq]
    exact f₆.readW (argC 1 (by omega)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.aB.sub_right (part_sub_reg fB (by omega))) (by decide)
  · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> rw [u₇.mem, m₆] <;>
      simp (disch := decide) only [M₄, B, rd_wr_ne fB', Mem.readW_writeW_self32]

/-! ## Between the loops -/

theorem blocksSetup_ok {s : State} {B E : BitVec 32} (hb : s.gpr .edi = B) (he : s.gpr .esp = E)
    (hfit : B.toNat + 2048 ≤ 2 ^ 32) (hw : reg32 B 2048 ∈ s.wr)
    (hin : ∀ i, i = 2 ∨ i = 3 → InRegions (s.rd ++ s.wr) (addr E (4 + 4 * i)) 4)
    (hsep : ∀ i, i = 2 ∨ i = 3 → Region.Disjoint ⟨addr E (4 + 4 * i), 4⟩ (reg32 B 2048))
    {P : State → Prop}
    (h : ∀ s', s'.gpr .edi = B → s'.gpr .esp = E → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem.readW (addr B dOff) 32 = s.mem.readW (addr E 12) 32 →
      s'.mem.readW (addr B nOff) 32 = s.mem.readW (addr E 16) 32 →
      s'.zf = some (s.mem.readW (addr E 16) 32 == 0) → Frame [⟨addr B dOff, 8⟩] s.mem s'.mem →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block blocksSetup) s P := by
  have hin' : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hw hfit ho (by decide)
  have hm : (⟨addr B dOff, 8⟩ : Region) ∈ [⟨addr B dOff, 8⟩] := List.mem_singleton_self _
  refine wp_ldm (B := E) (o := 12) he (hin 2 (.inl rfl)) fun s₁ u₁ => ?_
  refine wp_stm (B := B) (o := dOff) (by rw [u₁.other _ (by decide)]; exact hb) (hin' _ u₁.wr _ (by decide))
    fun s₂ u₂ => ?_
  have f₂ : Frame [⟨addr B dOff, 8⟩] s.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW hm _ (part_contains hfit (by decide) (by decide) (by decide) (by decide))
  refine wp_ldm (B := E) (o := 16) (by rw [u₂.gpr, u₁.other _ (by decide)]; exact he)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 3 (.inr rfl)) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (o := nOff) (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb)
    (hin' _ (by rw [u₃.wr, u₂.wr, u₁.wr]) _ (by decide)) fun s₄ u₄ => wp_test fun s₅ u₅ hz => WP.block_nil ?_
  have v₃ : s₃.gpr .eax = s.mem.readW (addr E 16) 32 := by
    rw [u₃.gpr]
    exact f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hsep 3 (.inr rfl)).sub_right (part_sub_reg hfit (by decide))) (by decide)
  refine h s₅ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact he
  · rw [u₅.gpr, u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem,
      rd_wr_ne hfit _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [u₅.mem, u₄.mem, Mem.readW_writeW_self32, v₃]
  · rw [hz, u₄.gpr, v₃, BitVec.and_self]
  · rw [u₅.mem, u₄.mem, u₃.mem]
    exact f₂.writeW hm _ (part_contains hfit (by decide) (by decide) (by decide) (by decide))

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : VG.Proof.Aes.X86.EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_left (show 16 * j + t < 16 * n by omega),
    show (16 * j + t) / 16 = j by omega, show (16 * j + t) % 16 = t by omega, getD_eq _ ht]

/-! ## The whole function -/

theorem correct_blocks {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : VG.Proof.Aes.X86.CryptOk crypt2 f) {s₀ : State} (hp : VG.Proof.Aes.X86.BPre s₀) :
    WP isa (VG.Impl.Aes.X86.blocks crypt2) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 f).post s₀ s' := by
  have fB := hp.fB; have fD := hp.fD; have fS := hp.fS; have fSp := hp.fSp
  have hR : VG.Proof.Aes.X86.bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  let B := VG.Proof.Aes.X86.bScrP s₀
  let D := VG.Proof.Aes.X86.bDatP s₀
  let S := VG.Proof.Aes.X86.bSchP s₀
  let E := s₀.gpr .esp
  let R := VG.Proof.Aes.X86.bRounds s₀
  let n := VG.Proof.Aes.X86.bN s₀
  let w := Spec.Aes.bytesAt s₀.mem (S.setWidth 64) (16 * (R + 1))
  have fS' : S.toNat + 240 ≤ 2 ^ 32 := fS
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  have fD' : D.toNat + 16 * n ≤ 2 ^ 32 := fD
  have fE' : E.toNat + 24 ≤ 2 ^ 32 := fSp
  have hR' : R ≤ 14 := hR
  have hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hwD : reg32 D (16 * n) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  have hrS : reg32 S 240 ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_self ..
  have hrA : VG.Proof.Aes.X86.bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argC : ∀ i < 5, (VG.Proof.Aes.X86.bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨VG.Proof.Aes.X86.bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have argSub : ∀ i < 5, Region.Sub ⟨addr E (4 + 4 * i), 4⟩ (VG.Proof.Aes.X86.bArgR s₀) := fun i hi =>
    part_sub (N := 24) (b := E) fSp (by omega) (by omega) (by omega)
  -- The prologue.
  unfold VG.Impl.Aes.X86.blocks
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.bPrologue_ok hp) fun s₁ h₁ => ?_)
  have F₁ := h₁.frame
  have d₁ : ∀ {r : Region}, r.Disjoint (VG.Proof.Aes.X86.bScrR s₀) → ∀ r' ∈ [(⟨addr B 256, 16⟩ : Region)], r.Disjoint r' := by
    intro r h1 r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    exact h1.sub_right (part_sub_reg fB (by omega))
  have arg₁ : ∀ i < 5, s₁.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    F₁.readW (argC i hi) (d₁ hp.aB) (by decide)
  have sched₁ : ∀ i < 240, s₁.mem (addr S i) = s₀.mem (addr S i) := fun i hi =>
    frame_one F₁ (reg_contains fS (by omega) (by decide)) (d₁ hp.dSB)
  have hk : KSetup s₁ B S R w :=
    { scr := by rw [h₁.wr]; exact hwB
      fitB := fB
      sch := by rw [h₁.rd]; exact List.mem_append_left _ hrS
      fitS := fS
      sep := hp.dSB
      rounds := hp.rounds
      base := h₁.edi
      argIn := fun i hi => by rw [h₁.esp]; exact argIn _ h₁.rd i (by omega)
      arg0 := by rw [h₁.esp]; exact arg₁ 0 (by omega)
      arg1 := by rw [h₁.esp, arg₁ 1 (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := fun i hi => by rw [h₁.esp]; exact hp.aB.sub_left (argSub i (by omega))
      w := fun i hi => by
        rw [sched₁ i (by omega)]
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        rw [addr_eq (by have := fS'; omega)] }
  have hi₁ : KInv s₁ B R w R s₁ :=
    { hj := Nat.le_refl _
      esi := by rw [h₁.esi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rd := rfl
      wr := rfl
      keep := fun _ _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₁) fun s₂ d₂ => ?_)
  have edi₂ : s₂.gpr .edi = B := (d₂.keep _ (by decide) (by decide)).trans h₁.edi
  have esp₂ : s₂.gpr .esp = E := (d₂.keep _ (by decide) (by decide)).trans h₁.esp
  have kfSub := hk.frame_sub
  have d₂' : ∀ {r : Region}, r.Disjoint (VG.Proof.Aes.X86.bScrR s₀) → ∀ r' ∈ keyFrame B, r.Disjoint r' :=
    fun h r' hr' => h.sub_right (kfSub r' hr')
  have arg₂ : ∀ i < 5, s₂.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [← arg₁ i hi]; exact d₂.frame.readW (argC i hi) (d₂' hp.aB) (by decide)
  -- Between the loops.
  refine WP.seq (VG.Proof.Aes.X86.blocksSetup_ok edi₂ esp₂ fB' (by rw [d₂.wr, h₁.wr]; exact hwB)
    (fun i hi => argIn _ (by rw [d₂.rd, h₁.rd]) i (by omega))
    (fun i hi => hp.aB.sub_left (argSub i (by omega)))
    fun s₃ edi₃ esp₃ g₃ ds₃ ns₃ z₃ F₃ rd₃ wr₃ => ?_)
  have d₃ : ∀ {r : Region}, r.Disjoint (VG.Proof.Aes.X86.bScrR s₀) → ∀ r' ∈ [(⟨addr B dOff, 8⟩ : Region)], r.Disjoint r' :=
    fun h r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact h.sub_right (part_sub_reg fB (by decide))
  have arg₃ : ∀ i < 5, s₃.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [← arg₂ i hi]; exact F₃.readW (argC i hi) (d₃ hp.aB) (by decide)
  have e16 : s₂.mem.readW (addr E 16) 32 = arg s₀ 3 := arg₂ 3 (by omega)
  have hs : VG.Proof.Aes.X86.ESetup s₃ B D n R w :=
    { scr := by rw [wr₃, d₂.wr, h₁.wr]; exact hwB
      fitB := fB
      dat := by rw [wr₃, d₂.wr, h₁.wr]; exact hwD
      fitD := fD
      sep := hp.dDB
      rounds := hp.rounds
      argIn := by rw [esp₃]; exact argIn _ (by rw [rd₃, d₂.rd, h₁.rd]) 1 (by omega)
      argR := by rw [esp₃, arg₃ 1 (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := by rw [esp₃]; exact hp.aB.sub_left (argSub 1 (by omega))
      argSepD := by rw [esp₃]; exact hp.aD.sub_left (argSub 1 (by omega))
      keys := fun j hj => by
        refine keyRel_congr (d₂.keys j hj) fun k hk => ?_
        have := keyOff_le (j := j) hR'
        exact F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact part_disj fB (by simp only [lastKey] at this; omega) (by decide)
            (.inr (by simp only [dOff, lastKey] at this ⊢; omega))) (by decide) }
  -- The memory the prologue, the key loop and the setup of the groups wrote.
  have G₃ : Frame [VG.Proof.Aes.X86.bScrR s₀] s₀.mem s₃.mem := by
    refine (F₁.sub fun r hr => ?_).trans ((d₂.frame.sub fun r hr => ?_).trans (F₃.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Aes.X86.bScrR s₀, by simp, part_sub_reg fB (by omega)⟩
    · exact ⟨VG.Proof.Aes.X86.bScrR s₀, by simp, kfSub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Aes.X86.bScrR s₀, by simp, part_sub_reg fB (by decide)⟩
  have dD : ∀ r ∈ [VG.Proof.Aes.X86.bScrR s₀], (VG.Proof.Aes.X86.bDatR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.dDB
  have hn64 : 16 * n < 2 ^ 64 := by omega
  have data₃ : VG.Proof.Aes.X86.EcbInv s₀.mem s₃.mem (D.setWidth 64) n 0
      (VG.Proof.Aes.X86.ecbOut f s₀.mem (D.setWidth 64) R w) := fun i hi => by
    rw [ite_eq_right (show ¬ i < 16 * 0 by omega)]
    exact G₃.bytes (R := VG.Proof.Aes.X86.bDatR s₀) dD (by show 16 * n ≤ 2 ^ 64; omega) hi
  -- The groups.
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.X86.EDone f s₀.mem s₃ B D n R w) ?_ fun s₄ h₄ => ?_)
  · refine WP.ite (arg s₀ 3 == 0) (by simp only [X86.eval, z₃, e16]) (fun hb => ?_) (fun hb => ?_)
    · have hn0 : n = 0 := by
        have : arg s₀ 3 = 0 := by simpa using hb
        show (arg s₀ 3).toNat = 0; rw [this]; rfl
      exact WP.block_nil ⟨edi₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
    · have hn0 : 0 < n := by
        have : arg s₀ 3 ≠ 0 := by simpa using hb
        show 0 < (arg s₀ 3).toNat
        exact Nat.pos_of_ne_zero fun h => this (BitVec.eq_of_toNat_eq (by simpa using h))
      refine VG.Proof.Aes.X86.ecbGroups_ok hs hcr ⟨by omega, edi₃, rfl, rfl, rfl, Frame.refl _ _, ?_, ?_, data₃⟩
      · rw [ds₃, arg₂ 2 (by omega)]; simp; rfl
      · rw [ns₃, e16, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · -- The epilogue.
    have G₄ : Frame [VG.Proof.Aes.X86.bScrR s₀, VG.Proof.Aes.X86.bDatR s₀] s₀.mem s₄.mem := by
      refine (G₃.mono (by simp)).trans (h₄.frame.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Aes.X86.bScrR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨VG.Proof.Aes.X86.bScrR s₀, by simp, part_sub_reg fB (by decide)⟩
      · exact ⟨VG.Proof.Aes.X86.bDatR s₀, by simp, fun _ h => h⟩
    have retD : ∀ r ∈ [VG.Proof.Aes.X86.bScrR s₀, VG.Proof.Aes.X86.bDatR s₀], (VG.Proof.Aes.X86.bRetR s₀).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.rB
      · exact hp.rD
    -- The saved registers.
    have saved : Spill.Saved s₄.mem (addr B) s₀.gpr savedRegs := fun p hp' => by
      have ho : 256 ≤ p.2 ∧ p.2 + 4 ≤ 272 := by revert p hp'; decide
      rw [← h₁.saved p hp']
      have e₄ : s₄.mem.readW (addr B p.2) 32 = s₃.mem.readW (addr B p.2) 32 :=
        h₄.frame.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
            rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
          · exact part_disj fB (by omega) (by decide) (.inl (by simp only [dOff]; omega))
          · exact (hp.dDB.sub_right (part_sub_reg fB (by omega))).symm) (by decide)
      rw [e₄, F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact part_disj fB (by omega) (by decide) (.inl (by simp only [dOff]; omega))) (by decide)]
      exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
          rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
        · exact part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
    have esp₄ : s₄.gpr .esp = E := h₄.esp.trans esp₃
    refine WP.mono (restore_ok h₄.base fB' (by rw [h₄.wr, wr₃, d₂.wr, h₁.wr]; exact hwB) saved)
      fun s₅ r₅ => ?_
    refine ⟨⟨r₅.abi (by decide) (by decide) esp₄, ?_⟩, ?_⟩
    · rw [r₅.mem]
      exact G₄.readW (Region.contains_self _ _) retD (by decide)
    · show Spec.Aes.statesAt s₅.mem (D.setWidth 64) n = _
      rw [r₅.mem, VG.Proof.Aes.X86.statesAt_of_ecbInv h₄.data]
      simp only [Spec.Aes.statesAt, List.map_map]
      rfl

theorem blocks_correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : VG.Proof.Aes.X86.CryptOk crypt2 f) (s : State) (hs : (Proof.Aes.blocksX86 f).pre s) :
    ∃ t s', Exec isa (VG.Impl.Aes.X86.blocks crypt2) s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s' :=
  (VG.Proof.Aes.X86.correct_blocks hcr (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s' :=
  VG.Proof.Aes.X86.blocks_correct VG.Proof.Aes.X86.encrypt2_cryptOk s hs

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s' :=
  VG.Proof.Aes.X86.blocks_correct VG.Proof.Aes.X86.decrypt2_cryptOk s hs

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.BlocksCT`. -/
section

/-!
# AES on whole blocks on x86 (32-bit): constant time, and `Verified`

The taint analysis (`VG.X86.Taint`) starts with `esp` public and knows
where the arguments are and which of them are the base addresses of the
data and the scratch buffer. As in `vg_aes_ctr32` (`Ctr32CT.lean`), the data
pointer and the count round-trip through public slots of the scratch
buffer; the stores of the blocks through the data pointer forget them, and
the code stores them again from the registers.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub Impl.Aes.X86.encryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.taint) VG.Proof.Aes.X86.blocksτ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Aes.X86.blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub Impl.Aes.X86.decryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.taint) VG.Proof.Aes.X86.blocksτ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Aes.X86.blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem encryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.encryptBlocks (Spec.Aes.encryptBlocksContract X86.abi) :=
  Verified.of_correct VG.Proof.Aes.X86.encryptBlocks_correct VG.Proof.Aes.X86.encryptBlocks_ct
    (by
      have a0 : arg VG.Proof.Aes.X86.blocksSat 0 = 0x1000 := by decide
      have a1 : arg VG.Proof.Aes.X86.blocksSat 1 = 10 := by decide
      have a2 : arg VG.Proof.Aes.X86.blocksSat 2 = 0x3000 := by decide
      have a3 : arg VG.Proof.Aes.X86.blocksSat 3 = 0 := by decide
      have a4 : arg VG.Proof.Aes.X86.blocksSat 4 = 0x4000 := by decide
      have e : argAddr VG.Proof.Aes.X86.blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using VG.Proof.Aes.X86.blocksSat)

theorem decryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.decryptBlocks (Spec.Aes.decryptBlocksContract X86.abi) :=
  Verified.of_correct VG.Proof.Aes.X86.decryptBlocks_correct VG.Proof.Aes.X86.decryptBlocks_ct
    (by
      have a0 : arg VG.Proof.Aes.X86.blocksSat 0 = 0x1000 := by decide
      have a1 : arg VG.Proof.Aes.X86.blocksSat 1 = 10 := by decide
      have a2 : arg VG.Proof.Aes.X86.blocksSat 2 = 0x3000 := by decide
      have a3 : arg VG.Proof.Aes.X86.blocksSat 3 = 0 := by decide
      have a4 : arg VG.Proof.Aes.X86.blocksSat 4 = 0x4000 := by decide
      have e : argAddr VG.Proof.Aes.X86.blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using VG.Proof.Aes.X86.blocksSat)

end VG.Proof.Aes.X86

end
