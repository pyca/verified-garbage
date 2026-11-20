module

public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.Framework.X86.ScrubSide
public import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyArith
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.X86.VariantProof
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyArith
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Aes.X86.Blocks
public import VerifiedGarbage.Proof.Aes.Rounds
public import VerifiedGarbage.Proof.Aes.X86.BlocksContract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Aes.X86.Blocks
meta import VerifiedGarbage.Proof.Aes.X86.BlocksContract
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86.Decrypt
import VerifiedGarbage.Proof.Aes.X86.Group
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
public import VerifiedGarbage.Proof.Aes.X86.Encrypt
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86.Ctr32
meta import VerifiedGarbage.Proof.Aes.X86.Decrypt
meta import VerifiedGarbage.Proof.Aes.X86.Group
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Proof.Framework.Bitslice.Sym
meta import VerifiedGarbage.Proof.Aes.X86.Encrypt
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.X86.Ctr32
meta import VerifiedGarbage.Proof.Aes.Rounds

/-! ### `Aes.X86.BlocksCT`, which only this module used -/

section

/-! ### `Aes.X86.Blocks`, which this module and modules that import it used -/

section

/-! ### `Aes.X86.Ecb`, which only this module used -/

section

/-!
# AES on whole blocks on x86 (32-bit): the groups

A group of `blocks` loads two blocks of the data (or the last one, into
both halves) into slots `0 … 7`, runs a transformation of two blocks
(`encrypt2` or `decrypt2`, whose proofs give `CryptOk`), and stores the
results back in place. The data pointer and the count stay in the scratch
buffer between the phases, as in `vg_aes_ctr32_to` (`Group.lean`). The data's
invariant (`EcbInv`) says that the first `k` blocks hold the transformation
of the original ones, and the others are still the original ones.
-/

@[expose] public section

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
  obtain hrel : Rel (NameRel fun k => s.mem.readW (wordAddr (s.gpr c.ext) k) 32) c (fun k => some k)
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
  obtain hslots : ∀ (c : Cfg), c.base = sb → c.slots = 8 → c.ext = .esi → c.exts ≤ 8 →
      16 * (2 * g) + 4 * c.exts ≤ 16 * n → Ok c s := fun c h1 h2 h3 h4 h5 =>
    Ok.of_off (r := reg32 B 2048) (r' := reg32 Dp (16 * n)) (b := B) (b' := Dp) (off := 0)
      (off' := 32 * g) (n := 2048) (n' := 16 * n) hscr rfl hfitB (Nat.le_refl _)
      (by rw [h1, hb]; simp) (by rw [h2]; omega_arith) (List.mem_append_right _ hdat) rfl hfitD (Nat.le_refl _)
      (by rw [h3, hesi]) (by omega_arith) (.inr (.inr (.inl hsep.symm)))
  obtain hfr : ∀ (c : Cfg), c.base = sb → c.slots = 8 → slotRegion c s = reg32 B 32 := fun c h1 h2 => by
    simp only [slotRegion, h1, h2, hb]
  obtain ea : ∀ k, 32 * g + 4 * k + 4 ≤ 16 * n →
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
      obtain e := p.rel.slot _ _ (by simp [loadCfg2]; omega_arith) this
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
      obtain e := p.rel.slot (2 * v + b) _ (by simp [loadCfg1]; omega_arith)
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
  obtain hb : i / 16 < 2 := by omega_arith
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
  obtain hslots : ∀ (c : Cfg), c.base = .esi → c.ext = sb → c.exts = 8 →
      32 * g + 4 * c.slots ≤ 16 * n → Ok c s := fun c h1 h2 h3 h5 =>
    Ok.of_off (r := reg32 Dp (16 * n)) (r' := reg32 B 2048) (b := Dp) (b' := B) (off := 32 * g)
      (off' := 0) (n := 16 * n) (n' := 2048) hdat rfl hfitD (Nat.le_refl _)
      (by rw [h1, hesi]) h5 (List.mem_append_right _ hscr) rfl hfitB (Nat.le_refl _)
      (by rw [h2, hb]; simp) (by rw [h3]; omega_arith) (.inr (.inr (.inl hsep)))
  obtain ea : ∀ k, 32 * g + 4 * k + 4 ≤ 16 * n →
      wordAddr (s.gpr .esi) k = Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 4 * k) := by
    intro k hk
    simp only [wordAddr, hesi]
    exact addr_off (by omega_arith)
  obtain hreg : ∀ (c : Cfg), c.base = .esi → 32 * g + 4 * c.slots ≤ 16 * n →
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
    obtain hw : ∀ b < 2, ∀ v < 4, s₁.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 16 * b + 4 * v)) 32 =
        Q s (2 * v + b) := by
      intro b hb' v hv
      have := List.all_eq_true.mp hpost b (List.mem_range.mpr hb')
      have := List.all_eq_true.mp this v (List.mem_range.mpr hv)
      simp only [beq_iff_eq] at this
      obtain e := p.rel.slot _ _ (by simp [storeCfg2]; omega_arith) this
      simp only [NameRel, storeCfg2] at e
      rw [show s₁.gpr .esi = s.gpr .esi from p.base] at e
      rw [show 32 * g + 16 * b + 4 * v = 32 * g + 4 * (4 * b + v) by omega_arith, ← ea _ (by omega_arith), e]
    obtain hmin : min 2 (n - 2 * g) = 2 := by omega_arith
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
    obtain hw : ∀ b < 1, ∀ v < 4, s₁.mem.readW (Dp.setWidth 64 + BitVec.ofNat 64 (32 * g + 16 * b + 4 * v)) 32 =
        Q s (2 * v + b) := by
      intro b hb' v hv
      have := List.all_eq_true.mp hpost v (List.mem_range.mpr hv)
      simp only [beq_iff_eq] at this
      obtain e := p.rel.slot _ _ (by simp [storeCfg1]; omega_arith) this
      simp only [NameRel, storeCfg1] at e
      rw [show s₁.gpr .esi = s.gpr .esi from p.base] at e
      rw [show b = 0 by omega_arith, show 32 * g + 16 * 0 + 4 * v = 32 * g + 4 * v by omega_arith, ← ea _ (by omega_arith), e]
      rfl
    obtain hmin : min 2 (n - 2 * g) = 1 := by omega_arith
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
  obtain hin : InRegions (s.rd ++ s.wr) (addr B dOff) 4 := in_rd (in_reg hscr hfitB (by decide) (by decide))
  obtain hin' : InRegions (s.rd ++ s.wr) (addr B nOff) 4 := in_rd (in_reg hscr hfitB (by decide) (by decide))
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
  obtain hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hfitB := hs.fitB
  have hfitD := hs.fitD
  have hg := hi.hg
  obtain hn32 : n < 2 ^ 32 := by omega_arith
  obtain hscr : reg32 B 2048 ∈ s.wr := hi.wr ▸ hs.scr
  obtain hdat : reg32 Dp (16 * n) ∈ s.wr := hi.wr ▸ hs.dat
  let D := Dp.setWidth 64
  let F := ecbOut f m₀ D R w
  obtain d32 : ∀ r ∈ [reg32 B 32], Region.Disjoint (reg32 Dp (16 * n)) r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  obtain d256 : ∀ r ∈ [reg32 B 256], Region.Disjoint (reg32 Dp (16 * n)) r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  obtain hn64 : 16 * n < 2 ^ 64 := by omega_arith
  -- Reads of the scratch buffer beyond the slots, through the writes of the slots.
  obtain slotFar : ∀ {m m' : Mem} {N : Nat}, N ≤ 256 → Frame [reg32 B N] m m' → ∀ o, 256 ≤ o → o + 4 ≤ 2048 →
      m'.readW (addr B o) 32 = m.readW (addr B o) 32 := fun hN hf o h1 h2 =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint _ ⟨B.setWidth 64, _⟩
      rw [← addr_zero]; exact part_disj hfitB h2 (by omega_arith) (.inr (by omega_arith))) (by decide)
  unfold blockGroup loadGroup
  refine WP.seq (WP.seq (groupLoad_wp hi.base hfitB hscr hi.dslot hi.nslot hn32
    fun s₁ esi₁ ebp₁ g₁ m₁ rd₁ wr₁ cf₁ => ?_))
  obtain hb₁ : s₁.gpr sb = B := (g₁ sb (by decide) (by decide)).trans hi.base
  refine loads_ok hg hb₁ esi₁ hfitD (wr₁ ▸ hdat) hfitB (wr₁ ▸ hscr) hs.sep cf₁
    fun s₃ q₃ f₃ g₃ rd₃ wr₃ => ?_
  rw [m₁] at q₃ f₃
  obtain keep₃ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 =>
    (g₃ r h1).trans (g₁ r h2 h3)
  obtain hb₃ : s₃.gpr sb = B := (keep₃ sb (by decide) (by decide) (by decide)).trans hi.base
  obtain hesp₃ : s₃.gpr .esp = s₂.gpr .esp := (keep₃ _ (by decide) (by decide) (by decide)).trans hi.esp
  obtain hf₃ : Frame (eRegions B Dp n) s₂.mem s₃.mem :=
    hi.frame.trans (f₃.sub fun r hr => ⟨reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩)
  obtain hp : EncPre s₃ R w :=
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
  obtain hin : InRel (Q s₃) S := by
    obtain h := inRel_of_words (Q' := Q s₃) (m := s.mem) (a := fun b => D + BitVec.ofNat 64 (16 * blk n g b))
      (fun b hb v hv => by rw [q₃ b hb v hv, BitVec.add_assoc, ← BitVec.ofNat_add])
    obtain e : (fun b => Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16 * blk n g b))) = S := by
      funext b
      have := blk_lt (b := b) hg
      exact ecbInv_orig hi.data this.1 this.2
    rwa [e] at h
  refine WP.seq (WP.mono (hcr hp hin) fun s₄ ⟨hc₄, hin₄⟩ => ?_)
  have fr₄ := hc₄.frame
  rw [hb₃] at fr₄
  obtain hb₄ : s₄.gpr .edi = B := hc₄.base.trans hb₃
  obtain hesp₄ : s₄.gpr .esp = s₂.gpr .esp := hc₄.esp.trans hesp₃
  obtain far₄ : ∀ o, 256 ≤ o → o + 4 ≤ 2048 → s₄.mem.readW (addr B o) 32 = s.mem.readW (addr B o) 32 :=
    fun o h1 h2 => (slotFar (Nat.le_refl _) fr₄ o h1 h2).trans (slotFar (by omega_arith) f₃ o h1 h2)
  obtain data₄ : EcbInv m₀ s₄.mem D n (2 * g) F :=
    ecbInv_frame fr₄ d256 hn64 (ecbInv_frame f₃ d32 hn64 hi.data)
  -- The store phase.
  unfold storeGroup
  refine WP.seq (groupLoad_wp hb₄ hfitB (by rw [hc₄.wr, wr₃, wr₁]; exact hscr)
    (by rw [far₄ _ (by decide) (by decide)]; exact hi.dslot)
    (by rw [far₄ _ (by decide) (by decide)]; exact hi.nslot) hn32
    fun s₅ esi₅ ebp₅ g₅ m₅ rd₅ wr₅ cf₅ => ?_)
  obtain hb₅ : s₅.gpr sb = B := (g₅ sb (by decide) (by decide)).trans hb₄
  obtain hq₅ : Q s₅ = Q s₄ := Q_congr (g₅ sb (by decide) (by decide)) m₅
  obtain wr₅' : s₅.wr = s₂.wr := by rw [wr₅, hc₄.wr, wr₃, wr₁, hi.wr]
  refine WP.seq (stores_ok (T := fun b => f R w (S b)) hg hb₅ esi₅ ebp₅ hfitD (wr₅' ▸ hs.dat) hfitB
    (wr₅' ▸ hs.scr) hs.sep cf₅ (by rw [hq₅]; exact hin₄)
    fun s₆ v₆ f₆ g₆ ebp₆ esi₆ rd₆ wr₆ => ?_)
  rw [m₅] at f₆
  obtain hc : min 2 (n - 2 * g) ≤ 2 ∧ 2 * g + min 2 (n - 2 * g) ≤ n := by omega_arith
  obtain hsub : (⟨D + BitVec.ofNat 64 (16 * (2 * g)), 16 * min 2 (n - 2 * g)⟩ : Region).Sub
      (reg32 Dp (16 * n)) := Offset.sub_base _ (by omega_arith)
  obtain data₆ : EcbInv m₀ s₆.mem D n (2 * g + min 2 (n - 2 * g)) F := by
    refine ecbInv_store hn64 hc.2 data₄ f₆ fun i hi' => ?_
    refine (v₆ i hi').trans ?_
    obtain e : blk n g (i / 16) = 2 * g + i / 16 := by simp only [blk]; omega_arith
    simp only [F, ecbOut, S, e]
  obtain hesi₆ : s₆.gpr .edi = B := by rw [g₆ _ (by decide) (by decide) (by decide)]; exact hb₅
  obtain hin₆ : ∀ o, o + 4 ≤ 2048 → InRegions s₆.wr (addr B o) 4 := fun o ho => by
    rw [wr₆, wr₅']; exact in_reg hs.scr hfitB ho (by decide)
  refine wp_stm hesi₆ (hin₆ dOff (by decide)) fun s₇ u₇ => ?_
  refine wp_stm ((congrFun u₇.gpr .edi).trans hesi₆) (u₇.wr ▸ hin₆ nOff (by decide))
    fun s₈ u₈ => wp_test fun s₉ u₉ hz => WP.block_nil ?_
  obtain fr : Frame [⟨addr B dOff, 8⟩] s₆.mem s₉.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem]
    obtain hm : (⟨addr B dOff, 8⟩ : Region) ∈ [⟨addr B dOff, 8⟩] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (part_contains hfitB (by decide) (by decide) (by decide) (by decide))).writeW
      hm _ (part_contains hfitB (by decide) (by decide) (by decide) (by decide))
  obtain dsj : ∀ r ∈ [(⟨addr B dOff, 8⟩ : Region)], Region.Disjoint (reg32 Dp (16 * n)) r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hs.sep.sub_right (part_sub_reg hfitB (by decide))
  obtain data₉ := ecbInv_frame fr dsj hn64 data₆
  obtain hds : s₉.mem.readW (addr B dOff) 32 = s₆.gpr .esi := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₇.gpr, rd_wr_ne hfitB _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), Mem.readW_writeW_self32]
  obtain hns : s₉.mem.readW (addr B nOff) 32 = s₆.gpr .ebp := by
    rw [u₉.mem, u₈.mem, u₇.gpr, u₇.mem, Mem.readW_writeW_self32]
  obtain keep₉ : ∀ r, r ∉ tmpRegs → r ≠ .esi → s₉.gpr r = s.gpr r := fun r h1 h2 => by
    obtain h3 : r ≠ .eax := fun h => h1 (h ▸ by decide)
    obtain h4 : r ≠ .ebp := fun h => h1 (h ▸ by decide)
    rw [u₉.gpr, u₈.gpr, u₇.gpr, g₆ r h3 h2 h4, g₅ r h2 h4, hc₄.keep r h1 h2, keep₃ r h3 h2 h4]
  obtain base' : s₉.gpr sb = B := (keep₉ sb (by decide) (by decide)).trans hi.base
  obtain esp' : s₉.gpr .esp = s₂.gpr .esp := (keep₉ .esp (by decide) (by decide)).trans hi.esp
  obtain rd' : s₉.rd = s₂.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, hc₄.rd, rd₃, rd₁, hi.rd]
  obtain wr' : s₉.wr = s₂.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅']
  obtain frame' : Frame (eRegions B Dp n) s₂.mem s₉.mem := by
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

end

end


/-!
# AES on whole blocks on x86 (32-bit): the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt2` and `decrypt2`, and are proven at once, for any transformation
of two blocks with `CryptOk`: the prologue saves the callee-saved registers
in the scratch buffer and bitslices the round keys as `vg_aes_ctr32_to`'s does
(`Ctr32.lean`, `Keys.lean`); the groups (`Ecb.lean`) do the rest; the
epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.X86.Wp (wp_mov wp_ldm wp_stm wp_test)

/-! ## The prologue -/

/-- After the prologue. -/
structure BP1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  edi : s.gpr .edi = bScrP s₀
  esi : s.gpr .esi = arg s₀ 1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (bScrP s₀) 256, 16⟩] s₀.mem s.mem
  saved : ∀ p ∈ savedRegs, s.mem.readW (addr (bScrP s₀) p.2) 32 = s₀.gpr p.1

theorem bPrologue_eq : saveRegs 4 ++ keySetup = ([
    .mov .eax (.mem (at_ .esp 20)), .store (at_ .eax 256) .ebx, .store (at_ .eax 260) .esi,
    .store (at_ .eax 264) .edi, .store (at_ .eax 268) .ebp, .mov .edi (.reg .eax),
    .mov .esi (.mem (at_ .esp 8))] : List Instr) := rfl

theorem bPrologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (saveRegs 4 ++ keySetup)) s₀ (BP1 s₀) := by
  obtain fB := hp.fB; have fSp := hp.fSp
  let B := bScrP s₀
  let E := s₀.gpr .esp
  obtain hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain hrA : bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain argC : ∀ i < 5, (bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide)
  obtain argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  obtain bIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  obtain cB : ∀ o, 256 ≤ o → o + 4 ≤ 272 → (⟨addr B 256, 16⟩ : Region).Contains (addr B o) (32 / 8) :=
    fun o h1 h2 => part_contains fB (by omega_arith) h1 (by omega_arith) (by decide)
  obtain hmB : (⟨addr B 256, 16⟩ : Region) ∈ [⟨addr B 256, 16⟩] := List.mem_singleton_self _
  rw [bPrologue_eq]
  refine wp_ldm (B := E) (o := 20) rfl (argIn _ rfl 4 (by omega_arith)) fun s₁ u₁ => ?_
  obtain e₁ : s₁.gpr .eax = B := by rw [u₁.gpr]; rfl
  refine wp_stm e₁ (bIn _ u₁.wr 256 (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (bIn _ (by rw [u₂.wr, u₁.wr]) 260 (by omega_arith)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁) (bIn _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 264 (by omega_arith))
    fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    (bIn _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 268 (by omega_arith)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  obtain g₆ : ∀ r, r ≠ .eax → r ≠ .edi → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₆.other r h2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h1]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  let M₄ := (((s₀.mem.writeW (addr B 256) (s₀.gpr .ebx)).writeW (addr B 260) (s₀.gpr .esi)).writeW
    (addr B 264) (s₀.gpr .edi)).writeW (addr B 268) (s₀.gpr .ebp)
  obtain m₆ : s₆.mem = M₄ := by
    simp only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr]
    rw [u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.mem]
  obtain f₆ : Frame [⟨addr B 256, 16⟩] s₀.mem s₆.mem := by
    rw [m₆]
    exact ((((Frame.refl _ _).writeW hmB _ (cB 256 (by omega_arith) (by omega_arith))).writeW hmB _
      (cB 260 (by omega_arith) (by omega_arith))).writeW hmB _ (cB 264 (by omega_arith) (by omega_arith))).writeW hmB _
      (cB 268 (by omega_arith) (by omega_arith))
  obtain esp₆ : s₆.gpr .esp = E := g₆ _ (by decide) (by decide)
  refine wp_ldm (B := E) (o := 8) esp₆ (argIn _ rd₆ 1 (by omega_arith)) fun s₇ u₇ => WP.block_nil ?_
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  refine ⟨by rw [u₇.other _ (by decide)]; exact esp₆, ?_, ?_, by rw [u₇.rd, rd₆],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₇.mem]; exact f₆, fun p hp' => ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁
  · rw [u₇.gpr, arg_eq]
    exact f₆.readW (argC 1 (by omega_arith)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.aB.sub_right (part_sub_reg fB (by omega_arith))) (by decide)
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
  obtain hin' : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hw hfit ho (by decide)
  obtain hm : (⟨addr B dOff, 8⟩ : Region) ∈ [⟨addr B dOff, 8⟩] := List.mem_singleton_self _
  refine wp_ldm (B := E) (o := 12) he (hin 2 (.inl rfl)) fun s₁ u₁ => ?_
  refine wp_stm (B := B) (o := dOff) (by rw [u₁.other _ (by decide)]; exact hb) (hin' _ u₁.wr _ (by decide))
    fun s₂ u₂ => ?_
  obtain f₂ : Frame [⟨addr B dOff, 8⟩] s.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW hm _ (part_contains hfit (by decide) (by decide) (by decide) (by decide))
  refine wp_ldm (B := E) (o := 16) (by rw [u₂.gpr, u₁.other _ (by decide)]; exact he)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 3 (.inr rfl)) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (o := nOff) (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb)
    (hin' _ (by rw [u₃.wr, u₂.wr, u₁.wr]) _ (by decide)) fun s₄ u₄ => wp_test fun s₅ u₅ hz => WP.block_nil ?_
  obtain v₃ : s₃.gpr .eax = s.mem.readW (addr E 16) 32 := by
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
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  obtain hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (show 16 * j + t < 16 * n by omega_arith),
    show (16 * j + t) / 16 = j by omega_arith, show (16 * j + t) % 16 = t by omega_arith, getD_eq _ ht]

/-! ## The whole function -/

theorem correct_blocks {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {s₀ : State} (hp : BPre s₀) :
    WP isa (blocks crypt2) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 f).post s₀ s' := by
  obtain fB := hp.fB; have fD := hp.fD; have fS := hp.fS; have fSp := hp.fSp
  obtain hR : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  let B := bScrP s₀
  let D := bDatP s₀
  let S := bSchP s₀
  let E := s₀.gpr .esp
  let R := bRounds s₀
  let n := bN s₀
  let w := Spec.Aes.bytesAt s₀.mem (S.setWidth 64) (16 * (R + 1))
  have fS' : S.toNat + 240 ≤ 2 ^ 32 := fS
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  have fD' : D.toNat + 16 * n ≤ 2 ^ 32 := fD
  have fE' : E.toNat + 24 ≤ 2 ^ 32 := fSp
  have hR' : R ≤ 14 := hR
  obtain hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain hwD : reg32 D (16 * n) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  obtain hrS : reg32 S 240 ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_self ..
  obtain hrA : bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain argC : ∀ i < 5, (bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide)
  obtain argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  obtain argSub : ∀ i < 5, Region.Sub ⟨addr E (4 + 4 * i), 4⟩ (bArgR s₀) := fun i hi =>
    part_sub (N := 24) (b := E) fSp (by omega_arith) (by omega_arith) (by omega_arith)
  -- The prologue.
  unfold blocks
  refine WP.seq (WP.mono (bPrologue_ok hp) fun s₁ h₁ => ?_)
  have F₁ := h₁.frame
  obtain d₁ : ∀ {r : Region}, r.Disjoint (bScrR s₀) → ∀ r' ∈ [(⟨addr B 256, 16⟩ : Region)], r.Disjoint r' := by
    intro r h1 r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    exact h1.sub_right (part_sub_reg fB (by omega_arith))
  obtain arg₁ : ∀ i < 5, s₁.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    F₁.readW (argC i hi) (d₁ hp.aB) (by decide)
  obtain sched₁ : ∀ i < 240, s₁.mem (addr S i) = s₀.mem (addr S i) := fun i hi =>
    frame_one F₁ (reg_contains fS (by omega_arith) (by decide)) (d₁ hp.dSB)
  obtain hk : KSetup s₁ B S R w :=
    { scr := by rw [h₁.wr]; exact hwB
      fitB := fB
      sch := by rw [h₁.rd]; exact List.mem_append_left _ hrS
      fitS := fS
      sep := hp.dSB
      rounds := hp.rounds
      base := h₁.edi
      argIn := fun i hi => by rw [h₁.esp]; exact argIn _ h₁.rd i (by omega_arith)
      arg0 := by rw [h₁.esp]; exact arg₁ 0 (by omega_arith)
      arg1 := by rw [h₁.esp, arg₁ 1 (by omega_arith), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := fun i hi => by rw [h₁.esp]; exact hp.aB.sub_left (argSub i (by omega_arith))
      w := fun i hi => by
        rw [sched₁ i (by omega_arith)]
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        rw [addr_eq (by have := fS'; omega_arith)] }
  obtain hi₁ : KInv s₁ B R w R s₁ :=
    { hj := Nat.le_refl _
      esi := by rw [h₁.esi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rd := rfl
      wr := rfl
      keep := fun _ _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₁) fun s₂ d₂ => ?_)
  obtain edi₂ : s₂.gpr .edi = B := (d₂.keep _ (by decide) (by decide)).trans h₁.edi
  obtain esp₂ : s₂.gpr .esp = E := (d₂.keep _ (by decide) (by decide)).trans h₁.esp
  have kfSub := hk.frame_sub
  obtain d₂' : ∀ {r : Region}, r.Disjoint (bScrR s₀) → ∀ r' ∈ keyFrame B, r.Disjoint r' :=
    fun h r' hr' => h.sub_right (kfSub r' hr')
  obtain arg₂ : ∀ i < 5, s₂.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [← arg₁ i hi]; exact d₂.frame.readW (argC i hi) (d₂' hp.aB) (by decide)
  -- Between the loops.
  refine WP.seq (blocksSetup_ok edi₂ esp₂ fB' (by rw [d₂.wr, h₁.wr]; exact hwB)
    (fun i hi => argIn _ (by rw [d₂.rd, h₁.rd]) i (by omega_arith))
    (fun i hi => hp.aB.sub_left (argSub i (by omega_arith)))
    fun s₃ edi₃ esp₃ g₃ ds₃ ns₃ z₃ F₃ rd₃ wr₃ => ?_)
  obtain d₃ : ∀ {r : Region}, r.Disjoint (bScrR s₀) → ∀ r' ∈ [(⟨addr B dOff, 8⟩ : Region)], r.Disjoint r' :=
    fun h r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact h.sub_right (part_sub_reg fB (by decide))
  obtain arg₃ : ∀ i < 5, s₃.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [← arg₂ i hi]; exact F₃.readW (argC i hi) (d₃ hp.aB) (by decide)
  obtain e16 : s₂.mem.readW (addr E 16) 32 = arg s₀ 3 := arg₂ 3 (by omega_arith)
  obtain hs : ESetup s₃ B D n R w :=
    { scr := by rw [wr₃, d₂.wr, h₁.wr]; exact hwB
      fitB := fB
      dat := by rw [wr₃, d₂.wr, h₁.wr]; exact hwD
      fitD := fD
      sep := hp.dDB
      rounds := hp.rounds
      argIn := by rw [esp₃]; exact argIn _ (by rw [rd₃, d₂.rd, h₁.rd]) 1 (by omega_arith)
      argR := by rw [esp₃, arg₃ 1 (by omega_arith), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := by rw [esp₃]; exact hp.aB.sub_left (argSub 1 (by omega_arith))
      argSepD := by rw [esp₃]; exact hp.aD.sub_left (argSub 1 (by omega_arith))
      keys := fun j hj => by
        refine keyRel_congr (d₂.keys j hj) fun k hk => ?_
        have := keyOff_le (j := j) hR'
        exact F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact part_disj fB (by simp only [lastKey] at this; omega_arith) (by decide)
            (.inr (by simp only [dOff, lastKey] at this ⊢; omega_arith))) (by decide) }
  -- The memory the prologue, the key loop and the setup of the groups wrote.
  obtain G₃ : Frame [bScrR s₀] s₀.mem s₃.mem := by
    refine (F₁.sub fun r hr => ?_).trans ((d₂.frame.sub fun r hr => ?_).trans (F₃.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨bScrR s₀, by simp, part_sub_reg fB (by omega_arith)⟩
    · exact ⟨bScrR s₀, by simp, kfSub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨bScrR s₀, by simp, part_sub_reg fB (by decide)⟩
  obtain dD : ∀ r ∈ [bScrR s₀], (bDatR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.dDB
  obtain hn64 : 16 * n < 2 ^ 64 := by omega_arith
  obtain data₃ : EcbInv s₀.mem s₃.mem (D.setWidth 64) n 0
      (ecbOut f s₀.mem (D.setWidth 64) R w) := fun i hi => by
    rw [ite_eq_right (show ¬ i < 16 * 0 by omega_arith)]
    exact G₃.bytes (R := bDatR s₀) dD (by show 16 * n ≤ 2 ^ 64; omega_arith) hi
  -- The groups.
  refine WP.seq (WP.mono (Q := EDone f s₀.mem s₃ B D n R w) ?_ fun s₄ h₄ => ?_)
  · refine WP.ite (arg s₀ 3 == 0) (by simp only [X86.eval, z₃, e16]) (fun hb => ?_) (fun hb => ?_)
    · have hn0 : n = 0 := by
        have : arg s₀ 3 = 0 := by simpa using hb
        show (arg s₀ 3).toNat = 0; rw [this]; rfl
      exact WP.block_nil ⟨edi₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_arith)⟩
    · have hn0 : 0 < n := by
        have : arg s₀ 3 ≠ 0 := by simpa using hb
        show 0 < (arg s₀ 3).toNat
        exact Nat.pos_of_ne_zero fun h => this (BitVec.eq_of_toNat_eq (by simpa using h))
      refine ecbGroups_ok hs hcr ⟨by omega_arith, edi₃, rfl, rfl, rfl, Frame.refl _ _, ?_, ?_, data₃⟩
      · rw [ds₃, arg₂ 2 (by omega_arith)]; simp; rfl
      · rw [ns₃, e16, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · -- The epilogue.
    obtain G₄ : Frame [bScrR s₀, bDatR s₀] s₀.mem s₄.mem := by
      refine (G₃.mono (by simp)).trans (h₄.frame.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨bScrR s₀, by simp, Region.sub_prefix (by omega_arith)⟩
      · exact ⟨bScrR s₀, by simp, part_sub_reg fB (by decide)⟩
      · exact ⟨bDatR s₀, by simp, fun _ h => h⟩
    obtain retD : ∀ r ∈ [bScrR s₀, bDatR s₀], (bRetR s₀).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.rB
      · exact hp.rD
    -- The saved registers.
    obtain saved : Spill.Saved s₄.mem (addr B) s₀.gpr savedRegs := fun p hp' => by
      obtain ho : 256 ≤ p.2 ∧ p.2 + 4 ≤ 272 := by revert p hp'; decide
      rw [← h₁.saved p hp']
      obtain e₄ : s₄.mem.readW (addr B p.2) 32 = s₃.mem.readW (addr B p.2) 32 :=
        h₄.frame.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
            rw [← addr_zero]; exact part_disj fB (by omega_arith) (by omega_arith) (.inr (by omega_arith))
          · exact part_disj fB (by omega_arith) (by decide) (.inl (by simp only [dOff]; omega_arith))
          · exact (hp.dDB.sub_right (part_sub_reg fB (by omega_arith))).symm) (by decide)
      rw [e₄, F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact part_disj fB (by omega_arith) (by decide) (.inl (by simp only [dOff]; omega_arith))) (by decide)]
      exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
          rw [← addr_zero]; exact part_disj fB (by omega_arith) (by omega_arith) (.inr (by omega_arith))
        · exact part_disj fB (by omega_arith) (by omega_arith) (.inl (by omega_arith))) (by decide)
    obtain esp₄ : s₄.gpr .esp = E := h₄.esp.trans esp₃
    refine WP.mono (restore_ok h₄.base fB' (by rw [h₄.wr, wr₃, d₂.wr, h₁.wr]; exact hwB) saved)
      fun s₅ r₅ => ?_
    refine ⟨⟨r₅.abi (by decide) (by decide) esp₄, ?_⟩, ?_⟩
    · rw [r₅.mem]
      exact G₄.readW (Region.contains_self _ _) retD (by decide)
    · show Spec.Aes.statesAt s₅.mem (D.setWidth 64) n = _
      rw [r₅.mem, statesAt_of_ecbInv h₄.data]
      simp only [Spec.Aes.statesAt, List.map_map]
      rfl

theorem blocks_correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) (s : State) (hs : (Proof.Aes.blocksX86 f).pre s) :
    ∃ t s', Exec isa (blocks crypt2) s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s' :=
  (correct_blocks hcr (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s' :=
  blocks_correct encrypt2_cryptOk s hs

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s' :=
  blocks_correct decrypt2_cryptOk s hs

end VG.Proof.Aes.X86

end

end

/-!
# AES on whole blocks on x86 (32-bit): constant time, and `Verified`

The taint analysis (`VG.X86.Taint`) starts with `esp` public and knows
where the arguments are and which of them are the base addresses of the
data and the scratch buffer. As in `vg_aes_ctr32_to` (`Ctr32CT.lean`), the data
pointer and the count round-trip through public slots of the scratch
buffer; the stores of the blocks through the data pointer forget them, and
the code stores them again from the registers.
-/

@[expose] public section

namespace VG.Proof.Aes.X86

open VG VG.X86

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub Impl.Aes.X86.encryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.taint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub Impl.Aes.X86.decryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.taint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem encryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.encryptBlocks (Proof.Aes.encryptBlocksRoundsContract X86.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.decryptBlocks (Proof.Aes.decryptBlocksRoundsContract X86.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

end VG.Proof.Aes.X86

end

end

/-!
# Implementations of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86

A `BlocksImpl` is what a function that encrypts and decrypts whole blocks
with AES needs of them, so that its proof holds for every implementation:
each is a variant of the interface `AesBlocks` on x86
(`Variants/AesBlocks/X86/`), and each caller (in `Generic/AesBlocks/X86/`)
is emitted once for each of them (see `TCB/Emit.lean`). Each states how
much of `scratch` its functions may write (`encWritten`, `decWritten`), so
that its callers zero only that. Both functions are
proven against the same contract, `Proof.Aes.blocksX86` (with
`Spec.Aes.cipher` and `Spec.Aes.invCipher`), and make no calls. They come
with the implementation of `vg_aes_expand_key` that goes with them (with
the same suffix and CPU features), for the callers that also expand the
key, proven against `Proof.Aes.expandKeyX86`.
-/

@[expose] public section

namespace VG.Impl.Aes.X86
materialize_code encryptBlocks
materialize_code decryptBlocks
namespace AesNi
materialize_code encryptBlocks
materialize_code decryptBlocks
end AesNi
end VG.Impl.Aes.X86

namespace VG.Proof.Aes.X86

open VG.X86

/-- An implementation of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
on x86, and of `vg_aes_expand_key`. -/
structure BlocksImpl where
  /-- `vg_aes_encrypt_blocks`: its symbol and code. -/
  enc : Impl.Aes.X86.Blocks
  encStack : stackUse enc.code = 0
  encOk : ∀ s, (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s'
  encCt : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre (Proof.Aes.blocksX86 Spec.Aes.cipher).pub
    enc.code
  encNosp : NoSp enc.code
  encSpSafe : enc.code.all (fun i => !isa.writesSp i) = true
  /-- `enc`'s code has no MMX instruction and makes no indirect call (`calleeOk`):
  what the cleanup of every function that calls it needs of it, with its
  stack (`X86.Scrub.calleeSide`), so that each proves only its own code,
  whatever the implementation (`Proof/Framework/X86/ScrubCall.lean`). -/
  encScrub : calleeOk enc.code = true
  /-- `vg_aes_decrypt_blocks`: its symbol and code. -/
  dec : Impl.Aes.X86.Blocks
  decStack : stackUse dec.code = 0
  decOk : ∀ s, (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s'
  decCt : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub dec.code
  decNosp : NoSp dec.code
  decSpSafe : dec.code.all (fun i => !isa.writesSp i) = true
  /-- `encScrub`, of `dec`. -/
  decScrub : calleeOk dec.code = true
  /-- `enc` writes no byte of `scratch` at offset `encWritten` or beyond:
  its callers need to zero only the first `encWritten` bytes. -/
  encWritten : Nat
  encWrittenLe : encWritten ≤ 2048
  encWrittenOk : ∀ s, (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s → ∀ t s', Exec isa enc.code s t s' →
    ∀ i, encWritten ≤ i → i < 2048 →
      s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i)
  /-- `dec` writes no byte of `scratch` at offset `decWritten` or beyond. -/
  decWritten : Nat
  decWrittenLe : decWritten ≤ 2048
  decWrittenOk : ∀ s, (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s → ∀ t s', Exec isa dec.code s t s' →
    ∀ i, decWritten ≤ i → i < 2048 →
      s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i)
  /-- What the names of its callers' instances end with (e.g. `_aesni`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.X86.ExpandKey
  expandStack : stackUse expand.code = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86.pre Proof.Aes.expandKeyX86.pub expand.code
  expandNosp : NoSp expand.code
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true
  /-- `encScrub`, of `expand`. -/
  expandScrub : calleeOk expand.code = true

namespace BlocksImpl

/-- The bitsliced implementation, in the baseline ISA. -/
def scalar : BlocksImpl where
  enc := .encScalar
  encStack := by lit_decide
  encOk := encryptBlocks_correct
  encCt := encryptBlocks_ct
  encNosp := NoSp.of_all (by lit_decide)
  encSpSafe := Code.all_of_spTest (by lit_decide)
  encScrub := by lit_decide
  dec := .decScalar
  decStack := by lit_decide
  decOk := decryptBlocks_correct
  decCt := decryptBlocks_ct
  decNosp := NoSp.of_all (by lit_decide)
  decSpSafe := Code.all_of_spTest (by lit_decide)
  decScrub := by lit_decide
  encWritten := 2048
  encWrittenLe := Nat.le_refl _
  encWrittenOk := fun _ _ _ _ _ _ h1 h2 => absurd h2 (Nat.not_lt.mpr h1)
  decWritten := 2048
  decWrittenLe := Nat.le_refl _
  decWrittenOk := fun _ _ _ _ _ _ h1 h2 => absurd h2 (Nat.not_lt.mpr h1)
  suffix := ""
  features := []
  expand := Ctr32Impl.scalar.expand
  expandStack := Ctr32Impl.scalar.expandStack
  expandOk := Ctr32Impl.scalar.expandOk
  expandCt := Ctr32Impl.scalar.expandCt
  expandNosp := Ctr32Impl.scalar.expandNosp
  expandSpSafe := Ctr32Impl.scalar.expandSpSafe
  expandScrub := Ctr32Impl.scalar.expandScrub

/-- AES-NI. -/
def aesni : BlocksImpl where
  enc := .encAesni
  encStack := by lit_decide
  encOk := AesNi.encryptBlocks_correct
  encCt := AesNi.encryptBlocks_ct
  encNosp := NoSp.of_all (by lit_decide)
  encSpSafe := Code.all_of_spTest (by lit_decide)
  encScrub := by lit_decide
  dec := .decAesni
  decStack := by lit_decide
  decOk := AesNi.decryptBlocks_correct
  decCt := AesNi.decryptBlocks_ct
  decNosp := NoSp.of_all (by lit_decide)
  decSpSafe := Code.all_of_spTest (by lit_decide)
  decScrub := by lit_decide
  encWritten := 0
  encWrittenLe := Nat.zero_le _
  encWrittenOk := AesNi.encryptBlocks_unwritten
  decWritten := 240
  decWrittenLe := by decide
  decWrittenOk := AesNi.decryptBlocks_unwritten
  suffix := "_aesni"
  features := ["aes"]
  expand := Ctr32Impl.aesni.expand
  expandStack := Ctr32Impl.aesni.expandStack
  expandOk := Ctr32Impl.aesni.expandOk
  expandCt := Ctr32Impl.aesni.expandCt
  expandNosp := Ctr32Impl.aesni.expandNosp
  expandSpSafe := Ctr32Impl.aesni.expandSpSafe
  expandScrub := Ctr32Impl.aesni.expandScrub

end BlocksImpl

end VG.Proof.Aes.X86
