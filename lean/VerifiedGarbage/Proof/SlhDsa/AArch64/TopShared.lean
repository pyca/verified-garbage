module

public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Contracts
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Shake
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Impl.Aes.AArch64.Linear
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-!
# SLH-DSA (SHAKE) on AArch64: the blocks the functions share

What the straight-line pieces of `Impl/SlhDsa/AArch64/` (`Layout.lean`,
`Shake.lean`) do, as weakest preconditions over the instruction rules of
`Proof/MlKem/AArch64/Wp.lean`: each states the registers it may change
(`Only`, or `Keep` when it writes memory), the bytes it writes (`bytesAt`)
and the ranges it writes in (`Frame`).

* constants and addresses: `movV_ok`, `lea_ok`, `mulN_ok`, `maskZero_ok`;
* fields of an address: `setField_ok`, `setFieldR_ok` (the value's four
  bytes, big-endian, `toByte`);
* copies and zeroing of words: `copyWords_ok`, `zeroWords_ok`;
* saving and restoring registers: `saveRegsAt_ok`, `restoreRegsAt_ok`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_x wp_movz wp_addImm wp_add wp_lsl wp_lsr wp_subImm
  wp_sub wp_ldrx wp_strx wp_strw)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64

/-! ## Ranges within ranges -/

theorem contains_sub {r : Region} {a : Addr} {n k m : Nat} (h : r.Contains a n) (hk : k + m ≤ n) :
    r.Contains (a + BitVec.ofNat 64 k) m := by
  simp only [Region.Contains] at h ⊢
  rw [show a + BitVec.ofNat 64 k - r.base = (a - r.base) + BitVec.ofNat 64 k by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  have e := Nat.mod_le ((a - r.base).toNat + k % 2 ^ 64) (2 ^ 64)
  have e' := Nat.mod_le k (2 ^ 64)
  omega_using [h, hk, e, e']

theorem InRegions.sub {rs : List Region} {a : Addr} {n k m : Nat} (h : InRegions rs a n) (hk : k + m ≤ n) :
    InRegions rs (a + BitVec.ofNat 64 k) m := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, contains_sub hc hk⟩

theorem InRegions.rdwr {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem addr_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Bytes of memory -/

theorem ofNat_of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem bytesAt_ext {m m' : Mem} {a a' : Addr} {n : Nat}
    (h : ∀ i < n, m' (a' + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) : bytesAt m' a' n = bytesAt m a n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem bytesAt_eq_of {m : Mem} {a : Addr} {n : Nat} {L : List Byte} (hl : L.length = n)
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = L.getD i 0) : bytesAt m a n = L := by
  apply List.ext_getElem (by simp [bytesAt, hl])
  intro i h₁ h₂
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [h i h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

theorem bytesAt_getD (m : Mem) (a : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m a n).getD i 0 = m (a + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- Bytes a frame does not meet are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' a n = bytesAt m a n :=
  bytesAt_ext fun _ hi => hf.bytes (R := ⟨a, n⟩) hd hn hi

theorem write_byte (m : Mem) (a : Addr) {k j : Nat} (v : BitVec (8 * k)) (hj : j < k) (hk : k < 2 ^ 64) :
    m.write a k v (a + BitVec.ofNat 64 j) = v.extractLsb' (8 * j) 8 := by
  simp only [Mem.write, Mem.sub_ofNat_toNat a (show j < 2 ^ 64 by omega_using [hj, hk]), hj, ite_true]

theorem write_off (m : Mem) (a x : Addr) {k : Nat} (v : BitVec (8 * k)) (h : ¬ (x - a).toNat < k) :
    m.write a k v x = m x := Mem.write_apply h

theorem frame_write (m : Mem) (a : Addr) {k : Nat} (v : BitVec (8 * k)) : Frame [⟨a, k⟩] m (m.write a k v) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)

/-! ## Constants and addresses -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

private theorem half_ofNat {v : Nat} (hv : v < 2 ^ 64) (k : Nat) :
    Impl.Aes.AArch64.half (BitVec.ofNat 64 v) k = BitVec.ofNat 16 (v / 2 ^ (16 * k)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Impl.Aes.AArch64.half, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.shiftRight_eq_div_pow]

private theorem movV_eq_imm (d : Reg) {v : Nat} (hv : v < 2 ^ 64) :
    movV d v = Impl.Aes.AArch64.imm d (BitVec.ofNat 64 v) := by
  have hz : ∀ x : Nat, (BitVec.ofNat 16 x = 0#16) ↔ x % 65536 = 0 := fun x => by
    constructor
    · intro h; have := congrArg BitVec.toNat h; simpa using this
    · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
  simp only [movV, Impl.Aes.AArch64.imm, List.range, List.range.loop, List.filterMap_cons,
    List.filterMap_nil, List.filter_cons, List.filter_nil, half_ofNat hv]
  by_cases h1 : v / 2 ^ (16 * 1) % 65536 = 0 <;> by_cases h2 : v / 2 ^ (16 * 2) % 65536 = 0 <;>
    by_cases h3 : v / 2 ^ (16 * 3) % 65536 = 0 <;> simp_all

theorem read_x (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

/-- The `movk`s of the halfwords in `R`. -/
private theorem wp_movks (d : Reg) (v : BitVec 64) : ∀ (R : List Nat) (t : State), (∀ k ∈ R, k < 4) →
    (∀ i < 64, i / 16 ∉ R → (t.gpr d).getLsbD i = v.getLsbD i) →
    (∀ t', Only [d] t t' → t'.gpr d = v → WP isa (.block is) t' Q) →
    WP isa (.block ((R.map fun k => .movk .x d (Impl.Aes.AArch64.half v k) k) ++ is)) t Q
  | [], t, _, h, k => k t (Only.refl _ _) (BitVec.eq_of_getLsbD_eq fun i hi => h i hi List.not_mem_nil)
  | j :: R, t, hR, h, k => by
    have hj := hR j List.mem_cons_self
    refine wp_x (v := (t.read .x d &&& ~~~((0xFFFF : BitVec 64) <<< (16 * j))) |||
      ((Impl.Aes.AArch64.half v j).setWidth 64 <<< (16 * j)))
      (by simp only [exec, Size.bits, show 16 * j < 64 by omega_using [hj], ite_true]; rfl) fun t₁ o₁ e₁ => ?_
    refine wp_movks d v R t₁ (fun i hi => hR i (List.mem_cons_of_mem _ hi)) (fun i hi hn => ?_)
      fun t' o' e' => k t' ((o₁.trans o').mono (by simp)) e'
    rw [e₁, read_x, Proof.Sm4.AArch64.movk_bit _ _ hj hi]
    by_cases hik : i / 16 = j
    · simp [hik]
    · simp only [hik, ↓reduceIte]
      exact h i hi (by simp only [List.mem_cons, not_or]; exact ⟨hik, hn⟩)

/-- `movV d v`: `d ← v`, for `v < 2⁶⁴`. -/
theorem movV_ok {d : Reg} {v : Nat} (hv : v < 2 ^ 64)
    (k : ∀ s', Only [d] s s' → s'.gpr d = BitVec.ofNat 64 v → WP isa (.block is) s' Q) :
    WP isa (.block (movV d v ++ is)) s Q := by
  rw [movV_eq_imm d hv]
  simp only [Impl.Aes.AArch64.imm, List.cons_append]
  refine wp_x (d := d) (v := (Impl.Aes.AArch64.half (BitVec.ofNat 64 v) 0).setWidth 64 <<< (16 * 0))
    (by simp only [exec, Size.bits, show 16 * 0 < 64 by decide, ite_true]) fun t₀ o₀ e₀ => ?_
  refine wp_movks d _ _ t₀ (fun k hk => by
      simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk])
    (fun i hi hn => ?_) fun t' o' e' => k t' ((o₀.trans o').mono (by simp)) e'
  rw [e₀]
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.getLsbD_setWidth]
  by_cases h : i / 16 = 0
  · rw [show i = 16 * 0 + i by omega_using [], Proof.Sm4.AArch64.getLsbD_half _ (by omega_using [h])]
    simp [show i < 64 by omega_using [hi]]
  · rw [BitVec.getLsbD_of_ge _ i (by omega_using [h])]
    have hz : Impl.Aes.AArch64.half (BitVec.ofNat 64 v) (i / 16) = 0 := by
      simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, bne_iff_ne, ne_eq,
        not_and, Decidable.not_not] at hn
      exact hn (by omega_using [hi, h])
    rw [show i = 16 * (i / 16) + i % 16 by omega_using [], ← Proof.Sm4.AArch64.getLsbD_half _ (by omega_using []), hz]
    simp

/-- `lea d b off`: `d ← b + off` (`d ≠ b` if `off ≥ 4096`). -/
theorem lea_ok {d b : Reg} {off : Nat} (hd : off < 4096 ∨ d ≠ b) (hoff : off < 2 ^ 64)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr b + BitVec.ofNat 64 off → WP isa (.block is) s' Q) :
    WP isa (.block (lea d b off ++ is)) s Q := by
  unfold lea
  split
  · exact wp_addImm ‹_› k
  · rename_i h
    have hdb : d ≠ b := hd.resolve_left h
    rw [List.append_assoc]
    refine movV_ok hoff fun s₁ h₁ e₁ => wp_add fun s₂ h₂ e₂ => k s₂ ((h₁.trans h₂).mono (by simp)) ?_
    rw [e₂, h₁.get b (by simpa using hdb.symm), e₁]

/-- `mulN n r tmp`: `r ← r·n`, for `n` 16, 24 or 32 and `tmp ≠ r`. -/
theorem mulN_ok {n : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32) {r tmp : Reg} (hrt : r ≠ tmp)
    (k : ∀ s', Only [r, tmp] s s' → s'.gpr r = s.gpr r * BitVec.ofNat 64 n → WP isa (.block is) s' Q) :
    WP isa (.block (mulN n r tmp ++ is)) s Q := by
  rcases hn with rfl | rfl | rfl
  · simp only [mulN, show (16 : Nat) ≠ 24 by decide, ite_false, ite_true, List.cons_append, List.nil_append]
    refine wp_lsl (by decide) fun s₁ o₁ e₁ => k s₁ (o₁.mono (by simp)) ?_
    rw [e₁, BitVec.shiftLeft_eq_mul_twoPow]; rfl
  · simp only [mulN, ite_true, List.cons_append, List.nil_append]
    refine wp_lsl (by decide) fun s₁ o₁ e₁ => wp_lsl (by decide) fun s₂ o₂ e₂ => wp_add fun s₃ o₃ e₃ =>
      k s₃ ((o₁.trans (o₂.trans o₃)).mono (by simp)) ?_
    rw [e₃, e₂, o₂.get tmp (by simpa using hrt.symm), e₁, o₁.get r (by simpa using hrt),
      BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow, ← BitVec.mul_add]; rfl
  · simp only [mulN, show (32 : Nat) ≠ 24 by decide, show (32 : Nat) ≠ 16 by decide, ite_false,
      List.cons_append, List.nil_append]
    refine wp_lsl (by decide) fun s₁ o₁ e₁ => k s₁ (o₁.mono (by simp)) ?_
    rw [e₁, BitVec.shiftLeft_eq_mul_twoPow]; rfl

end

/-! ## Fields of an address -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem ofNat16_setWidth32 {u : Nat} (hu : u < 65536) : (BitVec.ofNat 16 u).setWidth 32 = BitVec.ofNat 32 u := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [hu]

theorem write_w_low (s : State) (d : Reg) (v : BitVec 32) : ((s.write .w d v).gpr d).setWidth 32 = v := by
  simp only [State.write, ite_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt
  omega_using [this]

theorem only_write_w (s : State) (d : Reg) (v : BitVec 32) : Only [d] s (s.write .w d v) :=
  ⟨fun r h => by simp only [List.mem_singleton] at h; simp [State.write, h], rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- `movW9 u`: the low 32 bits of `x9` set to `u < 2³²`. -/
theorem movW9_ok {u : Nat} (hu : u < 2 ^ 32)
    (k : ∀ s', Only [.x9] s s' → (s'.gpr .x9).setWidth 32 = BitVec.ofNat 32 u → WP isa (.block is) s' Q) :
    WP isa (.block (movW9 u ++ is)) s Q := by
  unfold movW9
  split
  · rename_i h
    refine MlKem.AArch64.WP.cons (s' := s.write .w .x9 ((BitVec.ofNat 16 (u / 65536)).setWidth 32 <<< 16))
      (by simp only [reduceExec, Size.bits, show 16 * 1 < 32 by decide, ite_true]) (k _ (only_write_w _ _ _) ?_)
    rw [write_w_low, ofNat16_setWidth32 (by omega_using [hu])]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using [hu, h]
  · split
    · rename_i _ h
      refine MlKem.AArch64.WP.cons (s' := s.write .w .x9 ((BitVec.ofNat 16 u).setWidth 32))
        (by simp only [reduceExec, Size.bits, show 16 * 0 < 32 by decide, ite_true, Nat.mul_zero,
          BitVec.shiftLeft_zero]) (k _ (only_write_w _ _ _) ?_)
      rw [write_w_low, ofNat16_setWidth32 (by omega_using [hu, h])]
    · simp only [List.cons_append]
      refine MlKem.AArch64.WP.cons (exec_movz_w (s := s) (d := .x9) (imm := BitVec.ofNat 16 u)) ?_
      refine MlKem.AArch64.WP.cons exec_movk_w (k _ (((only_write_w _ _ _).trans (only_write_w _ _ _)).mono
        (by simp)) ?_)
      rw [write_w_low, write_w_low]
      have e₁ : (BitVec.ofNat 16 u) = (BitVec.ofNat 32 u).extractLsb' 0 16 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
        omega_using [hu]
      have e₂ : (BitVec.ofNat 16 (u / 65536)) = (BitVec.ofNat 32 u).extractLsb' 16 16 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
        omega_using [hu]
      rw [e₁, e₂]
      exact movz_movk _

/-- What a store of a field leaves: `x9` aside, the four bytes at `a` are
`toByte v 4`, and nothing else in memory changed. -/
structure FieldPost (s s' : State) (a : Addr) (v : Nat) : Prop where
  keep : Keep [.x9] s s'
  bytes : bytesAt s'.mem a 4 = Spec.SlhDsa.toByte v 4
  frame : Frame [⟨a, 4⟩] s.mem s'.mem

theorem bytesAt_writeW32 (m : Mem) (a : Addr) (x : BitVec 32) :
    bytesAt (m.writeW a x) a 4 = (List.range 4).map fun j => x.extractLsb' (8 * j) 8 := by
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj' := List.mem_range.mp hj
  simp only [Mem.writeW]
  rw [write_byte _ _ _ hj' (by decide)]
  congr 1

theorem frame_writeW32 (m : Mem) (a : Addr) (x : BitVec 32) : Frame [⟨a, 4⟩] m (m.writeW a x) :=
  frame_write m a _

theorem frame_writeW (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) : Frame [⟨a, w / 8⟩] m (m.writeW a v) :=
  frame_write m a _

theorem frame_writeW64 (m : Mem) (a : Addr) (x : BitVec 64) : Frame [⟨a, 8⟩] m (m.writeW a x) :=
  frame_write m a _

theorem toByte4_eq (x : BitVec 32) (v : Nat) (h : ∀ j < 4, (x.toNat / 2 ^ (8 * j)) % 256 = v / 256 ^ (3 - j) % 256) :
    ((List.range 4).map fun j => x.extractLsb' (8 * j) 8) = Spec.SlhDsa.toByte v 4 := by
  simp only [Spec.SlhDsa.toByte]
  refine List.map_congr_left fun j hj => ?_
  have hj' := List.mem_range.mp hj
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show 4 - 1 - j = 3 - j by omega_using []]
  exact h j hj'

theorem bswap32_bytes (v : Nat) :
    ((List.range 4).map fun j => (BitVec.ofNat 32 (bswap32 v)).extractLsb' (8 * j) 8) = Spec.SlhDsa.toByte v 4 := by
  refine toByte4_eq _ _ fun j hj => ?_
  rw [BitVec.toNat_ofNat]
  simp only [bswap32]
  have b0 := Nat.mod_lt v (show 0 < 256 by decide)
  have b1 := Nat.mod_lt (v / 256) (show 0 < 256 by decide)
  have b2 := Nat.mod_lt (v / 65536) (show 0 < 256 by decide)
  have b3 := Nat.mod_lt (v / 16777216) (show 0 < 256 by decide)
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reducePow, Nat.reduceSub, Nat.pow_zero,
      Nat.div_one] <;>
  · generalize v % 256 = x0 at b0 ⊢
    generalize v / 256 % 256 = x1 at b1 ⊢
    generalize v / 65536 % 256 = x2 at b2 ⊢
    generalize v / 16777216 % 256 = x3 at b3 ⊢
    omega_using [b0, b1, b2, b3]

theorem rev32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (rev32 x).extractLsb' (8 * j) 8 = x.extractLsb' (8 * (3 - j)) 8 := by
  ext r hr
  simp only [BitVec.getElem_extractLsb', rev32, VG.AArch64.getLsbD_append_block _ _ _ hr]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h <;>
  simp (disch := omega_using [hr]) only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and, Nat.add_comm]

theorem rev32_bytes {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    ((List.range 4).map fun j => (rev32 (x.setWidth 32)).extractLsb' (8 * j) 8) = Spec.SlhDsa.toByte x.toNat 4 := by
  simp only [Spec.SlhDsa.toByte]
  refine List.map_congr_left fun j hj => ?_
  have hj' := List.mem_range.mp hj
  rw [rev32_byte _ hj']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hx]
  rw [show 4 - 1 - j = 3 - j by omega_using [], Nat.pow_mul]

theorem rev32_bytes32 (y : BitVec 32) :
    ((List.range 4).map fun j => (rev32 y).extractLsb' (8 * j) 8) = Spec.SlhDsa.toByte y.toNat 4 := by
  simp only [Spec.SlhDsa.toByte]
  refine List.map_congr_left fun j hj => ?_
  have hj' := List.mem_range.mp hj
  rw [rev32_byte _ hj']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show 4 - 1 - j = 3 - j by omega_using [], Nat.pow_mul]

theorem bswap32_lt (v : Nat) : bswap32 v < 2 ^ 32 := by
  simp only [bswap32]; omega_using []

/-- `setField b d v`: the field at `b + d` set to `v` (mod `2³²`), big-endian. -/
theorem setField_ok {b : Reg} (hb : b ≠ .x9) {d v : Nat} (hd : d % 4 = 0 ∧ d < 16384)
    (hin : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 4)
    (k : ∀ s', FieldPost s s' (s.gpr b + BitVec.ofNat 64 d) v → WP isa (.block is) s' Q) :
    WP isa (.block (setField b d v ++ is)) s Q := by
  simp only [setField, List.append_assoc, List.cons_append, List.nil_append]
  refine movW9_ok (bswap32_lt v) fun s₁ o₁ e₁ => ?_
  refine wp_strw (a := s.gpr b + BitVec.ofNat 64 d) hd (by rw [o₁.get b (by simpa using hb)])
    (by rw [o₁.wr]; exact hin) fun s₂ m₂ => k s₂ ⟨(o₁.keep.trans m₂.keep).mono (by simp), ?_, ?_⟩
  · rw [m₂.mem, e₁, o₁.mem, bytesAt_writeW32, bswap32_bytes v]
  · rw [m₂.mem, o₁.mem]; exact frame_writeW32 _ _ _

/-- `setFieldR b d r`: the field at `b + d` set to the register `r`, whose
value is below `2³²`, big-endian. -/
theorem setFieldR_ok {b r : Reg} (hb : b ≠ .x9) {d : Nat} (hr : (s.gpr r).toNat < 2 ^ 32)
    (hd : d % 4 = 0 ∧ d < 16384) (hin : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 4)
    (k : ∀ s', FieldPost s s' (s.gpr b + BitVec.ofNat 64 d) (s.gpr r).toNat → WP isa (.block is) s' Q) :
    WP isa (.block (setFieldR b d r ++ is)) s Q := by
  simp only [setFieldR, List.cons_append, List.nil_append]
  refine MlKem.AArch64.WP.cons exec_rev32 ?_
  refine wp_strw (a := s.gpr b + BitVec.ofNat 64 d) hd
    (by rw [(only_write_w s .x9 _).get b (by simpa using hb)]) (by exact hin) fun s₂ m₂ =>
      k s₂ ⟨((only_write_w s .x9 _).keep.trans m₂.keep).mono (by simp), ?_, ?_⟩
  · rw [m₂.mem, write_w_low, bytesAt_writeW32]
    simp only [State.read]
    exact rev32_bytes hr
  · rw [m₂.mem]; exact frame_writeW32 _ _ _

end

/-! ## Copies and zeroing of words -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_ldrq16 {n : Reg} {off : Nat} {a : Addr} (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', Keep [] s s' → s'.mem = s.mem → s'.v .v16 = s.mem.read a 16 → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrq .v16 n off :: is)) s Q :=
  MlKem.AArch64.WP.cons (s' := s.setV .v16 (s.mem.read a 16))
    (by simp only [reduceExec, addr, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
      Option.map_some])
    (k _ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
      rw [RegUpd.v_setV_of_ne s _ (by intro e; subst e; revert hr; decide)]⟩ rfl (RegUpd.v_setV_self s _ _))

theorem wp_strq16 {n : Reg} {off : Nat} {a : Addr} (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', Keep [] s s' → s'.v = s.v → s'.mem = s.mem.write a 16 (s.v .v16) → WP isa (.block is) s' Q) :
    WP isa (.block (.strq .v16 n off :: is)) s Q :=
  MlKem.AArch64.WP.cons (s' := { s with mem := s.mem.write a 16 (s.v .v16) })
    (by simp only [reduceExec, addr, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout])
    (k _ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ rfl rfl)

theorem off_window (p : Addr) {j o n : Nat} (hb : o + n ≤ 2 ^ 64) (hj : j < 2 ^ 64) :
    ((p + BitVec.ofNat 64 j) - (p + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ j ∧ j < o + n := by
  rw [Offset.lt_iff _ _ hb, Mem.sub_ofNat_toNat _ hj]

/-- What `copyWords` has done after its first `i` words, from the state `s`. -/
def CopyInv (s : State) (D Sa : Addr) (w i : Nat) (st : State) : Prop :=
  Keep [.x14] s st ∧ Frame [⟨D, 8 * w⟩] s.mem st.mem ∧
    ∀ j < 8 * i, st.mem (D + BitVec.ofNat 64 j) = s.mem (Sa + BitVec.ofNat 64 j)

section copy
variable {t sr : Reg} {d₂ d₁ w : Nat}

/-- What a copy needs of its operands. -/
structure CopyOk (s : State) (t sr : Reg) (d₂ d₁ w : Nat) : Prop where
  ht : t ≠ .x14
  hs : sr ≠ .x14
  h₁ : d₁ % 8 = 0 ∧ d₁ + 8 * w ≤ 32768
  h₂ : d₂ % 8 = 0 ∧ d₂ + 8 * w ≤ 32768
  hin : InRegions (s.rd ++ s.wr) (s.gpr sr + BitVec.ofNat 64 d₁) (8 * w)
  hout : InRegions s.wr (s.gpr t + BitVec.ofNat 64 d₂) (8 * w)
  hdis : Region.Disjoint ⟨s.gpr t + BitVec.ofNat 64 d₂, 8 * w⟩ ⟨s.gpr sr + BitVec.ofNat 64 d₁, 8 * w⟩

local notation "Dst" => s.gpr t + BitVec.ofNat 64 d₂
local notation "Src" => s.gpr sr + BitVec.ofNat 64 d₁

private theorem src_keep {st : State} (c : CopyOk s t sr d₂ d₁ w) {i : Nat} (inv : CopyInv s Dst Src w i st)
    {x : Nat} (hx : x < 8 * w) : st.mem (Src + BitVec.ofNat 64 x) = s.mem (Src + BitVec.ofNat 64 x) :=
  inv.2.1.bytes (R := ⟨Src, 8 * w⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c.hdis.symm) (by show 8 * w ≤ 2 ^ 64; omega_using [c.h₁]) hx

private theorem step8 (c : CopyOk s t sr d₂ d₁ w) {i : Nat} (hi : i < w) {st : State} {rest : List Instr}
    (inv : CopyInv s Dst Src w i st) (k : ∀ st', CopyInv s Dst Src w (i + 1) st' → WP isa (.block rest) st' Q) :
    WP isa (.block (.ldr .x .x14 sr (d₁ + 8 * i) :: .str .x .x14 t (d₂ + 8 * i) :: rest)) st Q := by
  have gs : st.gpr sr = s.gpr sr := inv.1.get sr (by simpa using c.hs)
  have gt : st.gpr t = s.gpr t := inv.1.get t (by simpa using c.ht)
  refine wp_ldrx (a := Src + BitVec.ofNat 64 (8 * i)) ⟨by omega_using [c.h₁], by omega_using [c.h₁, hi]⟩
    (by rw [gs, addr_add]) (by rw [inv.1.rd, inv.1.wr]; exact InRegions.sub c.hin (by omega_using [hi])) fun s₁ o₁ e₁ => ?_
  refine wp_strx (a := Dst + BitVec.ofNat 64 (8 * i)) ⟨by omega_using [c.h₂], by omega_using [c.h₂, hi]⟩
    (by rw [o₁.get t (by simpa using c.ht), gt, addr_add])
    (by rw [o₁.wr, inv.1.wr]; exact InRegions.sub c.hout (by omega_using [hi])) fun s₂ m₂ => k s₂ ⟨?_, ?_, ?_⟩
  · exact (inv.1.trans (o₁.keep.trans m₂.keep)).mono (by simp)
  · rw [m₂.mem, o₁.mem]
    exact inv.2.1.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, c.h₂]))
  · intro j hj
    rw [m₂.mem, o₁.mem, e₁]
    by_cases hj' : j < 8 * i
    · simp only [Mem.writeW]
      rw [Mem.write_apply (by
        rw [off_window _ (by omega_using [hi, c.h₂]) (by omega_using [hj, hi, c.h₂])]; omega_using [hj'])]
      exact inv.2.2 j hj'
    · rw [show Dst + BitVec.ofNat 64 j = Dst + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (j - 8 * i) by
          rw [BitVec.add_assoc _ (BitVec.ofNat 64 (8 * i)), ← BitVec.ofNat_add,
            show 8 * i + (j - 8 * i) = j by omega_using [hj']],
        MlKem.AArch64.KeyGen.writeW64_byte _ _ _ (by omega_using [hj, hj']),
        MlKem.AArch64.KeyGen.readW64_byte _ _ (by omega_using [hj, hj']),
        BitVec.add_assoc _ (BitVec.ofNat 64 (8 * i)), ← BitVec.ofNat_add, show 8 * i + (j - 8 * i) = j by omega_using [hj']]
      exact src_keep c inv (by omega_using [hj, hi])

private theorem step16 (c : CopyOk s t sr d₂ d₁ w) {i : Nat} (hi : i + 2 ≤ w) {st : State} {rest : List Instr}
    (ha : (d₁ + 8 * i) % 16 = 0 ∧ (d₂ + 8 * i) % 16 = 0)
    (inv : CopyInv s Dst Src w i st) (k : ∀ st', CopyInv s Dst Src w (i + 2) st' → WP isa (.block rest) st' Q) :
    WP isa (.block (.ldrq .v16 sr (d₁ + 8 * i) :: .strq .v16 t (d₂ + 8 * i) :: rest)) st Q := by
  have gs : st.gpr sr = s.gpr sr := inv.1.get sr (by simpa using c.hs)
  have gt : st.gpr t = s.gpr t := inv.1.get t (by simpa using c.ht)
  refine wp_ldrq16 (a := Src + BitVec.ofNat 64 (8 * i)) ⟨ha.1, by omega_using [c.h₁, hi]⟩
    (by rw [gs, addr_add]) (by rw [inv.1.rd, inv.1.wr]; exact InRegions.sub c.hin (by omega_using [hi]))
    fun s₁ o₁ m₁ e₁ => ?_
  refine wp_strq16 (a := Dst + BitVec.ofNat 64 (8 * i)) ⟨ha.2, by omega_using [c.h₂, hi]⟩
    (by rw [o₁.get t (by simp), gt, addr_add])
    (by rw [o₁.wr, inv.1.wr]; exact InRegions.sub c.hout (by omega_using [hi])) fun s₂ o₂ _ m₂ => k s₂ ⟨?_, ?_, ?_⟩
  · exact (inv.1.trans (o₁.trans o₂)).mono (by simp)
  · rw [m₂, m₁]
    exact inv.2.1.write (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, c.h₂]))
  · intro j hj
    rw [m₂, m₁, e₁]
    by_cases hj' : j < 8 * i
    · rw [Mem.write_apply (by
        rw [off_window _ (by omega_using [hi, c.h₂]) (by omega_using [hj, hi, c.h₂])]; omega_using [hj'])]
      exact inv.2.2 j hj'
    · rw [show Dst + BitVec.ofNat 64 j = Dst + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (j - 8 * i) by
          rw [BitVec.add_assoc _ (BitVec.ofNat 64 (8 * i)), ← BitVec.ofNat_add,
            show 8 * i + (j - 8 * i) = j by omega_using [hj']],
        write_byte _ _ _ (by omega_using [hj, hj']) (by decide),
        Mem.extractLsb'_read _ _ (by omega_using [hj, hj']),
        BitVec.add_assoc _ (BitVec.ofNat 64 (8 * i)), ← BitVec.ofNat_add, show 8 * i + (j - 8 * i) = j by omega_using [hj']]
      exact src_keep c inv (by omega_using [hj, hi])

private theorem copy_go (c : CopyOk s t sr d₂ d₁ w) :
    ∀ m i (st : State), i + m = w → CopyInv s Dst Src w i st →
      (∀ st', CopyInv s Dst Src w w st' → WP isa (.block is) st' Q) →
      WP isa (.block (copyWords.go t d₂ sr d₁ m i ++ is)) st Q
  | 0, i, st, hm, inv, k => by
    simp only [copyWords.go, List.nil_append]
    rw [Nat.add_zero] at hm; subst hm; exact k st inv
  | 1, i, st, hm, inv, k => by
    simp only [copyWords.go, List.cons_append, List.nil_append]
    subst hm; exact step8 c (by omega_using []) inv fun st' inv' => k st' inv'
  | m + 2, i, st, hm, inv, k => by
    simp only [copyWords.go]
    split
    · rename_i ha
      simp only [List.cons_append, List.nil_append]
      exact step16 c (by omega_using [hm]) ha inv fun st' inv' =>
        copy_go c m (i + 2) st' (by omega_using [hm]) inv' k
    · simp only [List.cons_append, List.nil_append]
      exact step8 c (by omega_using [hm]) inv fun st' inv' =>
        copy_go c (m + 1) (i + 1) st' (by omega_using [hm]) inv' k

/-- `copyWords t d₂ sr d₁ w`: the `8w` bytes at `sr + d₁` copied to the
`8w` bytes at `t + d₂`, apart from them; only `x14` (and `v16`) change. -/
theorem copyWords_ok (c : CopyOk s t sr d₂ d₁ w)
    (k : ∀ s', Keep [.x14] s s' → Frame [⟨Dst, 8 * w⟩] s.mem s'.mem →
      bytesAt s'.mem Dst (8 * w) = bytesAt s.mem Src (8 * w) → WP isa (.block is) s' Q) :
    WP isa (.block (copyWords t d₂ sr d₁ w ++ is)) s Q :=
  copy_go c w 0 s (Nat.zero_add _) ⟨Keep.refl _ _, Frame.refl _ _, fun j hj => absurd hj (by omega_using [])⟩
    fun st ⟨k₁, f₁, b₁⟩ => k st k₁ f₁ (bytesAt_ext b₁)

end copy

/-- `zeroWords t d w`: the `8w` bytes at `t + d` zeroed; only `x14` (and
`v16`) change. -/
theorem zeroWords_ok {t : Reg} {d w : Nat} (ht : t ≠ .x14) (hd : d % 16 = 0 ∧ d + 8 * w ≤ 32768)
    (hout : InRegions s.wr (s.gpr t + BitVec.ofNat 64 d) (8 * w))
    (k : ∀ s', Keep [.x14] s s' → Frame [⟨s.gpr t + BitVec.ofNat 64 d, 8 * w⟩] s.mem s'.mem →
      bytesAt s'.mem (s.gpr t + BitVec.ofNat 64 d) (8 * w) = List.replicate (8 * w) 0 → WP isa (.block is) s' Q) :
    WP isa (.block (zeroWords t d w ++ is)) s Q := by
  simp only [zeroWords, List.cons_append, List.append_assoc]
  refine MlKem.AArch64.WP.cons (s' := s.setV .v16 0) (by simp only [reduceExec]; rfl) ?_
  -- after `q` of the pairs
  have hpairs : ∀ q ≤ w / 2, ∀ {rest : List Instr},
      (∀ st, Keep [.x14] s st → st.v .v16 = 0 → Frame [⟨s.gpr t + BitVec.ofNat 64 d, 8 * w⟩] s.mem st.mem →
        (∀ j < 16 * q, st.mem (s.gpr t + BitVec.ofNat 64 d + BitVec.ofNat 64 j) = 0) → WP isa (.block rest) st Q) →
      WP isa (.block ((List.range q).map (fun i => .strq .v16 t (d + 16 * i)) ++ rest)) (s.setV .v16 0) Q := by
    intro q
    induction q with
    | zero =>
      intro _ rest k'
      exact k' _ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
        rw [RegUpd.v_setV_of_ne s _ (by intro e; subst e; revert hr; decide)]⟩ (RegUpd.v_setV_self s _ _)
        (Frame.refl _ _) fun j hj => absurd hj (by omega_using [])
    | succ q ih =>
      intro hq rest k'
      rw [List.range_succ, List.map_append, List.append_assoc]
      refine ih (by omega_using [hq]) fun st k₁ v₁ f₁ b₁ => ?_
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      refine wp_strq16 (a := s.gpr t + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * q))
        ⟨by omega_using [hd], by omega_using [hd, hq]⟩
        (by rw [k₁.get t (by simpa using ht), addr_add])
        (by rw [k₁.wr]; exact InRegions.sub hout (by omega_using [hq])) fun st' k₂ v₂ m₂ =>
          k' st' ((k₁.trans k₂).mono (by simp)) (by rw [v₂, v₁]) ?_ ?_
      · rw [m₂]
        exact f₁.write (List.mem_singleton_self _) _
          (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq, hd]))
      · intro j hj
        rw [m₂]
        by_cases hj' : j < 16 * q
        · rw [Mem.write_apply (by
            rw [off_window _ (by omega_using [hq, hd]) (by omega_using [hj, hq, hd])]; omega_using [hj'])]
          exact b₁ j hj'
        · rw [show s.gpr t + BitVec.ofNat 64 d + BitVec.ofNat 64 j =
              s.gpr t + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * q) + BitVec.ofNat 64 (j - 16 * q) by
              rw [BitVec.add_assoc _ (BitVec.ofNat 64 (16 * q)), ← BitVec.ofNat_add,
                show 16 * q + (j - 16 * q) = j by omega_using [hj']],
            write_byte _ _ _ (by omega_using [hj, hj']) (by decide), v₁]
          apply BitVec.eq_of_toNat_eq; simp
  have hfin : ∀ st, Keep [.x14] s st → Frame [⟨s.gpr t + BitVec.ofNat 64 d, 8 * w⟩] s.mem st.mem →
      (∀ j < 8 * w, st.mem (s.gpr t + BitVec.ofNat 64 d + BitVec.ofNat 64 j) = 0) → WP isa (.block is) st Q :=
    fun st k₁ f₁ b₁ => k st k₁ f₁ (bytesAt_eq_of (by simp) fun j hj => by
      rw [b₁ j hj, List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hj])
  refine hpairs (w / 2) (Nat.le_refl _) fun st k₁ _ f₁ b₁ => ?_
  split
  · rename_i hw
    simp only [List.cons_append, List.nil_append]
    refine wp_movz fun s₁ o₁ e₁ => ?_
    refine wp_strx (a := s.gpr t + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * (w / 2)))
      ⟨by omega_using [hd], by omega_using [hd, hw]⟩
      (by rw [o₁.get t (by simpa using ht), k₁.get t (by simpa using ht), addr_add])
      (by rw [o₁.wr, k₁.wr]; exact InRegions.sub hout (by omega_using [hw])) fun s₂ m₂ =>
        hfin s₂ ((k₁.trans (o₁.keep.trans m₂.keep)).mono (by simp)) ?_ ?_
    · rw [m₂.mem, o₁.mem]
      exact f₁.writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hw]) (by omega_using [hw, hd]))
    · intro j hj
      rw [m₂.mem, o₁.mem, e₁]
      by_cases hj' : j < 16 * (w / 2)
      · simp only [Mem.writeW]
        rw [Mem.write_apply (by
          rw [off_window _ (by omega_using [hw, hd]) (by omega_using [hj, hw, hd])]; omega_using [hj'])]
        exact b₁ j hj'
      · rw [show s.gpr t + BitVec.ofNat 64 d + BitVec.ofNat 64 j =
            s.gpr t + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * (w / 2)) + BitVec.ofNat 64 (j - 16 * (w / 2)) by
            rw [BitVec.add_assoc _ (BitVec.ofNat 64 (16 * (w / 2))), ← BitVec.ofNat_add,
              show 16 * (w / 2) + (j - 16 * (w / 2)) = j by omega_using [hj']],
          MlKem.AArch64.KeyGen.writeW64_byte _ _ _ (by omega_using [hj, hj', hw])]
        apply BitVec.eq_of_toNat_eq; simp
  · rename_i hw
    simp only [List.nil_append]
    exact hfin st k₁ f₁ fun j hj => b₁ j (by omega_using [hj, hw])

/-- `maskZero r tmp`: `r ← -1` if `r` was 0, else 0 (for `r < 2⁶³`). -/
theorem maskZero_ok {r tmp : Reg} (hrt : r ≠ tmp) (hr : (s.gpr r).toNat < 2 ^ 63)
    (k : ∀ s', Only [r, tmp] s s' → s'.gpr r = (if s.gpr r = 0 then BitVec.allOnes 64 else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (maskZero r tmp ++ is)) s Q := by
  simp only [maskZero, List.cons_append, List.nil_append]
  refine wp_subImm (by decide) fun s₁ o₁ e₁ => wp_lsr (by decide) fun s₂ o₂ e₂ => wp_movz fun s₃ o₃ e₃ =>
    wp_sub fun s₄ o₄ e₄ => k s₄ ((o₁.trans (o₂.trans (o₃.trans o₄))).mono (by simp)) ?_
  rw [e₄, e₃, o₃.get r (by simpa using hrt), e₂, e₁]
  by_cases h : s.gpr r = 0
  · rw [h]; decide
  · simp only [h, ↓reduceIte]
    have h1 : (s.gpr r - BitVec.ofNat 64 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      have : (s.gpr r).toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      show _ = 0
      omega_using [hr, this]
    rw [h1]; decide


end

/-! ## Saving and restoring registers -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem zipIdx_map_eq {β : Type} (rs : List Reg) (f : Reg → Nat → β) :
    rs.zipIdx.map (fun p => f p.1 p.2) = (List.range rs.length).map fun i => f (rs.getD i .x0) i := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.length_map, List.length_zipIdx] at h₁
  simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, h₁]

/-- `saveRegsAt o b rs`: register `rs[i]` to the word at `b + o + 8i`. -/
theorem saveRegsAt_ok {o : Nat} {b : Reg} {rs : List Reg} (ho : o % 8 = 0 ∧ o + 8 * rs.length ≤ 32768)
    (hout : InRegions s.wr (s.gpr b + BitVec.ofNat 64 o) (8 * rs.length))
    (k : ∀ s', Keep [] s s' → (∀ i (h : i < rs.length),
        s'.mem.readW (s.gpr b + BitVec.ofNat 64 (o + 8 * i)) 64 = s.gpr rs[i]) →
      Frame [⟨s.gpr b + BitVec.ofNat 64 o, 8 * rs.length⟩] s.mem s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (saveRegsAt o b rs ++ is)) s Q := by
  have e : saveRegsAt o b rs = (List.range rs.length).map fun i => .str .x (rs.getD i .x0) b (o + 8 * i) :=
    zipIdx_map_eq rs fun r i => Instr.str .x r b (o + 8 * i)
  rw [e]
  have h : ∀ q ≤ rs.length, ∀ {rest : List Instr},
      (∀ st, Keep [] s st → st.gpr = s.gpr → (∀ i < q, st.mem.readW (s.gpr b + BitVec.ofNat 64 (o + 8 * i)) 64 =
          s.gpr (rs.getD i .x0)) →
        Frame [⟨s.gpr b + BitVec.ofNat 64 o, 8 * rs.length⟩] s.mem st.mem → WP isa (.block rest) st Q) →
      WP isa (.block ((List.range q).map (fun i => .str .x (rs.getD i .x0) b (o + 8 * i)) ++ rest)) s Q := by
    intro q
    induction q with
    | zero => intro _ rest k'; exact k' s (Keep.refl _ _) rfl (fun i hi => absurd hi (by omega_using [])) (Frame.refl _ _)
    | succ q ih =>
      intro hq rest k'
      rw [List.range_succ, List.map_append, List.append_assoc]
      refine ih (by omega_using [hq]) fun st k₁ g₁ z₁ f₁ => ?_
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      refine wp_strx (a := s.gpr b + BitVec.ofNat 64 (o + 8 * q)) ⟨by omega_using [ho], by omega_using [ho, hq]⟩
        (by rw [g₁]) (by rw [k₁.wr, ← addr_add]; exact InRegions.sub hout (by omega_using [hq]))
        fun st' m₂ => k' st' (k₁.trans m₂.keep) (by rw [m₂.gpr, g₁]) (fun i hi => ?_) ?_
      · rw [m₂.mem, g₁]
        by_cases e : i = q
        · subst e; exact Mem.readW_writeW_self64 _ _ _
        · rw [Mem.readW_writeW_sep (MlKem.AArch64.sep_off _ (by omega_using [e, hi]) (by omega_using [ho, hq, hi])
            (by omega_using [ho, hq])) (by decide)]
          exact z₁ i (by omega_using [hi, e])
      · rw [m₂.mem, ← addr_add]
        exact f₁.writeW (List.mem_singleton_self _) _
          (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq, ho]))
  exact h _ (Nat.le_refl _) fun st k₁ _ z₁ f₁ => k st k₁ (fun i hi => by
    rw [z₁ i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]) f₁

/-- Loads of the registers `L.map (·.1)`, none `x19`, from `x19 + o + 8i`. -/
private theorem loads_ok {o : Nat} :
    ∀ (L : List (Reg × Nat)) {st : State} {rest : List Instr}, (∀ p ∈ L, p.1 ≠ .x19) → (L.map (·.1)).Nodup →
      (∀ p ∈ L, (o + 8 * p.2) % 8 = 0 ∧ o + 8 * p.2 < 32768 ∧
        InRegions (st.rd ++ st.wr) (st.gpr .x19 + BitVec.ofNat 64 (o + 8 * p.2)) 8) →
      (∀ st', Only (L.map (·.1)) st st' →
        (∀ p ∈ L, st'.gpr p.1 = st.mem.readW (st.gpr .x19 + BitVec.ofNat 64 (o + 8 * p.2)) 64) →
        WP isa (.block rest) st' Q) →
      WP isa (.block (L.map (fun p => .ldr .x p.1 .x19 (o + 8 * p.2)) ++ rest)) st Q
  | [], st, rest, _, _, _, k => k st (Only.refl _ _) fun p hp => absurd hp List.not_mem_nil
  | q :: L, st, rest, h19, hnd, hb, k => by
    simp only [List.map_cons, List.cons_append]
    have hq := hb q List.mem_cons_self
    have hq19 := h19 q List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldrx (a := st.gpr .x19 + BitVec.ofNat 64 (o + 8 * q.2)) ⟨hq.1, hq.2.1⟩ rfl hq.2.2 fun s₁ o₁ e₁ => ?_
    have g₁ : s₁.gpr .x19 = st.gpr .x19 := o₁.get .x19 (by simpa using hq19.symm)
    refine loads_ok L (fun p hp => h19 p (List.mem_cons_of_mem _ hp)) hnd.2 (fun p hp => by
        rw [o₁.rd, o₁.wr, g₁]; exact hb p (List.mem_cons_of_mem _ hp)) fun st' o' v' => k st' ?_ ?_
    · exact (o₁.trans o').mono (by simp)
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [o'.get _ hnd.1, e₁]
      · rw [v' p hp, o₁.mem, g₁]

theorem nodup_fst {l : List (Reg × Nat)} (h : (l.map (·.1)).Nodup) (P : Reg × Nat → Bool) :
    ((l.filter P).map (·.1)).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases hp : P a
    · simp only [List.filter_cons, hp, ite_true, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => h.1 ?_, ih h.2⟩
      obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
      exact List.mem_map.mpr ⟨b, (List.mem_filter.mp hb).1, e⟩
    · simp only [List.filter_cons, hp]; exact ih h.2

/-- `restoreRegsAt o rs`: register `rs[i]` from the word at `x19 + o + 8i`,
for distinct `rs` (`x19` last). -/
theorem restoreRegsAt_ok {o : Nat} {rs : List Reg} (hnd : rs.Nodup) (ho : o % 8 = 0 ∧ o + 8 * rs.length ≤ 32768)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 o) (8 * rs.length))
    (k : ∀ s', Only rs s s' → (∀ i (h : i < rs.length),
        s'.gpr rs[i] = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 (o + 8 * i)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (restoreRegsAt o rs ++ is)) s Q := by
  have hz : (rs.zipIdx.map (·.1)).Nodup := by rw [List.zipIdx_map_fst]; exact hnd
  have hmem : ∀ p ∈ rs.zipIdx, ∀ st : State, st.gpr .x19 = s.gpr .x19 → st.rd = s.rd → st.wr = s.wr →
      (o + 8 * p.2) % 8 = 0 ∧ o + 8 * p.2 < 32768 ∧
        InRegions (st.rd ++ st.wr) (st.gpr .x19 + BitVec.ofNat 64 (o + 8 * p.2)) 8 := by
    intro p hp st g r w
    obtain ⟨-, h₂, -⟩ := List.mem_zipIdx (x := p.1) (i := p.2) hp
    refine ⟨by omega_using [ho], by omega_using [ho, h₂], ?_⟩
    rw [g, r, w, ← addr_add]; exact InRegions.sub hin (by omega_using [h₂])
  simp only [restoreRegsAt, List.append_assoc]
  refine loads_ok _ (fun p hp => by simpa using (List.mem_filter.mp hp).2) (nodup_fst hz _)
    (fun p hp => hmem p (List.mem_filter.mp hp).1 s rfl rfl rfl) fun s₁ o₁ v₁ => ?_
  have g₁ : s₁.gpr .x19 = s.gpr .x19 := o₁.gpr .x19 fun h => by
    obtain ⟨p, hp, e⟩ := List.mem_map.mp h
    have := (List.mem_filter.mp hp).2
    simp [e] at this
  have hidx : ∀ i (h : i < rs.length), (rs[i], i) ∈ rs.zipIdx := fun i h => by
    have := List.getElem_mem (l := rs.zipIdx) (n := i) (by simpa using h)
    simpa [List.getElem_zipIdx] using this
  have hnd2 := nodup_fst hz (fun p => p.1 == .x19)
  generalize hL : rs.zipIdx.filter (fun p => p.1 == .x19) = L₂ at hnd2
  have hL₂ : ∀ p ∈ L₂, p.1 = .x19 ∧ p ∈ rs.zipIdx := fun p hp => by
    rw [← hL] at hp; have := List.mem_filter.mp hp; exact ⟨by simpa using this.2, this.1⟩
  have fin : ∀ s₂ : State, Only (L₂.map (·.1)) s₁ s₂ →
      (∀ i (h : i < rs.length), rs[i] = .x19 → s₂.gpr .x19 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 (o + 8 * i)) 64) →
      WP isa (.block is) s₂ Q := fun s₂ o₂ v₂ => k s₂ ((o₁.trans o₂).mono fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
          rw [List.mem_filter] at hp
          have := (List.mem_zipIdx (x := p.1) (i := p.2) hp.1)
          rw [this.2.2]; exact List.getElem_mem _
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
          have := List.mem_zipIdx (x := p.1) (i := p.2) (hL₂ p hp).2
          rw [this.2.2]; exact List.getElem_mem _) fun i h => by
        by_cases e : rs[i] = .x19
        · rw [e]; exact v₂ i h e
        · rw [o₂.get _ (fun hm => by
            obtain ⟨p, hp, ep⟩ := List.mem_map.mp hm
            exact e (ep ▸ (hL₂ p hp).1))]
          exact v₁ (rs[i], i) (List.mem_filter.mpr ⟨hidx i h, by simpa using e⟩)
  rcases L₂ with _ | ⟨p, _ | ⟨p', L⟩⟩
  · simp only [List.map_nil, List.nil_append]
    refine fin s₁ (Only.refl _ _) fun i h e => absurd (hL ▸ List.mem_filter.mpr
      ⟨hidx i h, by simp [e]⟩ : (rs[i], i) ∈ ([] : List (Reg × Nat))) List.not_mem_nil
  · obtain ⟨hp1, hpz⟩ := hL₂ p List.mem_cons_self
    obtain ⟨-, hp2, hpr⟩ := List.mem_zipIdx (x := p.1) (i := p.2) hpz
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [hp1]
    refine wp_ldrx (a := s₁.gpr .x19 + BitVec.ofNat 64 (o + 8 * p.2)) ⟨by omega_using [ho], by omega_using [ho, hp2]⟩
      rfl (by rw [o₁.rd, o₁.wr, g₁, ← addr_add]; exact InRegions.sub hin (by omega_using [hp2])) fun s₂ o₂ e₂ =>
        fin s₂ (by rw [List.map_cons, List.map_nil, hp1]; exact o₂) fun i h e => ?_
    have hi : i = p.2 := by
      have hm : (rs[i], i) ∈ [p] := hL ▸ List.mem_filter.mpr ⟨hidx i h, by simp [e]⟩
      rw [← List.mem_singleton.mp hm]
    subst hi
    rw [e₂, o₁.mem, g₁]
  · obtain ⟨h₁, -⟩ := hL₂ p List.mem_cons_self
    obtain ⟨h₂, -⟩ := hL₂ p' (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, h₁, h₂, true_or, not_true_eq_false, false_and]
      at hnd2
end

end VG.Proof.SlhDsa.AArch64
