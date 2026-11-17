module

public import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
public import VerifiedGarbage.Proof.Cast5.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Cast5.Scan
public import VerifiedGarbage.Impl.Cast5.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `Cast5.AArch64.Scan`, which only this module used -/

section

/-!
# CAST5 on AArch64: the scan of a table

`scan sym` visits the 256 entries of 16 bytes of the table at `T` (the
address of `sym`), in order, and leaves in each lane `k` of `v1` word `k` of
the entry whose number is in lane `k` of `v0` (`scan_ok`). Vector values
are kept as their four lanes (`L`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (s1234Sym s5678Sym)
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## Lanes -/

/-- The value whose lanes are `f 0, f 1, f 2, f 3`. -/
def L (f : Nat → BitVec 32) : BitVec 128 := ofVWords (f 0) (f 1) (f 2) (f 3)

theorem vword_L (f : Nat → BitVec 32) {k : Nat} (hk : k < 4) : vword (L f) k = f k := by
  rw [L, vword_ofVWords _ _ _ _ hk]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> rfl

theorem L_vword (x : BitVec 128) : L (vword x ·) = x := ofVWords_vword x

theorem L_congr {f g : Nat → BitVec 32} (h : ∀ k < 4, f k = g k) : L f = L g := by
  simp only [L, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

theorem vword_and (x y : BitVec 128) (k : Nat) : vword (x &&& y) k = vword x k &&& vword y k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [vword, hj]

theorem vword_or (x y : BitVec 128) (k : Nat) : vword (x ||| y) k = vword x k ||| vword y k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [vword, hj]

theorem and_L (f g : Nat → BitVec 32) : (L f &&& L g) = L fun k => f k &&& g k :=
  vec_ext fun k hk => by rw [vword_and, vword_L _ hk, vword_L _ hk, vword_L _ hk]

theorem or_L (f g : Nat → BitVec 32) : (L f ||| L g) = L fun k => f k ||| g k :=
  vec_ext fun k hk => by rw [vword_or, vword_L _ hk, vword_L _ hk, vword_L _ hk]

theorem cmeq_L (f g : Nat → BitVec 32) :
    VArr.s4.map2 (fun w x y => if x = y then BitVec.allOnes w else 0) (L f) (L g) =
      L fun k => if f k = g k then 0xFFFFFFFF else 0 :=
  vec_ext fun k hk => by
    rw [vword_map2 _ _ _ hk, vword_L _ hk, vword_L _ hk, vword_L _ hk]
    rfl

theorem add_L (f g : Nat → BitVec 32) :
    VArr.s4.map2 (fun _ x y => x + y) (L f) (L g) = L fun k => f k + g k :=
  vec_ext fun k hk => by rw [vword_map2 _ _ _ hk, vword_L _ hk, vword_L _ hk, vword_L _ hk]

/-- A 16-byte load, as its four words. -/
theorem read16_L (m : Mem) (a : Addr) :
    m.read a 16 = L fun k => m.readW (a + BitVec.ofNat 64 (4 * k)) 32 :=
  vec_ext fun k hk => by rw [vword_read16 _ _ hk, vword_L _ hk]

theorem xor_L (f g : Nat → BitVec 32) : (L f ^^^ L g) = L fun k => f k ^^^ g k :=
  vec_ext fun k hk => by
    have hx (x y : BitVec 128) : vword (x ^^^ y) k = vword x k ^^^ vword y k := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp [vword, hj]
    rw [hx, vword_L _ hk, vword_L _ hk, vword_L _ hk]

theorem sub_L (f g : Nat → BitVec 32) :
    VArr.s4.map2 (fun _ x y => x - y) (L f) (L g) = L fun k => f k - g k :=
  vec_ext fun k hk => by rw [vword_map2 _ _ _ hk, vword_L _ hk, vword_L _ hk, vword_L _ hk]

theorem shr_L (x : BitVec 128) (f : Nat → BitVec 32) (n : Nat) :
    VArr.s4.map2 (fun w a b => VShiftOp.eval .ushr n w a b) x (L f) =
      L fun k => f k >>> n :=
  vec_ext fun k hk => by
    rw [vword_map2 _ _ _ hk, vword_L _ hk, vword_L _ hk]
    rfl

theorem bit_L (f g h : Nat → BitVec 32) :
    VSelOp.eval .bit (L f) (L g) (L h) = L fun k => mux (f k) (g k) (h k) := by
  simp only [VSelOp.eval, xor_L, and_L, mux, BitVec.xor_comm]

/-- Everything except the public scan pointer/counter, flags, v1–v5 and v16–v19. -/
structure ScanKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x10 → r ≠ .x11 → t.gpr r = s.gpr r
  v : ∀ x, x ≠ .v1 → x ≠ .v2 → x ≠ .v3 → x ≠ .v4 → x ≠ .v5 →
    x ≠ .v16 → x ≠ .v17 → x ≠ .v18 → x ≠ .v19 → t.v x = s.v x
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem ScanKeep.trans {s t u : State} (h : ScanKeep s t) (h' : ScanKeep t u) : ScanKeep s u :=
  ⟨fun r a b => (h'.gpr r a b).trans (h.gpr r a b),
   fun x a b c d e f g h8 i => (h'.v x a b c d e f g h8 i).trans (h.v x a b c d e f g h8 i),
   h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

/-- State after q groups of four fixed-address loads. -/
structure ScanAt (s₀ : State) (T : Addr) (idx : Nat → BitVec 32) (q : Nat) (s : State) : Prop where
  v0 : s.v .v0 = L idx
  v1 : s.v .v1 = L (acc s₀.mem T idx (4 * q))
  v2 : s.v .v2 = L (splat q)
  v3 : s.v .v3 = L (splat 1)
  v16 : s.v .v16 = L fun k => bitMask (idx k)
  v17 : s.v .v17 = L fun k => bitMask (idx k >>> 1)
  v18 : s.v .v18 = L fun k => idx k >>> 2
  keep : ScanKeep s₀ s

/-- The table at T is readable. -/
def Readable (s : State) (T : Addr) : Prop := InRegions (s.rd ++ s.wr) T 4096

theorem tile_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {q : Nat} (hq : q < 64)
    (hT : Readable s₀ T) (hx10 : s.gpr .x10 = T + BitVec.ofNat 64 (64 * q))
    (h : ScanAt s₀ T idx q s) :
    WP isa (.block scanTile) s fun t => ScanAt s₀ T idx (q + 1) t ∧ t.gpr = s.gpr := by
  obtain ⟨h0, h1, h2, h3, h16, h17, h18, hk⟩ := h
  have ha (e : Nat) : s.gpr .x10 + BitVec.ofNat 64 (16 * e) =
      T + BitVec.ofNat 64 (16 * (4 * q + e)) := by
    rw [hx10, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega_using []
  have hr (e : Nat) (he : e < 4) :
      InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (16 * (4 * q + e))) 16 := by
    rw [hk.rd, hk.wr]
    exact CallLay.inRegions_sub hT (by omega_using [hq, he]) (by decide)
  unfold scanTile
  crun [ha 0, ha 1, ha 2, ha 3, hr 0 (by decide), hr 1 (by decide),
    hr 2 (by decide), hr 3 (by decide)]
  have hm : s.mem = s₀.mem := hk.mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [v_setV_of_ne, h0]
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self, h1, h2, h16, h17, h18,
      read16_L, bit_L, cmeq_L, and_L, or_L, hm]
    refine L_congr fun k _ => ?_
    rw [← acc_tile _ _ _ hq k]
    simp only [tileVal, ent, splat, Offset.add_add, Nat.add_zero]
    rfl
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self, h2, h3, add_L]
    exact L_congr fun k _ => by simp only [splat, BitVec.ofNat_add]
  · simp (disch := decide) only [v_setV_of_ne, h3]
  · simp (disch := decide) only [v_setV_of_ne, h16]
  · simp (disch := decide) only [v_setV_of_ne, h17]
  · simp (disch := decide) only [v_setV_of_ne, h18]
  · refine hk.trans ⟨fun _ _ _ => by simp only [gpr_setV],
      fun x a b c d e f g h8 i => ?_, by simp only [mem_setV],
      by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩
    simp only [v_setV_of_ne _ _ a, v_setV_of_ne _ _ b, v_setV_of_ne _ _ d,
      v_setV_of_ne _ _ e, v_setV_of_ne _ _ i]

theorem body_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {q : Nat} (hq : q < 64)
    (hT : Readable s₀ T) (hx10 : s.gpr .x10 = T + BitVec.ofNat 64 (64 * q))
    (h : ScanAt s₀ T idx q s) :
    WP isa (.block scanBody) s fun t => ScanAt s₀ T idx (q + 1) t ∧
      t.gpr .x10 = T + BitVec.ofNat 64 (64 * (q + 1)) ∧
      t.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 := by
  unfold scanBody
  rw [WP.block_append_iff]
  refine WP.mono (tile_ok hq hT hx10 h) fun t ⟨ht, hg⟩ => ?_
  crun
  rw [hg, hx10, BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * q + 64 = 64 * (q + 1) by omega_using []]
  refine ⟨⟨ht.v0, ht.v1, ht.v2, ht.v3, ht.v16, ht.v17, ht.v18,
    ht.keep.trans ⟨fun r a b => ?_, fun _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩, rfl, rfl⟩
  simp only [gpr_write_of_ne _ _ _ b, gpr_write_of_ne _ _ _ a]

theorem acc_zero (m : Mem) (T : Addr) (idx : Nat → BitVec 32) : L (acc m T idx 0) = 0 := by
  rw [show (0 : BitVec 128) = L fun _ => 0 by decide]
  exact L_congr fun k _ => by simp [acc]

theorem ones_L (x y : BitVec 128) :
    VArr.s4.map2 (fun w a b => VShiftOp.eval .ushr 31 w a b) y
      (VArr.s4.map2 (fun w a b => if a = b then BitVec.allOnes w else 0) x x) = L (splat 1) := by
  rw [← L_vword x, cmeq_L]
  refine vec_ext fun k hk => ?_
  rw [vword_map2 _ _ _ hk, vword_L _ hk, ite_eq_left rfl, vword_L _ hk]
  simp only [VShiftOp.eval, splat]
  decide

/-- Public counters, zero accumulator, and masks of the low two index bits. -/
theorem start_ok (s : State) (sym : String) {idx : Nat → BitVec 32} (h0 : s.v .v0 = L idx) :
    WP isa (.block (scanStart sym)) s
      fun t => ScanAt s (s.syms sym) idx 0 t ∧ t.gpr .x10 = s.syms sym ∧
        t.gpr .x11 = BitVec.ofNat 64 64 := by
  unfold scanStart
  crun [VShiftOp.ok, VArr.esize]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r a b => ?_,
    fun x a b c d e f g h8 i => ?_, rfl, rfl, rfl, rfl⟩⟩, rfl⟩
  · simp (disch := decide) only [v_setV_of_ne, v_write, h0]
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self, Nat.mul_zero]
    exact (acc_zero _ _ _).symm
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self]
    decide
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self, ones_L]
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self, v_write, h0, ones_L,
      show (0 : BitVec 128) = L (fun _ => 0) by decide, and_L, sub_L]
    rfl
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self, v_write, h0, ones_L,
      show (0 : BitVec 128) = L (fun _ => 0) by decide, shr_L, and_L, sub_L]
    rfl
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self, v_write, h0, shr_L]
  · simp only [gpr_setV, gpr_write_of_ne _ _ _ b, gpr_write_of_ne _ _ _ a]
  · simp only [v_setV_of_ne _ _ a, v_setV_of_ne _ _ b, v_setV_of_ne _ _ c,
      v_setV_of_ne _ _ d, v_setV_of_ne _ _ f, v_setV_of_ne _ _ g,
      v_setV_of_ne _ _ h8, v_write]

/-- Every lane selects its indexed word after all 64 groups. -/
theorem scan_ok (s : State) (sym : String) {idx : Nat → BitVec 32} (h0 : s.v .v0 = L idx)
    (hidx : ∀ k < 4, (idx k).toNat < 256) (hT : Readable s (s.syms sym)) :
    WP isa (scan sym) s fun t =>
      t.v .v1 = L (fun k => ent s.mem (s.syms sym) (idx k).toNat k) ∧ ScanKeep s t := by
  unfold scan
  refine WP.seq (WP.mono (start_ok s sym h0) fun t ⟨ht, h10, h11⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x11) (N := 64) (by decide) (by decide)
    (fun q u => ScanAt s (s.syms sym) idx q u ∧
      u.gpr .x10 = s.syms sym + BitVec.ofNat 64 (64 * q))
    (fun q hq u ⟨hu, h10⟩ _ => WP.mono (body_ok hq hT h10 hu) fun v ⟨hv, h10', h11'⟩ =>
      ⟨⟨hv, h10'⟩, h11'⟩)
    ⟨ht, by rw [h10]; exact (BitVec.add_zero _).symm⟩ h11) fun u ⟨hu, _⟩ => ⟨?_, hu.keep⟩
  rw [hu.v1]
  exact L_congr fun k hk => by rw [acc, ite_eq_left (by have := hidx k hk; omega_using [this])]

end VG.Proof.Cast5.AArch64

end

end

/-! ### `Cast5.AArch64.Round`, which only this module used -/

section

/-!
# CAST5 on AArch64: a round

`round t up` computes `I` (`mask`, `rotate`), spreads its bytes over the
lanes of `v0` (`spread`), scans `VG_CAST5_S1234` and combines the four
values into `f` (`combine`), then makes the Feistel step (`feistel`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym)
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The rotation -/

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (hax : s.gpr .x4 = a.setWidth 64) (h13 : s.gpr .x13 = kb.setWidth 64) :
    WP isa (.block (rotateStep b)) s fun t =>
      t.gpr .x4 = (Proof.Cast5.selStep a kb b).setWidth 64 ∧
      t.gpr .x13 = (if b < 4 then kb >>> 1 else kb).setWidth 64 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.v = s.v := by
  have hn : 32 - 2 ^ b < 32 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    crun [hax, h13, hn, CondCode.holds, zf_write]
    refine ⟨?_, by rw [ite_eq_left h4]⟩
    unfold Proof.Cast5.selStep
    simp
  · rw [ite_eq_right h4]
    crun [hax, h13, hn, CondCode.holds, zf_write]
    refine ⟨?_, by rw [ite_eq_right h4]⟩
    unfold Proof.Cast5.selStep
    simp

theorem rotate_ok (s : State) {a kb : BitVec 32}
    (hax : s.gpr .x4 = a.setWidth 64) (h13 : s.gpr .x13 = kb.setWidth 64) :
    WP isa (.block rotate) s fun t =>
      t.gpr .x4 = (a.rotateLeft (kb.toNat % 32)).setWidth 64 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.v = s.v := by
  have e : rotate = rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++ rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rotateStep_ok s (by decide) hax h13) fun t₁ ⟨a₁, k₁, m₁, r₁, w₁, x₁⟩ => ?_
  rw [ite_eq_left (by decide)] at k₁
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, m₂, r₂, w₂, x₂⟩ => ?_
  rw [ite_eq_left (by decide)] at k₂
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, m₃, r₃, w₃, x₃⟩ => ?_
  rw [ite_eq_left (by decide)] at k₃
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, m₄, r₄, w₄, x₄⟩ => ?_
  rw [ite_eq_left (by decide)] at k₄
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, m₅, r₅, w₅, x₅⟩ => ?_
  refine ⟨?_, by rw [m₅, m₄, m₃, m₂, m₁], by rw [r₅, r₄, r₃, r₂, r₁], by rw [w₅, w₄, w₃, w₂, w₁],
    by rw [x₅, x₄, x₃, x₂, x₁]⟩
  rw [a₅]
  simp only [Proof.Cast5.selStep_eq_step _ _ (show 0 < 5 by decide),
    Proof.Cast5.selStep_eq_step _ _ (show 1 < 5 by decide), Proof.Cast5.selStep_eq_step _ _ (show 2 < 5 by decide),
    Proof.Cast5.selStep_eq_step _ _ (show 3 < 5 by decide), Proof.Cast5.selStep_eq_step _ _ (show 4 < 5 by decide),
    Proof.Cast5.steps_eq]

/-! ## The indices -/

/-- Lane `k` of the indices `spread` makes of `I`: byte `3 - k` of `I`. -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i <<< 24 >>> 24
  | 1 => i <<< 16 >>> 24
  | 2 => i <<< 8 >>> 24
  | _ => i >>> 24

theorem idx_toNat (i : BitVec 32) {k : Nat} (hk : k < 4) :
    (idx i k).toNat = i.toNat / 2 ^ (8 * k) % 256 := by
  have := i.isLt
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq] <;> omega_using []

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rw [idx_toNat i hk]; omega_using []

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, idx_toNat i hk]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> omega_using []

theorem spread_ok (s : State) {i : BitVec 32} (hax : s.gpr .x4 = i.setWidth 64) :
    WP isa (.block spread) s fun t =>
      t.v .v0 = L (idx i) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        (∀ x, x ≠ .v0 → t.v x = s.v x) := by
  unfold spread
  crun [hax]
  refine ⟨?_, fun x h0 => ?_⟩
  · rw [setLane_four]
    rfl
  · simp only [v_write, v_setV_of_ne _ _ h0]

/-! ## The round -/

theorem mask_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km kr d : Spec.Cast5.Word}
    (h6 : s.gpr .x6 = d.setWidth 64)
    (hm : InRegions (s.rd ++ s.wr) (s.gpr .x12) 4) (hmv : s.mem.readW (s.gpr .x12) 32 = km)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 64) 4)
    (hrv : s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 64) 32 = kr) :
    WP isa (.block (mask t)) s fun u =>
      u.gpr .x4 = (Proof.Cast5.mix t km d).setWidth 64 ∧ u.gpr .x13 = kr.setWidth 64 ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v := by
  have e0 : s.gpr .x12 + BitVec.ofNat 64 0 = s.gpr .x12 := BitVec.add_zero _
  have hm' : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 0) 4 := by rw [e0]; exact hm
  have hmv' : s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 0) 32 = km := by rw [e0]; exact hmv
  rcases ht with rfl | rfl | rfl <;>
  · unfold mask
    crun [h6, hm', hmv', hr, hrv]
    rfl

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

theorem post_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {v : Nat → Spec.Cast5.Word} {l r : Spec.Cast5.Word}
    (h1 : s.v .v1 = L v) (h5 : s.gpr .x5 = l.setWidth 64) (h6 : s.gpr .x6 = r.setWidth 64) :
    WP isa (.block (combine t ++ feistel up)) s fun u =>
      u.gpr .x5 = r.setWidth 64 ∧
        u.gpr .x6 = (l ^^^ Proof.Cast5.comb t (v 3) (v 2) (v 1) (v 0)).setWidth 64 ∧
        u.gpr .x12 = (if up then s.gpr .x12 + 4 else s.gpr .x12 - 4) ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v := by
  have d0 : vword (L v) 0 = v 0 := vword_L v (by decide)
  have d1 : vword (L v) 1 = v 1 := vword_L v (by decide)
  have d2 : vword (L v) 2 = v 2 := vword_L v (by decide)
  have d3 : vword (L v) 3 = v 3 := vword_L v (by decide)
  rcases ht with rfl | rfl | rfl <;> cases up <;>
  · unfold combine feistel
    crun [h1, h5, h6, d0, d1, d2, d3, BitVec.or_self]
    exact ⟨by rw [BitVec.xor_comm]; rfl, rfl⟩

/-- The registers a round writes. -/
def roundRegs : List Reg := [.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

/-- What a round needs: `(L, R)` in `w5`, `w6`; `Kmᵢ` at `x12` and `Krᵢ` at
`x12 + 64`; the table. -/
structure RoundPre (s : State) (km kr l r : Spec.Cast5.Word) : Prop where
  x5 : s.gpr .x5 = l.setWidth 64
  x6 : s.gpr .x6 = r.setWidth 64
  inM : InRegions (s.rd ++ s.wr) (s.gpr .x12) 4
  valM : s.mem.readW (s.gpr .x12) 32 = km
  inR : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 64) 4
  valR : s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 64) 32 = kr
  tab : Readable s (s.syms s1234Sym)
  held : Held s.mem (s.syms s1234Sym) s1234

/-- The first block of a round: `I`, and its bytes in the lanes of `v0`. -/
theorem first_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km kr l r : Spec.Cast5.Word}
    (h : RoundPre s km kr l r) :
    WP isa (.block (mask t ++ rotate ++ spread)) s
      fun u => u.v .v0 = L (idx ((Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32))) ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mask_ok s ht h.x6 h.inM h.valM h.inR h.valR) fun u ⟨ua, u13, um, urd, uwr, _⟩ => ?_
  refine WP.mono (rotate_ok u ua u13) fun v ⟨va, vm, vrd, vwr, _⟩ => ?_
  refine WP.mono (spread_ok v va) fun w ⟨w0, wm, wrd, wwr, _⟩ => ?_
  exact ⟨w0, wm.trans (vm.trans um), wrd.trans (vrd.trans urd), wwr.trans (vwr.trans uwr)⟩

theorem round_writes {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool) :
    writesOnly roundRegs (round t up) = true ∧ (round t up).noCalls = true ∧
      (round t up).allInstrs keepsV = true := by
  rcases ht with rfl | rfl | rfl <;> cases up <;> exact ⟨by decide, by decide, by decide +kernel⟩

theorem round_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {km kr l r : Spec.Cast5.Word} (h : RoundPre s km kr l r) :
    WP isa (round t up) s fun u =>
      u.gpr .x5 = r.setWidth 64 ∧ u.gpr .x6 = (l ^^^ fT t km kr r).setWidth 64 ∧
      u.gpr .x12 = (if up then s.gpr .x12 + 4 else s.gpr .x12 - 4) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧ Keep roundRegs s u := by
  obtain ⟨hw, hn, hv⟩ := round_writes ht up
  suffices main : WP isa (round t up) s fun u =>
      u.gpr .x5 = r.setWidth 64 ∧ u.gpr .x6 = (l ^^^ fT t km kr r).setWidth 64 ∧
      u.gpr .x12 = (if up then s.gpr .x12 + 4 else s.gpr .x12 - 4) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr by
    exact WP.mono_syms (WP.keep roundRegs main hw hn hv) fun u ⟨⟨a, b, c, d, e, f⟩, hku⟩ hsy =>
      ⟨a, b, c, d, e, f, hsy, hku⟩
  unfold round
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  have hw1 : writesOnly [.x4, .x9, .x13, .x14, .x15] (.block (mask t ++ rotate ++ spread)) = true ∧
      (.block (mask t ++ rotate ++ spread) : Prog isa).allInstrs keepsV = true := by
    rcases ht with rfl | rfl | rfl <;> exact ⟨by decide, by decide +kernel⟩
  refine WP.seq (WP.mono_syms (WP.keep [.x4, .x9, .x13, .x14, .x15] (first_ok s ht h) hw1.1 rfl hw1.2)
    fun u ⟨⟨u0, um, urd, uwr⟩, uk⟩ usy => ?_)
  rw [hi] at u0
  have hT : Readable u (u.syms s1234Sym) := by unfold Readable; rw [usy, urd, uwr]; exact h.tab
  refine WP.seq (WP.mono (scan_ok u s1234Sym u0 (fun k hk => idx_lt i hk) hT) fun v ⟨v1, vk⟩ => ?_)
  have g (q : Reg) (hq : q ∉ [Reg.x4, .x9, .x13, .x14, .x15]) (h10 : q ≠ .x10) (h11 : q ≠ .x11) :
      v.gpr q = s.gpr q := (vk.gpr q h10 h11).trans (uk.gpr q hq)
  refine WP.mono (post_ok v ht up (l := l) (r := r) v1 (by rw [g .x5 (by decide) (by decide) (by decide)]; exact h.x5)
    (by rw [g .x6 (by decide) (by decide) (by decide)]; exact h.x6))
    fun w ⟨w5, w6, w12, wm, wrd, wwr, _⟩ => ?_
  refine ⟨w5, ?_, ?_, by rw [wm, vk.mem, um], by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr]⟩
  · rw [w6]
    congr 2
    unfold fT
    rw [hi]
    have e (k : Nat) (hk : k < 4) : ent u.mem (u.syms s1234Sym) (idx i k).toNat k =
        tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1 (idx i k).toNat k :=
      ent_table (by rw [um, usy]; exact h.held) (idx_lt i hk) hk
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  · rw [w12, g .x12 (by decide) (by decide) (by decide)]

end VG.Proof.Cast5.AArch64

end

end


/-!
# CAST5 on AArch64: a block

The rounds of a block, three at a time (`group`), and the block functions
`encryptBlock` and `decryptBlock`: from the block at `x2` to its encryption
or decryption there.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym)
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)

/-- `fT` of the type of round `i` is the spec's `f`. -/
theorem fT_eq {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (km kr d : Spec.Cast5.Word) :
    fT t km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]
  unfold fT roundI
  rcases ht with rfl | rfl | rfl <;> rw [← hti] <;> rfl

theorem s1234_length : s1234.length = 512 := table_length _ _ _ _

/-- What every round of a block reads: the subkeys `k` at `x0` and the table. -/
structure Ctx (s : State) (k : Spec.Cast5.Schedule) : Prop where
  sched : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128
  key : ∀ j < 32, s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0
  tab : Readable s (s.syms s1234Sym)
  held : Held s.mem (s.syms s1234Sym) s1234

theorem Ctx.transfer {s u : State} {k : Spec.Cast5.Schedule} (h : Ctx s k)
    (h0 : u.gpr .x0 = s.gpr .x0) (hm : u.mem = s.mem) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsy : u.syms = s.syms) : Ctx u k :=
  ⟨by rw [hrd, hwr, h0]; exact h.sched, fun j hj => by rw [h0, hm]; exact h.key j hj,
    by unfold Readable; rw [hrd, hwr, hsy]; exact h.tab, by rw [hm, hsy]; exact h.held⟩

/-- Round `i`'s precondition, with `x12` at `Kmᵢ`. -/
theorem Ctx.roundPre {s : State} {k : Spec.Cast5.Schedule} (h : Ctx s k) {i : Nat}
    (hi : 1 ≤ i ∧ i ≤ 16) (h12 : s.gpr .x12 = s.gpr .x0 + BitVec.ofNat 64 (4 * (i - 1)))
    {l r : Spec.Cast5.Word} (h5 : s.gpr .x5 = l.setWidth 64) (h6 : s.gpr .x6 = r.setWidth 64) :
    RoundPre s (k.getD (i - 1) 0) (k.getD (15 + i) 0) l r := by
  have h64 : s.gpr .x12 + BitVec.ofNat 64 64 = s.gpr .x0 + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [h12, add_ofNat_add]; congr 2; omega_arith
  refine ⟨h5, h6, ?_, ?_, ?_, ?_, h.tab, h.held⟩
  · rw [h12]; exact CallLay.inRegions_sub h.sched (by omega_arith) (by decide)
  · rw [h12]; exact h.key _ (by omega_arith)
  · rw [h64]; exact CallLay.inRegions_sub h.sched (by omega_arith) (by decide)
  · rw [h64]; exact h.key _ (by omega_arith)

/-- The registers a block writes. -/
def blockRegs : List Reg := roundRegs ++ [.x7, .x8]

/-- The state of a block's rounds, from `s`, with the halves `lr`. -/
structure RInv (s : State) (k : Spec.Cast5.Schedule) (lr : Spec.Cast5.Word × Spec.Cast5.Word)
    (u : State) : Prop where
  x5 : u.gpr .x5 = lr.1.setWidth 64
  x6 : u.gpr .x6 = lr.2.setWidth 64
  ctx : Ctx u k
  same : ∀ q, q ∉ blockRegs → u.gpr q = s.gpr q
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  mem : u.mem = s.mem

theorem round_step {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3)
    (hi : 1 ≤ i ∧ i ≤ 16) (h12 : u.gpr .x12 = u.gpr .x0 + BitVec.ofNat 64 (4 * (i - 1))) (up : Bool) :
    WP isa (round t up) u fun v => RInv s k (Spec.Cast5.round k i lr) v ∧
      v.gpr .x12 = (if up then u.gpr .x12 + 4 else u.gpr .x12 - 4) ∧ v.gpr .x7 = u.gpr .x7 ∧
      v.gpr .x8 = u.gpr .x8 := by
  refine WP.mono (round_ok u ht up (h.ctx.roundPre hi h12 h.x5 h.x6))
    fun v ⟨v5, v6, v12, vm, vrd, vwr, vsy, vk⟩ => ?_
  have g (q : Reg) (hq : q ∉ roundRegs) : v.gpr q = u.gpr q := vk.gpr q hq
  refine ⟨⟨v5, ?_, h.ctx.transfer (g .x0 (by decide)) vm vrd vwr vsy,
    fun q hq => (g q fun e => hq (List.mem_append_left _ e)).trans (h.same q hq), vrd.trans h.rd,
    vwr.trans h.wr, vsy.trans h.syms, vm.trans h.mem⟩, v12, g .x7 (by decide), g .x8 (by decide)⟩
  rw [v6, fT_eq ht hti]
  rfl

/-- `sub x7, x7, 1`. -/
theorem countDown_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) :
    WP isa (.block [.subImm .x .x7 .x7 1]) u fun v => RInv s k lr v ∧ v.gpr .x12 = u.gpr .x12 ∧
      v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  crun
  refine ⟨h.x5, h.x6, h.ctx.transfer rfl rfl rfl rfl rfl, fun q hq => ?_, h.rd, h.wr, h.syms, h.mem⟩
  have : q ≠ .x7 := fun e => hq (by rw [e]; decide)
  rw [gpr_write_of_ne _ _ _ this]
  exact h.same q hq

theorem four : (4 : Addr) = BitVec.ofNat 64 4 := rfl

/-- Rounds `3 g + 1`, `3 g + 2`, `3 g + 3` of encryption. -/
theorem groupEnc_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {g : Nat} (hg : 3 * g + 3 ≤ 16) (h : RInv s k (encFold k (3 * g) lr) u)
    (h12 : u.gpr .x12 = u.gpr .x0 + BitVec.ofNat 64 (12 * g)) :
    WP isa (group true) u fun v => RInv s k (encFold k (3 * (g + 1)) lr) v ∧
      v.gpr .x12 = v.gpr .x0 + BitVec.ofNat 64 (12 * (g + 1)) ∧
      v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  have hdi : ∀ v : State, (∀ lr', RInv s k lr' v → v.gpr .x0 = u.gpr .x0) :=
    fun v lr' hv => (hv.same .x0 (by decide)).trans (h.same .x0 (by decide)).symm
  unfold group
  simp only [ite_true]
  refine WP.seq (WP.mono (round_step h (t := 1) (i := 3 * g + 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [h12]; congr 2; omega_arith) true) fun v₁ ⟨h₁, a₁, b₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := 3 * g + 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁, ite_eq_left rfl, h12, hdi v₁ _ h₁, four, add_ofNat_add]; congr 2; omega_arith) true)
    fun v₂ ⟨h₂, a₂, b₂, c₂⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₂ (t := 3) (i := 3 * g + 3) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h12, hdi v₂ _ h₂, four, add_ofNat_add, add_ofNat_add]
        congr 2; omega_arith)
    true) fun v₃ ⟨h₃, a₃, b₃, c₃⟩ => ?_)
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, c₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [c₄, c₃, c₂, c₁]⟩
  · rw [show 3 * (g + 1) = 3 * g + 2 + 1 by omega_arith, encFold_succ, encFold_succ, encFold_succ]
    exact h₄
  · rw [a₄, a₃, ite_eq_left rfl, a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h12, hdi v₄ _ h₄, four,
      add_ofNat_add, add_ofNat_add, add_ofNat_add, show 12 * g + 4 + 4 + 4 = 12 * (g + 1) by omega_arith]

/-- What a block needs: the context, `n` rounds in `x1`, and the block at
`x2`. -/
structure BPre (s : State) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  ctx : Ctx s k
  nv : n = 12 ∨ n = 16
  x1 : s.gpr .x1 = BitVec.ofNat 64 n
  data : InRegions s.wr (s.gpr .x2) 8

theorem rev32_eq (x : BitVec 32) : rev32 x = byteRev32 x := rfl

theorem BPre.ld0 {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 4 := by
  obtain ⟨g, hg, hc⟩ := h.data
  exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega_arith) (by decide)

theorem BPre.ld4 {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 4) 4 := by
  obtain ⟨g, hg, hc⟩ := h.data
  exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega_arith) (by decide)

theorem groups_x7 {n : Nat} (hn : n = 12 ∨ n = 16) :
    BitVec.ofNat 64 n >>> 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n / 4 + 1) := by
  rcases hn with rfl | rfl <;> decide

theorem x8_zero {n : Nat} (hn : n = 12 ∨ n = 16) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 16 == 0) = decide (n = 16) := by
  rcases hn with rfl | rfl <;> decide

/-- The block loaded, `x12` at the first subkeys, and the count of groups. -/
theorem blockStart_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa (.block (load ++ ([.addImm .x .x12 .x0 0] : List Instr) ++ groups)) s fun u =>
      RInv s k (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2))) u ∧
      u.gpr .x12 = u.gpr .x0 ∧ u.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) ∧
      u.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16 := by
  have hd0 := h.ld0
  have hd4 := h.ld4
  unfold load groups
  crun [hd0, hd4, h.x1]
  have hdec := decodeBlock_blockAt s.mem (s.gpr .x2)
  refine ⟨⟨?_, ?_, h.ctx.transfer ?_ rfl rfl rfl rfl, fun q hq => ?_, rfl, rfl, rfl, rfl⟩, BitVec.add_zero _,
    groups_x7 h.nv⟩
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, hdec, rev32_eq, BitVec.add_zero]
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, hdec, rev32_eq]
  · simp only [gpr_write, reduceCtorEq, ite_false]
  · have h1 : q ≠ .x5 := fun e => hq (by rw [e]; decide)
    have h2 : q ≠ .x6 := fun e => hq (by rw [e]; decide)
    have h3 : q ≠ .x12 := fun e => hq (by rw [e]; decide)
    have h4 : q ≠ .x7 := fun e => hq (by rw [e]; decide)
    have h5 : q ≠ .x8 := fun e => hq (by rw [e]; decide)
    simp only [gpr_write, h1, h2, h3, h4, h5, ite_false]

/-- `(Rₙ, Lₙ)` stored, then on to the next block. -/
theorem store_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (hd : InRegions u.wr (u.gpr .x2) 8) :
    WP isa (.block store) u fun v =>
      v.mem = (u.mem.writeW (u.gpr .x2) (byteRev32 lr.2)).writeW (u.gpr .x2 + BitVec.ofNat 64 4)
        (byteRev32 lr.1) ∧
      v.gpr .x2 = u.gpr .x2 + BitVec.ofNat 64 8 ∧ v.gpr .x3 = u.gpr .x3 - BitVec.ofNat 64 1 ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms ∧
      (∀ q, q ≠ .x5 → q ≠ .x6 → q ≠ .x2 → q ≠ .x3 → v.gpr q = u.gpr q) := by
  have hd0 : InRegions u.wr (u.gpr .x2 + BitVec.ofNat 64 0) 4 := CallLay.inRegions_sub hd (by omega_arith) (by decide)
  have hd4 : InRegions u.wr (u.gpr .x2 + BitVec.ofNat 64 4) 4 := CallLay.inRegions_sub hd (by omega_arith) (by decide)
  have h5 := h.x5
  have h6 := h.x6
  unfold store
  crun [hd0, hd4, h5, h6, rev32_eq]
  refine ⟨by rw [BitVec.add_zero], fun q a b c d => ?_⟩
  simp only [a, b, c, d, ite_false]

/-- What a block function does. -/
def BPost (s : State) (out : Spec.Cast5.Block) (v : State) : Prop :=
  Spec.Cast5.blockAt v.mem (s.gpr .x2) = out ∧
  Frame [⟨s.gpr .x2, 8⟩] s.mem v.mem ∧
  v.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 8 ∧ v.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 1 ∧
  v.rd = s.rd ∧ v.wr = s.wr ∧ v.syms = s.syms ∧
  (∀ q, q ∉ blockRegs → q ≠ .x2 → q ≠ .x3 → v.gpr q = s.gpr q)

/-- The store at the end of a block, from the halves `lr` after its rounds. -/
theorem finish_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (hd : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block store) u (BPost s (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have hdx : u.gpr .x2 = s.gpr .x2 := h.same .x2 (by decide)
  have hcx : u.gpr .x3 = s.gpr .x3 := h.same .x3 (by decide)
  refine WP.mono (store_ok h (by rw [h.wr, hdx]; exact hd)) fun v ⟨vm, vdx, vcx, vrd, vwr, vsy, vg⟩ => ?_
  refine ⟨?_, ?_, by rw [vdx, hdx], by rw [vcx, hcx], vrd.trans h.rd, vwr.trans h.wr,
    vsy.trans h.syms, fun q hq hdq hcq => ?_⟩
  · rw [vm, hdx, h.mem, blockAt_write]
  · rw [vm, hdx, h.mem]
    have c0 : Region.Contains ⟨s.gpr .x2, 8⟩ (s.gpr .x2) (32 / 8) := by
      simp [Region.Contains]
    exact (Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _ c0)
      List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith)))
  · rw [vg q (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide)) hdq hcq]
    exact h.same q hq

theorem encryptBlock_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa encryptBlock s
      (BPost s (Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .x2)))) := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 := by rcases h.nv with rfl | rfl <;> decide
  unfold encryptBlock
  refine WP.seq (WP.mono (blockStart_ok h) fun u ⟨hu, u12, u7, u8⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (cnt := .x7) (N := n / 4 + 1) hG.2 hG.1
    (fun g v => RInv s k (encFold k (3 * g) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2)))) v ∧
      v.gpr .x12 = v.gpr .x0 + BitVec.ofNat 64 (12 * g) ∧ v.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16)
    (fun g hg v ⟨hv, h12, h8⟩ _ => WP.mono (groupEnc_ok (by rcases h.nv with rfl | rfl <;> omega_arith) hv h12)
      fun w ⟨hw, w12, w7, w8⟩ => ⟨⟨hw, w12, w8.trans h8⟩, w7⟩)
    ⟨hu, by rw [u12, Nat.mul_zero, BitVec.add_zero], u8⟩ u7) fun v ⟨hv, v12, v8⟩ => ?_)
  refine WP.seq (WP.ite (decide (n = 16)) (by rw [eval_zero, v8, x8_zero h.nv]) (fun h16 => ?_)
    (fun h16 => ?_))
  · have hn : n = 16 := of_decide_eq_true h16
    have v12' : v.gpr .x12 = v.gpr .x0 + BitVec.ofNat 64 (4 * (16 - 1)) := by
      rw [v12, hn]
    refine WP.mono (round_step hv (t := 1) (i := 16) (by decide) (by decide) (by decide) v12' true)
      fun x ⟨hx, _, _, _⟩ => ?_
    have e : Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .x2)) =
        Spec.Cast5.encodeBlock
          ((Spec.Cast5.round k 16 (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock
            (Spec.Cast5.blockAt s.mem (s.gpr .x2))))).2,
          (Spec.Cast5.round k 16 (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock
            (Spec.Cast5.blockAt s.mem (s.gpr .x2))))).1) := by
      rw [encryptBlock_eq, hn, show 3 * (16 / 4 + 1) = 15 from rfl, show 16 = 15 + 1 from rfl,
        encFold_succ]
    rw [e]
    exact finish_ok hx h.data
  · have hn : n = 12 := by
      rcases h.nv with h' | h'
      · exact h'
      · exact absurd h' (of_decide_eq_false h16)
    have e : Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .x2)) =
        Spec.Cast5.encodeBlock
          ((encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2)))).2,
          (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2)))).1) := by
      rw [encryptBlock_eq, hn]
    rw [e]
    exact WP.block_nil (finish_ok hv h.data)

theorem dec_x12 {n : Nat} (hn : n = 12 ∨ n = 16) (x : Addr) :
    BitVec.ofNat 64 n <<< 2 + x - BitVec.ofNat 64 4 = x + BitVec.ofNat 64 (4 * (n - 1)) := by
  rcases hn with rfl | rfl <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    omega_arith

theorem decFold_zero (k : Spec.Cast5.Schedule) (n : Nat) (lr : Spec.Cast5.Word × Spec.Cast5.Word) :
    decFold k n 0 lr = lr := rfl

end VG.Proof.Cast5.AArch64