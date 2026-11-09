module

import VerifiedGarbage.Proof.Cast5.AArch64.Run
public import VerifiedGarbage.Proof.Cast5.Scan
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Impl.Cast5.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd

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
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

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
    omega
  have hr (e : Nat) (he : e < 4) :
      InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (16 * (4 * q + e))) 16 := by
    rw [hk.rd, hk.wr]
    exact CallLay.inRegions_sub hT (by omega) (by decide)
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
  rw [hg, hx10, BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * q + 64 = 64 * (q + 1) by omega]
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
  exact L_congr fun k hk => by rw [acc, ite_eq_left (by have := hidx k hk; omega)]

end VG.Proof.Cast5.AArch64
