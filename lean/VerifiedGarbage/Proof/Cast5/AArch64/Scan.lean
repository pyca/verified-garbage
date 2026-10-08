import VerifiedGarbage.Proof.Cast5.AArch64.Run
import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# CAST5 on AArch64: the scan of a table

`scan sym` visits the 256 entries of 16 bytes of the table at `T` (the
address of `sym`), in order, and leaves in each lane `k` of `v1` word `k` of
the entry whose number is in lane `k` of `v0` (`scan_ok`). Vector values
are kept as their four lanes (`L`).
-/

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

/-! ## One entry -/

/-- Lane `k` of the result once entries `0 … j - 1` are visited. -/
def acc (m : Mem) (T : Addr) (idx : Nat → BitVec 32) (j k : Nat) : BitVec 32 :=
  if (idx k).toNat < j then ent m T (idx k).toNat k else 0

/-- Every lane `n`. -/
def splat (n : Nat) : Nat → BitVec 32 := fun _ => BitVec.ofNat 32 n

theorem zero_or' (y : BitVec 32) : 0 ||| y = y := BitVec.eq_of_getLsbD_eq (by simp)
theorem or_zero' (y : BitVec 32) : y ||| 0 = y := BitVec.eq_of_getLsbD_eq (by simp)
theorem and_zero' (y : BitVec 32) : y &&& 0 = 0 := BitVec.eq_of_getLsbD_eq (by simp)
theorem and_ones' (y : BitVec 32) : y &&& 0xFFFFFFFF = y := by
  rw [show (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

theorem acc_succ (m : Mem) (T : Addr) (idx : Nat → BitVec 32) {j : Nat} (hj : j < 2 ^ 32) (k : Nat) :
    (acc m T idx j k ||| ((ent m T j k) &&& if idx k = BitVec.ofNat 32 j then 0xFFFFFFFF else 0)) =
      acc m T idx (j + 1) k := by
  unfold acc
  by_cases h : idx k = BitVec.ofNat 32 j
  · have hn : (idx k).toNat = j := by rw [h, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hj
    rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), hn, and_ones', zero_or']
  · have hn : (idx k).toNat ≠ j := fun h' => h (BitVec.eq_of_toNat_eq (by
      rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]))
    rw [ite_eq_right h, and_zero', or_zero']
    by_cases h2 : (idx k).toNat < j
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- What the scan keeps of a state: everything but `x10`, `x11`, the flags and
`v1`–`v5`. -/
structure ScanKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x10 → r ≠ .x11 → t.gpr r = s.gpr r
  v : ∀ x, x ≠ .v1 → x ≠ .v2 → x ≠ .v3 → x ≠ .v4 → x ≠ .v5 → t.v x = s.v x
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem ScanKeep.trans {s t u : State} (h : ScanKeep s t) (h' : ScanKeep t u) : ScanKeep s u :=
  ⟨fun r a b => (h'.gpr r a b).trans (h.gpr r a b),
   fun x a b c d e => (h'.v x a b c d e).trans (h.v x a b c d e),
   h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

/-- The state of the scan with entries `0 … j - 1` visited, from `s₀`. -/
structure ScanAt (s₀ : State) (T : Addr) (idx : Nat → BitVec 32) (j : Nat) (s : State) : Prop where
  v0 : s.v .v0 = L idx
  v1 : s.v .v1 = L (acc s₀.mem T idx j)
  v2 : s.v .v2 = L (splat j)
  v3 : s.v .v3 = L (splat 1)
  keep : ScanKeep s₀ s

theorem entry_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {j : Nat} (e : Nat) (he : e < 4)
    (hj : j < 256) (h : ScanAt s₀ T idx j s)
    (ha : s.gpr .x10 + BitVec.ofNat 64 (16 * e) = T + BitVec.ofNat 64 (16 * j))
    (hr : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block (scanEntry e)) s fun t => ScanAt s₀ T idx (j + 1) t ∧ t.gpr = s.gpr := by
  obtain ⟨h0, h1, h2, h3, hk⟩ := h
  have ho : 16 * e % 16 = 0 ∧ 16 * e < 65536 := ⟨by omega, by omega⟩
  unfold scanEntry
  crun [ho, ha, hr, h0, h1, h2, h3]
  have hm : s.mem = s₀.mem := hk.mem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [v_setV_of_ne _ _ (show VReg.v0 ≠ .v2 by decide), v_setV_of_ne _ _ (show VReg.v0 ≠ .v1 by decide),
      v_setV_of_ne _ _ (show VReg.v0 ≠ .v5 by decide), v_setV_of_ne _ _ (show VReg.v0 ≠ .v4 by decide), h0]
  · simp (disch := decide) only [v_setV_self, v_setV_of_ne, h1]
    rw [cmeq_L, read16_L, and_L, or_L, hm]
    refine L_congr fun k _ => ?_
    rw [← acc_succ _ _ _ (by omega)]
    unfold ent splat
    rw [Offset.add_add, BitVec.and_comm]
  · simp (disch := decide) only [v_setV_self, v_setV_of_ne, h2, h3]
    rw [add_L]
    refine L_congr fun k _ => ?_
    simp only [splat, BitVec.ofNat_add]
  · simp only [v_setV_of_ne _ _ (show VReg.v3 ≠ .v2 by decide), v_setV_of_ne _ _ (show VReg.v3 ≠ .v1 by decide),
      v_setV_of_ne _ _ (show VReg.v3 ≠ .v5 by decide), v_setV_of_ne _ _ (show VReg.v3 ≠ .v4 by decide), h3]
  · refine hk.trans ⟨fun _ _ _ => by simp only [gpr_setV], fun x a b c d e => ?_, by simp only [mem_setV],
      by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩
    simp only [v_setV_of_ne _ _ a, v_setV_of_ne _ _ b, v_setV_of_ne _ _ d, v_setV_of_ne _ _ e]

theorem flatMap_range_succ' {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The table at `T` is readable. -/
def Readable (s : State) (T : Addr) : Prop := InRegions (s.rd ++ s.wr) T 4096

theorem entries_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {q : Nat} (hq : q < 64)
    (hT : Readable s₀ T) (hx10 : s.gpr .x10 = T + BitVec.ofNat 64 (64 * q)) :
    ∀ e ≤ 4, ScanAt s₀ T idx (4 * q) s →
      WP isa (.block ((List.range e).flatMap scanEntry)) s
        fun t => ScanAt s₀ T idx (4 * q + e) t ∧ t.gpr = s.gpr := by
  intro e he h
  induction e with
  | zero => exact WP.block_nil ⟨h, rfl⟩
  | succ e ih =>
    rw [flatMap_range_succ', WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨ht, hg⟩ => ?_
    have hr : InRegions (t.rd ++ t.wr) (T + BitVec.ofNat 64 (16 * (4 * q + e))) 16 := by
      rw [ht.keep.rd, ht.keep.wr]
      exact CallLay.inRegions_sub hT (by omega) (by decide)
    refine WP.mono (entry_ok e (by omega) (by omega) ht ?_ hr) fun u ⟨hu, hug⟩ => ⟨hu, hug.trans hg⟩
    rw [hg, hx10, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega

theorem body_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {q : Nat} (hq : q < 64)
    (hT : Readable s₀ T) (hx10 : s.gpr .x10 = T + BitVec.ofNat 64 (64 * q))
    (h : ScanAt s₀ T idx (4 * q) s) :
    WP isa (.block scanBody) s fun t => ScanAt s₀ T idx (4 * (q + 1)) t ∧
      t.gpr .x10 = T + BitVec.ofNat 64 (64 * (q + 1)) ∧ t.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 := by
  unfold scanBody
  rw [WP.block_append_iff]
  refine WP.mono (entries_ok hq hT hx10 4 (Nat.le_refl _) h) fun t ⟨ht, hg⟩ => ?_
  crun
  rw [hg, hx10, BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * q + 64 = 64 * (q + 1) by omega]
  refine ⟨⟨ht.v0, ht.v1, ht.v2, ht.v3, ht.keep.trans ⟨fun r a b => ?_, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl,
    rfl⟩⟩, rfl, rfl⟩
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

/-- The setup of the scan: the table's address in `x10`, 64 groups to go in
`x11`, nothing found yet, entry 0 next, and ones. -/
theorem start_ok (s : State) (sym : String) {idx : Nat → BitVec 32} (h0 : s.v .v0 = L idx) :
    WP isa (.block [.adrSym .x10 sym, .movz .x .x11 64 0, .vop (.movi0 .v1), .vop (.movi0 .v2),
      .vop (.cmeq .s4 .v3 .v3 .v3), .vop (.shift .ushr .s4 .v3 .v3 31)]) s
      fun t => ScanAt s (s.syms sym) idx 0 t ∧ t.gpr .x10 = s.syms sym ∧ t.gpr .x11 = BitVec.ofNat 64 64 := by
  crun [VShiftOp.ok, VArr.esize]
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨fun r a b => ?_, fun x a b c d e => ?_, rfl, rfl, rfl, rfl⟩⟩, rfl⟩
  · simp (disch := decide) only [v_setV_of_ne, v_write, h0]
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self]
    exact (acc_zero _ _ _).symm
  · simp (disch := decide) only [v_setV_of_ne, v_setV_self]
    decide
  · simp only [v_setV_self, ones_L]
  · simp only [gpr_setV, gpr_write_of_ne _ _ _ b, gpr_write_of_ne _ _ _ a]
  · simp only [v_setV_of_ne _ _ a, v_setV_of_ne _ _ b, v_setV_of_ne _ _ c, v_write]

/-- The scan: lane `k` of `v1` is word `k` of the entry of the table at
`sym` whose number is lane `k` of `v0`. -/
theorem scan_ok (s : State) (sym : String) {idx : Nat → BitVec 32} (h0 : s.v .v0 = L idx)
    (hidx : ∀ k < 4, (idx k).toNat < 256) (hT : Readable s (s.syms sym)) :
    WP isa (scan sym) s fun t =>
      t.v .v1 = L (fun k => ent s.mem (s.syms sym) (idx k).toNat k) ∧ ScanKeep s t := by
  unfold scan
  refine WP.seq (WP.mono (start_ok s sym h0) fun t ⟨ht, h10, h11⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x11) (N := 64) (by decide) (by decide)
    (fun q u => ScanAt s (s.syms sym) idx (4 * q) u ∧
      u.gpr .x10 = s.syms sym + BitVec.ofNat 64 (64 * q))
    (fun q hq u ⟨hu, h10⟩ _ => WP.mono (body_ok hq hT h10 hu) fun v ⟨hv, h10', h11'⟩ =>
      ⟨⟨hv, h10'⟩, h11'⟩)
    ⟨ht, by rw [h10]; exact (BitVec.add_zero _).symm⟩ h11) fun u ⟨hu, _⟩ => ⟨?_, hu.keep⟩
  rw [hu.v1]
  exact L_congr fun k hk => by rw [acc, ite_eq_left (by have := hidx k hk; omega)]

end VG.Proof.Cast5.AArch64
