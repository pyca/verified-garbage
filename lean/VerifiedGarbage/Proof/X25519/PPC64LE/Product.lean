module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on PPC64LE: the eight words of a product

A field element's 32 bytes at `o` are four doublewords (`dw`) as well as
eight words (`limb`): `V` is `val4` of the doublewords (`V_eq4`). The
doublewords of memory after a store (`dw_write_self`, `dw_write_other`) and
through a frame (`dw_frame`); a doubleword load and store of the working
space (`ld0_ok`, `sd0_ok`); the carrying additions (`UpdC`, `wp_addc`, …)
and a sum added into a three-word accumulator with them (`acc3_ok`).

`product acc x y` stores the eight words of `[x] · [y]` at `acc`
(`product_ok`), by columns: a column's terms `a_i b_j` add into the
accumulator `rr k, rr (k + 1), rr (k + 2)` (`mulTerm_ok`, by `acc3_ok`), and
its end stores the accumulator's low word at `acc + 8k` (`colEnd_ok`), so
that after `k` columns the words below `acc + 8k` and the accumulator hold
the sum of the first `k` (`ColInv`, by induction on the columns:
`columns_ok`); the columns sum to the product (`mulCols_sum`).
-/

-- separate module: its proofs cost more than its imports, and its importer's changes need not
-- re-check them

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE

/-! ## Doublewords -/

/-- Byte `i` of two words joined into a doubleword. -/
theorem join_byte (x y : BitVec 32) {i : Nat} (hi : i < 8) :
    (x.setWidth 64 <<< 32 ||| y.setWidth 64).extractLsb' (8 * i) 8 =
      if i < 4 then y.extractLsb' (8 * i) 8 else x.extractLsb' (8 * (i - 4)) 8 := by
  ext j hj
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  split
  · simp only [BitVec.getElem_extractLsb']
    simp (disch := omega) [show 8 * i + j < 32 by omega, show 8 * i + j < 64 by omega]
  · simp only [BitVec.getElem_extractLsb']
    simp (disch := omega) [show ¬ 8 * i + j < 32 by omega, show 8 * i + j < 64 by omega,
      show 8 * i + j - 32 = 8 * (i - 4) + j by omega]
    intro; omega

/-- A little-endian doubleword is its two words. -/
theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = (m.readW (a + BitVec.ofNat 64 4) 32).setWidth 64 <<< 32 |||
      (m.readW a 32).setWidth 64 := by
  show m.read a 8 = _
  refine Mem.read_eq_of_bytes fun i hi => ?_
  rw [join_byte _ _ hi]
  split
  · exact Mem.readW_byte m a ‹_›
  · rw [← Mem.readW_byte m _ (by omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 3; omega

/-- The doubleword at `P + d`, as a number. -/
def dw (m : Mem) (P : Addr) (d : Nat) : Nat := (m.readW (P + BitVec.ofNat 64 d) 64).toNat

theorem dw_lt (m : Mem) (P : Addr) (d : Nat) : dw m P d < 2 ^ 64 := (m.readW _ 64).isLt

/-- A doubleword is its two words. -/
theorem dw_split (m : Mem) (P : Addr) (d : Nat) : dw m P d = wd m P d + 2 ^ 32 * wd m P (d + 4) := by
  unfold dw wd
  rw [readW64_split, Offset.add_add]
  have h1 := (m.readW (P + BitVec.ofNat 64 d) 32).isLt
  have h2 := (m.readW (P + BitVec.ofNat 64 (d + 4)) 32).isLt
  generalize m.readW (P + BitVec.ofNat 64 d) 32 = lo at *
  generalize m.readW (P + BitVec.ofNat 64 (d + 4)) 32 = hi at *
  have e : (hi.setWidth 64 <<< 32 ||| lo.setWidth 64) = hi.setWidth 64 <<< 32 + lo.setWidth 64 := by
    rw [BitVec.add_eq_or_of_and_eq_zero]
    ext i hi'
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getElem_zero]
    by_cases h : i < 32
    · simp [h]
    · simp [h, BitVec.getLsbD_of_ge lo i (by omega)]
  rw [e, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : hi.toNat < 2 ^ 64),
    Nat.shiftLeft_eq]
  omega_using [h1, h2]

/-- Four doublewords, lowest first. -/
def val4 (f : Nat → Nat) : Nat := f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * f 3))

theorem val4_congr {f g : Nat → Nat} (h : ∀ i < 4, f i = g i) : val4 f = val4 g := by
  unfold val4
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- The doublewords of the element at `o`. -/
abbrev ew (m : Mem) (P : Addr) (o : Nat) (i : Nat) : Nat := dw m P (o + 8 * i)

/-- The number of an element is its four doublewords. -/
theorem V_eq4 (m : Mem) (P : Addr) (o : Nat) : V m P o = val4 (ew m P o) := by
  simp only [V, val4, ew, val32, limb, dw_split]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
  omega_arith

theorem dw_write_self (m : Mem) (P : Addr) (d : Nat) (v : BitVec 64) :
    dw (m.writeW (P + BitVec.ofNat 64 d) v) P d = v.toNat := by
  rw [dw, Mem.readW_writeW_self64]

theorem dw_write_other (m : Mem) (P : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    dw (m.writeW (P + BitVec.ofNat 64 e) v) P d = dw m P d := by
  rw [dw, Mem.readW_writeW_sep (Offset.sep P h hd he) (by decide), dw]

theorem dw_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {d : Nat}
    (hd : ∀ r ∈ rs, (⟨P + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) : dw m' P d = dw m P d := by
  rw [dw, dw, hf.readW (Region.contains_self _ _) hd (by decide)]

/-! ## Loads and stores -/

section
variable {b : Addr} {is : List Instr} {s : State} {Q : State → Prop}

/-- `ld t, d(r6)` in the working space. -/
theorem ld0_ok (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 8 ≤ 4096) (hd4 : d % 4 = 0)
    (k : ∀ s', Upd s s' t (s.mem.readW (b + BitVec.ofNat 64 d) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t .r6 d :: is)) s Q := by
  have e := exec_load_d (s := s) (t := t) (n := .r6) (off := d) (by decide) ⟨by omega, hd4⟩
    (by rw [hc.r6]; exact hc.inR hd)
  rw [hc.r6] at e
  exact WP.cons e (k _ (Upd.write _ _ _))

/-- `std t, d(r6)` in the working space. -/
theorem sd0_ok (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 8 ≤ 4096) (hd4 : d % 4 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t .r6 d :: is)) s Q := by
  have e := exec_store_d (s := s) (t := t) (n := .r6) (off := d) (by decide) ⟨by omega, hd4⟩
    (by rw [hc.r6]; exact hc.inW hd)
  rw [hc.r6] at e
  exact WP.cons e (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

end

/-! ## The carry chain -/

/-- `s'` is `s` with a carrying write of `v` to `d`: `d` and CA hold `v`. -/
structure UpdC (s s' : State) (d : Reg) (v : Nat) : Prop where
  val : (s'.gpr d).toNat + 2 ^ 64 * s'.ca.toNat = v
  ca : s'.ca.toNat ≤ 1
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem UpdC.writeCarry (s : State) (d : Reg) {v : Nat} (h : v < 2 ^ 65) :
    UpdC s (s.writeCarry d v) d v :=
  ⟨RegUpd.toNat_add_ca s h, Bool.toNat_le _, fun r hr => by rw [RegUpd.gpr_writeCarry, ite_eq_right hr],
    rfl, rfl, rfl, rfl⟩

theorem UpdC.rest {s s' : State} {d : Reg} {v : Nat} (h : UpdC s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : Rest ws s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.rd, h.wr, h.sp⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addc {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (s.gpr m).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.addc d n m :: is)) s Q := by
  have := (s.gpr n).isLt; have := (s.gpr m).isLt
  exact WP.cons exec_addc (k _ (UpdC.writeCarry _ _ (by omega)))

theorem wp_adde {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (s.gpr m).toNat + s.ca.toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.adde d n m :: is)) s Q := by
  have := (s.gpr n).isLt; have := (s.gpr m).isLt; have : s.ca.toNat ≤ 1 := Bool.toNat_le _
  exact WP.cons exec_adde (k _ (UpdC.writeCarry _ _ (by omega)))

theorem wp_addze {d n : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + s.ca.toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.addze d n :: is)) s Q := by
  have := (s.gpr n).isLt; have : s.ca.toNat ≤ 1 := Bool.toNat_le _
  exact WP.cons exec_addze (k _ (UpdC.writeCarry _ _ (by omega)))

theorem wp_mulhu {d n m : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mulhu d n m :: is)) s Q :=
  WP.cons exec_mulhu (k _ (Upd.write _ _ _))

end

/-- The three-word number in `l, h, t`. -/
def v3 (s : State) (l h t : Reg) : Nat :=
  (s.gpr l).toNat + 2 ^ 64 * ((s.gpr h).toNat + 2 ^ 64 * (s.gpr t).toNat)

/-- A carrying write of a sum below `2⁶⁵`: its register and carry. -/
theorem writeCarry_split (s : State) (r : Reg) {v : Nat} (h : v < 2 ^ 65) :
    ((s.writeCarry r v).gpr r).toNat = v - 2 ^ 64 * (s.writeCarry r v).ca.toNat ∧
      (s.writeCarry r v).ca.toNat ≤ 1 ∧ 2 ^ 64 * (s.writeCarry r v).ca.toNat ≤ v := by
  have := RegUpd.toNat_add_ca s (r := r) h
  have hc : (s.writeCarry r v).ca.toNat ≤ 1 := Bool.toNat_le _
  have := ((s.writeCarry r v).gpr r).isLt
  omega

/-- `l, h, t += x + 2⁶⁴ y` with `addc`, `adde` and `addze`, if the sum fits
in three words. -/
theorem acc3_ok {s : State} {l h t x y : Reg} (hlh : l ≠ h) (hlt : l ≠ t) (hht : h ≠ t)
    (hly : l ≠ y)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (v3 s l h t + (s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat < 2 ^ 192 →
        v3 s' l h t = v3 s l h t + (s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat) →
      (∀ r, r ≠ l → r ≠ h → r ≠ t → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (.addc l l x :: .adde h h y :: .addze t t :: is)) s Q := by
  refine WP.cons exec_addc (WP.cons exec_adde (WP.cons exec_addze (k _ ?_ ?_ rfl rfl rfl rfl)))
  · intro hb
    generalize hs1 : s.writeCarry l ((s.gpr l).toNat + (s.gpr x).toNat) = s1
    generalize hs2 : s1.writeCarry h ((s1.gpr h).toNat + (s1.gpr y).toNat + s1.ca.toNat) = s2
    have hL := (s.gpr l).isLt; have hX := (s.gpr x).isLt; have hH := (s.gpr h).isLt
    have hY := (s.gpr y).isLt; have hT := (s.gpr t).isLt
    obtain ⟨e1, c1, b1⟩ := writeCarry_split s l (v := (s.gpr l).toNat + (s.gpr x).toNat) (by omega)
    rw [hs1] at e1 c1 b1
    have g1h : s1.gpr h = s.gpr h := by rw [← hs1, RegUpd.gpr_writeCarry, ite_eq_right (Ne.symm hlh)]
    have g1y : s1.gpr y = s.gpr y := by rw [← hs1, RegUpd.gpr_writeCarry, ite_eq_right (Ne.symm hly)]
    have g1t : s1.gpr t = s.gpr t := by rw [← hs1, RegUpd.gpr_writeCarry, ite_eq_right (Ne.symm hlt)]
    obtain ⟨e2, c2, b2⟩ := writeCarry_split s1 h
      (v := (s1.gpr h).toNat + (s1.gpr y).toNat + s1.ca.toNat) (by omega)
    rw [hs2] at e2 c2 b2
    have g2l : s2.gpr l = s1.gpr l := by rw [← hs2, RegUpd.gpr_writeCarry, ite_eq_right hlh]
    have g2t : s2.gpr t = s1.gpr t := by rw [← hs2, RegUpd.gpr_writeCarry, ite_eq_right (Ne.symm hht)]
    unfold v3 at hb ⊢
    simp only [RegUpd.gpr_writeCarry_self, RegUpd.gpr_writeCarry, hlt, hht, ite_false]
    rw [g2l, BitVec.toNat_ofNat, g2t, g1t]
    rw [g1h, g1y] at e2 b2
    have : (s.gpr t).toNat + s2.ca.toNat < 2 ^ 64 := by omega_arith
    rw [Nat.mod_eq_of_lt this, e1, e2]
    omega_arith
  · intro r h1 h2 h3
    rw [RegUpd.gpr_writeCarry, ite_eq_right h3, RegUpd.gpr_writeCarry, ite_eq_right h2, RegUpd.gpr_writeCarry,
      ite_eq_right h1]


/-! ## Sums of terms and of columns -/

/-- The sum of a list of terms, given by a function. -/
def tsum (f : Nat × Nat → Nat) (ps : List (Nat × Nat)) : Nat := (ps.map f).sum

theorem tsum_cons (f : Nat × Nat → Nat) (p : Nat × Nat) (ps : List (Nat × Nat)) :
    tsum f (p :: ps) = f p + tsum f ps := by simp [tsum]

theorem tsum_le {f : Nat × Nat → Nat} {B : Nat} :
    ∀ {ps : List (Nat × Nat)}, (∀ p ∈ ps, f p ≤ B) → tsum f ps ≤ ps.length * B
  | [], _ => by simp [tsum]
  | p :: ps, h => by
    rw [tsum_cons, List.length_cons, Nat.succ_mul]
    have := h p (List.mem_cons_self ..)
    have := tsum_le (ps := ps) fun q hq => h q (List.mem_cons_of_mem _ hq)
    omega

/-- The sum of the first `k` columns. -/
def colsV (cs : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => colsV cs k + (2 ^ 64) ^ k * cs k

/-! ## The accumulator's registers -/

theorem rr_ne : ∀ k < 14, rr k ≠ rr (k + 1) ∧ rr k ≠ rr (k + 2) ∧ rr (k + 1) ≠ rr (k + 2) ∧
    rr k ≠ .r4 ∧ rr k ≠ .r5 ∧ rr k ≠ .r7 ∧ rr (k + 1) ≠ .r4 ∧ rr (k + 1) ≠ .r5 ∧ rr (k + 1) ≠ .r7 ∧
    rr (k + 2) ≠ .r4 ∧ rr (k + 2) ≠ .r5 ∧ rr (k + 2) ≠ .r7 ∧ rr (k + 3) = rr k ∧
    rr k ∈ clob ∧ rr (k + 1) ∈ clob ∧ rr (k + 2) ∈ clob := by decide

section
variable {acc N : Nat} {b : Addr}

/-- The words below `acc + 8k`. -/
def accW (acc : Nat) (m : Mem) (b : Addr) : Nat → Nat
  | 0 => 0
  | k + 1 => accW acc m b k + (2 ^ 64) ^ k * dw m b (acc + 8 * k)

theorem accW_lt (m : Mem) (b : Addr) : ∀ k, accW acc m b k < (2 ^ 64) ^ k
  | 0 => by simp [accW]
  | k + 1 => by
    have := accW_lt m b k
    have := dw_lt m b (acc + 8 * k)
    rw [accW, Nat.pow_succ (n := 2 ^ 64)]
    calc accW acc m b k + (2 ^ 64) ^ k * dw m b (acc + 8 * k)
        < (2 ^ 64) ^ k + (2 ^ 64) ^ k * dw m b (acc + 8 * k) := by omega
      _ = (2 ^ 64) ^ k * (dw m b (acc + 8 * k) + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (2 ^ 64) ^ k * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)

theorem accW_congr {m m' : Mem} : ∀ {k}, (∀ c < k, dw m' b (acc + 8 * c) = dw m b (acc + 8 * c)) →
    accW acc m' b k = accW acc m b k
  | 0, _ => rfl
  | k + 1, h => by
    rw [accW, accW, accW_congr (fun c hc => h c (by omega)), h k (by omega)]

/-- The product's area at `acc`, of `N` words. -/
abbrev AR (acc N : Nat) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 acc, 8 * N⟩

/-- An element below `acc`, unchanged in a frame of the product's area. -/
theorem dw_acc (hA : acc + 8 * N ≤ 4096) {m m' : Mem} (hf : Frame [AR acc N b] m m') {d : Nat}
    (hd : d + 8 ≤ acc) : dw m' b d = dw m b d :=
  dw_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl hd) (by omega) (by omega)

/-! ## Columns -/

/-- After `k` columns, from `s0`: the words below `acc + 8k` and the
accumulator `rr k, rr (k + 1)` (with `rr (k + 2)` zero) hold the sum of the
first `k` columns `cs`; the code changed only `clob` and `acc`. -/
structure ColInv (acc N : Nat) (b : Addr) (s0 : State) (cs : Nat → Nat) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob s0 s
  frame : Frame [AR acc N b] s0.mem s.mem
  top : s.gpr (rr (k + 2)) = 0
  val : accW acc s.mem b k + (2 ^ 64) ^ k * ((s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat) =
    colsV cs k

/-- The end of column `k`: the low word stored, the register zeroed. -/
theorem colEnd_ok (hA : acc + 8 * N ≤ 4096) (hA4 : acc % 4 = 0) (hN : N ≤ 14) {s0 : State} {k : Nat}
    (hk : k < N)
    {s : State} (hc : Ctx b s) (hr : Rest clob s0 s) (hf : Frame [AR acc N b] s0.mem s.mem)
    {cs : Nat → Nat}
    (hv : accW acc s.mem b k + (2 ^ 64) ^ k * v3 s (rr k) (rr (k + 1)) (rr (k + 2)) = colsV cs (k + 1)) :
    WP isa (.block (colEnd acc k)) s (ColInv acc N b s0 cs (k + 1)) := by
  obtain ⟨h01, h02, h12, -, -, -, -, -, -, -, -, -, h3, hrr, -, -⟩ := rr_ne k (by omega)
  unfold colEnd
  refine sd0_ok hc (by omega) (by omega) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_
  have hm : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (acc + 8 * k)) (s.gpr (rr k)) := by
    rw [u2.mem, u1.mem]
  have hr2 : Rest clob s s2 := (u1.rest _).trans (u2.rest (ws := clob) hrr)
  refine ⟨hc.of_rest hr2 (by decide), hr.trans hr2, ?_, ?_, ?_⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains b (by omega) (by omega) (by omega))
  · rw [show k + 1 + 2 = k + 3 by omega, h3, u2.gpr]; rfl
  · have e1 : s2.gpr (rr (k + 1)) = s.gpr (rr (k + 1)) := by rw [u2.other _ (Ne.symm h01), u1.gpr]
    have e2 : s2.gpr (rr (k + 1 + 1)) = s.gpr (rr (k + 2)) := by
      rw [show k + 1 + 1 = k + 2 by omega, u2.other _ (Ne.symm h02), u1.gpr]
    have ea : accW acc s2.mem b k = accW acc s.mem b k := accW_congr fun c hc' => by
      rw [hm, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have ek : dw s2.mem b (acc + 8 * k) = (s.gpr (rr k)).toNat := by rw [hm, dw_write_self]
    rw [accW, ea, ek, e1, e2, ← hv, v3]
    rw [Nat.pow_succ (n := 2 ^ 64)]
    generalize (2 ^ 64) ^ k = K
    generalize (s.gpr (rr k)).toNat = a
    generalize (s.gpr (rr (k + 1))).toNat = c
    generalize (s.gpr (rr (k + 2))).toNat = d
    generalize 2 ^ 64 = W
    grind

/-- A column's terms: from a state with the accumulator `acc`, each term `p`
of `ps` adds `f p`. -/
def TermOk (acc N : Nat) (b : Addr) (s0 : State) (k : Nat) (f : Nat × Nat → Nat)
    (code : Nat × Nat → List Instr) (p : Nat × Nat) : Prop :=
  ∀ s, Ctx b s → Rest clob s0 s → Frame [AR acc N b] s0.mem s.mem →
    WP isa (.block (code p)) s fun s' => Ctx b s' ∧ Rest clob s0 s' ∧
      Frame [AR acc N b] s0.mem s'.mem ∧ s'.mem = s.mem ∧
      (v3 s (rr k) (rr (k + 1)) (rr (k + 2)) + f p < 2 ^ 192 →
        v3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = v3 s (rr k) (rr (k + 1)) (rr (k + 2)) + f p)

/-- A column's terms, by induction on them. -/
theorem terms_ok {s0 : State} {k : Nat} {f : Nat × Nat → Nat} {code : Nat × Nat → List Instr} :
    ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, TermOk acc N b s0 k f code p) → ∀ s, Ctx b s →
      Rest clob s0 s → Frame [AR acc N b] s0.mem s.mem →
      v3 s (rr k) (rr (k + 1)) (rr (k + 2)) + tsum f ps < 2 ^ 192 →
      WP isa (.block (ps.flatMap code)) s fun s' => Ctx b s' ∧ Rest clob s0 s' ∧
        Frame [AR acc N b] s0.mem s'.mem ∧ s'.mem = s.mem ∧
        v3 s' (rr k) (rr (k + 1)) (rr (k + 2)) = v3 s (rr k) (rr (k + 1)) (rr (k + 2)) + tsum f ps
  | [], _, s, hc, hr, hf, _ => WP.block_nil ⟨hc, hr, hf, rfl, by simp [tsum]⟩
  | p :: ps, hok, s, hc, hr, hf, hb => by
    rw [List.flatMap_cons]
    rw [tsum_cons] at hb
    refine WP.append (hok p (List.mem_cons_self ..) s hc hr hf) fun s1 ⟨hc1, hr1, hf1, hm1, hv1⟩ => ?_
    have hv1 := hv1 (by omega)
    refine WP.mono (terms_ok ps (fun q hq => hok q (List.mem_cons_of_mem _ hq)) s1 hc1 hr1 hf1
      (by omega)) fun s2 ⟨hc2, hr2, hf2, hm2, hv2⟩ => ⟨hc2, hr2, hf2, hm2.trans hm1, ?_⟩
    rw [hv2, hv1, tsum_cons]; omega

/-- Column `k`: its terms `ps`, which sum to `cs k`, then its end. -/
theorem column_ok (hA : acc + 8 * N ≤ 4096) (hA4 : acc % 4 = 0) (hN : N ≤ 14) {s0 : State} {k : Nat}
    (hk : k < N)
    {f : Nat × Nat → Nat} {code : Nat × Nat → List Instr} {cs : Nat → Nat} (ps : List (Nat × Nat))
    (hok : ∀ p ∈ ps, TermOk acc N b s0 k f code p) (hcs : cs k = tsum f ps)
    (hbd : tsum f ps < 7 * 2 ^ 128) {s : State} (h : ColInv acc N b s0 cs k s) :
    WP isa (.block (ps.flatMap code ++ colEnd acc k)) s (ColInv acc N b s0 cs (k + 1)) := by
  have hv0 : v3 s (rr k) (rr (k + 1)) (rr (k + 2)) =
      (s.gpr (rr k)).toNat + 2 ^ 64 * (s.gpr (rr (k + 1))).toNat := by
    simp only [v3, h.top]; rfl
  have hl := (s.gpr (rr k)).isLt
  have hh := (s.gpr (rr (k + 1))).isLt
  refine WP.append (terms_ok ps hok s h.ctx h.rest h.frame (by rw [hv0]; omega_arith))
    fun s1 ⟨hc1, hr1, hf1, hm1, hv1⟩ => ?_
  exact colEnd_ok (cs := cs) hA hA4 hN hk hc1 hr1 hf1 (by
    rw [hm1, hv1, hv0, colsV, ← h.val, hcs, Nat.mul_add]; omega_arith)

/-- The columns, by induction. -/
theorem columns_ok {s0 : State} {cs : Nat → Nat} {col : Nat → List Instr}
    (hcol : ∀ k < N, ∀ s, ColInv acc N b s0 cs k s →
      WP isa (.block (col k)) s (ColInv acc N b s0 cs (k + 1))) :
    ∀ n ≤ N, ∀ s, ColInv acc N b s0 cs 0 s →
      WP isa (.block ((List.range n).flatMap col)) s (ColInv acc N b s0 cs n)
  | 0, _, s, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.append (columns_ok hcol n (by omega) s h) fun s1 h1 => hcol n (by omega) s1 h1

/-- After the eight columns, the words at `acc` are the columns' sum. -/
theorem ColInv.final {s0 : State} {cs : Nat → Nat} {s : State} (h : ColInv acc N b s0 cs N s)
    (hlt : colsV cs N < (2 ^ 64) ^ N) : accW acc s.mem b N = colsV cs N := by
  have hv := h.val
  have := accW_lt (acc := acc) s.mem b N
  generalize (2 ^ 64) ^ N = K at *
  generalize accW acc s.mem b N = A at *
  generalize (s.gpr (rr N)).toNat + 2 ^ 64 * (s.gpr (rr (N + 1))).toNat = C at *
  generalize colsV cs N = V at *
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · omega
  · have : K ≤ K * C := Nat.le_mul_of_pos_right _ hC
    omega

/-! ## The product -/

/-- The columns of a product: column `k` is the sum of `a_i b_j` with `i + j = k`. -/
def mulF (X Y : Nat → Nat) (p : Nat × Nat) : Nat := X p.1 * Y p.2

def mulCs (n : Nat) (X Y : Nat → Nat) (k : Nat) : Nat := tsum (mulF X Y) (colPairs n k)

theorem colPairs_ok (n k : Nat) : ∀ p ∈ colPairs n k, p.1 < n ∧ p.2 < n := by
  intro p hp
  simp only [colPairs, List.mem_map, List.mem_filter, List.mem_reverse, List.mem_range,
    decide_eq_true_eq] at hp
  obtain ⟨i, ⟨hi, -, hk⟩, rfl⟩ := hp
  exact ⟨hi, hk⟩

theorem colPairs_len (n k : Nat) : (colPairs n k).length ≤ n := by
  simp only [colPairs, List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- A term `a_i b_j` of column `k`. -/
theorem mulTerm_ok {n : Nat} {s0 : State} {x y : Nat} (hx : x + 8 * n ≤ acc) (hy : y + 8 * n ≤ acc)
    (hA : acc + 8 * N ≤ 4096) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {k i j : Nat} (hk : k < 14)
    (hi : i < n) (hj : j < n) :
    TermOk acc N b s0 k (mulF (ew s0.mem b x) (ew s0.mem b y)) (mulTerm x y k) (i, j) := by
  intro s hc hr hf
  obtain ⟨h01, h02, h12, h04, h05, h07, h14, h15, h17, h24, h25, h27, -, c0, c1, c2⟩ := rr_ne k hk
  simp only [mulTerm]
  refine ld0_ok hc (d := x + 8 * i) (by omega) (by omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := clob) (by decide)) (by decide)
  refine ld0_ok hc1 (d := y + 8 * j) (by omega) (by omega) fun s2 u2 => ?_
  refine wp_mul fun s3 u3 => WP.cons exec_mulhu ?_
  generalize hs4 : s3.write .r4 (BitVec.ofNat 64 ((s3.gpr .r4).toNat * (s3.gpr .r5).toNat / 2 ^ 64)) = s4
  have u4 : Upd s3 s4 .r4 _ := hs4 ▸ Upd.write _ _ _
  refine acc3_ok h01 h02 h12 h04 fun s5 hv5 hg5 hm5 hrd5 hwr5 hsp5 => WP.block_nil ?_
  have hr4 : Rest clob s s4 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hr5 : Rest clob s4 s5 := ⟨fun r hr' => hg5 r (fun e => hr' (e ▸ c0)) (fun e => hr' (e ▸ c1))
    (fun e => hr' (e ▸ c2)), hrd5, hwr5, hsp5⟩
  have hm : s5.mem = s.mem := by rw [hm5, u4.mem, u3.mem, u2.mem, u1.mem]
  have hv4 : v3 s4 (rr k) (rr (k + 1)) (rr (k + 2)) = v3 s (rr k) (rr (k + 1)) (rr (k + 2)) := by
    simp only [v3, u4.other _ h04, u4.other _ h14, u4.other _ h24, u3.other _ h07, u3.other _ h17,
      u3.other _ h27, u2.other _ h05, u2.other _ h15, u2.other _ h25, u1.other _ h04,
      u1.other _ h14, u1.other _ h24]
  have ex : (s3.gpr .r4).toNat = ew s0.mem b x i := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; exact dw_acc hA hf (by omega)
  have ey : (s3.gpr .r5).toNat = ew s0.mem b y j := by
    rw [u3.other _ (by decide), u2.gpr, u1.mem]; exact dw_acc hA hf (by omega)
  have hX := dw_lt s0.mem b (x + 8 * i)
  have hY := dw_lt s0.mem b (y + 8 * j)
  have elo : (s4.gpr .r7).toNat = ew s0.mem b x i * ew s0.mem b y j % 2 ^ 64 := by
    rw [u4.other _ (by decide), u3.gpr, BitVec.toNat_mul, ← u3.other .r4 (by decide),
      ← u3.other .r5 (by decide), ex, ey]
  have ehi : (s4.gpr .r4).toNat = ew s0.mem b x i * ew s0.mem b y j / 2 ^ 64 := by
    rw [u4.gpr, ex, ey, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt hX hY)
  have e : (s4.gpr .r7).toNat + 2 ^ 64 * (s4.gpr .r4).toNat = ew s0.mem b x i * ew s0.mem b y j := by
    rw [elo, ehi]; exact Nat.mod_add_div _ _
  refine ⟨hc.of_rest (hr4.trans hr5) (by decide), hr.trans (hr4.trans hr5), by rw [hm]; exact hf, hm,
    fun hb => ?_⟩
  rw [hv5 (by rw [hv4, Nat.add_assoc, e]; exact hb), hv4, Nat.add_assoc, e]; rfl

theorem mulF_le (X Y : Nat → Nat) (hX : ∀ i, X i < 2 ^ 64) (hY : ∀ j, Y j < 2 ^ 64) (p : Nat × Nat) :
    mulF X Y p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := hX p.1; omega) (by have := hY p.2; omega)

theorem tsum_lt {f : Nat × Nat → Nat} (hf : ∀ p, f p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    {ps : List (Nat × Nat)} (hl : ps.length ≤ 7) : tsum f ps < 7 * 2 ^ 128 := by
  have := tsum_le (ps := ps) fun p _ => hf p
  have : ps.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) ≤ 7 * ((2 ^ 64 - 1) * (2 ^ 64 - 1)) :=
    Nat.mul_le_mul_right _ hl
  omega

/-- The columns sum to the product. -/
theorem mulCols_sum (X Y : Nat → Nat) : colsV (mulCs 4 X Y) 8 = val4 X * val4 Y := by
  simp only [colsV, val4]
  generalize 2 ^ 64 = B
  simp only [mulCs, colPairs, tsum, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mulF, Nat.reduceSub,
    Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  grind

theorem val4_lt {f : Nat → Nat} (h : ∀ i < 4, f i < 2 ^ 64) : val4 f < (2 ^ 64) ^ 4 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide)
  have := h 3 (by decide)
  unfold val4; omega_arith

/-- `product n acc x y`: the columns of `[x] · [y]`, `n` words each, at `acc`. -/
theorem productN_ok {n : Nat} (hn : 2 * n ≤ 14) (hn1 : 1 ≤ n) {x y : Nat} (hx : x + 8 * n ≤ acc)
    (hy : y + 8 * n ≤ acc) (hA : acc + 8 * (2 * n) ≤ 4096) (hA4 : acc % 4 = 0) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s0 : State} (hc : Ctx b s0)
    (hlt : colsV (mulCs n (ew s0.mem b x) (ew s0.mem b y)) (2 * n) < (2 ^ 64) ^ (2 * n)) :
    WP isa (.block (product n acc x y)) s0 fun s' => Ctx b s' ∧ Rest clob s0 s' ∧
      Frame [AR acc (2 * n) b] s0.mem s'.mem ∧
      accW acc s'.mem b (2 * n) = colsV (mulCs n (ew s0.mem b x) (ew s0.mem b y)) (2 * n) := by
  unfold product
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => wp_li (by decide) fun s3 u3 => ?_
  have hr3 : Rest clob s0 s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s0.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hinit : ColInv acc (2 * n) b s0 (mulCs n (ew s0.mem b x) (ew s0.mem b y)) 0 s3 :=
    ⟨hc.of_rest hr3 (by decide), hr3, by rw [hm3]; exact Frame.refl _ _, u3.gpr, by
      simp only [accW, colsV, show rr 0 = .r8 from rfl, show rr (0 + 1) = .r9 from rfl,
        u3.other .r8 (by decide), u3.other .r9 (by decide), u2.other .r8 (by decide), u2.gpr, u1.gpr]
      rfl⟩
  refine WP.mono (columns_ok (col := mulCol n acc x y)
    (fun k hk s h => column_ok hA hA4 hn hk (colPairs n k) (fun p hp => by
      obtain ⟨h1, h2⟩ := colPairs_ok n k p hp
      exact mulTerm_ok hx hy hA hx4 hy4 (by omega) h1 h2) rfl
      (tsum_lt (mulF_le _ _ (fun i => dw_lt _ _ _) (fun i => dw_lt _ _ _))
        (Nat.le_trans (colPairs_len n k) (by omega))) h)
    (2 * n) (Nat.le_refl _) s3 hinit)
    fun s4 h4 => ⟨h4.ctx, h4.rest, h4.frame, h4.final hlt⟩

/-- `product 4 acc x y`: the eight words of `[x] · [y]` at `acc`. -/
theorem product_ok {x y : Nat} (hx : x + 32 ≤ acc) (hy : y + 32 ≤ acc) (hA : acc + 64 ≤ 4096)
    (hA4 : acc % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (product 4 acc x y)) s0 fun s' => Ctx b s' ∧ Rest clob s0 s' ∧
      Frame [AR acc 8 b] s0.mem s'.mem ∧ accW acc s'.mem b 8 = V s0.mem b x * V s0.mem b y := by
  have hlt : val4 (ew s0.mem b x) * val4 (ew s0.mem b y) < (2 ^ 64) ^ 8 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (val4_lt fun i _ => dw_lt _ _ _)
      (val4_lt fun i _ => dw_lt _ _ _)) (by rw [← Nat.pow_add])
  refine WP.mono (productN_ok (n := 4) (by decide) (by decide) hx hy hA hA4 hx4 hy4 hc
    (by rw [mulCols_sum]; exact hlt)) fun s4 ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, ?_⟩
  rw [h4, mulCols_sum, V_eq4, V_eq4]

end

end VG.Proof.X25519.PPC64LE
