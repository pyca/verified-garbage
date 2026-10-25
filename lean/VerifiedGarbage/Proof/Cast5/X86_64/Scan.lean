module

public import VerifiedGarbage.Impl.Cast5.X86_64
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CAST5 on x86-64: the scan of a table

`scan sym` visits the 256 entries of 16 bytes of the table at `T` (the
address of `sym`), in order, and leaves in each dword lane `k` of `xmm1`
dword `k` of the entry whose number is in lane `k` of `xmm0`
(`scan_ok`). Vector values are kept as their four dword lanes (`L`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts keyConsts)
open VG.Proof.MlKem.X86_64 (Keep wp_countdown)

/-! ## Dword lanes -/

/-- The value whose dword lanes are `f 0, f 1, f 2, f 3`. -/
def L (f : Nat → BitVec 32) : BitVec 128 := ofDwords (f 0) (f 1) (f 2) (f 3)

theorem dword_L (f : Nat → BitVec 32) {k : Nat} (hk : k < 4) : dword (L f) k = f k := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp [L]

theorem L_dword (x : BitVec 128) : L (dword x ·) = x := ofDwords_dword x

theorem L_congr {f g : Nat → BitVec 32} (h : ∀ k < 4, f k = g k) : L f = L g := by
  simp only [L, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

theorem dword_pand (a b : BitVec 128) (k : Nat) :
    dword (XBinOp.eval .pand a b) k = dword a k &&& dword b k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem por_L (f g : Nat → BitVec 32) :
    XBinOp.eval .por (L f) (L g) = L fun k => f k ||| g k := by
  rw [← L_dword (XBinOp.eval .por (L f) (L g))]
  exact L_congr fun k hk => by rw [dword_por, dword_L _ hk, dword_L _ hk]

theorem pand_L (f g : Nat → BitVec 32) :
    XBinOp.eval .pand (L f) (L g) = L fun k => f k &&& g k := by
  rw [← L_dword (XBinOp.eval .pand (L f) (L g))]
  exact L_congr fun k hk => by rw [dword_pand, dword_L _ hk, dword_L _ hk]

theorem paddd_L (f g : Nat → BitVec 32) :
    XBinOp.eval .paddd (L f) (L g) = L fun k => f k + g k := by
  rw [← L_dword (XBinOp.eval .paddd (L f) (L g))]
  exact L_congr fun k hk => by rw [dword_paddd _ _ hk, dword_L _ hk, dword_L _ hk]

theorem pcmpeqd_L (f g : Nat → BitVec 32) :
    XBinOp.eval .pcmpeqd (L f) (L g) = L fun k => if f k = g k then 0xFFFFFFFF else 0 := by
  simp only [XBinOp.eval, L, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]

theorem movdqa_L (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

/-- A 16-byte load, as its four dwords. -/
theorem readW128_L (m : Mem) (a : Addr) :
    m.readW a 128 = L fun k => m.readW (a + BitVec.ofNat 64 (4 * k)) 32 := by
  rw [← L_dword (m.readW a 128)]
  exact L_congr fun k hk => dword_readW m a hk

/-! ## One entry -/

theorem pxor_L (f g : Nat → BitVec 32) :
    XBinOp.eval .pxor (L f) (L g) = L fun k => f k ^^^ g k := by
  rw [← L_dword (XBinOp.eval .pxor (L f) (L g))]
  exact L_congr fun k hk => by rw [dword_pxor, dword_L _ hk, dword_L _ hk]

theorem psubd_L (f g : Nat → BitVec 32) :
    XBinOp.eval .psubd (L f) (L g) = L fun k => f k - g k := by
  simp only [XBinOp.eval, L, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem psrld_L (f : Nat → BitVec 32) (n : BitVec 8) (hn : n.toNat < 32) :
    XShiftOp.eval .psrld (L f) n = L fun k => f k >>> n.toNat := by
  rw [← L_dword (XShiftOp.eval .psrld (L f) n)]
  exact L_congr fun k hk => by rw [dword_psrld _ _ hn hk, dword_L _ hk]

theorem zero_L (x : BitVec 128) : XBinOp.eval .pxor x x = L fun _ => 0 := by
  simp only [XBinOp.eval, BitVec.xor_self]
  rfl

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

/-- A replicated mask for the low bit, without a branch. -/
def bitMask (x : BitVec 32) : BitVec 32 := 0 - (x &&& 1)

def mux (a b mask : BitVec 32) : BitVec 32 := a ^^^ ((b ^^^ a) &&& mask)

theorem mux_bit (a b x : BitVec 32) :
    mux a b (bitMask x) = if x.toNat % 2 = 0 then a else b := by
  have hn : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 1
  unfold mux bitMask
  by_cases h : x.toNat % 2 = 0
  · have hv : x &&& 1 = 0 := BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)
    rw [hv, ite_eq_left h]
    simp only [BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]
  · have hv : x &&& 1 = 1 := BitVec.eq_of_toNat_eq (by change (x &&& 1).toNat = 1; rw [hn]; have := Nat.mod_lt x.toNat (by decide : 0 < 2); omega)
    rw [hv, ite_eq_right h, show (0 - (1 : BitVec 32)) = BitVec.allOnes 32 by rfl,
      BitVec.and_allOnes, BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Selecting one of four adjacent entries in each lane. -/
def tileVal (m : Mem) (T : Addr) (i : BitVec 32) (q k : Nat) : BitVec 32 :=
  mux (mux (ent m T (4 * q) k) (ent m T (4 * q + 1) k) (bitMask i))
    (mux (ent m T (4 * q + 2) k) (ent m T (4 * q + 3) k) (bitMask i)) (bitMask (i >>> 1))

theorem acc_tile (m : Mem) (T : Addr) (idx : Nat → BitVec 32) {q : Nat} (hq : q < 64) (k : Nat) :
    acc m T idx (4 * q) k |||
      (tileVal m T (idx k) q k &&& if idx k >>> 2 = BitVec.ofNat 32 q then 0xffffffff else 0) =
      acc m T idx (4 * (q + 1)) k := by
  have hn : (idx k >>> 2).toNat = (idx k).toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases he : idx k >>> 2 = BitVec.ofNat 32 q
  · have hdiv : (idx k).toNat / 4 = q := by
      have h := congrArg BitVec.toNat he
      rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
      exact h
    have hold : ¬ (idx k).toNat < 4 * q := by omega
    have hnew : (idx k).toNat < 4 * (q + 1) := by omega
    simp only [acc, ite_eq_right hold, ite_eq_left hnew, ite_eq_left he, and_ones', zero_or']
    unfold tileVal
    rw [mux_bit, mux_bit, mux_bit]
    have hs : (idx k >>> 1).toNat = (idx k).toNat / 2 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hs]
    rcases (show (idx k).toNat % 4 = 0 ∨ (idx k).toNat % 4 = 1 ∨
      (idx k).toNat % 4 = 2 ∨ (idx k).toNat % 4 = 3 by omega) with h | h | h | h
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), show (idx k).toNat = 4 * q by omega]
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), show (idx k).toNat = 4 * q + 1 by omega]
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), show (idx k).toNat = 4 * q + 2 by omega]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), show (idx k).toNat = 4 * q + 3 by omega]
  · have hdiv : (idx k).toNat / 4 ≠ q := by
      intro h
      apply he
      apply BitVec.eq_of_toNat_eq
      rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), h]
    rw [ite_eq_right he, and_zero', or_zero']
    unfold acc
    by_cases h : (idx k).toNat < 4 * q
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- What the scan keeps of a state: everything but `r10`, `r11`, the flags and
`xmm1`–`xmm9`. -/
structure ScanKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r
  xmm : ∀ x, x ≠ .xmm1 → x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → x ≠ .xmm5 → x ≠ .xmm6 → x ≠ .xmm7 → x ≠ .xmm8 → x ≠ .xmm9 → t.xmm x = s.xmm x
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem ScanKeep.refl (s : State) : ScanKeep s s := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩

theorem ScanKeep.trans {s t u : State} (h : ScanKeep s t) (h' : ScanKeep t u) : ScanKeep s u :=
  ⟨fun r a b => (h'.gpr r a b).trans (h.gpr r a b),
   fun x a b c d e f g h8 h9 => (h'.xmm x a b c d e f g h8 h9).trans (h.xmm x a b c d e f g h8 h9),
   h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

/-- The state of the scan with entries `0 … 4j - 1` visited, from `s₀`. -/
structure ScanAt (s₀ : State) (T : Addr) (idx : Nat → BitVec 32) (j : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = L idx
  x1 : s.xmm .xmm1 = L (acc s₀.mem T idx (4 * j))
  x2 : s.xmm .xmm2 = L (splat j)
  x3 : s.xmm .xmm3 = L (splat 1)
  x6 : s.xmm .xmm6 = L fun k => bitMask (idx k)
  x7 : s.xmm .xmm7 = L fun k => bitMask (idx k >>> 1)
  x8 : s.xmm .xmm8 = L fun k => idx k >>> 2
  keep : ScanKeep s₀ s

theorem ScanAt.setReg {s₀ t : State} {T : Addr} {idx : Nat → BitVec 32} {j : Nat}
    (h : ScanAt s₀ T idx j t) {r : Reg} (hr : r = .r10 ∨ r = .r11) (v : BitVec 64) :
    ScanAt s₀ T idx j (t.setReg r v) :=
  ⟨h.x0, h.x1, h.x2, h.x3, h.x6, h.x7, h.x8, h.keep.trans ⟨fun r' a b => by
    rw [gpr_setReg_of_ne t v (by rcases hr with rfl | rfl; exacts [a, b])], fun _ _ _ _ _ _ _ _ _ _ => rfl,
    rfl, rfl, rfl⟩⟩

theorem ScanAt.setFlags {s₀ t : State} {T : Addr} {idx : Nat → BitVec 32} {j : Nat}
    (h : ScanAt s₀ T idx j t) (a b c d : Option Bool) : ScanAt s₀ T idx j (t.setFlags a b c d) :=
  ⟨h.x0, h.x1, h.x2, h.x3, h.x6, h.x7, h.x8, h.keep.trans ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩⟩

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

/-- The table at `T` is readable. -/
def Readable (s : State) (T : Addr) : Prop := InRegions (s.rd ++ s.wr) T 4096

theorem tile_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {q : Nat} (hq : q < 64)
    (hT : Readable s₀ T) (hr10 : s.gpr .r10 = T + BitVec.ofNat 64 (64 * q))
    (h : ScanAt s₀ T idx q s) :
    WP isa (.block scanTile) s fun t => ScanAt s₀ T idx (q + 1) t ∧ t.gpr = s.gpr := by
  obtain ⟨h0, h1, h2, h3, h6, h7, h8, hk⟩ := h
  have ha (e : Nat) : s.gpr .r10 + BitVec.ofNat 64 (16 * e) = T + BitVec.ofNat 64 (16 * (4 * q + e)) := by
    rw [hr10, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  have hr (e : Nat) (he : e < 4) :
      InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (16 * (4 * q + e))) 16 := by
    rw [hk.rd, hk.wr]
    exact CallLay.inRegions_sub hT (by omega) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [scanTile, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
      ea_at, gpr_setXmm, rd_setXmm, wr_setXmm, ha 0, ha 1, ha 2, ha 3,
      hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), ite_true, Option.map_some]
    rfl, ?_⟩
  simp only [mem_setXmm, gpr_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne,
    reduceCtorEq, not_false_eq_true, h1, h2, h3, h6, h7, h8, and_true]
  have hm : s.mem = s₀.mem := hk.mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, h0]
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, xmm_setXmm_self,
      movdqa_L, pcmpeqd_L, readW128_L, pand_L, por_L, pxor_L, hm]
    refine L_congr fun k hk => ?_
    rw [← acc_tile _ _ _ hq k]
    simp only [tileVal, mux, ent, splat, Offset.add_add]
    rfl
  · rw [xmm_setXmm_self, paddd_L]
    exact L_congr fun k _ => by simp only [splat, BitVec.ofNat_add]
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, h3]
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, h6]
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, h7]
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, h8]
  · refine hk.trans ⟨fun _ _ _ => by simp only [gpr_setXmm], fun x a b c d e f g h i => ?_,
      by simp only [mem_setXmm], by simp only [rd_setXmm], by simp only [wr_setXmm]⟩
    simp only [xmm_setXmm_of_ne _ _ a, xmm_setXmm_of_ne _ _ b, xmm_setXmm_of_ne _ _ d,
      xmm_setXmm_of_ne _ _ e, xmm_setXmm_of_ne _ _ i]

theorem body_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {q : Nat} (hq : q < 64)
    (hT : Readable s₀ T) (hr10 : s.gpr .r10 = T + BitVec.ofNat 64 (64 * q))
    (h : ScanAt s₀ T idx q s) :
    WP isa (.block scanBody) s fun t => ScanAt s₀ T idx (q + 1) t ∧
      t.gpr .r10 = T + BitVec.ofNat 64 (64 * (q + 1)) ∧ t.gpr .r11 = s.gpr .r11 - 1 ∧
      t.zf = some (s.gpr .r11 - 1 == 0) := by
  unfold scanBody
  rw [WP.block_append_iff]
  refine WP.mono (tile_ok hq hT hr10 h) fun t ⟨ht, hg⟩ => ?_
  open VG.Proof.MlKem.X86_64 in xrun [imm, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  rw [hg, hr10, BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * q + 64 = 64 * (q + 1) by omega]
  exact ⟨(((ht.setFlags _ _ _ _).setReg (.inl rfl) _).setFlags _ _ _ _).setReg (.inr rfl) _,
    rfl, rfl, rfl⟩

theorem acc_zero (m : Mem) (T : Addr) (idx : Nat → BitVec 32) : L (acc m T idx 0) = 0 := by
  rw [show (0 : BitVec 128) = L fun _ => 0 by decide]
  exact L_congr fun k _ => by simp [acc]

theorem ones_L (x : BitVec 128) :
    XShiftOp.eval .psrld (XBinOp.eval .pcmpeqd x x) 31 = L (splat 1) := by
  have : XBinOp.eval .pcmpeqd x x = L fun _ => 0xFFFFFFFF := by
    simp only [XBinOp.eval, L, ite_true]
  rw [this, ← L_dword (XShiftOp.eval .psrld _ 31)]
  exact L_congr fun k hk => by
    rw [dword_psrld _ _ (by decide) hk, dword_L _ hk]
    simp [splat]

/-- The setup of the scan: the table's address in `r10`, 64 groups to go in
`r11`, nothing found yet, entry 0 next, and ones. -/
theorem start_ok (s : State) (sym : String) {idx : Nat → BitVec 32} (h0 : s.xmm .xmm0 = L idx) :
    WP isa (.block (scanStart sym)) s
      fun t => ScanAt s (s.syms sym) idx 0 t ∧ t.gpr .r10 = s.syms sym ∧ t.gpr .r11 = 64 := by
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [scanStart, runBlock_cons, runStep_some, exec, readSrc32, imm]
    rfl, ?_⟩
  simp only [XOp.exec]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r a b => ?_, fun x a b c d e f g h i => ?_, rfl, rfl, rfl⟩⟩, ?_, ?_⟩
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, State.setReg32, xmm_setReg, h0]
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, xmm_setXmm_self, Nat.mul_zero, acc_zero,
      XBinOp.eval, BitVec.xor_self]
    rfl
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, xmm_setXmm_self,
      XBinOp.eval, BitVec.xor_self]
    decide
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, xmm_setXmm_self, ones_L]
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, xmm_setXmm_self,
      State.setReg32, xmm_setReg, h0, movdqa_L, zero_L, ones_L, pand_L, psubd_L]
    rfl
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, xmm_setXmm_self,
      State.setReg32, xmm_setReg, h0, movdqa_L, zero_L, ones_L, psrld_L _ 1 (by decide), pand_L, psubd_L]
    rfl
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, xmm_setXmm_self,
      State.setReg32, xmm_setReg, h0, movdqa_L, psrld_L _ 2 (by decide)]
    rfl
  · simp only [gpr_setXmm, State.setReg32, gpr_setReg_of_ne _ _ a, gpr_setReg_of_ne _ _ b]
  · simp only [xmm_setXmm_of_ne _ _ a, xmm_setXmm_of_ne _ _ b, xmm_setXmm_of_ne _ _ c,
      xmm_setXmm_of_ne _ _ d, xmm_setXmm_of_ne _ _ f, xmm_setXmm_of_ne _ _ g,
      xmm_setXmm_of_ne _ _ h, State.setReg32, xmm_setReg]
  · simp only [gpr_setXmm, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.r10 ≠ .r11 by decide),
      gpr_setReg_self]
  · simp only [gpr_setXmm, State.setReg32, gpr_setReg_self]
    decide

/-- The scan: lane `k` of `xmm1` is dword `k` of the entry of the table at
`sym` whose number is lane `k` of `xmm0`. -/
theorem scan_ok (s : State) (sym : String) {idx : Nat → BitVec 32} (h0 : s.xmm .xmm0 = L idx)
    (hidx : ∀ k < 4, (idx k).toNat < 256) (hT : Readable s (s.syms sym)) :
    WP isa (scan sym) s fun t =>
      t.xmm .xmm1 = L (fun k => ent s.mem (s.syms sym) (idx k).toNat k) ∧ ScanKeep s t := by
  unfold scan
  refine WP.seq (WP.mono (start_ok s sym h0) fun t ⟨ht, h10, h11⟩ => ?_)
  refine wp_countdown (cnt := .r11) (N := 64) (by decide) (by decide)
    (fun q u => ScanAt s (s.syms sym) idx q u ∧
      u.gpr .r10 = s.syms sym + BitVec.ofNat 64 (64 * q))
    (fun q hq u ⟨hu, h10⟩ _ => WP.mono (body_ok hq hT h10 hu) fun v ⟨hv, h10', h11', hz⟩ =>
      ⟨⟨hv, h10'⟩, h11', hz⟩)
    (fun u ⟨hu, _⟩ => ⟨?_, hu.keep⟩) ⟨ht, by rw [h10]; exact (BitVec.add_zero _).symm⟩ (by rw [h11]; rfl)
  rw [hu.x1]
  exact L_congr fun k hk => by rw [acc, ite_eq_left (by have := hidx k hk; omega)]

end VG.Proof.Cast5.X86_64
