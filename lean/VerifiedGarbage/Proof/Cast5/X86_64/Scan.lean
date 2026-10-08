import VerifiedGarbage.Impl.Cast5.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# CAST5 on x86-64: the scan of a table

`scan sym` visits the 256 entries of 16 bytes of the table at `T` (the
address of `sym`), in order, and leaves in each dword lane `k` of `xmm1`
dword `k` of the entry whose number is in lane `k` of `xmm0`
(`scan_ok`). Vector values are kept as their four dword lanes (`L`).
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5.X86_64
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

/-- Dword `k` of entry `i` of the table at `T`. -/
def ent (m : Mem) (T : Addr) (i k : Nat) : BitVec 32 :=
  m.readW (T + BitVec.ofNat 64 (16 * i + 4 * k)) 32

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

/-- What the scan keeps of a state: everything but `r10`, `r11`, the flags and
`xmm1`–`xmm5`. -/
structure ScanKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r
  xmm : ∀ x, x ≠ .xmm1 → x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → x ≠ .xmm5 → t.xmm x = s.xmm x
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem ScanKeep.refl (s : State) : ScanKeep s s := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩

theorem ScanKeep.trans {s t u : State} (h : ScanKeep s t) (h' : ScanKeep t u) : ScanKeep s u :=
  ⟨fun r a b => (h'.gpr r a b).trans (h.gpr r a b),
   fun x a b c d e => (h'.xmm x a b c d e).trans (h.xmm x a b c d e),
   h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

/-- The state of the scan with entries `0 … j - 1` visited, from `s₀`. -/
structure ScanAt (s₀ : State) (T : Addr) (idx : Nat → BitVec 32) (j : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = L idx
  x1 : s.xmm .xmm1 = L (acc s₀.mem T idx j)
  x2 : s.xmm .xmm2 = L (splat j)
  x3 : s.xmm .xmm3 = L (splat 1)
  keep : ScanKeep s₀ s

theorem ScanAt.setReg {s₀ t : State} {T : Addr} {idx : Nat → BitVec 32} {j : Nat}
    (h : ScanAt s₀ T idx j t) {r : Reg} (hr : r = .r10 ∨ r = .r11) (v : BitVec 64) :
    ScanAt s₀ T idx j (t.setReg r v) :=
  ⟨h.x0, h.x1, h.x2, h.x3, h.keep.trans ⟨fun r' a b => by
    rw [gpr_setReg_of_ne t v (by rcases hr with rfl | rfl; exacts [a, b])], fun _ _ _ _ _ _ => rfl,
    rfl, rfl, rfl⟩⟩

theorem ScanAt.setFlags {s₀ t : State} {T : Addr} {idx : Nat → BitVec 32} {j : Nat}
    (h : ScanAt s₀ T idx j t) (a b c d : Option Bool) : ScanAt s₀ T idx j (t.setFlags a b c d) :=
  ⟨h.x0, h.x1, h.x2, h.x3, h.keep.trans ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩⟩

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

theorem entry_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {j : Nat} (e : Nat)
    (hj : j < 256) (h : ScanAt s₀ T idx j s)
    (ha : s.gpr .r10 + BitVec.ofNat 64 (16 * e) = T + BitVec.ofNat 64 (16 * j))
    (hr : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block (scanEntry e)) s fun t => ScanAt s₀ T idx (j + 1) t ∧ t.gpr = s.gpr := by
  obtain ⟨h0, h1, h2, h3, hk⟩ := h
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [scanEntry, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
      ea_at, gpr_setXmm, rd_setXmm, wr_setXmm, ha, hr, ite_true, Option.map_some]
    rfl, ?_⟩
  simp only [mem_setXmm, gpr_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne,
    reduceCtorEq, not_false_eq_true, h0, h1, h2, h3, and_true]
  have hm : s.mem = s₀.mem := hk.mem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, h0]
  · rw [xmm_setXmm_of_ne _ _ (by decide), xmm_setXmm_self, movdqa_L, pcmpeqd_L, readW128_L,
      pand_L, por_L, hm]
    refine L_congr fun k hk => ?_
    rw [← acc_succ _ _ _ (by omega)]
    unfold ent splat
    rw [Offset.add_add, BitVec.and_comm]
  · rw [xmm_setXmm_self, paddd_L]
    refine L_congr fun k _ => ?_
    simp only [splat, BitVec.ofNat_add]
  · simp only [xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, h3]
  · refine hk.trans ⟨fun _ _ _ => by simp only [gpr_setXmm], fun x a b c d e => ?_, by simp only [mem_setXmm],
      by simp only [rd_setXmm], by simp only [wr_setXmm]⟩
    simp only [xmm_setXmm_of_ne _ _ a, xmm_setXmm_of_ne _ _ b, xmm_setXmm_of_ne _ _ d,
      xmm_setXmm_of_ne _ _ e]

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The table at `T` is readable. -/
def Readable (s : State) (T : Addr) : Prop := InRegions (s.rd ++ s.wr) T 4096

theorem entries_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {q : Nat} (hq : q < 64)
    (hT : Readable s₀ T) (hr10 : s.gpr .r10 = T + BitVec.ofNat 64 (64 * q)) :
    ∀ e ≤ 4, ScanAt s₀ T idx (4 * q) s →
      WP isa (.block ((List.range e).flatMap scanEntry)) s
        fun t => ScanAt s₀ T idx (4 * q + e) t ∧ t.gpr = s.gpr := by
  intro e he h
  induction e with
  | zero => exact WP.block_nil ⟨h, rfl⟩
  | succ e ih =>
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨ht, hg⟩ => ?_
    have hr : InRegions (t.rd ++ t.wr) (T + BitVec.ofNat 64 (16 * (4 * q + e))) 16 := by
      rw [ht.keep.rd, ht.keep.wr]
      exact CallLay.inRegions_sub hT (by omega) (by decide)
    refine WP.mono (entry_ok e (by omega) ht ?_ hr) fun u ⟨hu, hug⟩ => ⟨hu, hug.trans hg⟩
    rw [hg, hr10, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega

theorem body_ok {s₀ s : State} {T : Addr} {idx : Nat → BitVec 32} {q : Nat} (hq : q < 64)
    (hT : Readable s₀ T) (hr10 : s.gpr .r10 = T + BitVec.ofNat 64 (64 * q))
    (h : ScanAt s₀ T idx (4 * q) s) :
    WP isa (.block scanBody) s fun t => ScanAt s₀ T idx (4 * (q + 1)) t ∧
      t.gpr .r10 = T + BitVec.ofNat 64 (64 * (q + 1)) ∧ t.gpr .r11 = s.gpr .r11 - 1 ∧
      t.zf = some (s.gpr .r11 - 1 == 0) := by
  unfold scanBody
  rw [WP.block_append_iff]
  refine WP.mono (entries_ok hq hT hr10 4 (Nat.le_refl _) h) fun t ⟨ht, hg⟩ => ?_
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
    WP isa (.block [.leaSym .r10 sym, .mov32 .r11 (imm 64), .xop (.bin .pxor .xmm1 .xmm1),
      .xop (.bin .pxor .xmm2 .xmm2), .xop (.bin .pcmpeqd .xmm3 .xmm3), .xop (.shift .psrld .xmm3 31)]) s
      fun t => ScanAt s (s.syms sym) idx 0 t ∧ t.gpr .r10 = s.syms sym ∧ t.gpr .r11 = 64 := by
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, exec, readSrc32, imm]
    rfl, ?_⟩
  simp only [XOp.exec]
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨fun r a b => ?_, fun x a b c d e => ?_, rfl, rfl, rfl⟩⟩, ?_, ?_⟩
  · simp only [xmm_setXmm_of_ne _ _ (show XReg.xmm0 ≠ .xmm3 by decide),
      xmm_setXmm_of_ne _ _ (show XReg.xmm0 ≠ .xmm2 by decide),
      xmm_setXmm_of_ne _ _ (show XReg.xmm0 ≠ .xmm1 by decide), State.setReg32, xmm_setReg, h0]
  · simp only [xmm_setXmm_of_ne _ _ (show XReg.xmm1 ≠ .xmm3 by decide),
      xmm_setXmm_of_ne _ _ (show XReg.xmm1 ≠ .xmm2 by decide), xmm_setXmm_self, acc_zero,
      XBinOp.eval, BitVec.xor_self]
    rfl
  · simp only [xmm_setXmm_of_ne _ _ (show XReg.xmm2 ≠ .xmm3 by decide), xmm_setXmm_self,
      XBinOp.eval, BitVec.xor_self]
    decide
  · simp only [xmm_setXmm_self, ones_L]
  · simp only [gpr_setXmm, State.setReg32, gpr_setReg_of_ne _ _ a, gpr_setReg_of_ne _ _ b]
  · simp only [xmm_setXmm_of_ne _ _ a, xmm_setXmm_of_ne _ _ b, xmm_setXmm_of_ne _ _ c,
      State.setReg32, xmm_setReg]
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
    (fun q u => ScanAt s (s.syms sym) idx (4 * q) u ∧
      u.gpr .r10 = s.syms sym + BitVec.ofNat 64 (64 * q))
    (fun q hq u ⟨hu, h10⟩ _ => WP.mono (body_ok hq hT h10 hu) fun v ⟨hv, h10', h11', hz⟩ =>
      ⟨⟨hv, h10'⟩, h11', hz⟩)
    (fun u ⟨hu, _⟩ => ⟨?_, hu.keep⟩) ⟨ht, by rw [h10]; exact (BitVec.add_zero _).symm⟩ (by rw [h11]; rfl)
  rw [hu.x1]
  exact L_congr fun k hk => by rw [acc, ite_eq_left (by have := hidx k hk; omega)]

end VG.Proof.Cast5.X86_64
