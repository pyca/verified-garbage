module

public import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Cast5.X86_64
public import VerifiedGarbage.Proof.Cast5.Scan
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `Cast5.X86_64.Scan`, which this module and modules that import it used -/

section

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

/-- What the scan keeps of a state: everything but `r10`, `r11`, the flags and
`xmm1`–`xmm9`. -/
structure ScanKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r
  xmm : ∀ x, x ≠ .xmm1 → x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → x ≠ .xmm5 → x ≠ .xmm6 → x ≠ .xmm7 → x ≠ .xmm8 → x ≠ .xmm9 → t.xmm x = s.xmm x
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

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
    omega_using []
  have hr (e : Nat) (he : e < 4) :
      InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (16 * (4 * q + e))) 16 := by
    rw [hk.rd, hk.wr]
    exact CallLay.inRegions_sub hT (by omega_using [hq, he]) (by decide)
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
  rw [hg, hr10, BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * q + 64 = 64 * (q + 1) by omega_using []]
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
  exact L_congr fun k hk => by rw [acc, ite_eq_left (by have := hidx k hk; omega_using [this])]

end VG.Proof.Cast5.X86_64

end

end

/-! ### `Cast5.X86_64.Round`, which only this module used -/

section

/-!
# CAST5 on x86-64: a round

`round t up` computes `I` (`mask`, `rotate`), spreads its bytes over the
lanes of `xmm0` (`spread`), scans `VG_CAST5_S1234` and combines the four
values into `f` (`combine`), then makes the Feistel step (`feistel`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts keyConsts)
open VG.Proof.MlKem.X86_64 (Keep sx_ofNat WP.keep writesOnly)

/-! ## The rotation -/

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (hax : s.gpr .rax = a.setWidth 64) (h9 : s.gpr .r9 = kb.setWidth 64) :
    WP isa (.block (rotateStep b)) s fun t =>
      t.gpr .rax = (Proof.Cast5.step a kb b).setWidth 64 ∧
      t.gpr .r9 = (if b < 4 then kb >>> 1 else kb).setWidth 64 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.xmm = s.xmm := by
  have hn : 1 ≤ 32 - 2 ^ b ∧ 32 - 2 ^ b ≤ 31 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    xrun [imm, hax, h9, execShift32, hn, List.cons_append, List.nil_append, xmm_setReg, xmm_setFlags]
    exact ⟨rfl, by rw [ite_eq_left h4]⟩
  · rw [ite_eq_right h4]
    xrun [imm, hax, h9, execShift32, hn, List.append_nil, xmm_setReg, xmm_setFlags]
    exact ⟨rfl, by rw [ite_eq_right h4]⟩

theorem rotate_ok (s : State) {a kb : BitVec 32}
    (hax : s.gpr .rax = a.setWidth 64) (h9 : s.gpr .r9 = kb.setWidth 64) :
    WP isa (.block rotate) s fun t =>
      t.gpr .rax = (a.rotateLeft (kb.toNat % 32)).setWidth 64 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.xmm = s.xmm := by
  have e : rotate = rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++ rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rotateStep_ok s (by decide) hax h9) fun t₁ ⟨a₁, k₁, m₁, r₁, w₁, x₁⟩ => ?_
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
  rw [a₅, Proof.Cast5.steps_eq]

/-- Lane `k` of the indices `spread` makes of `I`: byte `3 - k` of `I`. -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i &&& 255
  | 1 => (i >>> 8) &&& 255
  | 2 => (i >>> 16) &&& 255
  | _ => i >>> 24

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := i.isLt; omega_using []

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show (255 : BitVec 32).toNat = 255 from rfl, Nat.and_two_pow_sub_one_eq_mod _ 8] <;>
    omega_using []

theorem lanes_eq (a b c d : BitVec 32) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (a.setWidth 64 ||| b.setWidth 64 <<< 32))
      ((0 : BitVec 64) ++ (c.setWidth 64 ||| d.setWidth 64 <<< 32)) = ofDwords a b c d := by
  rw [punpcklqdq_eq]
  have lo (x y : BitVec 32) : dword ((0 : BitVec 64) ++ (x.setWidth 64 ||| y.setWidth 64 <<< 32)) 0 = x := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp (disch := omega_using [hj]) only [dword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
      BitVec.getLsbD_append, ite_eq_left, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, Nat.mul_zero, Nat.zero_add, decide_eq_true, Bool.not_true,
      Bool.false_and, Bool.or_false]
  have hi (x y : BitVec 32) : dword ((0 : BitVec 64) ++ (x.setWidth 64 ||| y.setWidth 64 <<< 32)) 1 = y := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp (disch := omega) only [dword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
      BitVec.getLsbD_append, ite_eq_left, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, Nat.mul_one, decide_eq_true, Nat.add_sub_cancel_left]
    rw [BitVec.getLsbD_of_ge x _ (by omega_using []), Bool.false_or, decide_eq_false (by omega_using []), Bool.not_false,
      Bool.true_and]
  rw [lo, hi, lo, hi]

theorem spread_ok (s : State) {i : BitVec 32} (hax : s.gpr .rax = i.setWidth 64) :
    WP isa (.block spread) s fun t =>
      t.xmm .xmm0 = L (idx i) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        (∀ x, x ≠ .xmm0 → x ≠ .xmm4 → t.xmm x = s.xmm x) := by
  unfold spread
  xrun [imm, hax, execShift32, XOp.exec, xmm_setReg, xmm_setFlags, gpr_setXmm, mem_setXmm, rd_setXmm,
    wr_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne]
  refine ⟨lanes_eq _ _ _ _, fun x h0 h4 => ?_⟩
  simp only [xmm_setXmm_of_ne _ _ h0, xmm_setXmm_of_ne _ _ h4, xmm_setReg, xmm_setFlags]

theorem mask_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km kr d : Spec.Cast5.Word}
    (hbp : s.gpr .rbp = d.setWidth 64)
    (hm : InRegions (s.rd ++ s.wr) (s.gpr .r12) 4) (hmv : s.mem.readW (s.gpr .r12) 32 = km)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 64) 4)
    (hrv : s.mem.readW (s.gpr .r12 + BitVec.ofNat 64 64) 32 = kr) :
    WP isa (.block (mask t ++ ([.mov32 .r9 (.mem (at_ .r12 64))] : List Instr))) s fun u =>
      u.gpr .rax = (Proof.Cast5.mix t km d).setWidth 64 ∧ u.gpr .r9 = kr.setWidth 64 ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.xmm = s.xmm ∧ u.gpr .r12 = s.gpr .r12 := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold mask
    xrun [VG.Proof.Cast5.X86_64.ea_at, hbp, hm, hmv, hr, hrv, xmm_setReg, xmm_setFlags,
      List.cons_append, List.nil_append]
    rfl

theorem rd_lane (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (4 * j)) 32 = dword v j := readW_writeW128 m a v hj

theorem rd_lane0 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 32 = dword v 0 := by
  rw [← readW_writeW128 m a v (j := 0) (by decide), BitVec.add_zero]

theorem rd_lane1 (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 4) 32 = dword v 1 := readW_writeW128 m a v (j := 1) (by decide)
theorem rd_lane2 (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 8) 32 = dword v 2 := readW_writeW128 m a v (j := 2) (by decide)
theorem rd_lane3 (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 12) 32 = dword v 3 := readW_writeW128 m a v (j := 3) (by decide)

theorem post_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {v : Nat → Spec.Cast5.Word} {l r : Spec.Cast5.Word}
    (h1 : s.xmm .xmm1 = L v) (hbx : s.gpr .rbx = l.setWidth 64) (hbp : s.gpr .rbp = r.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r8) 16) :
    WP isa (.block (([.movdquStore (at_ .r8 0) .xmm1] : List Instr) ++ combine t ++ feistel up)) s
      fun u => u.gpr .rbx = r.setWidth 64 ∧
        u.gpr .rbp = (l ^^^ Proof.Cast5.comb t (v 3) (v 2) (v 1) (v 0)).setWidth 64 ∧
        u.gpr .r12 = (if up then s.gpr .r12 + 4 else s.gpr .r12 - 4) ∧
        u.mem = s.mem.writeW (s.gpr .r8) (L v) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.xmm = s.xmm := by
  have hc (k : Nat) (hk : k < 4) :
      InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 (4 * k)) 4 := by
    obtain ⟨g, hg, hgc⟩ := hw
    exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hgc⟩ (by omega_using [hk]) (by decide)
  have e0 : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4 := by
    have := hc 0 (by decide); rwa [BitVec.add_zero] at this
  have e1 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 4) 4 := hc 1 (by decide)
  have e2 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 8) 4 := hc 2 (by decide)
  have e3 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 12) 4 := hc 3 (by decide)
  have d0 : dword (L v) 0 = v 0 := dword_L v (by decide)
  have d1 : dword (L v) 1 = v 1 := dword_L v (by decide)
  have d2 : dword (L v) 2 = v 2 := dword_L v (by decide)
  have d3 : dword (L v) 3 = v 3 := dword_L v (by decide)
  rcases ht with rfl | rfl | rfl <;> cases up <;>
  · unfold combine feistel
    xrun [VG.Proof.Cast5.X86_64.ea_at, imm, State.store128, hw, h1, hbx, hbp, e0, e1, e2, e3, rd_lane0,
      rd_lane1, rd_lane2, rd_lane3, d0, d1, d2, d3, xmm_setReg, xmm_setFlags, List.cons_append,
      List.nil_append, sx_ofNat (show 4 < 2 ^ 31 by decide)]
    exact ⟨by rw [BitVec.xor_comm]; rfl, rfl⟩

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- The registers a round writes. -/
def roundRegs : List Reg := [.rax, .rbx, .rbp, .r9, .r10, .r11, .r12, .r14, .r15]

/-- What a round needs: `(L, R)` in `ebx`, `ebp`; `Kmᵢ` at `r12` and `Krᵢ` at
`r12 + 64`; 16 writable bytes at `r8`; the table. -/
structure RoundPre (s : State) (km kr l r : Spec.Cast5.Word) : Prop where
  bx : s.gpr .rbx = l.setWidth 64
  bp : s.gpr .rbp = r.setWidth 64
  inM : InRegions (s.rd ++ s.wr) (s.gpr .r12) 4
  valM : s.mem.readW (s.gpr .r12) 32 = km
  inR : InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 64) 4
  valR : s.mem.readW (s.gpr .r12 + BitVec.ofNat 64 64) 32 = kr
  w : InRegions s.wr (s.gpr .r8) 16
  tab : Readable s (s.syms s1234Sym)
  held : Held s.mem (s.syms s1234Sym) s1234

/-- The first block of a round: `I`, and its bytes in the lanes of `xmm0`. -/
theorem first_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km kr l r : Spec.Cast5.Word}
    (h : RoundPre s km kr l r) :
    WP isa (.block (mask t ++ ([.mov32 .r9 (.mem (at_ .r12 64))] : List Instr) ++ rotate ++ spread)) s
      fun u => u.xmm .xmm0 = L (idx ((Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32))) ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mask_ok s ht h.bp h.inM h.valM h.inR h.valR) fun u ⟨ua, u9, um, urd, uwr, _, _⟩ => ?_
  refine WP.mono (rotate_ok u ua u9) fun v ⟨va, vm, vrd, vwr, _⟩ => ?_
  refine WP.mono (spread_ok v va) fun w ⟨w0, wm, wrd, wwr, _⟩ => ?_
  exact ⟨w0, wm.trans (vm.trans um), wrd.trans (vrd.trans urd), wwr.trans (vwr.trans uwr)⟩

theorem round_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {km kr l r : Spec.Cast5.Word} (h : RoundPre s km kr l r) :
    WP isa (round t up) s fun u =>
      u.gpr .rbx = r.setWidth 64 ∧ u.gpr .rbp = (l ^^^ fT t km kr r).setWidth 64 ∧
      u.gpr .r12 = (if up then s.gpr .r12 + 4 else s.gpr .r12 - 4) ∧
      Frame [⟨s.gpr .r8, 16⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧
      Keep roundRegs s u := by
  have hw : writesOnly roundRegs (round t up) = true := by
    rcases ht with rfl | rfl | rfl <;> cases up <;> decide
  suffices main : WP isa (round t up) s fun u =>
      u.gpr .rbx = r.setWidth 64 ∧ u.gpr .rbp = (l ^^^ fT t km kr r).setWidth 64 ∧
      u.gpr .r12 = (if up then s.gpr .r12 + 4 else s.gpr .r12 - 4) ∧
      Frame [⟨s.gpr .r8, 16⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr by
    exact WP.mono_syms (WP.keep roundRegs main hw) fun u ⟨⟨a, b, c, d, e, f⟩, hku⟩ hsy =>
      ⟨a, b, c, d, e, f, hsy, hku⟩
  unfold round
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  refine WP.seq (WP.mono_syms (WP.keep [.rax, .r9, .r14, .r15] (first_ok s ht h) (by
    rcases ht with rfl | rfl | rfl <;> decide)) fun u ⟨⟨u0, um, urd, uwr⟩, uk⟩ usy => ?_)
  rw [hi] at u0
  have hT : Readable u (u.syms s1234Sym) := by unfold Readable; rw [usy, urd, uwr]; exact h.tab
  refine WP.seq (WP.mono (scan_ok u s1234Sym u0 (fun k hk => idx_lt i hk) hT) fun v ⟨v1, vk⟩ => ?_)
  have g (q : Reg) (hq : q ∉ [Reg.rax, .r9, .r14, .r15]) (h10 : q ≠ .r10) (h11 : q ≠ .r11) :
      v.gpr q = s.gpr q := (vk.gpr q h10 h11).trans (uk.gpr hq)
  have hvw : InRegions v.wr (v.gpr .r8) 16 := by
    rw [vk.wr, uwr, g .r8 (by decide) (by decide) (by decide)]; exact h.w
  refine WP.mono (post_ok v ht up (l := l) (r := r) v1 (by rw [g .rbx (by decide) (by decide) (by decide)]; exact h.bx)
    (by rw [g .rbp (by decide) (by decide) (by decide)]; exact h.bp) hvw)
    fun w ⟨wbx, wbp, w12, wm, wrd, wwr, _⟩ => ?_
  refine ⟨wbx, ?_, ?_, ?_, by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr]⟩
  · rw [wbp]
    congr 2
    unfold fT
    rw [hi]
    have e (k : Nat) (hk : k < 4) : ent u.mem (u.syms s1234Sym) (idx i k).toNat k =
        tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1 (idx i k).toNat k :=
      ent_table (by rw [um, usy]; exact h.held) (idx_lt i hk) hk
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  · rw [w12, g .r12 (by decide) (by decide) (by decide)]
  · rw [wm, vk.mem, um, g .r8 (by decide) (by decide) (by decide)]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)

end VG.Proof.Cast5.X86_64

end

end


/-!
# CAST5 on x86-64: a block

The rounds of a block, three at a time (`group`), and the block functions
`encryptBlock` and `decryptBlock`: from the block at `rdx` to its encryption
or decryption there.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts keyConsts)
open VG.Proof.MlKem.X86_64 (Keep sx_ofNat WP.keep writesOnly wp_countdown)

/-- `fT` of the type of round `i` is the spec's `f`. -/
theorem fT_eq {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (km kr d : Spec.Cast5.Word) :
    fT t km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]
  unfold fT roundI
  rcases ht with rfl | rfl | rfl <;> rw [← hti] <;> rfl

theorem s1234_length : s1234.length = 512 := table_length _ _ _ _

/-- What every round of a block reads: the subkeys `k` at `rdi`, the table, and
16 bytes of working space at `r8`, apart from both. -/
structure Ctx (s : State) (k : Spec.Cast5.Schedule) : Prop where
  sched : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 128
  key : ∀ j < 32, s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0
  w : InRegions s.wr (s.gpr .r8) 16
  tab : Readable s (s.syms s1234Sym)
  held : Held s.mem (s.syms s1234Sym) s1234
  dsched : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .r8, 16⟩
  dtab : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .r8, 16⟩
  fitS : (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64

/-- The context holds in a state that differs only in registers other than
`rdi` and `r8` and in the working space. -/
theorem Ctx.transfer {s u : State} {k : Spec.Cast5.Schedule} (h : Ctx s k)
    (hdi : u.gpr .rdi = s.gpr .rdi) (h8 : u.gpr .r8 = s.gpr .r8) (hrd : u.rd = s.rd)
    (hwr : u.wr = s.wr) (hsy : u.syms = s.syms) (hf : Frame [⟨s.gpr .r8, 16⟩] s.mem u.mem) :
    Ctx u k := by
  refine ⟨?_, fun j hj => ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrd, hwr, hdi]; exact h.sched
  · rw [hdi, hf.readW (r := ⟨s.gpr .rdi, 128⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact h.dsched)
      (by decide)]
    exact h.key j hj
  · rw [hwr, h8]; exact h.w
  · unfold Readable; rw [hrd, hwr, hsy]; exact h.tab
  · have hi' : i < 512 := by rw [s1234_length] at hi; exact hi
    rw [hsy, hf.readW (r := ⟨s.syms s1234Sym, 4096⟩)
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact h.dtab)
      (by decide)]
    exact h.held i hi
  · rw [hdi, h8]; exact h.dsched
  · rw [hsy, h8]; exact h.dtab
  · rw [hdi]; exact h.fitS
  · rw [hsy]; exact h.fitT

/-- Round `i`'s precondition, with `r12` at `Kmᵢ`. -/
theorem Ctx.roundPre {s : State} {k : Spec.Cast5.Schedule} (h : Ctx s k) {i : Nat}
    (hi : 1 ≤ i ∧ i ≤ 16) (h12 : s.gpr .r12 = s.gpr .rdi + BitVec.ofNat 64 (4 * (i - 1)))
    {l r : Spec.Cast5.Word} (hbx : s.gpr .rbx = l.setWidth 64) (hbp : s.gpr .rbp = r.setWidth 64) :
    RoundPre s (k.getD (i - 1) 0) (k.getD (15 + i) 0) l r := by
  have h64 : s.gpr .r12 + BitVec.ofNat 64 64 = s.gpr .rdi + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [h12, add_ofNat_add]; congr 2; omega_arith
  refine ⟨hbx, hbp, ?_, ?_, ?_, ?_, h.w, h.tab, h.held⟩
  · rw [h12]; exact CallLay.inRegions_sub h.sched (by omega_arith) (by decide)
  · rw [h12]; exact h.key _ (by omega_arith)
  · rw [h64]; exact CallLay.inRegions_sub h.sched (by omega_arith) (by decide)
  · rw [h64]; exact h.key _ (by omega_arith)

/-- The state of a block's rounds, from `s`, with the halves `lr`. -/
structure RInv (s : State) (k : Spec.Cast5.Schedule) (lr : Spec.Cast5.Word × Spec.Cast5.Word)
    (u : State) : Prop where
  bx : u.gpr .rbx = lr.1.setWidth 64
  bp : u.gpr .rbp = lr.2.setWidth 64
  ctx : Ctx u k
  same : ∀ q, q ∉ roundRegs → q ≠ .r13 → u.gpr q = s.gpr q
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  frame : Frame [⟨s.gpr .r8, 16⟩] s.mem u.mem

theorem round_step {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3)
    (hi : 1 ≤ i ∧ i ≤ 16) (h12 : u.gpr .r12 = u.gpr .rdi + BitVec.ofNat 64 (4 * (i - 1))) (up : Bool) :
    WP isa (round t up) u fun v => RInv s k (Spec.Cast5.round k i lr) v ∧
      v.gpr .r12 = (if up then u.gpr .r12 + 4 else u.gpr .r12 - 4) ∧ v.gpr .r13 = u.gpr .r13 := by
  refine WP.mono (round_ok u ht up (h.ctx.roundPre hi h12 h.bx h.bp)) fun v ⟨vbx, vbp, v12, vf, vrd, vwr, vsy, vk⟩ => ?_
  have g (q : Reg) (hq : q ∉ roundRegs) : v.gpr q = u.gpr q := vk.gpr hq
  have h8 : u.gpr .r8 = s.gpr .r8 := h.same .r8 (by decide) (by decide)
  refine ⟨⟨vbx, ?_, h.ctx.transfer (g .rdi (by decide)) (g .r8 (by decide)) vrd vwr vsy vf,
    fun q hq h13 => (g q hq).trans (h.same q hq h13), vrd.trans h.rd, vwr.trans h.wr, vsy.trans h.syms,
    h.frame.trans (by rw [← h8]; exact vf)⟩, v12, g .r13 (by decide)⟩
  rw [vbp, fT_eq ht hti]
  rfl

theorem RInv.setReg {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) {q : Reg} (hq : q = .r13) (x : BitVec 64) : RInv s k lr (u.setReg q x) := by
  subst hq
  refine ⟨h.bx, h.bp, h.ctx.transfer rfl rfl rfl rfl rfl (Frame.refl _ _), fun q hq h13 => ?_, h.rd, h.wr,
    h.syms, h.frame⟩
  rw [gpr_setReg_of_ne _ _ h13]; exact h.same q hq h13

theorem RInv.setFlags {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (a b c d : Option Bool) : RInv s k lr (u.setFlags a b c d) :=
  ⟨h.bx, h.bp, h.ctx.transfer rfl rfl rfl rfl rfl (Frame.refl _ _), h.same, h.rd, h.wr, h.syms, h.frame⟩

/-- `sub r13, 1`. -/
theorem countDown_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) :
    WP isa (.block [.alu .sub .r13 (imm 1)]) u fun v => RInv s k lr v ∧ v.gpr .r12 = u.gpr .r12 ∧
      v.gpr .r13 = u.gpr .r13 - 1 ∧ v.zf = some (u.gpr .r13 - 1 == 0) := by
  xrun [imm, sx_ofNat (show 1 < 2 ^ 31 by decide)]
  exact ⟨(h.setFlags _ _ _ _).setReg rfl _, rfl, rfl⟩

theorem four : (4 : Addr) = BitVec.ofNat 64 4 := rfl

/-- Rounds `3 g + 1`, `3 g + 2`, `3 g + 3` of encryption. -/
theorem groupEnc_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {g : Nat} (hg : 3 * g + 3 ≤ 16) (h : RInv s k (encFold k (3 * g) lr) u)
    (h12 : u.gpr .r12 = u.gpr .rdi + BitVec.ofNat 64 (12 * g)) :
    WP isa (group true) u fun v => RInv s k (encFold k (3 * (g + 1)) lr) v ∧
      v.gpr .r12 = v.gpr .rdi + BitVec.ofNat 64 (12 * (g + 1)) ∧ v.gpr .r13 = u.gpr .r13 - 1 ∧
      v.zf = some (u.gpr .r13 - 1 == 0) := by
  have hdi : ∀ v : State, RInv s k (encFold k (3 * g) lr) u → (∀ lr', RInv s k lr' v → v.gpr .rdi = u.gpr .rdi) :=
    fun v hu lr' hv => (hv.same .rdi (by decide) (by decide)).trans (hu.same .rdi (by decide) (by decide)).symm
  unfold group
  simp only [ite_true]
  refine WP.seq (WP.mono (round_step h (t := 1) (i := 3 * g + 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [h12]; congr 2; omega_arith) true) fun v₁ ⟨h₁, a₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := 3 * g + 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁, ite_eq_left rfl, h12, hdi v₁ h _ h₁, four, add_ofNat_add]; congr 2; omega_arith) true)
    fun v₂ ⟨h₂, a₂, b₂⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₂ (t := 3) (i := 3 * g + 3) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h12, hdi v₂ h _ h₂, four, add_ofNat_add, add_ofNat_add]; congr 2; omega_arith)
    true) fun v₃ ⟨h₃, a₃, b₃⟩ => ?_)
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, z₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [z₄, b₃, b₂, b₁]⟩
  · rw [show 3 * (g + 1) = 3 * g + 2 + 1 by omega_arith, encFold_succ, encFold_succ, encFold_succ]
    exact h₄
  · rw [a₄, a₃, ite_eq_left rfl, a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h12, hdi v₄ h _ h₄, four, add_ofNat_add, add_ofNat_add,
      add_ofNat_add, show 12 * g + 4 + 4 + 4 = 12 * (g + 1) by omega_arith]

/-- Rounds `n - m`, `n - m - 1`, `n - m - 2` of decryption with `n` rounds,
after the first `m`. -/
theorem groupDec_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {n m : Nat} (hm : m + 3 ≤ n) (hn : n ≤ 16) (h3 : (n - m) % 3 = 0) (h : RInv s k (decFold k n m lr) u)
    (h12 : u.gpr .r12 = u.gpr .rdi + BitVec.ofNat 64 (4 * (n - m - 1))) :
    WP isa (group false) u fun v => RInv s k (decFold k n (m + 3) lr) v ∧
      v.gpr .r12 = u.gpr .r12 - 12 ∧ v.gpr .r13 = u.gpr .r13 - 1 ∧
      v.zf = some (u.gpr .r13 - 1 == 0) := by
  have hdi : ∀ v : State, (∀ lr', RInv s k lr' v → v.gpr .rdi = u.gpr .rdi) :=
    fun v lr' hv => (hv.same .rdi (by decide) (by decide)).trans (h.same .rdi (by decide) (by decide)).symm
  have sub4 (x : Addr) (a : Nat) (ha : 4 ≤ a) :
      x + BitVec.ofNat 64 a - 4 = x + BitVec.ofNat 64 (a - 4) := by
    rw [show (4 : Addr) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_sub _ ha]
  unfold group
  simp only [Bool.false_eq_true, ite_false]
  refine WP.seq (WP.mono (round_step h (t := 3) (i := n - m) (by decide) (by omega_arith) (by omega_arith)
    h12 false) fun v₁ ⟨h₁, a₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := n - m - 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁, ite_eq_right Bool.false_ne_true, h12, hdi v₁ _ h₁, sub4 _ _ (by omega_arith)]; congr 2; omega_arith)
    false) fun v₂ ⟨h₂, a₂, b₂⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₂ (t := 1) (i := n - m - 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂, ite_eq_right Bool.false_ne_true, a₁, ite_eq_right Bool.false_ne_true, h12, hdi v₂ _ h₂,
      sub4 _ _ (by omega_arith), sub4 _ _ (by omega_arith)]; congr 2; omega_arith) false) fun v₃ ⟨h₃, a₃, b₃⟩ => ?_)
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, z₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [z₄, b₃, b₂, b₁]⟩
  · rw [decFold_succ, decFold_succ, decFold_succ, show n - (m + 1) = n - m - 1 by omega_arith,
      show n - (m + 2) = n - m - 2 by omega_arith]
    exact h₄
  · rw [a₄, a₃, a₂, a₁]
    simp only [Bool.false_eq_true, ite_false]
    rw [BitVec.sub_sub, BitVec.sub_sub]
    rfl

/-- What a block needs: the context, `n` rounds in `rsi`, and the block at
`rdx`, apart from the working space. -/
structure BPre (s : State) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  ctx : Ctx s k
  nv : n = 12 ∨ n = 16
  rsi : s.gpr .rsi = BitVec.ofNat 64 n
  data : InRegions s.wr (s.gpr .rdx) 8

theorem bswap32_eq (x : BitVec 32) : bswap32 x = byteRev32 x := rfl

/-- The block loaded, `r12` at the first subkeys, and the count of groups. -/
theorem blockStart_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa (.block (load ++ ([.mov .r12 (.reg .rdi)] : List Instr) ++ groups)) s fun u =>
      RInv s k (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx))) u ∧
      u.gpr .r12 = u.gpr .rdi ∧ u.gpr .r13 = BitVec.ofNat 64 (n / 4 + 1) ∧
      u.zf = some (decide (n = 16)) := by
  have hd0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 4 := by
    obtain ⟨g, hg, hc⟩ := h.data
    exact CallLay.inRegions_sub (off := 0) (l := 4) ⟨g, List.mem_append_right _ hg, hc⟩ (by omega_arith)
      (by decide) |>.imp fun _ ⟨a, b⟩ => ⟨a, by rwa [BitVec.add_zero] at b⟩
  have hd4 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := h.data
    exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega_arith) (by decide)
  unfold load groups
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, hd0, hd4, h.rsi, execShift, List.cons_append, List.nil_append,
    sx_ofNat (show 16 < 2 ^ 31 by decide)]
  have hdec := decodeBlock_blockAt s.mem (s.gpr .rdx)
  refine ⟨⟨?_, ?_, h.ctx.transfer ?_ ?_ rfl rfl rfl (Frame.refl _ _), fun q hq h13 => ?_, rfl, rfl, rfl,
    Frame.refl _ _⟩, ?_, ?_⟩
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false, hdec, bswap32_eq]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false, hdec, bswap32_eq]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_false]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_false]
  · have h1 : q ≠ .r12 := fun e => hq (by rw [e]; decide)
    have h2 : q ≠ .rbp := fun e => hq (by rw [e]; decide)
    have h3 : q ≠ .rbx := fun e => hq (by rw [e]; decide)
    simp only [gpr_setFlags, gpr_setReg, h13, h1, h2, h3, ite_false]
  · rcases h.nv with rfl | rfl <;> decide
  · rcases h.nv with rfl | rfl <;> decide

/-- `(Rₙ, Lₙ)` stored, then on to the next block. -/
theorem store_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (hd : InRegions u.wr (u.gpr .rdx) 8) :
    WP isa (.block store) u fun v =>
      v.mem = (u.mem.writeW (u.gpr .rdx) (byteRev32 lr.2)).writeW (u.gpr .rdx + BitVec.ofNat 64 4)
        (byteRev32 lr.1) ∧
      v.gpr .rdx = u.gpr .rdx + 8 ∧ v.gpr .rcx = u.gpr .rcx - 1 ∧ v.zf = some (u.gpr .rcx - 1 == 0) ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms ∧
      (∀ q, q ≠ .rbx → q ≠ .rbp → q ≠ .rdx → q ≠ .rcx → v.gpr q = u.gpr q) := by
  have hd0 : InRegions u.wr (u.gpr .rdx) 4 := by
    obtain ⟨g, hg, hc⟩ := hd
    exact ⟨g, hg, by unfold Region.Contains at hc ⊢; omega_arith⟩
  have hd4 : InRegions u.wr (u.gpr .rdx + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := hd
    exact ⟨g, hg, CallLay.contains_trans hc (by omega_arith) (by decide)⟩
  have hbx := h.bx
  have hbp := h.bp
  unfold store
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, hd0, hd4, hbx, hbp, setWidth_setWidth_32, bswap32_eq,
    sx_ofNat (show 8 < 2 ^ 31 by decide), sx_ofNat (show 1 < 2 ^ 31 by decide)]
  refine ⟨rfl, rfl, rfl, rfl, fun q h1 h2 h3 h4 => ?_⟩
  simp only [h1, h2, h3, h4, ite_false]

/-- `cmp rsi, 16`. -/
theorem cmp16_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) {n : Nat} (hn : n = 12 ∨ n = 16) (hsi : u.gpr .rsi = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .rsi (imm 16)]) u fun v => RInv s k lr v ∧ v.gpr = u.gpr ∧
      v.zf = some (decide (n = 16)) := by
  xrun [imm, hsi, sx_ofNat (show 16 < 2 ^ 31 by decide)]
  exact ⟨h.setFlags _ _ _ _, by rcases hn with rfl | rfl <;> decide⟩

/-- What a block function does. -/
def BPost (s : State) (out : Spec.Cast5.Block) (v : State) : Prop :=
  Spec.Cast5.blockAt v.mem (s.gpr .rdx) = out ∧
  Frame [⟨s.gpr .rdx, 8⟩, ⟨s.gpr .r8, 16⟩] s.mem v.mem ∧
  v.gpr .rdx = s.gpr .rdx + 8 ∧ v.gpr .rcx = s.gpr .rcx - 1 ∧ v.zf = some (s.gpr .rcx - 1 == 0) ∧
  v.rd = s.rd ∧ v.wr = s.wr ∧ v.syms = s.syms ∧
  (∀ q, q ∉ roundRegs → q ≠ .r13 → q ≠ .rdx → q ≠ .rcx → v.gpr q = s.gpr q)

/-- The store at the end of a block, from the halves `lr` after its rounds. -/
theorem finish_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (hd : InRegions s.wr (s.gpr .rdx) 8) :
    WP isa (.block store) u (BPost s (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have hdx : u.gpr .rdx = s.gpr .rdx := h.same .rdx (by decide) (by decide)
  have hcx : u.gpr .rcx = s.gpr .rcx := h.same .rcx (by decide) (by decide)
  have h8 : u.gpr .r8 = s.gpr .r8 := h.same .r8 (by decide) (by decide)
  refine WP.mono (store_ok h (by rw [h.wr, hdx]; exact hd)) fun v ⟨vm, vdx, vcx, vz, vrd, vwr, vsy, vg⟩ => ?_
  refine ⟨?_, ?_, by rw [vdx, hdx], by rw [vcx, hcx], by rw [vz, hcx], vrd.trans h.rd, vwr.trans h.wr,
    vsy.trans h.syms, fun q hq h13 hdq hcq => ?_⟩
  · rw [vm, hdx, blockAt_write]
  · rw [vm, hdx]
    have c0 : Region.Contains ⟨s.gpr .rdx, 8⟩ (s.gpr .rdx) (32 / 8) := by
      simp [Region.Contains]
    refine (Frame.writeW (Frame.writeW (h.frame.mono fun r hr => ?_) List.mem_cons_self _ c0)
      List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact .inr hr
  · rw [vg q (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide)) hdq hcq]
    exact h.same q hq h13

theorem encryptBlock_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa encryptBlock s
      (BPost s (Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))) := by
  set_option linter.unusedVariables false in
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 ∧ 3 * (n / 4) ≤ 12 := by rcases h.nv with rfl | rfl <;> decide
  unfold encryptBlock
  refine WP.seq (WP.mono (blockStart_ok h) fun u ⟨hu, u12, u13, _⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (cnt := .r13) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g v => RInv s k (encFold k (3 * g) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))) v ∧
      v.gpr .r12 = v.gpr .rdi + BitVec.ofNat 64 (12 * g))
    (fun g hg v ⟨hv, h12⟩ _ => WP.mono (groupEnc_ok (by omega_arith) hv h12) fun w ⟨hw, w12, w13, wz⟩ =>
      ⟨⟨hw, w12⟩, w13, wz⟩)
    (fun _ h => h) ⟨hu, by rw [u12, Nat.mul_zero, BitVec.add_zero]⟩ u13) fun v ⟨hv, v12⟩ => ?_)
  have hsi : v.gpr .rsi = BitVec.ofNat 64 n := (hv.same .rsi (by decide) (by decide)).trans h.rsi
  refine WP.seq (WP.mono (cmp16_ok hv h.nv hsi) fun w ⟨hw, wg, wz⟩ => ?_)
  have w12 : w.gpr .r12 = w.gpr .rdi + BitVec.ofNat 64 (12 * (n / 4 + 1)) := by rw [wg]; exact v12
  refine WP.seq (WP.ite (decide (n = 16)) wz (fun h16 => ?_) (fun h16 => ?_))
  · have hn : n = 16 := of_decide_eq_true h16
    have w12' : w.gpr .r12 = w.gpr .rdi + BitVec.ofNat 64 (4 * (16 - 1)) := by
      rw [w12, hn]
    refine WP.mono (round_step hw (t := 1) (i := 16) (by decide) (by decide) (by decide) w12' true)
      fun x ⟨hx, _, _⟩ => ?_
    have e : Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)) =
        Spec.Cast5.encodeBlock
          ((Spec.Cast5.round k 16 (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock
            (Spec.Cast5.blockAt s.mem (s.gpr .rdx))))).2,
          (Spec.Cast5.round k 16 (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock
            (Spec.Cast5.blockAt s.mem (s.gpr .rdx))))).1) := by
      rw [encryptBlock_eq, hn, show 3 * (16 / 4 + 1) = 15 from rfl, show 16 = 15 + 1 from rfl,
        encFold_succ]
    rw [e]
    exact finish_ok hx h.data
  · have hn : n = 12 := by
      rcases h.nv with h' | h'
      · exact h'
      · exact absurd h' (of_decide_eq_false h16)
    have e : Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)) =
        Spec.Cast5.encodeBlock
          ((encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))).2,
          (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))).1) := by
      rw [encryptBlock_eq, hn]
    rw [e]
    exact WP.block_nil (finish_ok hw h.data)

/-- The block loaded, `r12` at the last round's subkeys, and the count of groups. -/
theorem decStart_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa (.block (load ++ ([.mov .r12 (.reg .rsi), .shift .shl .r12 2, .alu .add .r12 (.reg .rdi),
        .alu .sub .r12 (imm 4)] : List Instr) ++ groups)) s fun u =>
      RInv s k (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx))) u ∧
      u.gpr .r12 = u.gpr .rdi + BitVec.ofNat 64 (4 * (n - 1)) ∧ u.gpr .r13 = BitVec.ofNat 64 (n / 4 + 1) ∧
      u.zf = some (decide (n = 16)) := by
  have hd0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 4 := by
    obtain ⟨g, hg, hc⟩ := h.data
    exact CallLay.inRegions_sub (off := 0) (l := 4) ⟨g, List.mem_append_right _ hg, hc⟩ (by omega_arith)
      (by decide) |>.imp fun _ ⟨a, b⟩ => ⟨a, by rwa [BitVec.add_zero] at b⟩
  have hd4 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := h.data
    exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega_arith) (by decide)
  unfold load groups
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, hd0, hd4, h.rsi, execShift, List.cons_append, List.nil_append,
    sx_ofNat (show 16 < 2 ^ 31 by decide), sx_ofNat (show 4 < 2 ^ 31 by decide)]
  have hdec := decodeBlock_blockAt s.mem (s.gpr .rdx)
  refine ⟨⟨?_, ?_, h.ctx.transfer ?_ ?_ rfl rfl rfl (Frame.refl _ _), fun q hq h13 => ?_, rfl, rfl, rfl,
    Frame.refl _ _⟩, ?_, ?_⟩
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false, hdec, bswap32_eq]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false, hdec, bswap32_eq]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_false]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_false]
  · have h1 : q ≠ .r12 := fun e => hq (by rw [e]; decide)
    have h2 : q ≠ .rbp := fun e => hq (by rw [e]; decide)
    have h3 : q ≠ .rbx := fun e => hq (by rw [e]; decide)
    simp only [gpr_setFlags, gpr_setReg, h13, h1, h2, h3, ite_false]
  · rcases h.nv with rfl | rfl <;>
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      omega_arith
  · rcases h.nv with rfl | rfl <;> decide

theorem decFold_zero (k : Spec.Cast5.Schedule) (n : Nat) (lr : Spec.Cast5.Word × Spec.Cast5.Word) :
    decFold k n 0 lr = lr := rfl

theorem decryptBlock_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa decryptBlock s
      (BPost s (Spec.Cast5.decryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))) := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 ∧ n % 3 + 3 * (n / 4 + 1) = n ∧ n % 3 ≤ 1 := by
    rcases h.nv with rfl | rfl <;> decide
  -- The block's halves.
  obtain ⟨lr, hlr⟩ : ∃ lr, Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx)) = lr := ⟨_, rfl⟩
  unfold decryptBlock
  refine WP.seq (WP.mono (decStart_ok h) fun u ⟨hu, u12, u13, uz⟩ => ?_)
  rw [hlr] at hu
  -- Round 16 first, if there are 16.
  have first : WP isa (.ite .e (round 1 false) (.block [])) u fun v =>
      RInv s k (decFold k n (n % 3) lr) v ∧ v.gpr .r12 = v.gpr .rdi + BitVec.ofNat 64 (4 * (n - n % 3 - 1)) ∧
      v.gpr .r13 = BitVec.ofNat 64 (n / 4 + 1) := by
    refine WP.ite (decide (n = 16)) uz (fun h16 => ?_) (fun h16 => ?_)
    · have hn : n = 16 := of_decide_eq_true h16
      refine WP.mono (round_step hu (t := 1) (i := n) (by decide) (by rw [hn]) (by omega_arith)
        (by rw [u12]) false) fun x ⟨hx, x12, x13⟩ => ?_
      have hdi : x.gpr .rdi = u.gpr .rdi :=
        (hx.same .rdi (by decide) (by decide)).trans (hu.same .rdi (by decide) (by decide)).symm
      have hd : decFold k n (n % 3) lr = Spec.Cast5.round k n lr := by
        rw [hn, show 16 % 3 = 0 + 1 from rfl, decFold_succ, decFold_zero, Nat.sub_zero]
      refine ⟨(by rw [hd]; exact hx), ?_, x13.trans u13⟩
      rw [x12, ite_eq_right Bool.false_ne_true, u12, hdi, hn, four, Offset.add_ofNat_sub _ (by decide)]
    · have hn : n = 12 := by
        rcases h.nv with h' | h'
        · exact h'
        · exact absurd h' (of_decide_eq_false h16)
      have hd : decFold k n (n % 3) lr = lr := by rw [hn, show 12 % 3 = 0 from rfl, decFold_zero]
      refine WP.block_nil ⟨(by rw [hd]; exact hu), ?_, u13⟩
      rw [u12, hn]
  refine WP.seq (WP.mono first fun v ⟨hv, v12, v13⟩ => ?_)
  -- Then the groups of three.
  refine WP.seq (WP.mono (wp_countdown (cnt := .r13) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g w => RInv s k (decFold k n (n % 3 + 3 * g) lr) w ∧
      (n % 3 + 3 * g < n → w.gpr .r12 = w.gpr .rdi + BitVec.ofNat 64 (4 * (n - (n % 3 + 3 * g) - 1))))
    (fun g hg w ⟨hw, w12⟩ _ => WP.mono (groupDec_ok (m := n % 3 + 3 * g) (by omega_arith) (by
        rcases h.nv with rfl | rfl <;> decide) (by omega_arith) hw (w12 (by omega_arith)))
      fun x ⟨hx, x12, x13, xz⟩ =>
        ⟨⟨(show n % 3 + 3 * (g + 1) = n % 3 + 3 * g + 3 by omega_arith) ▸ hx, fun hlt => ?_⟩, x13, xz⟩)
    (fun _ h => h) ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hv, fun _ => by rw [Nat.mul_zero, Nat.add_zero]; exact v12⟩
    v13) fun w ⟨hw, _⟩ => ?_)
  · have hdi : x.gpr .rdi = w.gpr .rdi :=
      (hx.same .rdi (by decide) (by decide)).trans (hw.same .rdi (by decide) (by decide)).symm
    rw [x12, w12 (by omega_arith), hdi, show (12 : Addr) = BitVec.ofNat 64 12 from rfl,
      Offset.add_ofNat_sub _ (by omega_arith)]
    congr 2
    omega_arith
  · rw [hG.2.2.1] at hw
    have e : Spec.Cast5.decryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)) =
        Spec.Cast5.encodeBlock ((decFold k n n lr).2, (decFold k n n lr).1) := by
      rw [decryptBlock_eq, hlr]
    rw [e]
    exact finish_ok hw h.data

end VG.Proof.Cast5.X86_64
