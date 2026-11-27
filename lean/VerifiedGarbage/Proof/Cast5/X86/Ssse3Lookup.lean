module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.ByteLookup
public import VerifiedGarbage.Proof.Cast5.X86.Ecb
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Taint

-- separate module: the table's check against the S-boxes, which the functions' contracts do not re-check

/-!
# CAST5's look-ups by `pshufb` on x86 (32-bit): what the function computes

`vg_cast5_lookup_ssse3` (`Impl/Cast5/X86/Ssse3.lean`), an instruction at a
time on the XMM registers, as Blowfish's block function
(`Proof/Blowfish/X86/Ssse3Core.lean`), with the planes' rows read from the
static table:

* `row_wp`, `scan_wp`: a row of an S-box's four planes through the row's
  index vector, and the sixteen rows, ORed, in `xmm4` to `xmm7`
  (`ByteLookup.acc`); `indexes_wp`: the sixteen index vectors, to the
  working space;
* the table (`cst_C`, `cst_T`, `cst_M`, `cst_S`, and `cst_plane`: byte `c` of
  row `r` of plane `p` of S-box `j` is byte `p` of the specification's
  S-box's entry `16 r + c`), which the kernel evaluates on the table's
  literal;
* `entry_eq`, `sbox_wp`: an S-box's entries at the four indices' low bytes;
  `assemble_wp`: the four values a round uses, one of each S-box;
* `lookup_wp`, `call_wp`: the function and its call; `lookupLk`,
  `lookupLk_ok`: the call as the rounds' look-ups (`LkOk` of
  `Proof/Cast5/X86/Ecb.lean`), with eight bytes of stack, the working space's
  bytes 272 to 591, and no table in memory.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Ssse3

open VG VG.X86 VG.X86.ByteLookup
open VG.Impl.Cast5.X86 (at_ imm)
open VG.Impl.Cast5.X86.Ssse3

/-! ## States, an instruction at a time -/

/-- `s` with the memory `m` and the XMM registers `f`. -/
abbrev S (s : State) (m : Mem) (f : XReg → BitVec 128) : State := { s with mem := m, xmm := f }

/-- The XMM registers `f` with `d` set to `v`. -/
def upd (f : XReg → BitVec 128) (d : XReg) (v : BitVec 128) : XReg → BitVec 128 :=
  fun r => if r = d then v else f r

theorem upd_self (f : XReg → BitVec 128) (d : XReg) (v : BitVec 128) : upd f d v d = v := by
  simp only [upd, ↓reduceIte]

theorem upd_ne (f : XReg → BitVec 128) {d r : XReg} (v : BitVec 128) (h : r ≠ d) : upd f d v r = f r := by
  simp only [upd, h, ↓reduceIte]

/-- The sixteen bytes at the byte offset `off` of the table. -/
def cst (off : Nat) : BitVec 128 := table.getD (off / 8 + 1) 0 ++ table.getD (off / 8) 0

/-- Byte `d` of the working space at `B`. -/
abbrev slot (B : BitVec 32) (d : Nat) : Addr := B.setWidth 64 + BitVec.ofNat 64 d

variable {s : State} {m : Mem}

/-- An instruction that writes an XMM register. -/
theorem wp_xs {f : XReg → BitVec 128} {i : Instr} {is : List Instr} {Q : State → Prop} {d : XReg} {v : BitVec 128}
    (h : exec i (S s m f) = some (State.setXmm (S s m f) d v)) (k : WP isa (.block is) (S s m (upd f d v)) Q) :
    WP isa (.block (i :: is)) (S s m f) Q := Wp.cons h k

/-- An instruction of two XMM registers. -/
theorem wp_bin {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {op : XBinOp} {a b : XReg}
    (k : WP isa (.block is) (S s m (upd f a (op.eval (f a) (f b)))) Q) :
    WP isa (.block (x op a b :: is)) (S s m f) Q := Wp.cons rfl k

theorem table_length : table.length = 1072 := by lit_decide

/-- Sixteen bytes of the table. -/
theorem wp_tb {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {off : Nat}
    (hb : s.gpr tbr = s.syms tableName) (ho : off % 8 = 0 ∧ off / 8 + 2 ≤ 1072)
    (k : WP isa (.block is) (S s m (upd f d (cst off))) Q) : WP isa (.block (tb d off :: is)) (S s m f) Q :=
  Wp.cons (show (if s.gpr tbr = s.syms tableName ∧ off % 8 = 0 ∧ off / 8 + 2 ≤ table.length then some _ else none) = _ by
    rw [ite_eq_left (show _ ∧ _ ∧ _ from ⟨hb, ho.1, by rw [table_length]; exact ho.2⟩)]; rfl) k

/-- A 16-byte load. -/
theorem wp_ld {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {mo : MemOp} {a : Addr}
    (ha : s.ea mo = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : WP isa (.block is) (S s m (upd f d (m.readW a 128))) Q) :
    WP isa (.block (.movdquLoad d mo :: is)) (S s m f) Q :=
  Wp.cons (show (State.load128 (S s m f) (s.ea mo)).map _ = _ by
    rw [ha, State.load128, ite_eq_left hin]; rfl) k

/-- A 16-byte store. -/
theorem wp_st {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {r : XReg} {mo : MemOp} {a : Addr}
    (ha : s.ea mo = a) (hin : InRegions s.wr a 16) (k : WP isa (.block is) (S s (m.writeW a (f r)) f) Q) :
    WP isa (.block (.movdquStore mo r :: is)) (S s m f) Q :=
  Wp.cons (show State.store128 (S s m f) (s.ea mo) (f r) = _ by
    rw [ha, State.store128, ite_eq_left hin]) k

/-- The address at an offset from a register. -/
theorem ea_at {b : Reg} {B : BitVec 32} {o : Nat} (hB : s.gpr b = B) (h : B.toNat + o < 2 ^ 32) :
    s.ea (at_ b o) = slot B o := by
  show addr (s.gpr b) o = _
  rw [hB]; exact addr_eq h

/-! ## The registers' rotation -/

theorem xr_mod (k : Nat) : xr (k % 8) = xr k := by simp only [xr, Nat.mod_mod]

theorem xr_ne {a b : Nat} (h : a % 8 ≠ b % 8) : xr a ≠ xr b := fun e => by
  have inj : ∀ a < 8, ∀ b < 8, xr a = xr b → a = b := by decide
  exact h (inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) (by rw [xr_mod, xr_mod]; exact e))

theorem xr_congr {a b : Nat} (h : a % 8 = b % 8) : xr a = xr b := by rw [← xr_mod a, ← xr_mod b, h]

/-! ## A row of an S-box -/

/-- Row `r` of plane `p` of S-box `j`, in the table. -/
abbrev rowC (j p r : Nat) : BitVec 128 := cst (planeOff j p + 16 * r)

/-- The index vector of row `r`, in `m`, with the working space at `W`. -/
abbrev vAt (m : Mem) (W : BitVec 32) (r : Nat) : BitVec 128 := m.readW (slot W (vOff r)) 128

/-- Where the look-ups run: the working space at `W`, of which the bytes
272 to 591 are writable, in `esi`; the table's address in `edx`. -/
structure Env (W : BitVec 32) (s : State) : Prop where
  esi : s.gpr .esi = W
  edx : s.gpr tbr = s.syms tableName
  fW : W.toNat + 592 ≤ 2 ^ 32
  wrW : ∀ o n, 272 ≤ o → o + n ≤ 592 → InRegions s.wr (slot W o) n

theorem Env.rdW {W : BitVec 32} (E : Env W s) {o n : Nat} (h : 272 ≤ o) (h' : o + n ≤ 592) :
    InRegions (s.rd ++ s.wr) (slot W o) n := by
  obtain ⟨r, hr, hc⟩ := E.wrW o n h h'
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A row of a plane: the row through the row's index vector, ORed with the
rows before it but for row 0. -/
theorem plane_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {j r p : Nat}
    (hb : s.gpr tbr = s.syms tableName) (hj : j < 8) (hr : r < 16) (hp : p < 4)
    (k : ∀ g, g (xr (5 * r + 1 + p)) =
        (if r = 0 then XBinOp.eval .pshufb (rowC j p r) (f (xr (5 * r)))
         else XBinOp.eval .por (XBinOp.eval .pshufb (rowC j p r) (f (xr (5 * r)))) (f (xr (5 * r + 4 + p)))) →
      (∀ q, q ≠ xr (5 * r + 1 + p) → g q = f q) → WP isa (.block is) (S s m g) Q) :
    WP isa (.block (plane j r p ++ is)) (S s m f) Q := by
  have hv : xr (5 * r) ≠ xr (5 * r + 1 + p) := xr_ne (by omega)
  have hA : xr (5 * r + 4 + p) ≠ xr (5 * r + 1 + p) := xr_ne (by omega)
  have ho : (planeOff j p + 16 * r) % 8 = 0 ∧ (planeOff j p + 16 * r) / 8 + 2 ≤ 1072 := by
    simp only [planeOff]; omega
  by_cases h0 : r = 0
  · rw [show plane j r p = [tb (xr (5 * r + 1 + p)) (planeOff j p + 16 * r),
        x .pshufb (xr (5 * r + 1 + p)) (xr (5 * r))] by simp only [plane, ite_eq_left h0]; rfl]
    refine wp_tb hb ho (wp_bin (k _ ?_ fun q hq => ?_))
    · simp only [upd_self, upd_ne _ _ hv, ite_eq_left h0]
    · rw [upd_ne _ _ hq, upd_ne _ _ hq]
  · rw [show plane j r p = [tb (xr (5 * r + 1 + p)) (planeOff j p + 16 * r),
        x .pshufb (xr (5 * r + 1 + p)) (xr (5 * r)), x .por (xr (5 * r + 1 + p)) (xr (5 * r + 4 + p))] by
      simp only [plane, ite_eq_right h0]; rfl]
    refine wp_tb hb ho (wp_bin (wp_bin (k _ ?_ fun q hq => ?_)))
    · simp only [upd_self, upd_ne _ _ hv, upd_ne _ _ hA, ite_eq_right h0]
    · rw [upd_ne _ _ hq, upd_ne _ _ hq, upd_ne _ _ hq]

/-- A row of the four planes of S-box `j`. -/
theorem row_wp {W : BitVec 32} (E : Env W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {j r : Nat} (hj : j < 8) (hr : r < 16)
    (k : ∀ g, (∀ p < 4, g (xr (5 * r + 1 + p)) =
        (if r = 0 then XBinOp.eval .pshufb (rowC j p r) (vAt m W r)
         else XBinOp.eval .por (XBinOp.eval .pshufb (rowC j p r) (vAt m W r)) (f (xr (5 * r + 4 + p)))) ) →
      WP isa (.block is) (S s m g) Q) :
    WP isa (.block (row j r ++ is)) (S s m f) Q := by
  have hW : s.ea (at_ .esi (vOff r)) = slot W (vOff r) := ea_at E.esi (by have := E.fW; simp only [vOff]; omega)
  have ne : ∀ a b : Nat, a % 8 ≠ b % 8 → xr a ≠ xr b := fun _ _ => xr_ne
  rw [show row j r ++ is = ld (xr (5 * r)) .esi (vOff r) ::
      (plane j r 0 ++ (plane j r 1 ++ (plane j r 2 ++ (plane j r 3 ++ is)))) by
    simp only [row, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_ld hW (E.rdW (by simp only [vOff]; omega) (by simp only [vOff]; omega))
    (plane_wp E.edx hj hr (by decide) fun g0 h0 o0 =>
    plane_wp E.edx hj hr (by decide) fun g1 h1 o1 =>
    plane_wp E.edx hj hr (by decide) fun g2 h2 o2 =>
    plane_wp E.edx hj hr (by decide) fun g3 h3 o3 => k g3 fun p hp => ?_)
  -- the row's index vector and the planes' rows so far, through the writes of this row
  have v0 : upd f (xr (5 * r)) (vAt m W r) (xr (5 * r)) = vAt m W r := upd_self _ _ _
  have a0 : ∀ q, q < 4 → upd f (xr (5 * r)) (vAt m W r) (xr (5 * r + 4 + q)) = f (xr (5 * r + 4 + q)) :=
    fun q hq => upd_ne _ _ (ne _ _ (by omega))
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl
  · rw [o3 _ (ne _ _ (by omega)), o2 _ (ne _ _ (by omega)), o1 _ (ne _ _ (by omega)), h0, v0, a0 0 (by decide)]
  · rw [o3 _ (ne _ _ (by omega)), o2 _ (ne _ _ (by omega)), h1, o0 _ (ne _ _ (by omega)), v0,
      o0 _ (ne _ _ (by omega)), a0 1 (by decide)]
  · rw [o3 _ (ne _ _ (by omega)), h2, o1 _ (ne _ _ (by omega)), o0 _ (ne _ _ (by omega)), v0,
      o1 _ (ne _ _ (by omega)), o0 _ (ne _ _ (by omega)), a0 2 (by decide)]
  · rw [h3, o2 _ (ne _ _ (by omega)), o1 _ (ne _ _ (by omega)), o0 _ (ne _ _ (by omega)), v0,
      o2 _ (ne _ _ (by omega)), o1 _ (ne _ _ (by omega)), o0 _ (ne _ _ (by omega)), a0 3 (by decide)]

/-- The rows `r` to `r + n - 1` of S-box `j`, after the rows before `r`. -/
theorem rows_wp {W : BitVec 32} (E : Env W s) {is : List Instr} {Q : State → Prop} {j : Nat} (hj : j < 8)
    (n : Nat) : ∀ (r : Nat) (f : XReg → BitVec 128), 0 < r → r + n ≤ 16 →
      (∀ p < 4, f (xr (5 * r + 4 + p)) = ByteLookup.acc (rowC j p) (vAt m W) (r - 1)) →
      (∀ g, (∀ p < 4, g (xr (5 * (r + n) + 4 + p)) = ByteLookup.acc (rowC j p) (vAt m W) (r + n - 1)) →
        WP isa (.block is) (S s m g) Q) →
      WP isa (.block ((List.range' r n).flatMap (row j) ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun r f _ _ hf k => k f hf
  | succ n ih =>
    intro r f hr hn hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine row_wp E hj (by omega) fun g hg =>
      ih (r + 1) g (by omega) (by omega) (fun p hp => ?_) fun g' hg' => k g' fun p hp => ?_
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [xr_congr (show (5 * (r' + 1 + 1) + 4 + p) % 8 = (5 * (r' + 1) + 1 + p) % 8 by omega), hg p hp,
        ite_eq_right (Nat.succ_ne_zero r'), hf p hp, Nat.add_sub_cancel, Nat.add_sub_cancel]
      rfl
    · have e := hg' p hp
      rw [show r + 1 + n = r + (n + 1) by omega] at e
      exact e

/-- **The sixteen rows of S-box `j`**: its four planes' rows through their
index vectors, ORed, in `xmm4` to `xmm7`. -/
theorem scan_wp {W : BitVec 32} (E : Env W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {j : Nat} (hj : j < 8)
    (k : ∀ g, (∀ p < 4, g (xr (4 + p)) = ByteLookup.acc (rowC j p) (vAt m W) 15) → WP isa (.block is) (S s m g) Q) :
    WP isa (.block (scan j ++ is)) (S s m f) Q := by
  rw [show scan j ++ is = row j 0 ++ ((List.range' 1 15).flatMap (row j) ++ is) by
    rw [scan, show List.range 16 = 0 :: List.range' 1 15 from rfl, List.flatMap_cons, List.append_assoc]]
  refine row_wp E hj (by decide) fun g hg =>
    rows_wp E hj 15 1 g (by decide) (by decide) (fun p hp => ?_) fun g' hg' => k g' fun p hp => ?_
  · have e := hg p hp
    rw [ite_eq_left rfl] at e
    rw [xr_congr (show (5 * 1 + 4 + p) % 8 = (5 * 0 + 1 + p) % 8 by omega), e]
    rfl
  · rw [xr_congr (show (4 + p) % 8 = (5 * (1 + 15) + 4 + p) % 8 by omega), hg' p hp]

/-! ## The index vectors -/

/-- The working space's bytes that the look-ups write. -/
abbrev wR (W : BitVec 32) : Region := ⟨slot W 272, 320⟩

/-- The index vectors' bytes. -/
abbrev vR (W : BitVec 32) : Region := ⟨slot W 272, 256⟩

theorem vR_sub (W : BitVec 32) : Region.Sub (vR W) (wR W) := Region.sub_prefix (by decide)

theorem readW_self128 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 128 = v :=
  Mem.readW_writeW_self m a 16 v (by decide)

/-- The index vector of row `r`, to the working space. -/
theorem index_wp {W : BitVec 32} (E : Env W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {r : Nat} (hr : r < 16)
    (k : ∀ g, g .xmm0 = f .xmm0 → g .xmm1 = f .xmm1 →
      WP isa (.block is) (S s (m.writeW (slot W (vOff r)) (ByteLookup.idx (cst (oC r)) (f .xmm1) (f .xmm0))) g) Q) :
    WP isa (.block (index r ++ is)) (S s m f) Q := by
  have h0 : (.xmm0 : XReg) ≠ xr (2 + r % 6) := by
    rw [show (.xmm0 : XReg) = xr 0 from rfl]; exact xr_ne (by omega)
  have h1 : (.xmm1 : XReg) ≠ xr (2 + r % 6) := by
    rw [show (.xmm1 : XReg) = xr 1 from rfl]; exact xr_ne (by omega)
  have fW := E.fW
  show WP isa (.block (tb (xr (2 + r % 6)) (oC r) :: x .pshufb (xr (2 + r % 6)) .xmm1 ::
    x .por (xr (2 + r % 6)) .xmm0 :: stx .esi (vOff r) (xr (2 + r % 6)) :: is)) _ _
  refine wp_tb E.edx (by simp only [oC]; omega)
    (wp_bin (wp_bin (wp_st (ea_at E.esi (by simp only [vOff]; omega))
      (E.wrW _ _ (by simp only [vOff]; omega) (by simp only [vOff]; omega)) ?_)))
  simp only [upd_self, upd_ne _ _ h0, upd_ne _ _ h1]
  exact k _ (by rw [upd_ne _ _ h0, upd_ne _ _ h0, upd_ne _ _ h0]) (by rw [upd_ne _ _ h1, upd_ne _ _ h1, upd_ne _ _ h1])

/-- The index vectors of the rows `r` to `r + n - 1`, after those of the
rows before `r`: all of them in the working space, the memory outside it
kept. -/
theorem indexes_wp {W : BitVec 32} (E : Env W s) {is : List Instr} {Q : State → Prop} {H L : BitVec 128}
    {m₀ : Mem} (n : Nat) : ∀ (r : Nat) (m : Mem) (f : XReg → BitVec 128), r + n ≤ 16 → f .xmm0 = L → f .xmm1 = H →
      (∀ r' < r, vAt m W r' = ByteLookup.idx (cst (oC r')) H L) → Frame [vR W] m₀ m →
      (∀ m' g, (∀ r' < r + n, vAt m' W r' = ByteLookup.idx (cst (oC r')) H L) → Frame [vR W] m₀ m' →
        WP isa (.block is) (S s m' g) Q) →
      WP isa (.block ((List.range' r n).flatMap index ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun r m f _ _ _ hm hf k => k m f hm hf
  | succ n ih =>
    intro r m f hn hL hH hm hf k
    have fW := E.fW
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine index_wp E (by omega) fun g g0 g1 =>
      ih (r + 1) _ g (by omega) (g0.trans hL) (g1.trans hH) (fun r' hr' => ?_)
        (hf.writeW List.mem_cons_self _ (Offset.contains _ (by simp only [vOff]; omega)
          (by simp only [vOff]; omega) (by decide)))
        fun m' g' hm' hf' => k m' g' (fun r' hr' => hm' r' (by omega)) hf'
    rw [hL, hH]
    by_cases e : r' = r
    · rw [e]; exact readW_self128 _ _ _
    · exact (Mem.readW_writeW_sep (Offset.sep _ (by simp only [vOff]; omega) (by simp only [vOff]; omega)
        (by simp only [vOff]; omega)) (by decide)).trans (hm r' (by omega))

/-! ## The table -/

open VG.X86.ByteMap (byte_eq_dword byte_pshufb)
open VG.X86.Lanes (L dword_L L_ext)
open VG.Proof.Cast5 (tableEnt)

theorem cst_C : ∀ r < 16, ∀ b < 16, byte (cst (oC r)) b = if b = r then 0#8 else 0x80#8 := by lit_decide

theorem cst_T : ∀ i < 16, byte (cst oT) i = BitVec.ofNat 8 (4 * (i % 4) + i / 4) := by lit_decide

theorem cst_M : ∀ i < 16, byte (cst oM) i = 0x0f#8 := by lit_decide

theorem cst_S : ∀ i < 16, byte (cst oS) i = BitVec.ofNat 8 (4 * (i % 4)) := by lit_decide

/-- Byte `k` of eight bytes as a little-endian word. -/
theorem byte_le8 (f : Nat → Byte) {k : Nat} (hk : k < 8) : (le8 f).extractLsb' (8 * k) 8 = f k := by
  have hs {w : Nat} (x : BitVec w) (b : BitVec 8) (n : Nat) : (x ++ b).extractLsb' (n + 8) 8 = x.extractLsb' n 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, ite_eq_right (by omega_arith), BitVec.getLsbD_extractLsb',
      show n + 8 + i - 8 = n + i by omega_arith]
  have hz {w : Nat} (x : BitVec w) (b : BitVec 8) : (x ++ b).extractLsb' 0 8 = b := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, ite_eq_left (by omega_arith), decide_eq_true hi,
      Bool.true_and, Nat.zero_add]
  have h0 (b : BitVec 8) : b.extractLsb' 0 8 = b := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, Nat.zero_add]
  unfold le8
  match k, hk with
  | 0, _ => exact hz _ _
  | 1, _ => exact (hs _ _ _).trans (hz _ _)
  | 2, _ => exact (hs _ _ _).trans ((hs _ _ _).trans (hz _ _))
  | 3, _ => exact (hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans (hz _ _)))
  | 4, _ => exact (hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans (hz _ _))))
  | 5, _ => exact (hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans (hz _ _)))))
  | 6, _ =>
    exact (hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans
      ((hs _ _ _).trans (hz _ _))))))
  | 7, _ =>
    exact (hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans ((hs _ _ _).trans
      ((hs _ _ _).trans ((hs _ _ _).trans (h0 _)))))))

theorem planesOf_length (j : Nat) : (planesOf j).length = 128 := by
  rw [planesOf, List.length_map, List.length_range]

theorem planesOf_getD (j : Nat) {w : Nat} (hw : w < 128) :
    (planesOf j).getD w 0 = le8 fun c => planeByte j (w / 32) (8 * (w % 32) + c) := by
  rw [planesOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]; rfl

/-- Word `w` of the planes of S-box `j`, in the table. -/
theorem table_getD {j : Nat} (hj : j < 8) {w : Nat} (hw : w < 128) :
    table.getD (128 * j + 48 * (j / 4) + w) 0 = (planesOf j).getD w 0 := by
  have hc : consts.length = 48 := by decide
  have hg (l : List (BitVec 64)) {a b : Nat} (h : a = b) : l.getD a 0 = l.getD b 0 := h ▸ rfl
  have hp : planes.length = 512 := by simp only [planes, List.length_append, planesOf_length]
  have hl := planesOf_length
  rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega_using [hw]) only [table, planes, keyPlanes, getD_append', List.length_append, hl, hc,
    ↓ite_eq_left, ↓ite_eq_right] <;>
  exact hg _ (by omega_using [hw])

/-- **The planes are the S-boxes'**: byte `c` of row `r` of plane `p` of
S-box `j`, in the table, is byte `p` of the S-box's entry `16 r + c`. -/
theorem cst_plane : ∀ j < 8, ∀ p < 4, ∀ r < 16, ∀ c < 16,
    byte (cst (planeOff j p + 16 * r)) c = planeByte j p (16 * r + c) := by
  intro j hj p hp r hr c hc
  have e₀ : (planeOff j p + 16 * r) / 8 = 128 * j + 48 * (j / 4) + (32 * p + 2 * r) := by
    unfold planeOff; omega_arith
  rw [cst, e₀, Nat.add_assoc _ (32 * p + 2 * r) 1, table_getD hj (w := 32 * p + 2 * r + 1) (by omega_arith),
    table_getD hj (w := 32 * p + 2 * r) (by omega_arith), planesOf_getD j (w := 32 * p + 2 * r + 1) (by omega_arith),
    planesOf_getD j (w := 32 * p + 2 * r) (by omega_arith), ByteMap.byte_append _ _ hc]
  have hq : c % 8 < 8 := Nat.mod_lt _ (by decide)
  by_cases h : c < 8
  · rw [ite_eq_left h, byte_le8 _ hq, show (32 * p + 2 * r) / 32 = p by omega_arith,
      show 8 * ((32 * p + 2 * r) % 32) + c % 8 = 16 * r + c by omega_arith]
  · rw [ite_eq_right h, byte_le8 _ hq, show (32 * p + 2 * r + 1) / 32 = p by omega_arith,
      show 8 * ((32 * p + 2 * r + 1) % 32) + c % 8 = 16 * r + c by omega_arith]

theorem word_ext {x y : BitVec 32} (h : ∀ b < 4, x.extractLsb' (8 * b) 8 = y.extractLsb' (8 * b) 8) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (fun z : BitVec 8 => z.getLsbD (i % 8)) (h (i / 8) (by omega_arith))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega_arith, decide_true, Bool.true_and,
    show 8 * (i / 8) + i % 8 = i by omega_arith] at this
  exact this

/-- The low bytes of the four indices, in every doubleword. -/
abbrev yOf (idx : Nat → BitVec 32) : BitVec 128 := XBinOp.eval .pshufb (L idx) (cst oS)

/-- The high nibbles of the bytes of `Y`. -/
abbrev hiOf (Y : BitVec 128) : BitVec 128 := XBinOp.eval .pand (XShiftOp.eval .psrld Y 4) (cst oM)

/-- The low nibbles of the bytes of `Y`. -/
abbrev loOf (Y : BitVec 128) : BitVec 128 := XBinOp.eval .pand Y (cst oM)

theorem byte_yOf (idx : Nat → BitVec 32) {i : Nat} (hi : i < 16) :
    byte (yOf idx) i = (idx (i % 4)).extractLsb' 0 8 := by
  have e := (by decide : ∀ i < 16, (BitVec.ofNat 8 (4 * (i % 4))).msb = false ∧
    ((BitVec.ofNat 8 (4 * (i % 4))).extractLsb' 0 4).toNat = 4 * (i % 4) + 0) i hi
  rw [yOf, byte_pshufb _ _ hi, cst_S i hi, e.1, e.2, ite_eq_right Bool.false_ne_true, L,
    byte_at _ _ _ _ (Nat.mod_lt _ (by decide)) (by decide)]
  rcases cases4 (Nat.mod_lt i (show 0 < 4 by decide)) with h | h | h | h <;> rw [h] <;> rfl

/-- **A plane's byte.** With the index vectors of the bytes whose nibbles
are `H` and `L` in the working space, byte `i` of the sixteen rows of plane
`p` of S-box `j`, ORed, is byte `p` of the S-box's entry at the byte `x`
that `H` and `L` hold at `i`. -/
theorem acc_entry {m : Mem} {W : BitVec 32} {H L : BitVec 128} {x : BitVec 8} {j p i : Nat} (hj : j < 8)
    (hp : p < 4) (hi : i < 16) (hV : ∀ r < 16, vAt m W r = ByteLookup.idx (cst (oC r)) H L)
    (hH : byte H i = x >>> 4) (hL : byte L i = x &&& 0x0f#8) :
    byte (ByteLookup.acc (rowC j p) (vAt m W) 15) i = (sboxOf j x).extractLsb' (8 * p) 8 := by
  obtain ⟨-, -, -, -, -, h1, h2, h3⟩ := nibbles x
  rw [acc_congr (V' := fun r => ByteLookup.idx (cst (oC r)) H L) 15 (fun r hr => hV r (by omega)),
    byte_acc (x := x) hi cst_C hH hL]
  show byte (cst (planeOff j p + 16 * (x >>> 4).toNat)) (x &&& 0x0f#8).toNat = _
  rw [cst_plane j hj p hp _ h1 _ h2, h3, planeByte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and]

/-- **An S-box's entries.** With the index vectors of the indices `idx` in
the working space, the four planes' rows ORed and gathered hold, in
doubleword `k`, S-box `j`'s entry at the low byte of `idx k`. -/
theorem entry_eq {m : Mem} {W : BitVec 32} {idx : Nat → BitVec 32} {j k : Nat} (hj : j < 4) (hk : k < 4)
    (hV : ∀ r < 16, vAt m W r = ByteLookup.idx (cst (oC r)) (hiOf (yOf idx)) (loOf (yOf idx))) :
    dword (gather (ByteLookup.acc (rowC j 0) (vAt m W) 15) (ByteLookup.acc (rowC j 1) (vAt m W) 15)
      (ByteLookup.acc (rowC j 2) (vAt m W) 15) (ByteLookup.acc (rowC j 3) (vAt m W) 15) (cst oT)) k =
      sboxOf j ((idx k).extractLsb' 0 8) := by
  refine word_ext fun p hp => ?_
  obtain ⟨-, -, -, -, -, h1, h2, h3⟩ := nibbles ((idx k).extractLsb' 0 8)
  rw [byte_of_dword _ _ hp]
  refine (byte_gather (a := fun p => ByteLookup.acc (rowC j p) (vAt m W) 15) cst_T hk hp).trans ?_
  show byte (ByteLookup.acc (rowC j p) (vAt m W) 15) k = _
  rw [acc_congr (V' := fun r => ByteLookup.idx (cst (oC r)) (hiOf (yOf idx)) (loOf (yOf idx))) 15
      (fun r hr => hV r (by omega)),
    byte_acc (x := (idx k).extractLsb' 0 8) (by omega) cst_C
      ((byte_hi (by omega) (cst_M k (by omega))).trans (by rw [byte_yOf idx (by omega), Nat.mod_eq_of_lt hk]))
      ((byte_lo (cst_M k (by omega))).trans (by rw [byte_yOf idx (by omega), Nat.mod_eq_of_lt hk]))]
  show byte (cst (planeOff j p + 16 * ((idx k).extractLsb' 0 8 >>> 4).toNat))
    ((idx k).extractLsb' 0 8 &&& 0x0f#8).toNat = _
  rw [cst_plane j (by omega) p hp _ h1 _ h2, h3, planeByte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and]

/-! ## The function's pieces -/

/-- The head's instructions on the XMM registers. -/
def headX : List Instr :=
  [tb .xmm2 oS, x .pshufb .xmm0 .xmm2, tb .xmm2 oM, x .movdqa .xmm1 .xmm0, .xop (.shift .psrld .xmm1 4),
   x .pand .xmm1 .xmm2, x .pand .xmm0 .xmm2]

/-- The indices' nibbles, in `xmm1` and `xmm0`. -/
theorem headX_wp {W : BitVec 32} (E : Env W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {idx : Nat → BitVec 32} (h0 : f .xmm0 = L idx)
    (k : ∀ g, g .xmm0 = loOf (yOf idx) → g .xmm1 = hiOf (yOf idx) → WP isa (.block is) (S s m g) Q) :
    WP isa (.block (headX ++ is)) (S s m f) Q :=
  wp_tb E.edx (by decide) (wp_bin (wp_tb E.edx (by decide) (wp_bin (wp_xs rfl (wp_bin (wp_bin
    (k _ (by simp only [upd, reduceCtorEq, ↓reduceIte, h0]) (by simp only [upd, reduceCtorEq, ↓reduceIte, h0]; rfl))))))))

/-- **An S-box**: its entries at the four indices, in the working space,
with those of the S-boxes before it. -/
theorem sbox_wp {W : BitVec 32} (E : Env W s) {idx : Nat → BitVec 32} {m₀ : Mem} {f : XReg → BitVec 128}
    {is : List Instr} {Q : State → Prop} {j : Nat} (hj : j < 4)
    (hV : ∀ r < 16, vAt m W r = ByteLookup.idx (cst (oC r)) (hiOf (yOf idx)) (loOf (yOf idx)))
    (hf : Frame [wR W] m₀ m)
    (hF : ∀ j' < j, ∀ k < 4, dword (m.readW (slot W (eOff j')) 128) k = sboxOf j' ((idx k).extractLsb' 0 8))
    (k : ∀ m' g, (∀ r < 16, vAt m' W r = ByteLookup.idx (cst (oC r)) (hiOf (yOf idx)) (loOf (yOf idx))) →
      Frame [wR W] m₀ m' →
      (∀ j' < j + 1, ∀ k < 4, dword (m'.readW (slot W (eOff j')) 128) k = sboxOf j' ((idx k).extractLsb' 0 8)) →
      WP isa (.block is) (S s m' g) Q) :
    WP isa (.block (sbox j ++ is)) (S s m f) Q := by
  have fW := E.fW
  rw [sbox, List.append_assoc]
  refine scan_wp E (by omega) fun g hg => ?_
  have e4 : g .xmm4 = ByteLookup.acc (rowC j 0) (vAt m W) 15 := hg 0 (by decide)
  have e5 : g .xmm5 = ByteLookup.acc (rowC j 1) (vAt m W) 15 := hg 1 (by decide)
  have e6 : g .xmm6 = ByteLookup.acc (rowC j 2) (vAt m W) 15 := hg 2 (by decide)
  have e7 : g .xmm7 = ByteLookup.acc (rowC j 3) (vAt m W) 15 := hg 3 (by decide)
  show WP isa (.block (x .punpckldq .xmm4 .xmm5 :: x .punpckldq .xmm6 .xmm7 :: x .punpcklqdq .xmm4 .xmm6 ::
    tb .xmm0 oT :: x .pshufb .xmm4 .xmm0 :: stx .esi (eOff j) .xmm4 :: is)) _ _
  refine wp_bin (wp_bin (wp_bin (wp_tb E.edx (by decide) (wp_bin (wp_st (ea_at E.esi (by simp only [eOff]; omega))
    (E.wrW _ _ (by simp only [eOff]; omega) (by simp only [eOff]; omega)) ?_)))))
  simp only [upd, reduceCtorEq, ↓reduceIte, e4, e5, e6, e7]
  refine k _ _ (fun r hr => ?_) (hf.writeW List.mem_cons_self _ (Offset.contains _ (by simp only [eOff]; omega)
    (by simp only [eOff]; omega) (by decide))) fun j' hj' k hk => ?_
  · exact (Mem.readW_writeW_sep (Offset.sep _ (by simp only [vOff, eOff]; omega) (by simp only [vOff]; omega)
      (by simp only [eOff]; omega)) (by decide)).trans (hV r hr)
  · by_cases e : j' = j
    · rw [e, readW_self128]
      exact entry_eq hj hk hV
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by simp only [eOff]; omega) (by simp only [eOff]; omega)
        (by simp only [eOff]; omega)) (by decide)]
      exact hF j' (by omega) k hk

/-- The four S-boxes' entries, a lane of each. -/
theorem asm_eq (e0 e1 e2 e3 : BitVec 128) :
    XBinOp.eval .punpcklqdq (shufDwords (XBinOp.eval .punpckldq e3 e2) 0x0c)
      (shufDwords (XBinOp.eval .punpckhdq e1 e0) 0x0c) =
      ofDwords (dword e3 0) (dword e2 1) (dword e1 2) (dword e0 3) := by
  rw [punpcklqdq_eq, punpckldq_eq, punpckhdq_eq]
  refine ext_dword ?_ ?_ ?_ ?_
  · rw [dword_ofDwords_0, dword_ofDwords_0, dword_shufDwords _ _ (by decide)]; exact dword_ofDwords_0 _ _ _ _
  · rw [dword_ofDwords_1, dword_ofDwords_1, dword_shufDwords _ _ (by decide)]; exact dword_ofDwords_3 _ _ _ _
  · rw [dword_ofDwords_2, dword_ofDwords_2, dword_shufDwords _ _ (by decide)]; exact dword_ofDwords_0 _ _ _ _
  · rw [dword_ofDwords_3, dword_ofDwords_3, dword_shufDwords _ _ (by decide)]; exact dword_ofDwords_3 _ _ _ _

/-- **The four values**: `S4`'s at the first index, `S3`'s at the second,
`S2`'s at the third and `S1`'s at the fourth, in the lanes of `xmm1`. -/
theorem assemble_wp {W : BitVec 32} (E : Env W s) {idx : Nat → BitVec 32} {f : XReg → BitVec 128}
    {Q : State → Prop}
    (hF : ∀ j < 4, ∀ k < 4, dword (m.readW (slot W (eOff j)) 128) k = sboxOf j ((idx k).extractLsb' 0 8))
    (k : ∀ g, g .xmm1 = L (fun k => tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1 (idx k).toNat k) →
      Q (S s m g)) :
    WP isa (.block assemble) (S s m f) Q := by
  have fW := E.fW
  have ea : ∀ j < 4, s.ea (at_ .esi (eOff j)) = slot W (eOff j) := fun j hj =>
    ea_at E.esi (by simp only [eOff]; omega)
  have rd : ∀ j < 4, InRegions (s.rd ++ s.wr) (slot W (eOff j)) 16 := fun j hj =>
    E.rdW (by simp only [eOff]; omega) (by simp only [eOff]; omega)
  have lo8 : ∀ v : BitVec 32, BitVec.ofNat 8 v.toNat = v.extractLsb' 0 8 := fun v => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  refine wp_ld (ea 3 (by decide)) (rd 3 (by decide)) (wp_ld (ea 2 (by decide)) (rd 2 (by decide)) (wp_bin
    (wp_xs rfl (wp_ld (ea 1 (by decide)) (rd 1 (by decide)) (wp_ld (ea 0 (by decide)) (rd 0 (by decide))
      (wp_bin (wp_xs rfl (wp_bin (WP.block_nil (k _ ?_))))))))))
  simp only [upd, reduceCtorEq, ↓reduceIte]
  rw [asm_eq]
  refine L_ext fun k hk => ?_
  rcases cases4 hk with rfl | rfl | rfl | rfl
  · rw [dword_ofDwords_0, hF 3 (by decide) 0 (by decide), ← lo8]; rfl
  · rw [dword_ofDwords_1, hF 2 (by decide) 1 (by decide), ← lo8]; rfl
  · rw [dword_ofDwords_2, hF 1 (by decide) 2 (by decide), ← lo8]; rfl
  · rw [dword_ofDwords_3, hF 0 (by decide) 3 (by decide), ← lo8]; rfl

/-! ## The function -/

open VG.X86.Wp VG.X86.RegUpd

theorem lookup_eq : lookup = .seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.block (.mov tbr (.reg .eax) :: (headX ++ ((List.range' 0 16).flatMap index ++ (sbox 0 ++ (sbox 1 ++
      (sbox 2 ++ (sbox 3 ++ assemble)))))))) := by
  rw [lookup, head, List.range_eq_range']
  simp only [headX, List.append_assoc, List.cons_append, List.nil_append]

/-- **The look-ups' function**: for the four indices' low bytes in the
lanes of `xmm0`, `S4`'s, `S3`'s, `S2`'s and `S1`'s entries in those of
`xmm1`; it writes the working space's bytes 272 to 591 and the four bytes
below `esp`. -/
theorem lookup_wp {s : State} {W : BitVec 32} {idx : Nat → BitVec 32} (hW : s.gpr .esi = W)
    (fW : W.toNat + 592 ≤ 2 ^ 32) (wrW : ∀ o n, 272 ≤ o → o + n ≤ 592 → InRegions s.wr (slot W o) n)
    (hsp : 4 ≤ (s.gpr .esp).toNat) (h0 : s.xmm .xmm0 = L idx) :
    WP isa lookup s fun t =>
      t.xmm .xmm1 = L (fun k => tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1 (idx k).toNat k) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms ∧
      Frame [wR W, below (s.gpr .esp) 4] s.mem t.mem := by
  rw [lookup_eq]
  refine WP.seq (WP.mono (symFrame_ok' tableName s hsp) fun s₀ ⟨h₀, x₀⟩ => ?_)
  refine Wp.cons (s' := s₀.setReg tbr (s₀.gpr .eax)) rfl ?_
  obtain u₁ := Upd.setReg s₀ tbr (s₀.gpr .eax)
  obtain x₁ : (s₀.setReg tbr (s₀.gpr .eax)).xmm = s₀.xmm := xmm_setReg _ _ _
  generalize s₀.setReg tbr (s₀.gpr .eax) = s₁ at u₁ x₁ ⊢
  obtain E : Env W s₁ := ⟨(u₁.other _ (by decide)).trans ((h₀.gpr _ (by decide)).trans hW),
    by rw [u₁.gpr, h₀.addr, u₁.syms, h₀.syms], fW, by rw [u₁.wr, h₀.wr]; exact wrW⟩
  show WP isa _ (S s₁ s₁.mem s₁.xmm) _
  refine headX_wp E (by rw [x₁, x₀]; exact h0) fun g0 l0 hh0 =>
    indexes_wp E (m₀ := s₁.mem) 16 0 s₁.mem g0 (by decide) l0 hh0 (fun r' hr' => absurd hr' (Nat.not_lt_zero _))
      (Frame.refl _ _) fun m1 g1 hV1 hf1 =>
    sbox_wp E (by decide) hV1 (hf1.sub fun r hr => ⟨_, List.mem_cons_self, by
        rw [List.mem_singleton.mp hr]; exact vR_sub W⟩)
      (fun j' hj' => absurd hj' (Nat.not_lt_zero _)) fun m2 g2 hV2 hf2 hF2 =>
    sbox_wp E (by decide) hV2 hf2 hF2 fun m3 g3 hV3 hf3 hF3 =>
    sbox_wp E (by decide) hV3 hf3 hF3 fun m4 g4 hV4 hf4 hF4 =>
    sbox_wp E (by decide) hV4 hf4 hF4 fun m5 g5 _ hf5 hF5 =>
    assemble_wp E hF5 fun g6 h6 => ⟨h6, fun r a b c => ?_, u₁.rd.trans h₀.rd, u₁.wr.trans h₀.wr,
      u₁.syms.trans h₀.syms, ?_⟩
  · exact (u₁.other r c).trans (h₀.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a, b⟩))
  · refine (h₀.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_
    rw [← u₁.mem]
    exact hf5.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self

/-! ## The call -/

/-- The return address's slot and the callee's four bytes, in the eight
bytes below `sp`. -/
theorem call_regions {sp : BitVec 32} (low : 8 ≤ sp.toNat) :
    Region.Sub (below sp 4) (below sp 8) ∧ Region.Sub (below (sp - 4) 4) (below sp 8) ∧
      Region.Disjoint (below sp 4) (below (sp - 4) 4) := by
  have hsp := sp.isLt
  obtain e4 : (sp - BitVec.ofNat 32 4).setWidth 64 = (sp - BitVec.ofNat 32 8).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain e8 : (sp - 4 - BitVec.ofNat 32 4).setWidth 64 = (sp - BitVec.ofNat 32 8).setWidth 64 + BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  generalize hX : (sp - BitVec.ofNat 32 8).setWidth 64 = X at e4 e8
  obtain b8 : below sp 8 = ⟨X + BitVec.ofNat 64 0, 8⟩ := by rw [← hX, BitVec.add_zero]
  obtain b4 : below sp 4 = ⟨X + BitVec.ofNat 64 4, 4⟩ := by simp only [below]; rw [e4]
  obtain b4' : below (sp - 4) 4 = ⟨X + BitVec.ofNat 64 0, 4⟩ := by simp only [below]; rw [e8]
  rw [b8, b4, b4']
  exact ⟨Offset.sub X (by decide) (by decide), Offset.sub X (by decide) (by decide),
    Offset.disjoint X (by decide) (by decide) (by decide)⟩

/-- **The call of the look-ups' function**, with eight bytes of stack apart
from the working space's bytes it writes. -/
theorem call_wp {s : State} {W : BitVec 32} {idx : Nat → BitVec 32} (hW : s.gpr .esi = W)
    (fW : W.toNat + 592 ≤ 2 ^ 32) (wrW : ∀ o n, 272 ≤ o → o + n ≤ 592 → InRegions s.wr (slot W o) n)
    (hsp : 8 ≤ (s.gpr .esp).toNat) (dWS : Region.Disjoint (wR W) (below (s.gpr .esp) 8))
    (h0 : s.xmm .xmm0 = L idx) :
    WP isa (.call fnName lookup) s fun t =>
      t.xmm .xmm1 = L (fun k => tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1 (idx k).toNat k) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms ∧
      Frame [below (s.gpr .esp) 8, wR W] s.mem t.mem := by
  obtain ⟨r4, r8, d48⟩ := call_regions hsp
  obtain cm : s.callEntry.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := State.callEntry_mem s
  obtain fc : Frame [below (s.gpr .esp) 8] s.mem s.callEntry.mem := by
    rw [cm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_top (by decide) hsp (by decide))
  obtain esp' : s.callEntry.gpr .esp = s.gpr .esp - 4 := State.callEntry_esp s
  refine WP.callBody (WP.mono (lookup_wp (s := s.callEntry) ((State.callEntry_gpr s (by decide)).trans hW) fW wrW
    (by rw [esp', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.sub_toNat (by omega)]; omega) h0)
    fun u ⟨hres, hg, hrd, hwr, hsy, hfr⟩ => ⟨?_, ?_, ?_⟩)
  · exact (hg .esp (by decide) (by decide) (by decide)).trans esp'
  · rw [esp'] at hfr
    rw [hfr.readW (r := below (s.gpr .esp) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide), cm]
    · exact Mem.readW_writeW_self32 _ _ _
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact (dWS.sub_right r4).symm
      · rw [List.mem_singleton.mp hr]; exact d48
  · obtain U := Upd.setReg u .esp (s.gpr .esp)
    refine ⟨(congrFun (xmm_setReg u _ _) _).trans hres, fun r a b c => ?_, U.rd.trans hrd, U.wr.trans hwr,
      U.syms.trans hsy, ?_⟩
    · by_cases h : r = .esp
      · rw [h]; exact U.gpr
      · exact (U.other r h).trans ((hg r a b c).trans (State.callEntry_gpr s h))
    · rw [U.mem]
      refine (fc.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).trans
        (hfr.sub fun r hr => ?_)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · rw [List.mem_singleton.mp hr, esp']
        exact ⟨_, List.mem_cons_self, r8⟩

/-! ## The rounds' look-ups -/

/-- The function as the rounds' look-ups: eight bytes of stack, the working
space's bytes 272 to 591, which are writable and apart from the stack, and
no table in memory. -/
def lookupLk : Lk where
  code := .call fnName lookup
  n := 8
  X S := [slotR S 272 320]
  Pre s S := 8 ≤ (s.gpr .esp).toNat ∧ S.toNat + 592 ≤ 2 ^ 32 ∧
    (∀ o n, 272 ≤ o → o + n ≤ 592 → InRegions s.wr (slot S o) n) ∧
    Region.Disjoint (wR S) (below (s.gpr .esp) 8)

theorem lookupLk_ok : LkOk lookupLk where
  ok s S idx hS hp h0 _ := by
    obtain ⟨hsp, fS, wS, dS⟩ := hp
    exact WP.mono (call_wp hS fS wS hsp dS h0) fun t ⟨h1, hg, hrd, hwr, hsy, hf⟩ => ⟨h1, hg, hf, hrd, hwr, hsy⟩
  transfer {s u S} hp _ hsp _ hwr _ _ := by
    obtain ⟨h8, fS, wS, dS⟩ := hp
    exact ⟨by rw [hsp]; exact h8, fS, by rw [hwr]; exact wS, by rw [hsp]; exact dS⟩

end VG.Proof.Cast5.X86.Ssse3
