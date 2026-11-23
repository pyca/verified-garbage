module

public import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.ByteLookup
public import VerifiedGarbage.Proof.Blowfish.X86.Ecb
public import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.Blowfish.X86.KeyMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody

-- separate module: the block function's proof, which the functions' checks (`Ssse3Verified.lean`, generated
-- contracts, taint and residue analyses of every function) do not change with

/-!
# Blowfish's block function by `pshufb` on x86 (32-bit): what a round's look-ups compute

The code of `Impl/Blowfish/X86/Ssse3.lean`, from states given by their
memory and XMM registers (`S s m f`), an instruction at a time
(`wp_xs`, `wp_tb`, `wp_ld`, `wp_st`):

* a plane's row (`plane_wp`) and a row of the four planes (`row_wp`), for
  any row: the registers are those of the rotation (`xr`), which are
  apart where the code needs them (`xr_ne`); the sixteen rows of an S-box
  (`scan_wp`), by induction, leave in `xmm4` to `xmm7` the rows of each
  plane through their index vectors, ORed (`ByteLookup.acc`);
* the sixteen index vectors (`indexes_wp`), in the working space.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86.Ssse3

open VG VG.X86 VG.X86.ByteLookup
open VG.Impl.Blowfish.X86 (at_ imm planeOff pOff)
open VG.Impl.Blowfish.X86.Ssse3
open VG.Proof.MlDsa.X86.Pack (addr_of_fit)

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

/-- The constant at the byte offset `off` of the table. -/
def cst (off : Nat) : BitVec 128 := table.getD (off / 8 + 1) 0 ++ table.getD (off / 8) 0

variable {s : State} {m : Mem}

/-- An instruction that writes an XMM register. -/
theorem wp_xs {f : XReg → BitVec 128} {i : Instr} {is : List Instr} {Q : State → Prop} {d : XReg} {v : BitVec 128}
    (h : exec i (S s m f) = some (State.setXmm (S s m f) d v)) (k : WP isa (.block is) (S s m (upd f d v)) Q) :
    WP isa (.block (i :: is)) (S s m f) Q := Wp.cons h k

/-- An instruction of two XMM registers. -/
theorem wp_bin {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {op : XBinOp} {a b : XReg}
    (k : WP isa (.block is) (S s m (upd f a (op.eval (f a) (f b)))) Q) :
    WP isa (.block (x op a b :: is)) (S s m f) Q := Wp.cons rfl k

/-- A constant of the table. -/
theorem wp_tb {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {off : Nat}
    (hb : s.gpr tbr = s.syms tableName) (ho : off % 8 = 0 ∧ off / 8 + 2 ≤ table.length)
    (k : WP isa (.block is) (S s m (upd f d (cst off))) Q) : WP isa (.block (tb d off :: is)) (S s m f) Q :=
  Wp.cons (show (if s.gpr tbr = s.syms tableName ∧ off % 8 = 0 ∧ off / 8 + 2 ≤ table.length then some _ else none) = _ by
    rw [ite_eq_left (show _ ∧ _ ∧ _ from ⟨hb, ho.1, ho.2⟩)]; rfl) k

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
  rw [hB]; exact addr_of_fit h

/-! ## The registers' rotation -/

theorem xr_mod (k : Nat) : xr (k % 8) = xr k := by simp only [xr, Nat.mod_mod]

theorem xr_add8 (k : Nat) : xr (k + 8) = xr k := by simp only [xr, Nat.add_mod_right]

theorem xr_ne {a b : Nat} (h : a % 8 ≠ b % 8) : xr a ≠ xr b := fun e => by
  have inj : ∀ a < 8, ∀ b < 8, xr a = xr b → a = b := by decide
  exact h (inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) (by rw [xr_mod, xr_mod]; exact e))

/-! ## A row of an S-box -/

/-- Row `r` of plane `p` of S-box `j`, in `m`, with the schedule at `K`. -/
abbrev rowAt (m : Mem) (K : BitVec 32) (j p r : Nat) : BitVec 128 := m.readW (slot K (planeOff j p + 16 * r)) 128

/-- The index vector of row `r`, in `m`, with the working space at `W`. -/
abbrev vAt (m : Mem) (W : BitVec 32) (r : Nat) : BitVec 128 := m.readW (slot W (vOff r)) 128

/-- Where the block function runs: the schedule at `K`, readable, in `esi`;
the working space at `W`, of which its bytes 64 to 383 are writable, in
`edi`; the table's address in `ebx`. -/
structure Env (K W : BitVec 32) (s : State) : Prop where
  esi : s.gpr .esi = K
  edi : s.gpr .edi = W
  ebx : s.gpr tbr = s.syms tableName
  fK : K.toNat + 4168 ≤ 2 ^ 32
  fW : W.toNat + 384 ≤ 2 ^ 32
  rdK : ∀ o n, o + n ≤ 4168 → InRegions (s.rd ++ s.wr) (slot K o) n
  wrW : ∀ o n, 64 ≤ o → o + n ≤ 384 → InRegions s.wr (slot W o) n

theorem Env.rdW {K W : BitVec 32} (E : Env K W s) {o n : Nat} (h : 64 ≤ o) (h' : o + n ≤ 384) :
    InRegions (s.rd ++ s.wr) (slot W o) n := by
  obtain ⟨r, hr, hc⟩ := E.wrW o n h h'
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A row of a plane: the row through the row's index vector, ORed with the
rows before it but for row 0. -/
theorem plane_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {j r p : Nat} {a : Addr} (hp : p < 4)
    (ha : s.ea (at_ .esi (planeOff j p + 16 * r)) = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ g, g (xr (5 * r + 1 + p)) =
        (if r = 0 then XBinOp.eval .pshufb (m.readW a 128) (f (xr (5 * r)))
         else XBinOp.eval .por (XBinOp.eval .pshufb (m.readW a 128) (f (xr (5 * r)))) (f (xr (5 * r + 4 + p)))) →
      (∀ q, q ≠ xr (5 * r + 1 + p) → g q = f q) → WP isa (.block is) (S s m g) Q) :
    WP isa (.block (plane j r p ++ is)) (S s m f) Q := by
  have hv : xr (5 * r) ≠ xr (5 * r + 1 + p) := xr_ne (by omega)
  have hA : xr (5 * r + 4 + p) ≠ xr (5 * r + 1 + p) := xr_ne (by omega)
  by_cases h0 : r = 0
  · rw [show plane j r p = [ld (xr (5 * r + 1 + p)) .esi (planeOff j p + 16 * r),
        x .pshufb (xr (5 * r + 1 + p)) (xr (5 * r))] by simp only [plane, ite_eq_left h0]; rfl]
    refine wp_ld ha hin (wp_bin (k _ ?_ fun q hq => ?_))
    · simp only [upd_self, upd_ne _ _ hv, ite_eq_left h0]
    · rw [upd_ne _ _ hq, upd_ne _ _ hq]
  · rw [show plane j r p = [ld (xr (5 * r + 1 + p)) .esi (planeOff j p + 16 * r),
        x .pshufb (xr (5 * r + 1 + p)) (xr (5 * r)), x .por (xr (5 * r + 1 + p)) (xr (5 * r + 4 + p))] by
      simp only [plane, ite_eq_right h0]; rfl]
    refine wp_ld ha hin (wp_bin (wp_bin (k _ ?_ fun q hq => ?_)))
    · simp only [upd_self, upd_ne _ _ hv, upd_ne _ _ hA, ite_eq_right h0]
    · rw [upd_ne _ _ hq, upd_ne _ _ hq, upd_ne _ _ hq]

/-- A row of the four planes of S-box `j`. -/
theorem row_wp {K W : BitVec 32} (E : Env K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {j r : Nat} (hj : j < 4) (hr : r < 16)
    (k : ∀ g, (∀ p < 4, g (xr (5 * r + 1 + p)) =
        (if r = 0 then XBinOp.eval .pshufb (rowAt m K j p r) (vAt m W r)
         else XBinOp.eval .por (XBinOp.eval .pshufb (rowAt m K j p r) (vAt m W r)) (f (xr (5 * r + 4 + p)))) ) →
      WP isa (.block is) (S s m g) Q) :
    WP isa (.block (row j r ++ is)) (S s m f) Q := by
  have eK : ∀ p < 4, s.ea (at_ .esi (planeOff j p + 16 * r)) = slot K (planeOff j p + 16 * r) := fun p hp =>
    ea_at E.esi (by have := E.fK; simp only [planeOff]; omega)
  have iK : ∀ p < 4, InRegions (s.rd ++ s.wr) (slot K (planeOff j p + 16 * r)) 16 := fun p hp =>
    E.rdK _ _ (by simp only [planeOff]; omega)
  have hW : s.ea (at_ .edi (vOff r)) = slot W (vOff r) := ea_at E.edi (by have := E.fW; simp only [vOff]; omega)
  have ne : ∀ a b : Nat, a % 8 ≠ b % 8 → xr a ≠ xr b := fun _ _ => xr_ne
  rw [show row j r ++ is = ld (xr (5 * r)) .edi (vOff r) ::
      (plane j r 0 ++ (plane j r 1 ++ (plane j r 2 ++ (plane j r 3 ++ is)))) by
    simp only [row, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_ld hW (E.rdW (by simp only [vOff]; omega) (by simp only [vOff]; omega))
    (plane_wp (by decide) (eK 0 (by decide)) (iK 0 (by decide)) fun g0 h0 o0 =>
    plane_wp (by decide) (eK 1 (by decide)) (iK 1 (by decide)) fun g1 h1 o1 =>
    plane_wp (by decide) (eK 2 (by decide)) (iK 2 (by decide)) fun g2 h2 o2 =>
    plane_wp (by decide) (eK 3 (by decide)) (iK 3 (by decide)) fun g3 h3 o3 => k g3 fun p hp => ?_)
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

theorem xr_congr {a b : Nat} (h : a % 8 = b % 8) : xr a = xr b := by rw [← xr_mod a, ← xr_mod b, h]

/-- The rows `r` to `r + n - 1` of S-box `j`, after the rows before `r`. -/
theorem rows_wp {K W : BitVec 32} (E : Env K W s) {is : List Instr} {Q : State → Prop} {j : Nat} (hj : j < 4)
    (n : Nat) : ∀ (r : Nat) (f : XReg → BitVec 128), 0 < r → r + n ≤ 16 →
      (∀ p < 4, f (xr (5 * r + 4 + p)) = acc (rowAt m K j p) (vAt m W) (r - 1)) →
      (∀ g, (∀ p < 4, g (xr (5 * (r + n) + 4 + p)) = acc (rowAt m K j p) (vAt m W) (r + n - 1)) →
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
theorem scan_wp {K W : BitVec 32} (E : Env K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {j : Nat} (hj : j < 4)
    (k : ∀ g, (∀ p < 4, g (xr (4 + p)) = acc (rowAt m K j p) (vAt m W) 15) → WP isa (.block is) (S s m g) Q) :
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

/-- The working space's bytes that the block function writes. -/
abbrev wR (W : BitVec 32) : Region := ⟨slot W 64, 320⟩

theorem readW_self128 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 128 = v :=
  Mem.readW_writeW_self m a 16 v (by decide)

/-- The index vector of row `r`, to the working space. -/
theorem index_wp {K W : BitVec 32} (E : Env K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {r : Nat} (hr : r < 16)
    (k : ∀ g, g .xmm0 = f .xmm0 → g .xmm1 = f .xmm1 →
      WP isa (.block is) (S s (m.writeW (slot W (vOff r)) (idx (cst (oC r)) (f .xmm1) (f .xmm0))) g) Q) :
    WP isa (.block (index r ++ is)) (S s m f) Q := by
  have h0 : (.xmm0 : XReg) ≠ xr (2 + r % 6) := by
    rw [show (.xmm0 : XReg) = xr 0 from rfl]; exact xr_ne (by omega)
  have h1 : (.xmm1 : XReg) ≠ xr (2 + r % 6) := by
    rw [show (.xmm1 : XReg) = xr 1 from rfl]; exact xr_ne (by omega)
  have fW := E.fW
  show WP isa (.block (tb (xr (2 + r % 6)) (oC r) :: x .pshufb (xr (2 + r % 6)) .xmm1 ::
    x .por (xr (2 + r % 6)) .xmm0 :: stx .edi (vOff r) (xr (2 + r % 6)) :: is)) _ _
  refine wp_tb E.ebx ⟨by simp only [oC]; omega, by rw [show table.length = 36 from rfl]; simp only [oC]; omega⟩
    (wp_bin (wp_bin (wp_st (ea_at E.edi (by simp only [vOff]; omega))
      (E.wrW _ _ (by simp only [vOff]; omega) (by simp only [vOff]; omega)) ?_)))
  simp only [upd_self, upd_ne _ _ h0, upd_ne _ _ h1]
  exact k _ (by rw [upd_ne _ _ h0, upd_ne _ _ h0, upd_ne _ _ h0]) (by rw [upd_ne _ _ h1, upd_ne _ _ h1, upd_ne _ _ h1])

/-- The index vectors of the rows `r` to `r + n - 1`, after those of the
rows before `r`: all of them in the working space, the memory outside it
kept. -/
theorem indexes_wp {K W : BitVec 32} (E : Env K W s) {is : List Instr} {Q : State → Prop} {H L : BitVec 128}
    {m₀ : Mem} (n : Nat) : ∀ (r : Nat) (m : Mem) (f : XReg → BitVec 128), r + n ≤ 16 → f .xmm0 = L → f .xmm1 = H →
      (∀ r' < r, vAt m W r' = idx (cst (oC r')) H L) → Frame [wR W] m₀ m →
      (∀ m' g, (∀ r' < r + n, vAt m' W r' = idx (cst (oC r')) H L) → Frame [wR W] m₀ m' →
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

/-! ## What the look-ups give -/

open VG.Spec.Blowfish (Schedule scheduleAt sEntry pEntry)
open VG.Proof.Blowfish (sEntry_byte word_ext pEntry_read scheduleAt_eq_of_frame)
open VG.X86.ByteMap (byte_eq_dword)

theorem cst_C : ∀ r < 16, ∀ b < 16, byte (cst (oC r)) b = if b = r then 0#8 else 0x80#8 := by decide +kernel

theorem cst_T : ∀ i < 16, byte (cst oT) i = BitVec.ofNat 8 (4 * (i % 4) + i / 4) := by decide +kernel

theorem cst_M : ∀ i < 16, byte (cst oM) i = 0x0f#8 := by decide +kernel

/-- `x` in every doubleword. -/
abbrev bc (x : BitVec 32) : BitVec 128 := shufDwords ((0 : BitVec 96) ++ x) 0

/-- The high nibbles of the bytes of `x`, in every doubleword. -/
abbrev hiOf (x : BitVec 32) : BitVec 128 := XBinOp.eval .pand (XShiftOp.eval .psrld (bc x) 4) (cst oM)

/-- The low nibbles of the bytes of `x`, in every doubleword. -/
abbrev loOf (x : BitVec 32) : BitVec 128 := XBinOp.eval .pand (bc x) (cst oM)

theorem byte_bc (x : BitVec 32) {k : Nat} (hk : k < 4) : byte (bc x) k = x.extractLsb' (8 * k) 8 := by
  rw [bc, Lanes.bcast_L, byte_eq_dword, Lanes.dword_L _ (by omega), show k % 4 = k by omega]

/-- **An S-box's entries.** With the index vectors of `x` in the working
space, the four planes' rows ORed and gathered hold, in doubleword `k`,
S-box `j`'s entry at byte `k` of `x`. -/
theorem entry_eq {m : Mem} {K W : BitVec 32} {x : BitVec 32} {j k : Nat} (hj : j < 4) (hk : k < 4)
    (hV : ∀ r < 16, vAt m W r = idx (cst (oC r)) (hiOf x) (loOf x)) :
    dword (gather (acc (rowAt m K j 0) (vAt m W) 15) (acc (rowAt m K j 1) (vAt m W) 15)
      (acc (rowAt m K j 2) (vAt m W) 15) (acc (rowAt m K j 3) (vAt m W) 15) (cst oT)) k =
      sEntry (scheduleAt m (K.setWidth 64)) j (x.extractLsb' (8 * k) 8) := by
  refine word_ext fun p hp => ?_
  obtain ⟨-, -, -, -, -, h1, h2, h3⟩ := nibbles (x.extractLsb' (8 * k) 8)
  rw [byte_of_dword _ _ hp]
  refine (byte_gather (a := fun p => acc (rowAt m K j p) (vAt m W) 15) cst_T hk hp).trans ?_
  show byte (acc (rowAt m K j p) (vAt m W) 15) k = _
  rw [acc_congr (V' := fun r => idx (cst (oC r)) (hiOf x) (loOf x)) 15 (fun r hr => hV r (by omega)),
    byte_acc (x := x.extractLsb' (8 * k) 8) (by omega) cst_C
      ((byte_hi (by omega) (cst_M k (by omega))).trans (by rw [byte_bc x hk]))
      ((byte_lo (cst_M k (by omega))).trans (by rw [byte_bc x hk])),
    sEntry_byte m _ hj hp]
  show (m.readW (slot K (planeOff j p + 16 * (x.extractLsb' (8 * k) 8 >>> 4).toNat)) 128).extractLsb'
    (8 * (x.extractLsb' (8 * k) 8 &&& 0x0f#8).toNat) 8 = _
  rw [byte_readW _ _ (by omega), Offset.add_add,
    show planeOff j p + 16 * (x.extractLsb' (8 * k) 8 >>> 4).toNat + (x.extractLsb' (8 * k) 8 &&& 0x0f#8).toNat =
      1024 * j + 256 * p + (x.extractLsb' (8 * k) 8).toNat by simp only [planeOff]; omega]

/-! ## A round's pieces -/

/-- The head's instructions on the XMM registers. -/
def headX : List Instr :=
  [.xop (.movd .xmm0 .ecx), .xop (.pshufd .xmm0 .xmm0 0), tb .xmm2 oM, x .movdqa .xmm1 .xmm0,
   .xop (.shift .psrld .xmm1 4), x .pand .xmm1 .xmm2, x .pand .xmm0 .xmm2]

/-- xL's nibbles, in `xmm1` and `xmm0`. -/
theorem headX_wp {K W : BitVec 32} (E : Env K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    (k : ∀ g, g .xmm0 = loOf (s.gpr .ecx) → g .xmm1 = hiOf (s.gpr .ecx) → WP isa (.block is) (S s m g) Q) :
    WP isa (.block (headX ++ is)) (S s m f) Q :=
  wp_xs rfl (wp_xs rfl (wp_tb E.ebx (by decide) (wp_bin (wp_xs rfl (wp_bin (wp_bin (k _ rfl rfl)))))))

/-- **An S-box**: its entries at the four bytes of `y`, in the working
space, with those of the S-boxes before it. -/
theorem sbox_wp {K W : BitVec 32} (E : Env K W s) (dKW : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (wR W))
    {y : BitVec 32} {m₀ : Mem} {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {j : Nat} (hj : j < 4)
    (hV : ∀ r < 16, vAt m W r = idx (cst (oC r)) (hiOf y) (loOf y)) (hf : Frame [wR W] m₀ m)
    (hF : ∀ j' < j, ∀ k < 4, dword (m.readW (slot W (fOff j')) 128) k =
      sEntry (scheduleAt m₀ (K.setWidth 64)) j' (y.extractLsb' (8 * k) 8))
    (k : ∀ m' g, (∀ r < 16, vAt m' W r = idx (cst (oC r)) (hiOf y) (loOf y)) → Frame [wR W] m₀ m' →
      (∀ j' < j + 1, ∀ k < 4, dword (m'.readW (slot W (fOff j')) 128) k =
        sEntry (scheduleAt m₀ (K.setWidth 64)) j' (y.extractLsb' (8 * k) 8)) → WP isa (.block is) (S s m' g) Q) :
    WP isa (.block (sbox j ++ is)) (S s m f) Q := by
  have fW := E.fW
  rw [sbox, List.append_assoc]
  refine scan_wp E hj fun g hg => ?_
  have e4 : g .xmm4 = acc (rowAt m K j 0) (vAt m W) 15 := hg 0 (by decide)
  have e5 : g .xmm5 = acc (rowAt m K j 1) (vAt m W) 15 := hg 1 (by decide)
  have e6 : g .xmm6 = acc (rowAt m K j 2) (vAt m W) 15 := hg 2 (by decide)
  have e7 : g .xmm7 = acc (rowAt m K j 3) (vAt m W) 15 := hg 3 (by decide)
  show WP isa (.block (x .punpckldq .xmm4 .xmm5 :: x .punpckldq .xmm6 .xmm7 :: x .punpcklqdq .xmm4 .xmm6 ::
    tb .xmm0 oT :: x .pshufb .xmm4 .xmm0 :: stx .edi (fOff j) .xmm4 :: is)) _ _
  refine wp_bin (wp_bin (wp_bin (wp_tb E.ebx (by decide) (wp_bin (wp_st (ea_at E.edi (by simp only [fOff]; omega))
    (E.wrW _ _ (by simp only [fOff]; omega) (by simp only [fOff]; omega)) ?_)))))
  simp only [upd, reduceCtorEq, ↓reduceIte, e4, e5, e6, e7]
  refine k _ _ (fun r hr => ?_) (hf.writeW List.mem_cons_self _ (Offset.contains _ (by simp only [fOff]; omega)
    (by simp only [fOff]; omega) (by decide))) fun j' hj' k hk => ?_
  · exact (Mem.readW_writeW_sep (Offset.sep _ (by simp only [vOff, fOff]; omega) (by simp only [vOff]; omega)
      (by simp only [fOff]; omega)) (by decide)).trans (hV r hr)
  · by_cases e : j' = j
    · rw [e, readW_self128, ← scheduleAt_eq_of_frame (K.setWidth 64) hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact dKW]
      exact entry_eq hj hk hV
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by simp only [fOff]; omega) (by simp only [fOff]; omega)
        (by simp only [fOff]; omega)) (by decide)]
      exact hF j' (by omega) k hk

/-! ## A round -/

open VG.Proof.Blowfish (roundStep iter iter_succ feistel_eq fAcc_three)
open VG.X86.Wp

theorem round_eq : round = .alu .xor .ecx (.mem (at_ .ebp 0)) ::
    (headX ++ ((List.range' 0 16).flatMap index ++ (sbox 0 ++ (sbox 1 ++ (sbox 2 ++ (sbox 3 ++ tail)))))) := by
  rw [round, head, List.range_eq_range']
  simp only [headX, List.append_assoc, List.cons_append, List.nil_append]

/-- What does not change while the block function runs: the schedule at `K`
and the working space at `W`, as `Env` has them, apart. -/
structure Fix (K W : BitVec 32) (s₀ : State) : Prop where
  fK : K.toNat + 4168 ≤ 2 ^ 32
  fW : W.toNat + 384 ≤ 2 ^ 32
  rdK : ∀ o n, o + n ≤ 4168 → InRegions (s₀.rd ++ s₀.wr) (slot K o) n
  wrW : ∀ o n, 64 ≤ o → o + n ≤ 384 → InRegions s₀.wr (slot W o) n
  dKW : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (wR W)

/-- Before round `i`: the halves in `ecx` and `edx`, the pointer to the
round's entry of P in `ebp`. -/
structure RInv (s₀ : State) (K W : BitVec 32) (i : Nat) (st : BitVec 32 × BitVec 32) (u : State) : Prop where
  ecx : u.gpr .ecx = st.1
  edx : u.gpr .edx = st.2
  ebp : u.gpr .ebp = K + BitVec.ofNat 32 (pOff + 4 * i)
  esi : u.gpr .esi = K
  edi : u.gpr .edi = W
  ebx : u.gpr tbr = s₀.syms tableName
  esp : u.gpr .esp = s₀.gpr .esp
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  syms : u.syms = s₀.syms
  frame : Frame [wR W] s₀.mem u.mem

/-- An entry of an S-box, read from the working space. -/
theorem fread {m : Mem} {W : BitVec 32} (fW : W.toNat + 384 ≤ 2 ^ 32) {j k : Nat} (hj : j < 4) (hk : k < 4) :
    m.readW (addr W (fOff j + 4 * k)) 32 = dword (m.readW (slot W (fOff j)) 128) k := by
  rw [dword_readW _ _ hk, Offset.add_add, addr_of_fit (by simp only [fOff]; omega)]

theorem schedule_frame {K W : BitVec 32} {s₀ : State} (F : Fix K W s₀) {m : Mem} (h : Frame [wR W] s₀.mem m) :
    scheduleAt m (K.setWidth 64) = scheduleAt s₀.mem (K.setWidth 64) :=
  scheduleAt_eq_of_frame _ h fun r hr => by rw [List.mem_singleton.mp hr]; exact F.dKW

/-- **A round.** -/
theorem round_wp {s₀ : State} {K W : BitVec 32} (F : Fix K W s₀) {i : Nat} (hi : i < 16)
    {st : BitVec 32 × BitVec 32} {u : State} (hI : RInv s₀ K W i st u) :
    WP isa (.block round) u fun u' =>
      RInv s₀ K W (i + 1) (roundStep (scheduleAt s₀.mem (K.setWidth 64)) id st i) u' ∧
        eval .ne u' = some (decide (i + 1 < 16)) := by
  have fK := F.fK
  have fW := F.fW
  obtain hSK := schedule_frame F hI.frame
  obtain aP : addr (K + BitVec.ofNat 32 (pOff + 4 * i)) 0 = slot K (4096 + 4 * i) := by
    show (K + BitVec.ofNat 32 (pOff + 4 * i) + BitVec.ofNat 32 0).setWidth 64 = _
    rw [Offset.add_add]; exact addr_of_fit (by simp only [pOff]; omega)
  rw [round_eq]
  refine wp_xorm hI.ebp (by rw [aP, hI.rd, hI.wr]; exact F.rdK _ _ (by omega)) fun u₁ h₁ => ?_
  obtain hx : u₁.gpr .ecx = st.1 ^^^ pEntry (scheduleAt s₀.mem (K.setWidth 64)) i := by
    rw [h₁.gpr, hI.ecx, aP, ← hSK, pEntry_read _ _ (by omega)]
  obtain E₁ : Env K W u₁ := ⟨(h₁.other _ (by decide)).trans hI.esi, (h₁.other _ (by decide)).trans hI.edi,
    ((h₁.other _ (by decide)).trans hI.ebx).trans (by rw [h₁.syms, hI.syms]), fK, fW,
    by rw [h₁.rd, h₁.wr, hI.rd, hI.wr]; exact F.rdK, by rw [h₁.wr, hI.wr]; exact F.wrW⟩
  obtain f₁ : Frame [wR W] s₀.mem u₁.mem := by rw [h₁.mem]; exact hI.frame
  show WP isa _ (S u₁ u₁.mem u₁.xmm) _
  refine headX_wp E₁ fun g0 l0 h0 =>
    indexes_wp E₁ (m₀ := u₁.mem) 16 0 u₁.mem g0 (by decide) l0 h0 (fun r' hr' => absurd hr' (Nat.not_lt_zero _))
      (Frame.refl _ _) fun m1 g1 hV1 hf1 =>
    sbox_wp E₁ F.dKW (by decide) hV1 hf1 (fun j' hj' => absurd hj' (Nat.not_lt_zero _)) fun m2 g2 hV2 hf2 hF2 =>
    sbox_wp E₁ F.dKW (by decide) hV2 hf2 hF2 fun m3 g3 hV3 hf3 hF3 =>
    sbox_wp E₁ F.dKW (by decide) hV3 hf3 hF3 fun m4 g4 hV4 hf4 hF4 =>
    sbox_wp E₁ F.dKW (by decide) hV4 hf4 hF4 fun m5 g5 _ hf5 hF5 => ?_
  -- F, from the four entries
  obtain hSK₁ : scheduleAt u₁.mem (K.setWidth 64) = scheduleAt s₀.mem (K.setWidth 64) := schedule_frame F f₁
  rw [hSK₁, hx] at hF5
  generalize scheduleAt s₀.mem (K.setWidth 64) = SK at hF5 hx ⊢
  obtain ⟨xl, hxl⟩ : ∃ xl, xl = st.1 ^^^ pEntry SK i := ⟨_, rfl⟩
  rw [← hxl] at hF5 hx
  obtain inW : ∀ o, 64 ≤ o → o + 4 ≤ 384 → InRegions ((S u₁ m5 g5).rd ++ (S u₁ m5 g5).wr) (addr W o) 4 :=
    fun o h h' => by rw [addr_of_fit (by omega)]; exact E₁.rdW h h'
  obtain r0 : m5.readW (addr W (fOff 0 + 12)) 32 = sEntry SK 0 (xl.extractLsb' 24 8) :=
    (fread fW (j := 0) (k := 3) (by decide) (by decide)).trans (hF5 0 (by decide) 3 (by decide))
  obtain r1 : m5.readW (addr W (fOff 1 + 8)) 32 = sEntry SK 1 (xl.extractLsb' 16 8) :=
    (fread fW (j := 1) (k := 2) (by decide) (by decide)).trans (hF5 1 (by decide) 2 (by decide))
  obtain r2 : m5.readW (addr W (fOff 2 + 4)) 32 = sEntry SK 2 (xl.extractLsb' 8 8) :=
    (fread fW (j := 2) (k := 1) (by decide) (by decide)).trans (hF5 2 (by decide) 1 (by decide))
  obtain r3 : m5.readW (addr W (fOff 3)) 32 = sEntry SK 3 (xl.extractLsb' 0 8) :=
    (fread fW (j := 3) (k := 0) (by decide) (by decide)).trans (hF5 3 (by decide) 0 (by decide))
  show WP isa (.block tail) (S u₁ m5 g5) _
  refine wp_ldm (B := W) E₁.edi (inW _ (by decide) (by decide)) fun t₁ k₁ =>
    wp_addm (B := W) ((k₁.other _ (by decide)).trans E₁.edi) (by rw [k₁.rd, k₁.wr]; exact inW _ (by decide) (by decide))
      fun t₂ k₂ =>
    wp_xorm (B := W) ((k₂.other _ (by decide)).trans ((k₁.other _ (by decide)).trans E₁.edi))
      (by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact inW _ (by decide) (by decide)) fun t₃ k₃ =>
    wp_addm (B := W) ((k₃.other _ (by decide)).trans ((k₂.other _ (by decide)).trans
        ((k₁.other _ (by decide)).trans E₁.edi)))
      (by rw [k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact inW _ (by decide) (by decide)) fun t₄ k₄ =>
    wp_xor fun t₅ k₅ => wp_mov fun t₆ k₆ => wp_mov fun t₇ k₇ => wp_addi fun t₈ k₈ => wp_mov fun t₉ k₉ =>
    wp_addi fun t₁₀ k₁₀ => wp_cmp fun t₁₁ k₁₁ _ z₁₁ => WP.block_nil ?_
  -- eax: F of xL
  obtain eF : t₄.gpr .eax = Spec.Blowfish.f SK xl := by
    rw [k₄.gpr, k₃.mem, k₂.mem, k₁.mem, k₃.gpr, k₂.mem, k₁.mem, k₂.gpr, k₁.mem, k₁.gpr]
    show ((m5.readW (addr W (fOff 0 + 12)) 32 + m5.readW (addr W (fOff 1 + 8)) 32) ^^^
      m5.readW (addr W (fOff 2 + 4)) 32) + m5.readW (addr W (fOff 3)) 32 = _
    rw [r0, r1, r2, r3]
    exact fAcc_three SK xl
  -- the registers a tail's instruction does not write, back to `u₁`
  obtain G4 : ∀ r, r ≠ .eax → t₄.gpr r = u₁.gpr r := fun r h => by
    rw [k₄.other r h, k₃.other r h, k₂.other r h, k₁.other r h]
  obtain e5 : t₅.gpr .eax = Spec.Blowfish.f SK xl ^^^ st.2 := by
    rw [k₅.gpr, eF, G4 _ (by decide), h₁.other _ (by decide), hI.edx]
  obtain G7 : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → t₇.gpr r = u₁.gpr r := fun r a b c => by
    rw [k₇.other r c, k₆.other r b, k₅.other r a, G4 r a]
  obtain G11 : ∀ r, r ≠ .eax → r ≠ .ebp → t₁₁.gpr r = t₇.gpr r := fun r a b => by
    rw [k₁₁.gpr, k₁₀.other r a, k₉.other r a, k₈.other r b]
  obtain ebp8 : t₈.gpr .ebp = K + BitVec.ofNat 32 (pOff + 4 * (i + 1)) := by
    rw [k₈.gpr, G7 _ (by decide) (by decide) (by decide), h₁.other _ (by decide), hI.ebp]
    show K + BitVec.ofNat 32 (pOff + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add, show pOff + 4 * i + 4 = pOff + 4 * (i + 1) by omega]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [G11 _ (by decide) (by decide), k₇.gpr, k₆.other _ (by decide), e5, hxl]; rfl
  · rw [G11 _ (by decide) (by decide), k₇.other _ (by decide), k₆.gpr, k₅.other _ (by decide),
      G4 _ (by decide), hx, hxl]; rfl
  · rw [k₁₁.gpr, k₁₀.other _ (by decide), k₉.other _ (by decide), ebp8]
  · rw [G11 _ (by decide) (by decide), G7 _ (by decide) (by decide) (by decide)]; exact E₁.esi
  · rw [G11 _ (by decide) (by decide), G7 _ (by decide) (by decide) (by decide)]; exact E₁.edi
  · rw [G11 _ (by decide) (by decide), G7 _ (by decide) (by decide) (by decide), h₁.other _ (by decide)]
    exact hI.ebx
  · rw [G11 _ (by decide) (by decide), G7 _ (by decide) (by decide) (by decide), h₁.other _ (by decide)]
    exact hI.esp
  · rw [k₁₁.rd, k₁₀.rd, k₉.rd, k₈.rd, k₇.rd, k₆.rd, k₅.rd, k₄.rd, k₃.rd, k₂.rd, k₁.rd]; exact h₁.rd.trans hI.rd
  · rw [k₁₁.wr, k₁₀.wr, k₉.wr, k₈.wr, k₇.wr, k₆.wr, k₅.wr, k₄.wr, k₃.wr, k₂.wr, k₁.wr]; exact h₁.wr.trans hI.wr
  · rw [k₁₁.syms, k₁₀.syms, k₉.syms, k₈.syms, k₇.syms, k₆.syms, k₅.syms, k₄.syms, k₃.syms, k₂.syms, k₁.syms]
    exact h₁.syms.trans hI.syms
  · rw [k₁₁.mem, k₁₀.mem, k₉.mem, k₈.mem, k₇.mem, k₆.mem, k₅.mem, k₄.mem, k₃.mem, k₂.mem, k₁.mem]
    exact f₁.trans hf5
  · show (t₁₁.zf).map (!·) = _
    rw [z₁₁, k₁₀.other _ (by decide), k₉.other _ (by decide), ebp8, k₁₀.gpr, k₉.gpr,
      k₈.other _ (by decide), G7 _ (by decide) (by decide) (by decide), E₁.esi]
    show some (!(K + BitVec.ofNat 32 (pOff + 4 * (i + 1)) - (K + BitVec.ofNat 32 (pOff + 64)) == 0)) = _
    rw [Offset.add_sub_add_left, sub_beq (by simp only [pOff]; omega) (by decide)]
    by_cases h : i + 1 < 16
    · simp only [pOff, h, decide_true, show ¬ 4096 + 4 * (i + 1) = 4096 + 64 by omega, decide_false, Bool.not_false]
    · simp only [pOff, h, decide_false, show 4096 + 4 * (i + 1) = 4096 + 64 by omega, decide_true, Bool.not_true]

/-! ## The block function -/

/-- A loop that runs its body `n` times: the body takes `I t` to `I (t + 1)`
and leaves ZF clear but after the last. -/
theorem count_loop {I : Nat → State → Prop} {n : Nat} {body : Prog isa} (hn : 0 < n) (hs : I 0 s)
    (step : ∀ t u, t < n → I t u → WP isa body u fun u' => I (t + 1) u' ∧ eval .ne u' = some (decide (t + 1 < n))) :
    WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m u => ∃ t, m = n - t ∧ t < n ∧ I t u) (fun m u ⟨t, hm, ht, hI⟩ => ?_) (n - 0) s
    ⟨0, rfl, hn, hs⟩
  refine WP.mono (step t u ht hI) fun u' ⟨hI', hc⟩ => ?_
  by_cases h : t + 1 < n
  · exact .inr ⟨hc.trans (by simp [h]), n - (t + 1), by omega, t + 1, rfl, h, hI'⟩
  · obtain rfl : t + 1 = n := by omega
    exact .inl ⟨hc.trans (by simp), hI'⟩

/-- **The block function**: the halves in `edx` and `ebp`, encrypted under
the schedule at `esi`, in `ecx` and `edx`; it writes the working space's
bytes 64 to 383 and the four bytes below `esp`. -/
theorem encryptBlock_wp {s : State} {K W : BitVec 32} (F : Fix K W s) (hK : s.gpr .esi = K) (hW : s.gpr .edi = W)
    (hsp : 4 ≤ (s.gpr .esp).toNat) (dKS : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (below (s.gpr .esp) 4)) :
    WP isa encryptBlock s fun s' =>
      (s'.gpr .ecx, s'.gpr .edx) =
        Spec.Blowfish.feistel (scheduleAt s.mem (K.setWidth 64)) id (s.gpr .edx) (s.gpr .ebp) ∧
      s'.gpr .esi = K ∧ s'.gpr .edi = W ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.syms = s.syms ∧ Frame [wR W, below (s.gpr .esp) 4] s.mem s'.mem := by
  have fK := F.fK
  refine WP.seq (WP.mono (symFrame_ok tableName s hsp) fun s₀ h₀ => WP.seq ?_)
  show WP isa (.block [.mov tbr (.reg .eax), .mov .ecx (.reg .edx), .mov .edx (.reg .ebp), .mov .ebp (.reg .esi),
    .alu .add .ebp (imm pOff)]) s₀ _
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ =>
    WP.block_nil ?_
  obtain RD : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h₀.rd]
  obtain WR : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₀.wr]
  obtain SY : s₅.syms = s.syms := by rw [u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms, h₀.syms]
  obtain M : s₅.mem = s₀.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain F₅ : Fix K W s₅ := ⟨F.fK, F.fW, by rw [RD, WR]; exact F.rdK, by rw [WR]; exact F.wrW, F.dKW⟩
  obtain hS5 : scheduleAt s₅.mem (K.setWidth 64) = scheduleAt s.mem (K.setWidth 64) := by
    rw [M]; exact scheduleAt_eq_of_frame _ h₀.frame fun r hr => by rw [List.mem_singleton.mp hr]; exact dKS
  obtain G : ∀ r, r ≠ tbr → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → r ≠ .eax → s₅.gpr r = s.gpr r := fun r a b c d e => by
    rw [u₅.other r d, u₄.other r d, u₃.other r c, u₂.other r b, u₁.other r a]
    exact h₀.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨e, b⟩)
  obtain ebx₅ : s₅.gpr tbr = s₅.syms tableName := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      h₀.addr, SY]
  obtain ecx₅ : s₅.gpr .ecx = s.gpr .edx := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
    exact h₀.gpr _ (by decide)
  obtain edx₅ : s₅.gpr .edx = s.gpr .ebp := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
    exact h₀.gpr _ (by decide)
  obtain ebp₅ : s₅.gpr .ebp = K + BitVec.ofNat 32 (pOff + 4 * 0) := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h₀.gpr _ (by decide), hK]
    rfl
  refine WP.seq (WP.mono (count_loop (n := 16)
    (I := fun i u => RInv s₅ K W i (iter (scheduleAt s₅.mem (K.setWidth 64)) id i (s.gpr .edx, s.gpr .ebp)) u)
    (by decide) ⟨ecx₅, edx₅, ebp₅, (G _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK,
      (G _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW, ebx₅, rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩ fun t u ht hI => ?_) fun s₆ h₆ => ?_)
  · have h := round_wp F₅ ht hI
    rw [← iter_succ] at h
    exact h
  -- the last exchange undone
  obtain hS6 := schedule_frame F₅ h₆.frame
  obtain a16 : addr (K + BitVec.ofNat 32 (pOff + 4 * 16)) 0 = slot K (4096 + 4 * 16) := by
    show (K + BitVec.ofNat 32 (pOff + 4 * 16) + BitVec.ofNat 32 0).setWidth 64 = _
    rw [Offset.add_add]; exact addr_of_fit (by simp only [pOff]; omega)
  obtain a17 : addr (K + BitVec.ofNat 32 (pOff + 4 * 16)) 4 = slot K (4096 + 4 * 17) := by
    show (K + BitVec.ofNat 32 (pOff + 4 * 16) + BitVec.ofNat 32 4).setWidth 64 = _
    rw [Offset.add_add]; exact addr_of_fit (by simp only [pOff]; omega)
  show WP isa (.block [.alu .xor .ecx (.mem (at_ .ebp 0)), .alu .xor .edx (.mem (at_ .ebp 4)), .mov .eax (.reg .ecx),
    .mov .ecx (.reg .edx), .mov .edx (.reg .eax)]) s₆ _
  refine wp_xorm h₆.ebp (by rw [a16, h₆.rd]; rw [h₆.wr]; exact F₅.rdK _ _ (by decide)) fun v₁ w₁ =>
    wp_xorm ((w₁.other _ (by decide)).trans h₆.ebp)
      (by rw [a17, w₁.rd, w₁.wr, h₆.rd, h₆.wr]; exact F₅.rdK _ _ (by decide)) fun v₂ w₂ =>
    wp_mov fun v₃ w₃ => wp_mov fun v₄ w₄ => wp_mov fun v₅ w₅ => WP.block_nil ?_
  obtain G' : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .eax → v₅.gpr r = s₆.gpr r := fun r a b c => by
    rw [w₅.other r b, w₄.other r a, w₃.other r c, w₂.other r b, w₁.other r a]
  refine ⟨?_, (G' _ (by decide) (by decide) (by decide)).trans h₆.esi,
    (G' _ (by decide) (by decide) (by decide)).trans h₆.edi,
    ((G' _ (by decide) (by decide) (by decide)).trans h₆.esp).trans
      ((G _ (by decide) (by decide) (by decide) (by decide) (by decide))),
    by rw [w₅.rd, w₄.rd, w₃.rd, w₂.rd, w₁.rd, h₆.rd, RD], by rw [w₅.wr, w₄.wr, w₃.wr, w₂.wr, w₁.wr, h₆.wr, WR],
    by rw [w₅.syms, w₄.syms, w₃.syms, w₂.syms, w₁.syms, h₆.syms, SY], ?_⟩
  · rw [feistel_eq, ← hS5, show (id 17 : Nat) = 17 from rfl, show (id 16 : Nat) = 16 from rfl]
    refine Prod.ext ?_ ?_
    · show v₅.gpr .ecx = _
      rw [w₅.other _ (by decide), w₄.gpr, w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), h₆.edx, w₁.mem,
        a17, ← hS6, pEntry_read _ _ (i := 17) (by decide)]
    · show v₅.gpr .edx = _
      rw [w₅.gpr, w₄.other _ (by decide), w₃.gpr, w₂.other _ (by decide), w₁.gpr, h₆.ecx, a16, ← hS6,
        pEntry_read _ _ (i := 16) (by decide)]
  · rw [w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
    refine (h₀.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_
    rw [← M]
    exact h₆.frame.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self

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

/-- **The call of the block function**, with eight bytes of stack apart from
the schedule and from the working space. -/
theorem call_wp {s : State} {K W : BitVec 32} (F : Fix K W s) (hK : s.gpr .esi = K) (hW : s.gpr .edi = W)
    (hsp : 8 ≤ (s.gpr .esp).toNat) (dKS : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (below (s.gpr .esp) 8))
    (dWS : Region.Disjoint (wR W) (below (s.gpr .esp) 8)) {Q : State → Prop}
    (hQ : ∀ s', (s'.gpr .ecx, s'.gpr .edx) =
        Spec.Blowfish.feistel (scheduleAt s.mem (K.setWidth 64)) id (s.gpr .edx) (s.gpr .ebp) →
      s'.gpr .esi = K → s'.gpr .edi = W → s'.gpr .esp = s.gpr .esp → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → Frame [wR W, below (s.gpr .esp) 8] s.mem s'.mem → Q s') :
    WP isa (.call fnName encryptBlock) s Q := by
  obtain ⟨r4, r8, d48⟩ := call_regions hsp
  obtain cm : s.callEntry.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := State.callEntry_mem s
  obtain fc : Frame [below (s.gpr .esp) 8] s.mem s.callEntry.mem := by
    rw [cm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_top (by decide) hsp (by decide))
  obtain hS : scheduleAt s.callEntry.mem (K.setWidth 64) = scheduleAt s.mem (K.setWidth 64) :=
    scheduleAt_eq_of_frame _ fc fun r hr => by rw [List.mem_singleton.mp hr]; exact dKS
  obtain esp' : s.callEntry.gpr .esp = s.gpr .esp - 4 := State.callEntry_esp s
  refine WP.callBody (WP.mono (encryptBlock_wp (s := s.callEntry) ⟨F.fK, F.fW, F.rdK, F.wrW, F.dKW⟩
    ((State.callEntry_gpr s (by decide)).trans hK) ((State.callEntry_gpr s (by decide)).trans hW)
    (by rw [esp', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.sub_toNat (by omega)]; omega)
    (by rw [esp']; exact dKS.sub_right r8)) fun u ⟨hres, hesi, hedi, hesp, hrd, hwr, hsy, hfr⟩ => ⟨?_, ?_, ?_⟩)
  · exact hesp.trans esp'
  · rw [esp'] at hfr
    rw [hfr.readW (r := below (s.gpr .esp) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide), cm]
    · exact Mem.readW_writeW_self32 _ _ _
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact (dWS.sub_right r4).symm
      · rw [List.mem_singleton.mp hr]; exact d48
  · obtain U := Upd.setReg u .esp (s.gpr .esp)
    refine hQ _ ?_ ((U.other _ (by decide)).trans hesi) ((U.other _ (by decide)).trans hedi) U.gpr
      (U.rd.trans hrd) (U.wr.trans hwr) (U.syms.trans hsy) ?_
    · rw [U.other _ (by decide), U.other _ (by decide), hres, hS, State.callEntry_gpr s (by decide),
        State.callEntry_gpr s (by decide)]
    · rw [U.mem]
      refine (fc.mono fun r hr => List.mem_cons_of_mem _ hr).trans (hfr.sub fun r hr => ?_)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · rw [List.mem_singleton.mp hr, esp']
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, r8⟩

/-! ## The modes' core -/

open VG.Proof.Modes.X86 (ScrIn coreRegion blkAddr blkRegion slotA stkRegion CoreSpec)
open VG.Proof.Blowfish (dirCipher dirCipher_len dirCipher_bytes bytesAt_eq dirBlock)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Blowfish (blockAt decodeWord encodeBlock)

/-- The key ready for the core at `B`: the schedule through the first stack
argument, apart from every writable region, and the core's eight bytes of
stack apart from the schedule, from that argument and from the scratch
buffer. -/
def Rdy (s : State) (B : BitVec 32) (k : Schedule) : Prop :=
  ∃ S, SchedAt s k S ∧ Apart S (s.ea (at_ .esp 4)) s.wr ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨S.setWidth 64, 4168⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨s.ea (at_ .esp 4), 4⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨B.setWidth 64, 4 * core.total⟩ ∧ B.toNat + 4 * core.total ≤ 2 ^ 32

theorem ea_congr {s s' : State} (h : s'.gpr .esp = s.gpr .esp) : s'.ea (at_ .esp 4) = s.ea (at_ .esp 4) := by
  show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [h]

/-- The block of the core's buffer, encrypted in place. -/
theorem crypt_wp {s : State} {B : BitVec 32} {k : Schedule} (hB : s.gpr VG.Impl.Modes.X86.sb = B)
    (hs : ScrIn s B core.total) (hr : Rdy s B k) (hsp : core.stack ≤ (s.gpr .esp).toNat) :
    WP isa core.crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Rdy s' B k ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧
      (∀ j < core.G, bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        dirCipher true k (bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨S, ⟨hin, hv, hk, hsch, hSfit⟩, ha, dSK, dSA, dSB, hfit⟩ := hr
  have hB' : s.gpr .edi = B := hB
  have hsp' : 8 ≤ (s.gpr .esp).toNat := hsp
  have scr : (⟨B.setWidth 64, 424⟩ : Region) ∈ s.wr := hs.wr
  have hfit' : B.toNat + 424 ≤ 2 ^ 32 := hfit
  obtain wB : ∀ d n, d + n ≤ 424 → InRegions s.wr (slot B d) n := fun d n h =>
    ⟨_, scr, Offset.contains_base _ (by omega) (by omega)⟩
  obtain aB : ∀ d, d + 4 ≤ 424 → addr B d = slot B d := fun d h => addr_of_fit (by omega)
  obtain rin : ∀ {a : Addr} {n : Nat}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n := fun ⟨r, hr, hc⟩ =>
    ⟨r, List.mem_append_right _ hr, hc⟩
  obtain e12 : slot B 8 + BitVec.ofNat 64 4 = slot B 12 := Offset.add_add _ _ _
  obtain aS := (ha _ scr).1
  obtain aA := (ha _ scr).2
  obtain coreSub : Region.Sub (coreRegion core B) ⟨B.setWidth 64, 424⟩ := Region.sub_prefix (by decide)
  obtain wSub : Region.Sub (wR B) (coreRegion core B) := Offset.sub_base _ (by decide)
  show WP isa (.seq (.block [.mov .esi (.mem ⟨.esp, 4⟩), .mov .edx (.mem ⟨.edi, 8⟩), .bswap .edx,
    .mov .ebp (.mem ⟨.edi, 12⟩), .bswap .ebp]) (.seq (.call fnName encryptBlock)
    (.block [.bswap .ecx, .bswap .edx, .store ⟨.edi, 8⟩ .ecx, .store ⟨.edi, 12⟩ .edx]))) s _
  apply WP.seq
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ =>
    wp_ldm (B := B) ((u₁.other _ (by decide)).trans hB')
      (by rw [u₁.rd, u₁.wr, aB 8 (by decide)]; exact rin (wB 8 4 (by decide))) fun s₂ u₂ =>
    wp_bswap fun s₃ u₃ =>
    wp_ldm (B := B) ((u₃.other _ (by decide)).trans ((u₂.other _ (by decide)).trans ((u₁.other _ (by decide)).trans hB')))
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, aB 12 (by decide)]; exact rin (wB 12 4 (by decide)))
      fun s₄ u₄ =>
    wp_bswap fun s₅ u₅ => WP.block_nil ?_
  obtain RD : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain WR : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain M : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain G : ∀ r, r ≠ .esi → r ≠ .edx → r ≠ .ebp → s₅.gpr r = s.gpr r := fun r a b c => by
    rw [u₅.other r c, u₄.other r c, u₃.other r b, u₂.other r b, u₁.other r a]
  obtain esi₅ : s₅.gpr .esi = S := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    exact hv
  obtain edx₅ : s₅.gpr .edx = decodeWord (blockAt s.mem (slot B 8)) 0 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.mem, aB 8 (by decide)]
    have h := bswap_load s.mem (slot B 8) (o := 0) (by decide)
    rw [Offset.add_add] at h
    exact h
  obtain ebp₅ : s₅.gpr .ebp = decodeWord (blockAt s.mem (slot B 8)) 4 := by
    rw [u₅.gpr, u₄.gpr, u₃.mem, u₂.mem, u₁.mem, aB 12 (by decide), ← e12]
    exact bswap_load s.mem (slot B 8) (o := 4) (by decide)
  obtain esp₅ : s₅.gpr .esp = s.gpr .esp := G _ (by decide) (by decide) (by decide)
  apply WP.seq
  refine call_wp (K := S) (W := B) ⟨hSfit, by omega, fun o n h => by
      rw [RD, WR]; exact ⟨_, hsch, Offset.contains_base _ (by omega) (by omega)⟩,
    fun o n h h' => by rw [WR]; exact wB o n (by omega), aS.sub_right (fun a h => coreSub a (wSub a h))⟩ esi₅
    ((G _ (by decide) (by decide) (by decide)).trans hB') (by rw [esp₅]; exact hsp') (by rw [esp₅]; exact dSK.symm)
    (by rw [esp₅]; exact (dSB.sub_right (fun a h => coreSub a (wSub a h))).symm)
    fun u hres hesi hedi hesp hrd hwr hsy hfr => ?_
  rw [esp₅, M] at hfr
  rw [M, ← hk, edx₅, ebp₅] at hres
  refine wp_bswap fun t₁ v₁ => wp_bswap fun t₂ v₂ =>
    wp_stm (B := B) ((v₂.other _ (by decide)).trans ((v₁.other _ (by decide)).trans hedi))
      (by rw [v₂.wr, v₁.wr, hwr, WR, aB 8 (by decide)]; exact wB 8 4 (by decide)) fun t₃ v₃ =>
    wp_stm (B := B) (by rw [v₃.gpr]; exact (v₂.other _ (by decide)).trans ((v₁.other _ (by decide)).trans hedi))
      (by rw [v₃.wr, v₂.wr, v₁.wr, hwr, WR, aB 12 (by decide)]; exact wB 12 4 (by decide)) fun t₄ v₄ =>
    WP.block_nil ?_
  obtain M₄ : t₄.mem = (u.mem.writeW (slot B 8) (bswap (u.gpr .ecx))).writeW (slot B 8 + BitVec.ofNat 64 4)
      (bswap (u.gpr .edx)) := by
    rw [v₄.mem, v₃.mem, v₃.gpr, v₂.mem, v₁.mem, v₂.gpr, v₂.other _ (by decide), v₁.gpr, v₁.other _ (by decide),
      aB 8 (by decide), aB 12 (by decide), e12]
  obtain esp₄ : t₄.gpr .esp = s.gpr .esp := by
    rw [v₄.gpr, v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), hesp, esp₅]
  obtain rd₄ : t₄.rd = s.rd := by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, hrd, RD]
  obtain wr₄ : t₄.wr = s.wr := by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, hwr, WR]
  obtain FR : Frame [coreRegion core B, stkRegion (s.gpr .esp) 8] s.mem t₄.mem := by
    rw [M₄, e12]
    refine ((hfr.sub fun r hr => ?_).writeW List.mem_cons_self _ (Offset.contains_base _ (d := 8) (n := 4)
      (by decide) (by decide))).writeW List.mem_cons_self _ (Offset.contains_base _ (d := 12) (n := 4)
      (by decide) (by decide))
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_, List.mem_cons_self, wSub⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  obtain apS : Apart S (s.ea (at_ .esp 4)) [coreRegion core B, stkRegion (s.gpr .esp) 8] := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨aS.sub_right coreSub, aA.sub_right coreSub⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨dSK.symm, dSA.symm⟩
  refine ⟨by rw [v₄.gpr, v₃.gpr]; exact (v₂.other _ (by decide)).trans ((v₁.other _ (by decide)).trans hedi), esp₄,
    ⟨S, SchedAt.frame ⟨hin, hv, hk, hsch, hSfit⟩ apS esp₄ rd₄ wr₄ FR, by rw [wr₄, ea_congr esp₄]; exact ha,
      by rw [esp₄]; exact dSK, by rw [esp₄, ea_congr esp₄]; exact dSA, by rw [esp₄]; exact dSB, hfit⟩,
    FR, fun j hj => ?_, rd₄, wr₄⟩
  obtain rfl : j = 0 := by simp only [core] at hj; omega
  obtain hba : blkAddr core B 0 = slot B 8 := by
    simp only [blkAddr, slotA, core, Offset.add_add]
  rw [hba]
  simp only [core, Nat.reduceMul]
  rw [dirCipher_bytes, bytesAt_eq, M₄, stored_block, show dirBlock k true = blockOut k true from rfl, blockOut_eq,
    show ord true = id from rfl, ← hres]

theorem keyArgsN_congr {s s' : State} {rs : List Region} {k : Schedule} (h : KeyArgsN 8 s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgsN 8 s' rs k := by
  obtain ⟨hk, d1, d2, d3⟩ := h
  obtain ⟨S, hS, ha, hw⟩ := hk
  obtain e : arg s' 0 = arg s 0 := by
    show s'.mem.readW (s'.ea (at_ .esp 4)) 32 = s.mem.readW (s.ea (at_ .esp 4)) 32
    rw [ea_congr hesp]
    exact hf.readW (Region.contains_self _ _) (fun r hr => (ha r hr).2) (by decide)
  exact ⟨keyArgs_congr ⟨S, hS, ha, hw⟩ hesp hrd hwr hf, by rw [hesp]; exact d1, by rw [hesp, e]; exact d2,
    by rw [hesp, ea_congr hesp]; exact d3⟩

theorem rdy_frame {s s' : State} {B : BitVec 32} {k : Schedule} {rs : List Region} (h : Rdy s B k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') : Rdy s' B k := by
  obtain ⟨S, hS, ha, d1, d2, d3, hfit⟩ := h
  exact ⟨S, hS.frame (ha.sub hs) hesp hrd hwr hf, by rw [hwr, ea_congr hesp]; exact ha, by rw [hesp]; exact d1,
    by rw [hesp, ea_congr hesp]; exact d2, by rw [hesp]; exact d3, hfit⟩

/-- **The core by `pshufb` meets what the modes need**, with nothing to
prepare. -/
def ssse3CoreSpec : CoreSpec core where
  Key := Schedule
  cipher := dirCipher true
  KeyArgs := KeyArgsN 8
  Ready := Rdy
  cipher_len _ _ := dirCipher_len _ _ _
  layout := ⟨by decide, .inl rfl, by decide, by decide⟩
  keyArgs_congr h e r w _ f := keyArgsN_congr h e r w f
  ready_frame h e r w _ hf hs _ := rdy_frame h e r w hf hs
  prepare_wp hB hs hR hk _ := by
    obtain ⟨⟨S, hS, -, hw⟩, hsr, hsk, hsa⟩ := hk
    obtain e : arg _ 0 = S := hS.2.1
    rw [e] at hsk
    exact WP.block_nil ⟨⟨S, hS, hw, hsk, hsa, hsr _ hR, hs.fit⟩, hB, rfl, Frame.refl _ _, rfl, rfl⟩
  crypt_wp hB hs hr hsp := crypt_wp hB hs hr hsp

/-- It fits Blowfish's functions, with 53 words of working space and eight
bytes of stack. -/
def ssse3Fits : Fits ssse3CoreSpec 53 8 := ⟨id, id, rfl, rfl, rfl, rfl⟩

/-! ## Key expansion's block function -/

/-- What key expansion's block function needs of the state `s₀` key
expansion starts in, besides what the baseline's does (`CipherEnv`): the
schedule at `K` readable, the rest of the working space at `B`, and eight
bytes of stack, apart from both. -/
structure KeyX (K B : BitVec 32) (s₀ : State) : Prop where
  fW : B.toNat + 384 ≤ 2 ^ 32
  rdK : ∀ o n, o + n ≤ 4168 → InRegions (s₀.rd ++ s₀.wr) (slot K o) n
  wrW : ∀ o n, 64 ≤ o → o + n ≤ 384 → InRegions s₀.wr (slot B o) n
  dKW : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (wR B)
  sp : 8 ≤ (s₀.gpr .esp).toNat
  dKS : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (below (s₀.gpr .esp) 8)
  dWS : Region.Disjoint (wR B) (below (s₀.gpr .esp) 8)

/-- **`blkKey` is a block function for key expansion** (`BlkOk`), which
writes, besides the halves' slots, the rest of the working space and eight
bytes of stack. -/
theorem blkOk_blkKey {K B : BitVec 32} {s₀ : State} (X : KeyX K B s₀) :
    BlkOk blkKey K B [wR B, below (s₀.gpr .esp) 8] s₀ := fun u E hesp hrd hwr => by
  have bfit := E.bfit
  obtain aB : ∀ d, d + 4 ≤ 40 → addr B d = slot B d := fun d h => addr_of_fit (by omega)
  obtain rin : ∀ {a : Addr} {n : Nat}, InRegions u.wr a n → InRegions (u.rd ++ u.wr) a n := fun ⟨r, hr, hc⟩ =>
    ⟨r, List.mem_append_right _ hr, hc⟩
  show WP isa (.seq (.block [.mov .edx (.mem ⟨.ebp, 16⟩), .mov .esi (.mem ⟨.esp, 12⟩), .mov .edi (.reg .ebp),
    .mov .ebp (.mem ⟨.ebp, 20⟩)]) (.seq (.call fnName encryptBlock)
    (.block [.mov .ebp (.reg .edi), .store ⟨.ebp, 16⟩ .ecx, .store ⟨.ebp, 20⟩ .edx]))) u _
  apply WP.seq
  refine wp_ldm (B := B) E.bp (by rw [aB 16 (by decide)]; exact rin (E.slotW (by decide))) fun s₁ u₁ =>
    wp_ldm (B := u.gpr .esp) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact E.schRd) fun s₂ u₂ =>
    wp_mov fun s₃ u₃ =>
    wp_ldm (B := B) ((u₃.other _ (by decide)).trans ((u₂.other _ (by decide)).trans ((u₁.other _ (by decide)).trans E.bp)))
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, aB 20 (by decide)]; exact rin (E.slotW (by decide)))
      fun s₄ u₄ => WP.block_nil ?_
  obtain RD : s₄.rd = u.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain WR : s₄.wr = u.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain M : s₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain esi₄ : s₄.gpr .esi = K := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]; exact E.schVal
  obtain edi₄ : s₄.gpr .edi = B := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact E.bp
  obtain edx₄ : s₄.gpr .edx = u.mem.readW (slot B 16) 32 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, aB 16 (by decide)]
  obtain ebp₄ : s₄.gpr .ebp = u.mem.readW (slot B 20) 32 := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, aB 20 (by decide)]
  obtain esp₄ : s₄.gpr .esp = s₀.gpr .esp := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp]
  apply WP.seq
  refine call_wp (K := K) (W := B) ⟨E.fit, X.fW, by rw [RD, WR, hrd, hwr]; exact X.rdK,
    by rw [WR, hwr]; exact X.wrW, X.dKW⟩ esi₄ edi₄ (by rw [esp₄]; exact X.sp) (by rw [esp₄]; exact X.dKS)
    (by rw [esp₄]; exact X.dWS) fun v hres hesi hedi hesp' hrd' hwr' hsy hfr => ?_
  rw [esp₄, M] at hfr
  rw [M, edx₄, ebp₄] at hres
  obtain w16 : InRegions v.wr (slot B 16) 4 := by rw [hwr', WR]; exact E.slotW (by decide)
  obtain w20 : InRegions v.wr (slot B 20) 4 := by rw [hwr', WR]; exact E.slotW (by decide)
  refine wp_mov fun t₁ w₁ =>
    wp_stm (B := B) (w₁.gpr.trans hedi) (by rw [w₁.wr, aB 16 (by decide)]; exact w16) fun t₂ w₂ =>
    wp_stm (B := B) (by rw [w₂.gpr]; exact w₁.gpr.trans hedi)
      (by rw [w₂.wr, w₁.wr, aB 20 (by decide)]; exact w20) fun t₃ w₃ => WP.block_nil ⟨?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [w₃.mem, w₂.mem, w₂.gpr, w₁.mem, w₁.other _ (by decide), w₁.other _ (by decide), aB 16 (by decide),
      aB 20 (by decide), Mem.readW_writeW_self32,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, show ord true = id from rfl]
    exact hres
  · rw [w₃.gpr, w₂.gpr]
    cases r <;> first | exact absurd (by decide) hr | skip
    case ebp => rw [w₁.gpr, hedi]; exact E.bp.symm
    case esp => rw [w₁.other _ (by decide), hesp', esp₄, hesp]
  · rw [w₃.rd, w₂.rd, w₁.rd, hrd', RD]
  · rw [w₃.wr, w₂.wr, w₁.wr, hwr', WR]
  · rw [w₃.mem, w₂.mem, w₁.mem, aB 16 (by decide), aB 20 (by decide)]
    exact ((hfr.mono fun r hr => List.mem_cons_of_mem _ hr).writeW List.mem_cons_self _
      (Offset.contains _ (d := 16) (n := 4) (by decide) (by decide) (by decide))).writeW List.mem_cons_self _
      (Offset.contains _ (d := 20) (n := 4) (by decide) (by decide) (by decide))

end VG.Proof.Blowfish.X86.Ssse3
