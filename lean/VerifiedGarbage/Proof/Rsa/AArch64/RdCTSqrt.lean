module
-- separate module: the square root's leakage proof, its taint checks and runs of every piece, builds beside `RdCT4`

public import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrtDigits
public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
import VerifiedGarbage.Proof.Rsa.AArch64.RdCT4
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrtDigits
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT4
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes_det` on AArch64: the square root's digits leak nothing

A digit reloads its count `m` from the header slot `sCnt` four times, and the taint analysis takes
whatever is loaded from memory as secret. So the digit is cut after each reload: the pieces between
the cuts are checked by the taint analysis from registers that correctness pins (`DC`, the digit's
fixed registers and its count), and each cut carries what the rest of its block runs to.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Impl.Bignum.Public (sCnt)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A digit's layout: the working space, the remainder `R` (`eR`), the root `S` (`eS`), `W` words, and
the count `m` of digits so far. -/
structure DPar where
  B : Addr
  Z : Nat
  eR : Nat
  eS : Nat
  W : Nat
  m : Nat

/-- The window's base: `R`'s word `W - 2 m - 2`. -/
abbrev DPar.d (p : DPar) : Nat := p.eR + (8 * p.W - 16 * p.m - 16)

/-- `S`'s word `k - m`. -/
abbrev DPar.e (p : DPar) : Nat := p.eS + 8 * (p.W / 2 - p.m)

/-- The registers a digit keeps, and its count. -/
structure DC (p : DPar) (t : State) : Prop where
  scr : Scr t p.B p.Z
  x0 : t.gpr .x0 = p.B
  x7 : t.gpr .x7 = 0
  x10 : t.gpr .x10 = off p.B p.eR
  x11 : t.gpr .x11 = off p.B p.eS
  x12 : t.gpr .x12 = BitVec.ofNat 64 p.W
  cnt : word t.mem p.B (8 * sCnt) = BitVec.ofNat 64 p.m

/-- `digit_ok`'s bounds. -/
structure DS (p : DPar) : Prop where
  hm1 : 1 ≤ p.m
  hW : 2 * p.m + 2 ≤ p.W
  hW' : p.W < 2 ^ 24
  hH : 8 * 32 ≤ p.Z
  hR : p.eR + 8 * p.W ≤ p.Z
  hR8 : 256 ≤ p.eR
  hS : p.eS + 8 * p.W ≤ p.Z
  hS8 : 256 ≤ p.eS
  hRS : p.eR + 8 * p.W ≤ p.eS ∨ p.eS + 8 * p.W ≤ p.eR

theorem DC.keep {p : DPar} {s t : State} (h : DC p s) {rs : List Reg} (k : Keep rs s t) (h0 : .x0 ∉ rs)
    (h7 : .x7 ∉ rs) (h10 : .x10 ∉ rs) (h11 : .x11 ∉ rs) (h12 : .x12 ∉ rs)
    (hc : word t.mem p.B (8 * sCnt) = word s.mem p.B (8 * sCnt)) : DC p t :=
  ⟨h.scr.congr k.wr, (k.gpr .x0 h0).trans h.x0, (k.gpr .x7 h7).trans h.x7, (k.gpr .x10 h10).trans h.x10,
    (k.gpr .x11 h11).trans h.x11, (k.gpr .x12 h12).trans h.x12, hc.trans h.cnt⟩

/-- A write in the working space past the header keeps the count. -/
theorem cnt_writeW {B : Addr} {m : Mem} {d : Nat} (hd : 256 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) (v : BitVec 64) :
    word (m.writeW (off B d) v) B (8 * sCnt) = word m B (8 * sCnt) :=
  (writeW_outside m B v (d := d) (by omega_using [hd'])).word (by rw [show 8 * sCnt = 208 from rfl]; omega_using [hd])
    (by rw [show 8 * sCnt = 208 from rfl]; omega_using [])

/-! ## The pieces' code -/

/-- The first block after its reload of the count. -/
abbrev dR1 : List Instr := [.sub .x .x3 .x12 .x8, .lsl .x .x3 .x3 3, .add .x .x16 .x10 .x3,
  .subImm .x .x16 .x16 16, ld .x2 .x16 16, ld .x3 .x16 8, ld .x4 .x16, .lsl .x .x5 .x2 63, .lsr .x .x6 .x3 1,
  .logic .orr .x .x2 .x5 .x6, .lsl .x .x6 .x3 63, .lsr .x .x4 .x4 1, .logic .orr .x .x3 .x6 .x4, ldh .x5 sS0,
  .addImm .x .x6 .x0 (8 * sV)]

/-- The estimate, up to the count's reload. -/
abbrev dQ1 : List Instr := R2Div.quotMG ++ [.subs .x .x4 .x2 .x5, .adc .x .x4 .x7 .x7, .sub .x .x4 .x7 .x4,
  .logic .orr .x .x1 .x14 .x4, ldh .x9 sCnt]

/-- The window's low word, up to the count's reload. -/
abbrev dQ2a : List Instr := [.lsl .x .x3 .x9 4, .lsl .x .x4 .x12 3, .sub .x .x3 .x4 .x3, .subImm .x .x3 .x3 16,
  .add .x .x8 .x10 .x3, .mul .x .x3 .x1 .x1, .umulh .x4 .x1 .x1, ld .x5 .x8, .subs .x .x5 .x5 .x3, st .x5 .x8,
  .sbc .x .x6 .x7 .x7, .sub .x .x13 .x4 .x6, .addImm .x .x16 .x8 8]

abbrev dQ2 : List Instr := dQ2a ++ [ldh .x6 sCnt]

/-- `rowPtrs` after its reload of the count. -/
abbrev dQ3 : List Instr := [.lsr .x .x3 .x12 1, .sub .x .x3 .x3 .x6, .lsl .x .x3 .x3 3,
  .add .x .x17 .x11 .x3, movi .x2 0, .addImm .x .x14 .x6 1]

/-- A correction's head, up to the count's reload. -/
abbrev dCHa : List Instr := [.sub .x .x15 .x7 .x9, .logic .and .x .x4 .x1 .x15, .subImm .x .x5 .x1 1,
  .logic .and .x .x5 .x5 .x15, ld .x3 .x8, .adds .x .x3 .x3 .x4, .adc .x .x13 .x7 .x7, .adds .x .x3 .x3 .x5,
  .adc .x .x13 .x13 .x7, st .x3 .x8, .addImm .x .x16 .x8 8]

abbrev dCH : List Instr := dCHa ++ [ldh .x6 sCnt]

/-- The last block after its reload of the count. -/
abbrev dB4 : List Instr := [.lsr .x .x3 .x12 1, .sub .x .x3 .x3 .x9, .subImm .x .x3 .x3 1, .lsl .x .x3 .x3 3,
  .add .x .x3 .x11 .x3, st .x1 .x3, .addImm .x .x9 .x9 1, sth .x9 sCnt, .lsr .x .x3 .x12 1, .sub .x .x3 .x3 .x9]

abbrev dTop : List Instr := [ld .x3 .x16, .subs .x .x3 .x3 .x13, st .x3 .x16, .sbc .x .x5 .x7 .x7, .sub .x .x9 .x7 .x5]

abbrev dCT : List Instr := [ld .x3 .x16, .adds .x .x3 .x3 .x13, st .x3 .x16, .adc .x .x4 .x7 .x7, .sub .x .x1 .x1 .x9,
  movi .x5 1, .logic .eor .x .x4 .x4 .x5, .logic .and .x .x9 .x9 .x4]

theorem correct_eq : correct = seqs [.block (dCH ++ dQ3), countLoop .x14 corBody, .block dCT] := rfl

theorem digit_eq : digit = seqs [.block ([ldh .x8 sCnt] ++ dR1), .block (dQ1 ++ (dQ2 ++ dQ3)),
    countLoop .x14 msBody, .block dTop, correct, correct, correct, .block ([ldh .x9 sCnt] ++ dB4)] := rfl

/-! ## What each piece runs to -/

/-- After the first block: the reciprocal's address. -/
def P1 (p : DPar) (t : State) : Prop := DC p t ∧ t.gpr .x6 = off p.B (8 * sV)

/-- After the estimate: the window and the row pointers. -/
def P2 (p : DPar) (t : State) : Prop :=
  DC p t ∧ t.gpr .x8 = off p.B p.d ∧ t.gpr .x16 = off p.B (p.d + 8) ∧ t.gpr .x17 = off p.B p.e ∧ t.gpr .x2 = 0 ∧
    t.gpr .x14 = BitVec.ofNat 64 (p.m + 1)

/-- After the rows: the window's top word. -/
def P3 (p : DPar) (t : State) : Prop :=
  DC p t ∧ t.gpr .x8 = off p.B p.d ∧ t.gpr .x16 = off p.B (p.d + 8 + 8 * (p.m + 1))

/-- After the borrow and each correction: the sign. -/
def P4 (p : DPar) (t : State) : Prop :=
  DC p t ∧ t.gpr .x8 = off p.B p.d ∧ ∃ b : Bool, t.gpr .x9 = BitVec.ofNat 64 b.toNat

/-- After a correction's head. -/
def PC1 (p : DPar) (t : State) : Prop :=
  P2 p t ∧ ∃ b : Bool, t.gpr .x15 = mask b ∧ t.gpr .x9 = BitVec.ofNat 64 b.toNat

/-- After a correction's rows. -/
def PC2 (p : DPar) (t : State) : Prop := P3 p t ∧ ∃ b : Bool, t.gpr .x9 = BitVec.ofNat 64 b.toNat

/-- After a digit: the next count, and `x3` the digits left. -/
def P5 (p : DPar) (t : State) : Prop :=
  DC { p with m := p.m + 1 } t ∧ t.gpr .x3 = BitVec.ofNat 64 (p.W / 2 - (p.m + 1))

/-- A reload of the count: the cut's registers. -/
def PL (r : Reg) (p : DPar) (t : State) : Prop := DC p t ∧ t.gpr r = BitVec.ofNat 64 p.m

/-- After a reload in the middle of the estimate's block. -/
def PQ2 (p : DPar) (t : State) : Prop :=
  DC p t ∧ t.gpr .x6 = BitVec.ofNat 64 p.m ∧ t.gpr .x8 = off p.B p.d ∧ t.gpr .x16 = off p.B (p.d + 8)

theorem ldh_dc {p : DPar} {s : State} (h : DC p s) (hp : DS p) (r : Reg) (hr : r = .x8 ∨ r = .x9) :
    WP isa (.block [ldh r sCnt]) s (PL r p) := by
  have hl := h.scr.ld (show 8 * sCnt + 8 ≤ p.Z by have := hp.hH; rw [show 8 * sCnt = 208 from rfl]; omega_using [this])
  rcases hr with rfl | rfl
  · exact WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = BitVec.ofNat 64 p.m ∧ t.mem = s.mem)
      (by brun [h.x0, h.cnt, hdr_enc (show sCnt < 32 by decide), hl]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h8, hm⟩, k⟩ => ⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hm]), h8⟩
  · exact WP.mono (WP.keep [.x9] (Q := fun t => t.gpr .x9 = BitVec.ofNat 64 p.m ∧ t.mem = s.mem)
      (by brun [h.x0, h.cnt, hdr_enc (show sCnt < 32 by decide), hl]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h9, hm⟩, k⟩ => ⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hm]), h9⟩

/-- The bounds a digit's pieces need. -/
theorem DS.bnd {p : DPar} (hp : DS p) {s : State} (h : DC p s) :
    p.B.toNat + p.Z ≤ 2 ^ 64 ∧ 256 ≤ p.d ∧ p.d + 8 * (p.m + 3) ≤ p.Z ∧ p.e + 8 * (p.m + 1) ≤ p.Z ∧
      (p.e + 8 * (p.m + 1) ≤ p.d ∨ p.d + 8 * (p.m + 3) ≤ p.e) ∧ (p.d + 8 * (p.m + 3) ≤ p.eS ∨ p.eS + 8 * p.W ≤ p.d) := by
  have hn := h.scr.nowrap
  have := hp.hm1; have := hp.hW; have := hp.hR; have := hp.hR8; have := hp.hS; have := hp.hS8; have := hp.hRS
  simp only [DPar.d, DPar.e]
  omega_arith

theorem b1_dc {p : DPar} {s : State} (h : DC p s) (hp : DS p) :
    WP isa (.block ([ldh .x8 sCnt] ++ dR1)) s (P1 p) := by
  have := hp.hm1; have := hp.hW
  exact WP.mono (dLoad_ok (p := p.d + 8 * p.m) h.scr h.x0 h.x10 h.x12 (by simp only [DPar.d]; omega_using [this]) h.cnt hp.hm1
    (by omega_using [this]) hp.hW' hp.hH hp.hR hp.hR8) fun t ⟨⟨_, _, _, u6, um⟩, uk⟩ =>
    ⟨h.keep uk (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [um]), u6⟩

theorem q1_dc {p : DPar} {s : State} (h : P1 p s) (hp : DS p) : WP isa (.block dQ1) s (PL .x9 p) := by
  obtain ⟨h, h6⟩ := h
  have := hp.hH
  exact WP.mono (WP.keep [.x1, .x3, .x4, .x5, .x9, .x13, .x14, .x15, .x16, .x17]
    (Q := fun t => t.gpr .x9 = BitVec.ofNat 64 p.m ∧ t.mem = s.mem) (by
      brun [dQ1, h.x0, h.x7, h6, h.cnt, r2d_exec_tst, r2d_exec_cselc, CondCode.holds, R2Div.quotMG,
        hdr_enc (show sCnt < 32 by decide), h.scr.ld (show 8 * sV + 8 ≤ p.Z by simp only [sV, sFn]; omega_using [this]),
        h.scr.ld (show 8 * sCnt + 8 ≤ p.Z by rw [show 8 * sCnt = 208 from rfl]; omega_using [this])])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h9, hm⟩, k⟩ =>
    ⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hm]), h9⟩

/-- `x8 :=` the window's base, from `m` and `W`. -/
theorem win_eq {B : Addr} {eR W m : Nat} (hW : 2 * m + 2 ≤ W) (hW' : W < 2 ^ 24) :
    off B eR + (BitVec.ofNat 64 W <<< 3 - BitVec.ofNat 64 m <<< 4 - BitVec.ofNat 64 16) =
      off B (eR + (8 * W - 16 * m - 16)) := by
  rw [shl_ofNat (show W * 2 ^ 3 < 2 ^ 64 by omega_using [hW']), shl_ofNat (show m * 2 ^ 4 < 2 ^ 64 by omega_using [hW, hW']),
    ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW']), ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW']), off_add]
  congr 2; omega_using []

theorem q2_dc {p : DPar} {s : State} (h : PL .x9 p s) (hp : DS p) : WP isa (.block dQ2) s (PQ2 p) := by
  obtain ⟨h, h9⟩ := h
  obtain ⟨_, hd8, hdZ, -, -, -⟩ := hp.bnd h
  have := hp.hW; have := hp.hW'; have := hp.hR
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x8, .x13, .x16] (Q := fun t => t.gpr .x8 = off p.B p.d ∧
      t.gpr .x16 = off p.B (p.d + 8) ∧ word t.mem p.B (8 * sCnt) = BitVec.ofNat 64 p.m) (by
    brun [exec_sbc_x', h9, h.x7, h.x12, h.x10, win_eq (B := p.B) (eR := p.eR) hp.hW hp.hW', off_add,
      h.scr.ld (show p.d + 8 ≤ p.Z by omega_using [hdZ]), h.scr.st (show p.d + 8 ≤ p.Z by omega_using [hdZ]),
      cnt_writeW (B := p.B) hd8 (show p.d + 8 ≤ 2 ^ 64 by omega_arith), h.cnt])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h8, h16, hc⟩, k⟩ => ?_
  have ht : DC p t := h.keep k (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hc, h.cnt])
  have hl := ht.scr.ld (show 8 * sCnt + 8 ≤ p.Z by have := hp.hH; rw [show 8 * sCnt = 208 from rfl]; omega_using [this])
  exact WP.mono (WP.keep [.x6] (Q := fun u => u.gpr .x6 = BitVec.ofNat 64 p.m ∧ u.mem = t.mem)
    (by brun [ht.x0, ht.cnt, hdr_enc (show sCnt < 32 by decide), hl]) (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨h6, hm⟩, k'⟩ => ⟨ht.keep k' (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hm]), h6,
      by rw [k'.gpr .x8 (by decide), h8], by rw [k'.gpr .x16 (by decide), h16]⟩

theorem b2_dc {p : DPar} {s : State} (h : P1 p s) (hp : DS p) : WP isa (.block (dQ1 ++ (dQ2 ++ dQ3))) s (P2 p) := by
  obtain ⟨h, h6⟩ := h
  obtain ⟨hn, hd8, -, -, -, -⟩ := hp.bnd h
  exact WP.mono (dEst_ok h.scr h.x0 h.x7 h6 h.x12 h.x10 h.x11 h.cnt hp.hW hp.hW' hp.hR hp.hH hp.hR8)
    fun t ⟨⟨_, tm, _, a8, a16, a17, a2, a14⟩, k⟩ =>
    ⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [tm, cnt_writeW hd8 (by have := hp.hR; have := hp.hW; simp only [DPar.d] at *; omega_arith)]),
      a8, a16, a17, a2, a14⟩

theorem ms_dc {p : DPar} {s : State} (h : P2 p s) (hp : DS p) : WP isa (countLoop .x14 msBody) s (P3 p) := by
  obtain ⟨h, a8, a16, a17, a2, a14⟩ := h
  obtain ⟨hn, hd8, hdZ, heZ, hed, -⟩ := hp.bnd h
  have := hp.hW'; have := hp.hW
  exact WP.mono (msLoop_ok (n := p.m + 1) h.scr a16 a17 a14 a2 h.x7 (by omega_using []) (by omega_arith) (by omega_using [hdZ]) heZ
    (by omega_using [hed])) fun t ⟨_, _, o, k, t16, _⟩ =>
    ⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide)
      (o.word (by rw [show 8 * sCnt = 208 from rfl]; omega_using [hd8]) (by rw [show 8 * sCnt = 208 from rfl]; omega_using [])),
      by rw [k.gpr .x8 (by decide), a8], t16⟩

theorem top_dc {p : DPar} {s : State} (h : P3 p s) (hp : DS p) : WP isa (.block dTop) s (P4 p) := by
  obtain ⟨h, a8, a16⟩ := h
  obtain ⟨hn, hd8, hdZ, -, -, -⟩ := hp.bnd h
  exact WP.mono (dTop_ok h.scr h.x7 a16 (by omega_using [hdZ])) fun t ⟨⟨tm, t9⟩, k⟩ =>
    ⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [tm, cnt_writeW (by omega_using [hd8]) (by omega_using [hn, hdZ])]), by rw [k.gpr .x8 (by decide), a8], _, t9⟩

theorem ch_dc {p : DPar} {s : State} (h : P4 p s) (hp : DS p) : WP isa (.block dCH) s (PQ2 p) := by
  obtain ⟨h, a8, -⟩ := h
  obtain ⟨hn, hd8, hdZ, -, -, -⟩ := hp.bnd h
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x13, .x15, .x16] (Q := fun t =>
      t.gpr .x16 = off p.B (p.d + 8) ∧ word t.mem p.B (8 * sCnt) = BitVec.ofNat 64 p.m) (by
    brun [h.x7, a8, off_add, h.scr.ld (show p.d + 8 ≤ p.Z by omega_using [hdZ]), h.scr.st (show p.d + 8 ≤ p.Z by omega_using [hdZ]),
      cnt_writeW (B := p.B) hd8 (show p.d + 8 ≤ 2 ^ 64 by omega_using [hn, hdZ]), h.cnt])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16, hc⟩, k⟩ => ?_
  have ht : DC p t := h.keep k (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hc, h.cnt])
  have hl := ht.scr.ld (show 8 * sCnt + 8 ≤ p.Z by have := hp.hH; rw [show 8 * sCnt = 208 from rfl]; omega_using [this])
  exact WP.mono (WP.keep [.x6] (Q := fun u => u.gpr .x6 = BitVec.ofNat 64 p.m ∧ u.mem = t.mem)
    (by brun [ht.x0, ht.cnt, hdr_enc (show sCnt < 32 by decide), hl]) (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨h6, hm⟩, k'⟩ => ⟨ht.keep k' (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hm]), h6,
      by rw [k'.gpr .x8 (by decide), k.gpr .x8 (by decide), a8], by rw [k'.gpr .x16 (by decide), h16]⟩

theorem cb_dc {p : DPar} {s : State} (h : P4 p s) (hp : DS p) : WP isa (.block (dCH ++ dQ3)) s (PC1 p) := by
  obtain ⟨h, a8, b, h9⟩ := h
  obtain ⟨hn, hd8, hdZ, -, -, -⟩ := hp.bnd h
  exact WP.mono (cHead_ok (eS := p.eS) h.scr h.x0 h.x7 a8 h.x12 h.x11 h.cnt hp.hW hp.hW' hp.hH hd8 (by omega_using [hdZ]))
    fun t ⟨⟨tm, _, t15, t16, t17, t2, t14⟩, k⟩ =>
    ⟨⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [tm, cnt_writeW hd8 (by omega_using [hn, hdZ])]),
      by rw [k.gpr .x8 (by decide), a8], t16, t17, t2, t14⟩, b, by rw [t15, h9, neg_bit_mask],
      by rw [k.gpr .x9 (by decide), h9]⟩

theorem cl_dc {p : DPar} {s : State} (h : PC1 p s) (hp : DS p) : WP isa (countLoop .x14 corBody) s (PC2 p) := by
  obtain ⟨⟨h, a8, a16, a17, a2, a14⟩, b, h15, h9⟩ := h
  obtain ⟨hn, hd8, hdZ, heZ, hed, -⟩ := hp.bnd h
  have := hp.hW'; have := hp.hW
  exact WP.mono (corLoop_ok (n := p.m + 1) h.scr a16 a17 a14 a2 h.x7 h15 (by omega_using []) (by omega_arith) (by omega_using [hdZ]) heZ
    (by omega_using [hed])) fun t ⟨_, _, o, k, t16, _⟩ =>
    ⟨⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide)
      (o.word (by rw [show 8 * sCnt = 208 from rfl]; omega_using [hd8]) (by rw [show 8 * sCnt = 208 from rfl]; omega_using [])),
      by rw [k.gpr .x8 (by decide), a8], t16⟩, b, by rw [k.gpr .x9 (by decide), h9]⟩

theorem ct_dc {p : DPar} {s : State} (h : PC2 p s) (hp : DS p) : WP isa (.block dCT) s (P4 p) := by
  obtain ⟨⟨h, a8, a16⟩, b, h9⟩ := h
  obtain ⟨hn, hd8, hdZ, -, -, -⟩ := hp.bnd h
  exact WP.mono (cTail_ok h.scr h.x7 a16 (by omega_using [hdZ])) fun t ⟨⟨tm, _, t9⟩, k⟩ =>
    ⟨h.keep k (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [tm, cnt_writeW (by omega_using [hd8]) (by omega_using [hn, hdZ])]), by rw [k.gpr .x8 (by decide), a8], _,
      by rw [t9, h9, sign_clear]⟩

theorem cor_dc {p : DPar} {s : State} (h : P4 p s) (hp : DS p) : WP isa correct s (P4 p) := by
  rw [correct_eq]
  simp only [seqs]
  exact WP.seq (WP.mono (cb_dc h hp) fun t ht => WP.seq (WP.mono (cl_dc ht hp) fun u hu => ct_dc hu hp))

theorem b4_dc {p : DPar} {s : State} (h : P4 p s) (hp : DS p) : WP isa (.block ([ldh .x9 sCnt] ++ dB4)) s (P5 p) := by
  obtain ⟨h, -, -⟩ := h
  obtain ⟨hn, hd8, hdZ, -, -, -⟩ := hp.bnd h
  have := hp.hS; have := hp.hS8; have := hp.hW
  exact WP.mono (dNext_ok h.scr h.x0 h.x11 h.x12 h.cnt hp.hW hp.hW' hp.hH hp.hS) fun t ⟨⟨tm, t3⟩, k⟩ =>
    ⟨⟨h.scr.congr k.wr, (k.gpr .x0 (by decide)).trans h.x0, (k.gpr .x7 (by decide)).trans h.x7,
      (k.gpr .x10 (by decide)).trans h.x10, (k.gpr .x11 (by decide)).trans h.x11,
      (k.gpr .x12 (by decide)).trans h.x12, by rw [tm, word_writeW_self]⟩, t3⟩

/-! ## Leaking the same -/

/-- `P` and the bounds. -/
abbrev D (P : DPar → State → Prop) : DPar → State → Prop := fun p s => P p s ∧ DS p

/-- `c` leaks the same from `Φ`, and runs from `Φ p` to `Ψ p`. -/
def CTA (Φ Ψ : DPar → State → Prop) (c : Prog isa) : Prop :=
  RelCT isa (Two Φ) c (fun _ _ => True) ∧ ∀ p s, Φ p s → WP isa c s (Ψ p)

theorem CTA.seq {Φ Ψ Ξ : DPar → State → Prop} {c₁ c₂ : Prog isa} (h₁ : CTA Φ Ψ c₁) (h₂ : CTA Ψ Ξ c₂) :
    CTA Φ Ξ (.seq c₁ c₂) :=
  ⟨RelCT.seq (two_post h₁.1 h₁.2) h₂.1, fun p s h => WP.seq (WP.mono (h₁.2 p s h) fun t ht => h₂.2 p t ht)⟩

abbrev dcRegs : List Reg := [.x0, .x7, .x10, .x11, .x12]

/-- `DC`'s registers, and `ex` at `F p`. -/
theorem pins_D {P : DPar → State → Prop} (hdc : ∀ p s, P p s → DC p s) (ex : List Reg) (F : DPar → Reg → BitVec 64)
    (hex : ∀ p s, P p s → ∀ r ∈ ex, s.gpr r = F p r) : Pins (D P) (dcRegs ++ ex) := by
  intro p s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · have d₁ := hdc _ _ h₁.1
    have d₂ := hdc _ _ h₂.1
    simp only [dcRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [d₁.x0, d₂.x0]
    · rw [d₁.x7, d₂.x7]
    · rw [d₁.x10, d₂.x10]
    · rw [d₁.x11, d₂.x11]
    · rw [d₁.x12, d₂.x12]
  · rw [hex _ _ h₁.1 r hr, hex _ _ h₂.1 r hr]

theorem pins_D0 {P : DPar → State → Prop} (hdc : ∀ p s, P p s → DC p s) : Pins (D P) [.x0] :=
  fun p s₁ s₂ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr, (hdc _ _ h₁.1).x0, (hdc _ _ h₂.1).x0]

theorem e1_ct : CTA (D DC) (D P1) (.block ([ldh .x8 sCnt] ++ dR1)) := by
  refine ⟨RelCT.block_append (RelCT.seq (two_post (Ψ := D (PL .x8)) (two_taint [.x0] (pins_D0 fun _ _ h => h)
      (by taint_decide)) fun p s h => WP.mono (ldh_dc h.1 h.2 .x8 (.inl rfl)) fun t ht => ⟨ht, h.2⟩)
    (two_taint _ (pins_D (fun _ _ h => h.1) [.x8] (fun p _ => BitVec.ofNat 64 p.m)
      fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2) (by taint_decide))),
    fun p s h => WP.mono (b1_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩⟩

theorem e2_ct : CTA (D P1) (D P2) (.block (dQ1 ++ (dQ2 ++ dQ3))) := by
  refine ⟨RelCT.block_append (RelCT.seq (two_post (Ψ := D (PL .x9)) (two_taint _ (pins_D (fun _ _ h => h.1) [.x6]
      (fun p _ => off p.B (8 * sV)) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2) (by taint_decide))
      fun p s h => WP.mono (q1_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩)
    (RelCT.block_append (RelCT.seq (two_post (Ψ := D PQ2) (two_taint _ (pins_D (fun _ _ h => h.1) [.x9]
      (fun p _ => BitVec.ofNat 64 p.m) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2)
      (by taint_decide)) fun p s h => WP.mono (q2_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩)
    (two_taint _ (pins_D (fun _ _ h => h.1) [.x6, .x8, .x16]
      (fun p r => if r = .x6 then BitVec.ofNat 64 p.m else if r = .x8 then off p.B p.d else off p.B (p.d + 8))
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2) (by taint_decide))))),
    fun p s h => WP.mono (b2_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩⟩

theorem e3_ct : CTA (D P2) (D P3) (countLoop .x14 msBody) :=
  ⟨two_taint _ (pins_D (fun _ _ h => h.1) [.x14, .x16, .x17]
      (fun p r => if r = .x14 then BitVec.ofNat 64 (p.m + 1) else if r = .x16 then off p.B (p.d + 8) else off p.B p.e)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.2.2.2.2.2
        · exact h.2.2.1
        · exact h.2.2.2.1) (by taint_decide),
    fun p s h => WP.mono (ms_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩⟩

theorem e4_ct : CTA (D P3) (D P4) (.block dTop) :=
  ⟨two_taint _ (pins_D (fun _ _ h => h.1) [.x16] (fun p _ => off p.B (p.d + 8 + 8 * (p.m + 1)))
      fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.2) (by taint_decide),
    fun p s h => WP.mono (top_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩⟩

theorem e5_ct : CTA (D P4) (D P4) correct := by
  rw [correct_eq]
  show CTA (D P4) (D P4) (.seq (.block (dCH ++ dQ3)) (.seq (countLoop .x14 corBody) (.block dCT)))
  refine CTA.seq (Ψ := D PC1) ⟨RelCT.block_append (RelCT.seq (two_post (Ψ := D PQ2) (two_taint _ (pins_D (fun _ _ h => h.1) [.x8]
      (fun p _ => off p.B p.d) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.1) (by taint_decide))
      fun p s h => WP.mono (ch_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩)
    (two_taint _ (pins_D (fun _ _ h => h.1) [.x6, .x8, .x16]
      (fun p r => if r = .x6 then BitVec.ofNat 64 p.m else if r = .x8 then off p.B p.d else off p.B (p.d + 8))
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2) (by taint_decide))), fun p s h => WP.mono (cb_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩⟩ ?_
  refine CTA.seq (Ψ := D PC2) ⟨two_taint _ (pins_D (fun _ _ h => h.1.1) [.x14, .x16, .x17]
      (fun p r => if r = .x14 then BitVec.ofNat 64 (p.m + 1) else if r = .x16 then off p.B (p.d + 8) else off p.B p.e)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1.2.2.2.2.2
        · exact h.1.2.2.1
        · exact h.1.2.2.2.1) (by taint_decide),
    fun p s h => WP.mono (cl_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩⟩ ?_
  exact ⟨two_taint _ (pins_D (fun _ _ h => h.1.1) [.x16] (fun p _ => off p.B (p.d + 8 + 8 * (p.m + 1)))
      fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.1.2.2) (by taint_decide),
    fun p s h => WP.mono (ct_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩⟩

theorem e6_ct : CTA (D P4) (D P5) (.block ([ldh .x9 sCnt] ++ dB4)) :=
  ⟨RelCT.block_append (RelCT.seq (two_post (Ψ := D (PL .x9)) (two_taint [.x0] (pins_D0 fun _ _ h => h.1)
      (by taint_decide)) fun p s h => WP.mono (ldh_dc h.1.1 h.2 .x9 (.inr rfl)) fun t ht => ⟨ht, h.2⟩)
    (two_taint _ (pins_D (fun _ _ h => h.1) [.x9] (fun p _ => BitVec.ofNat 64 p.m)
      fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2) (by taint_decide))),
    fun p s h => WP.mono (b4_dc h.1 h.2) fun t ht => ⟨ht, h.2⟩⟩

/-- A digit leaks the same from `DC` at the same layout and count. -/
theorem digit_ct : CTA (D DC) (D P5) digit := by
  rw [digit_eq]
  exact e1_ct.seq (e2_ct.seq (e3_ct.seq (e4_ct.seq (e5_ct.seq (e5_ct.seq (e5_ct.seq e6_ct))))))

/-! ## The square root -/

/-- `setWid`, then `ws` and code the taint analysis checks from `x0`, `x12` and `x11`. -/
theorem setWid_ws_ct0 {w : Nat → Nat} {X : Pub → State → Prop} {Φ : Pub → State → Prop}
    (hΦ : ∀ a s, Φ a s → GC w X a s) {rest : List Instr} {body : Prog isa} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block rest) body) hc).isSome = true) :
    RelCT isa (Two Φ) (.seq (.block (setWid ++ (ws ++ rest))) body) fun _ _ => True :=
  RelCT.block_seq (RelCT.seq (two_post (Ψ := GC Wk XT) (two_taint [.x0] (pins_GC' hΦ) (by taint_decide))
    fun ⟨P, i⟩ s h => (hΦ _ s h).elim fun I m₀ c e g L _ => by
      subst e
      exact WP.mono (g.setWid_ok L.1) fun t ⟨g', _, _⟩ => ⟨I, m₀, c, rfl, g', L, trivial⟩)
    (ws_ct0 (fun a => a.1.B) (fun a => a.1.Z) (fun a => Wk a.1.k) (fun _ _ h => h.ws) ht))

/-- The root's array zero. -/
def zS (P : DP) (s : State) : Prop := wv s.mem P.B (slot (Wk P.k) wS) (Wk P.k) = 0

/-- A mask in `sZ`. -/
def XZ (a : Pub) (s : State) : Prop := ∃ b : Bool, word s.mem a.1.B (8 * sZ) = mask b

/-- The bounds of `c₂` (`sT1`) and `c` (`sC`). -/
abbrev bN (P : DP) : Nat := 64 * Wk P.k
abbrev bC (P : DP) : Nat := 32 * Wk P.k + 1

/-- What the square root carries from `norm` to its end. -/
abbrev XE (a : Pub) (s : State) : Prop := XS sC bC a s ∧ XZ a s

theorem XZ.frm {a : Pub} {s t : State} (x : XZ a s) {rs : List (Nat × Nat)} (f : Frm a.1.B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * sZ + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sZ) : XZ a t := by
  obtain ⟨b, hb⟩ := x
  exact ⟨b, (f.word_eq hr (by rw [show 8 * sZ = 248 from rfl]; omega_using [])).trans hb⟩

theorem XS.frm {sl : Nat} (hsl : sl < 32) {bnd : DP → Nat} {a : Pub} {s t : State} (x : XS sl bnd a s)
    {rs : List (Nat × Nat)} (f : Frm a.1.B rs s.mem t.mem) (hr : ∀ r ∈ rs, 8 * sl + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sl) :
    XS sl bnd a t := by
  obtain ⟨T, hT, hb, hT'⟩ := x
  exact ⟨T, (f.word_eq hr (by omega_using [hsl])).trans hT, hb, hT'⟩

theorem XZ.out {a : Pub} {s t : State} (x : XZ a s) {d n : Nat} (hd : 256 ≤ d)
    (o : Outside a.1.B d n s.mem t.mem) : XZ a t := by
  obtain ⟨b, hb⟩ := x
  exact ⟨b, (o.word (.inl (by rw [show 8 * sZ = 248 from rfl]; omega_using [hd])) (by rw [show 8 * sZ = 248 from rfl]; omega_using [])).trans hb⟩

theorem XZ.hdr {a : Pub} {s t : State} (x : XZ a s) (f : Frm a.1.B hdrW s.mem t.mem) : XZ a t := by
  obtain ⟨b, hb⟩ := x
  exact ⟨b, (hdrW_word f (by decide) (by decide) (by decide)).trans hb⟩

theorem stable_XZ {N : DP → Nat} {j : Nat} : Stable N j XZ := fun _ _ _ _ _ _ f ⟨b, hb⟩ =>
  ⟨b, (stage_word f (by decide) (by decide) (by decide)).trans hb⟩

theorem stable_zS {j : Nat} (hj : j = wX4) : Stable (fun P => nw P.k true) j fun a s => zS a.1 s :=
  fun ⟨P, i⟩ s t w X h f z => h.elim fun I m₀ c e g L _ => by
    subst e hj
    have hn := g.ws.scr.nowrap
    have := g.bndW L.1 (j := wS) (k := Wk I.k) (by decide) (by omega_using [])
    have f' : Frm I.B (hdrW ++ [(slot (Wk I.k) wX4, 8 * Wk I.k)]) s.mem t.mem := f
    show wv t.mem I.B (slot (Wk I.k) wS) (Wk I.k) = 0
    rw [f'.wv_eq (fun r hr => by
      have h256 := hdr_lt_slot (Wk I.k) wS (i := 31) (by decide)
      simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact .inr (by simp only [sW]; omega_using [h256])
      · exact .inr (by simp only [sArr]; omega_using [h256])
      · exact .inr (by simp only [sStride, sFn]; omega_using [h256])
      · left; dsimp only; simp only [slot, hdrBytes, wS, wX4]; omega_using []) (by omega_using [this])]
    exact z

/-- The pins of `norm`'s scan. -/
def fNs (a : Pub) (r : Reg) : BitVec 64 :=
  if r = .x0 then a.1.B else if r = .x16 then off a.1.B (slot (Wk a.1.k) wX4) else BitVec.ofNat 64 (Wk a.1.k)

theorem nPre_ct : CTW (GC Wk fun a s => zS a.1 s)
    (GC Wk fun a s => XS sT1 bN a s ∧ (XE a s ∧ zS a.1 s)) (seqs nPre) := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L z => ?_⟩
  · refine rel_pin (Ψ := fun _ _ => True) [.x0, .x12, .x14, .x16] fNs pins_GC (by taint_decide)
      (fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => ?_) (two_taint _ pins_of (by taint_decide))
    subst e
    exact WP.mono (nHead_ok g L.1) fun t ⟨_, _, x16, x12, x14, _⟩ => ⟨trivial, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [‹G I m₀ (Wk I.k) c t›.ws.x0]; rfl
      · rw [x12]; rfl
      · rw [x14]; rfl
      · rw [x16]; rfl⟩
  · subst e
    have hk1 := L.1.k1
    have hk2 := L.1.k2
    have hWk : Wk I.k < 300 := by simp only [Wk, vk]; omega_using [hk2]
    refine WP.mono (nPre_ok g L.1) fun t ⟨c2, gt, f, _, w1, wC, wZ, _, c2l, _⟩ =>
      ⟨I, m₀, c, rfl, gt, L, ⟨c2, w1, c2l, by omega_using [hWk, c2l]⟩, ⟨⟨c2 / 2, wC, by show c2 / 2 < 32 * Wk I.k + 1; omega_using [c2l],
        by omega_using [hWk, c2l]⟩, _, wZ⟩, ?_⟩
    have hn := g.ws.scr.nowrap
    have := gt.bndW L.1 (j := wS) (k := Wk I.k) (by decide) (by omega_using [])
    have z' : wv s.mem I.B (slot (Wk I.k) wS) (Wk I.k) = 0 := z
    show wv t.mem I.B (slot (Wk I.k) wS) (Wk I.k) = 0
    rw [f.wv_eq (fun r hr => by
      have h256 := hdr_lt_slot (Wk I.k) wS (i := 31) (by decide)
      simp only [npRanges, hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl
      · exact .inr (by simp only [sW]; omega_using [h256])
      · exact .inr (by simp only [sArr]; omega_using [h256])
      · exact .inr (by simp only [sStride, sFn]; omega_using [h256])
      all_goals exact .inr (by simp only [sT1, sC, sZ, sFn]; omega_using [h256])) (by omega_using [this])]
    exact z'

theorem norm_ct : CTW (GC Wk fun a s => zS a.1 s) (GC vk fun a s => XE a s ∧ zS a.1 s) norm := by
  rw [norm_eq]
  refine CTW.app (by simp) (by simp [shiftBy]) nPre_ct ((shiftBy_ct (sl := sT1) (bnd := bN) true true
    (stable_and (stable_and (stable_XS (by decide) (by decide) (by decide)) stable_XZ) (stable_zS rfl))
    (by decide) (by decide) (by decide) (by decide) (fun P T h => by simp only [nw, bN, ↓reduceIte] at *; omega_using [h])
    (by taints9) (by taints9) (by taints9) (by taints6) (by taints6)).mono (fun _ _ h => h) fun _ _ h => h.map
      fun x => x.2)

theorem first_ct : CTW (GC vk fun a s => XE a s ∧ zS a.1 s) (GC Wk XE) first := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨⟨xs, xz⟩, z⟩ => ?_⟩
  · show RelCT isa _ (.seq (.block (setWid ++ (ws ++ (base wX4 .x10 ++ base wS .x9 ++ [mov .x11 .x9, movi .x7 0] ++
      [.lsl .x .x3 .x12 3, .add .x .x16 .x10 .x3, .subImm .x .x16 .x16 16, ld .x2 .x16 8, ld .x3 .x16,
        movi .x1 0, movi .x4 0, movi .x5 0, movi .x14 64])))) _) _
    exact setWid_ws_ct0 (fun _ _ h => h) (by taint_decide)
  · subst e
    have hk1 := L.1.k1
    have hk2 := L.1.k2
    refine WP.mono (first_ok g L.1 z) fun t ⟨gt, f, _⟩ => ⟨I, m₀, c, rfl, gt, L,
      XS.frm (by decide) xs f fun r hr => ?_, XZ.frm xz f fun r hr => ?_⟩ <;>
    · have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
      have qS : slot (Wk I.k) wS = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
      have hW : 2 ≤ Wk I.k := by simp only [Wk, vk]; omega_using []
      simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl <;>
        simp only [sW, sArr, sStride, sS0, sV, sC, sZ, sFn] <;> omega_arith

/-- A digit's layout in the working space, at step `j`. -/
def dpar (a : Pub) (j : Nat) : DPar :=
  ⟨a.1.B, a.1.Z, slot (Wk a.1.k) wX4, slot (Wk a.1.k) wS, Wk a.1.k, j + 1⟩

/-- The digits after the first. -/
abbrev Nd (a : Pub) : Nat := Wk a.1.k / 2 - 1

theorem ds_dpar {I : RpIn} {i j : Nat} (L : RpLens I) (hj : j < Wk I.k / 2 - 1) :
    DS (dpar (dpub I, i) j) := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hZ := L.z
  refine ⟨by simp only [dpar]; omega_using [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [dpar, dpub, slot, hdrBytes, wX4, wS, Wk, vk] at * <;> omega_arith

theorem digits_ct : CTW (GC Wk XE) (GC Wk XE) digits := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨xs, xz⟩ => ?_⟩
  · refine RelCT.seq (two_post (Ψ := fun a t => 0 < Nd a ∧ D DC (dpar a 0) t) ?_ ?_) ?_
    · show RelCT isa _ (.block (setWid ++ (ws ++ (base wX4 .x10 ++ base wS .x9 ++ [mov .x11 .x9, movi .x7 0] ++
        [movi .x3 1, sth .x3 sCnt])))) _
      exact setWid_ws_rel (fun _ _ h => h) (by taint_decide)
    · intro ⟨P, i⟩ s h
      obtain ⟨I, m₀, c, e, g, L, -⟩ := h
      subst e
      have hk1 := L.1.k1
      have h0 : 0 < Wk I.k / 2 - 1 := by simp only [Wk, vk]; omega_using []
      exact WP.mono (dsHead_ok g L.1) fun t ⟨gt, _, x10, x11, x12, x7, _, cn, _⟩ =>
        ⟨h0, ⟨gt.ws.scr, gt.ws.x0, x7, x10, x11, x12, cn⟩, ds_dpar L.1 h0⟩
    refine (two_loop (Φ := fun a j t => D DC (dpar a j) t) (Ψ := fun _ _ => True) Nd
      (two_map (fun q => dpar q.1 q.2) (fun q s h => h.2) digit_ct.1) ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
    intro a j s hj h
    refine WP.mono (digit_ct.2 _ s h) fun t ⟨⟨dc, x3⟩, hp⟩ => ⟨?_, fun hl => ⟨dc, ?_⟩, fun _ => trivial⟩
    · have hW := hp.hW
      have hW' := hp.hW'
      simp only [dpar] at x3 hW hW'
      rw [VG.Proof.MlKem.AArch64.eval_nonzero, VG.Proof.MlKem.AArch64.ne_zero_iff, x3, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [hW'])]
      congr 1
      exact decide_eq_decide.mpr (by simp only [Nd] at hj ⊢; omega_using [])
    · have hp' := hp
      refine ⟨by simp only [dpar]; omega_using [], ?_, hp.hW', hp.hH, hp.hR, hp.hR8, hp.hS, hp.hS8, hp.hRS⟩
      have := hp.hW
      simp only [dpar, Nd] at this hl ⊢
      omega_using [hl]
  · subst e
    have hk1 := L.1.k1
    refine WP.mono (digits_ok g L.1) fun t ⟨gt, f, _⟩ => ⟨I, m₀, c, rfl, gt, L,
      XS.frm (by decide) xs f fun r hr => ?_, XZ.frm xz f fun r hr => ?_⟩ <;>
    · have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
      have qS : slot (Wk I.k) wS = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
      simp only [dsRanges, hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl <;>
        simp only [sW, sArr, sStride, sC, sZ, sFn, show 8 * sCnt = 208 from rfl] <;> omega_arith

/-- The remainder's OR, and `R = 0` where `X ≠ 0` and'ed into the mask. -/
theorem back1_ct : CTW (GC Wk XE) (GC Wk XE) (seqs [.block (sqBases ++ [mov .x16 .x10, movi .x9 0, mov .x14 .x12]),
    countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16],
    .block ([ldh .x3 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x9 .x9 .x3] ++
      andZero)]) := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨xs, xz⟩ => ?_⟩
  · show RelCT isa _ (.seq (.block (setWid ++ (ws ++ (base wX4 .x10 ++ base wS .x9 ++ [mov .x11 .x9, movi .x7 0] ++
      [mov .x16 .x10, movi .x9 0, mov .x14 .x12])))) _) _
    exact setWid_ws_ct0 (fun _ _ h => h) (by taint_decide)
  · subst e
    have hk1 := L.1.k1
    have hk2 := L.1.k2
    simp only [seqs]
    refine WP.seq (WP.mono (stHead_ok g L.1) fun s₁ ⟨g₁, f₁, x16, x9, x14, k₁⟩ => ?_)
    have hn := g₁.ws.scr.nowrap
    have hZW := g₁.ws.hZ
    have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
    have q16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
    refine WP.seq (WP.mono (orAll_ok g₁.ws.scr x16 x14 x9 (by simp only [Wk, vk]; omega_using [])
      (by simp only [Wk, vk]; omega_using [hk2]) (by omega_using [hZW, qX, q16])) fun s₂ ⟨m₂, _, k₂⟩ => ?_)
    have g₂ : G I m₀ (Wk I.k) c s₂ := g₁.same m₂ k₂ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x3, .x4, .x9] (Q := fun t => t.mem = s₂.mem) (by
      brun [g₂.ws.x0, hdr_enc (show sZ < 32 by decide), g₂.ws.scr.ld (d := 8 * sZ) (by
        rw [show 8 * sZ = 248 from rfl]; omega_using [hZW, q16])]) (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨m₃, k₃⟩ => ?_
    have g₃ : G I m₀ (Wk I.k) c s₃ := g₂.same m₃ k₃ (by decide)
    refine WP.mono (andZero_ok (z := s₃.gpr .x9 = 0) g₃.ws g₃.msk Iff.rfl) fun t ⟨⟨mt, _⟩, kt⟩ => ?_
    have o : Outside I.B (8 * Public.sMask) 8 s₃.mem t.mem := by
      rw [mt]; exact writeW_outside s₃.mem I.B _ (by simp only [Public.sMask, sFn]; omega_using [])
    have F : Frm I.B (hdrW ++ [(8 * Public.sMask, 8)]) s.mem t.mem :=
      (f₁.mono fun r hr => List.mem_append_left _ hr).trans (by
        rw [← m₂, ← m₃]; exact Frm.of_outside o (List.mem_append_right _ (List.mem_singleton_self _)))
    refine ⟨I, m₀, _, rfl, g₃.store mt kt (by decide), L, XS.frm (by decide) xs F fun r hr => ?_,
      XZ.frm xz F fun r hr => ?_⟩ <;>
    · simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl <;>
        simp only [sW, sArr, sStride, sC, sZ, Public.sMask, sFn] <;> omega_using []

/-- The narrow root, masked to zero where `X` is not a square. -/
theorem back4_ct : CTW (GC vk XZ) (GC vk XT) (seqs
    [.block (ws ++ base nY .x16 ++ [ldh .x15 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x15 .x15 .x4,
       mov .x14 .x12]),
     countLoop .x14 [ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x16, next .x16]]) :=
  wsop (rest := base nY .x16 ++ [ldh .x15 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x15 .x15 .x4,
      mov .x14 .x12]) (body := countLoop .x14 [ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x16, next .x16])
    (by simp only [seqs, List.append_assoc]) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨b, z⟩ => by
    subst e
    have hk1 := L.1.k1
    have hk2 := L.1.k2
    have hv1 : 1 ≤ vk I.k := by simp only [vk]; omega_using []
    have hn := g.ws.scr.nowrap
    have hZW := g.ws.hZ
    have qY : slot (vk I.k) nY = 256 + 4 * (8 * (vk I.k + 2)) := rfl
    have q16 : slot (vk I.k) 16 = 256 + 16 * (8 * (vk I.k + 2)) := rfl
    simp only [seqs]
    refine WP.seq ?_
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ws_ok g.ws.scr g.ws.x0 g.ws.h256 g.ws.hw g.ws.hS) fun s₉ ⟨⟨h12, h11, m₉, _⟩, k₉⟩ => ?_
    refine WP.mono (base_ok nY .x16 ((k₉.gpr .x0 (by decide)).trans g.ws.x0) h11) fun s₁₀ ⟨⟨h16, m₁₀, _⟩, k₁₀⟩ => ?_
    have hs₁₀ := g.ws.scr.congr (k₉.trans k₁₀).wr
    have z' : word s₁₀.mem I.B (8 * sZ) = mask b := by rw [m₁₀, m₉]; exact z
    refine WP.mono (WP.keep [.x4, .x14, .x15] (Q := fun t => t.gpr .x15 = mask (!b) ∧
        t.gpr .x14 = BitVec.ofNat 64 (vk I.k) ∧ t.mem = s₁₀.mem) (by
      brun [(k₁₀.gpr .x0 (by decide)).trans ((k₉.gpr .x0 (by decide)).trans g.ws.x0), hdr_enc (show sZ < 32 by decide),
        hs₁₀.ld (d := 8 * sZ) (by rw [show 8 * sZ = 248 from rfl]; omega_using [hZW, q16]), z', mask_xor_ones, k₁₀.get .x12, h12])
      (by decide) (by decide) (by decide +kernel)) fun s₁₁ ⟨⟨x15, x14', m₁₁⟩, k₁₁⟩ => ?_
    have m11 : s₁₁.mem = s.mem := by rw [m₁₁, m₁₀, m₉]
    have g₁₁ : G I m₀ (vk I.k) c s₁₁ := g.same m11 ((k₉.trans k₁₀).trans k₁₁) (by decide)
    exact WP.mono (maskAll_ok (d := slot (vk I.k) nY) g₁₁.ws.scr (by rw [k₁₁.get .x16]; exact h16) x14' x15 hv1
      (by simp only [vk]; omega_using [hk2]) (by omega_using [hZW, qY, q16])) fun t ⟨_, ot, kt⟩ =>
      ⟨I, m₀, c, rfl, g₁₁.out (by decide) (by omega_using []) ot kt (by decide), L, trivial⟩

theorem sqrt_ct : CTW (GC Wk XT) (GC vk XT) sqrt := by
  have e : sqrt = seqs ([.block setWid, zeroA wS, norm, first, digits] ++
      ([.block (sqBases ++ [mov .x16 .x10, movi .x9 0, mov .x14 .x12]),
        countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16],
        .block ([ldh .x3 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x3 .x3 .x4,
          .logic .and .x .x9 .x9 .x3] ++ andZero)] ++
      (shiftBy wS true false sC ++ ([.block setNar, zeroA nY, copyA nY (2 * wS)] ++
      [.block (ws ++ base nY .x16 ++ [ldh .x15 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x15 .x15 .x4,
         mov .x14 .x12]),
       countLoop .x14 [ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x16, next .x16]])))) := by
    simp only [sqrt, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine CTW.app (by simp) (by simp) ?_ (CTW.app (by simp) (by simp [shiftBy]) back1_ct
    (CTW.app (by simp [shiftBy]) (by simp) ((shiftBy_ct (sl := sC) (bnd := bC) (E := XZ) true false stable_XZ
      (by decide) (by decide) (by decide) (by decide) (fun P T h => by simp only [nw, bC, Wk, ↓reduceIte] at *; omega_using [h])
      (by taints9) (by taints9) (by taints9) (by taints6) (by taints6)).mono (fun _ _ h => h) fun _ _ h => h.map
        fun x => x.2) (CTW.app (by simp) (by simp) ?_ back4_ct)))
  · refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := fun a s => zS a.1 s) (by decide) (fun ⟨P, i⟩ s t h _ _ z => by
      obtain ⟨I, m₀, c, e, g, L, -⟩ := h
      subst e
      have z' : wv t.mem I.B (slot (Wk I.k) wS) (Wk I.k + 2) = 0 := z
      show wv t.mem I.B (slot (Wk I.k) wS) (Wk I.k) = 0
      rw [wv_low_of_lt (w := Wk I.k + 2) (by omega_using []) (by rw [z']; exact Nat.two_pow_pos _)]; exact z')
      (by taint_decide)) ?_
    refine CTW.cons (by simp) norm_ct ?_
    exact CTW.cons (by simp) first_ct (CTW.one digits_ct)
  · refine CTW.cons (by simp) (setNar_w (Y := XZ) fun _ _ _ h f _ => h.x.hdr f) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := XZ) (by decide) (fun _ _ _ h o _ _ => h.x.out (slot_ge _ _) o)
      (by taint_decide)) ?_
    exact CTW.one (copyA_w (Y := XZ) (by decide) (by decide) (by decide) (fun _ _ _ h o _ => h.x.out (slot_ge _ _) o)
      (by taint_decide))

end VG.Proof.Rsa.AArch64.Rd
