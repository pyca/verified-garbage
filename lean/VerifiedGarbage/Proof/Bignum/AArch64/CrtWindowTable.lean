module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
public import VerifiedGarbage.Proof.Bignum.CrtWindowTable
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive

/-! Safety and correctness of the 32-entry scalar selection fallback,
including full-table reads and preservation of the Montgomery context. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)

/-! ## The prime's workspace -/

/-- What the exponentiation keeps in the workspace at `P` (`w_X` words) and
its table: the prime `X` (and its low word, for `-X⁻¹`), and `Xc`. -/
structure TableCtx (t : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) : Prop where
  good : Good t P (slot wx 8) wx minv
  scrT : Scr t P (slot wx 8 + VG.Proof.Bignum.CrtWindowFive.tabBytes32 wx)
  n : wv t.mem P (slot wx aN) wx = X
  inv : ((word t.mem P (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem P (slot wx Crt.aXc) wx = Xc

/-- `TableCtx` is `CExpCtx` for a table of 32 entries. -/
theorem TableCtx.toC {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) : CExpCtx t P wx minv X Xc 32 :=
  ⟨hc.good, hc.scrT, hc.n, hc.inv, hc.x⟩

theorem TableCtx.ofC {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc 32) : TableCtx t P wx minv X Xc :=
  ⟨hc.good, hc.scrT, hc.n, hc.inv, hc.x⟩

theorem TableCtx.ld {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) {i : Nat} (hi : i < 32) : InRegions (t.rd ++ t.wr) (off P (8 * i)) 8 :=
  hc.toC.ld hi

theorem TableCtx.st {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) {i : Nat} (hi : i < 32) : InRegions t.wr (off P (8 * i)) 8 :=
  hc.toC.st hi

/-- What changes only within the exponentiation's ranges keeps the context. -/
theorem TableCtx.of_frm {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) (hf : Frm P (VG.Proof.Bignum.CrtWindowFive.crtExpRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (h0 : t'.gpr .x0 = t.gpr .x0) : TableCtx t' P wx minv X Xc :=
  TableCtx.ofC (hc.toC.of_frm hf hwr h0)

theorem TableCtx.of_win {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) (hf : Frm P (crtWinRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (h0 : t'.gpr .x0 = t.gpr .x0) : TableCtx t' P wx minv X Xc :=
  TableCtx.ofC (hc.toC.of_win hf hwr h0)

/-- Advance the entry pointer by one full table entry. -/
theorem nextEnt_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) (hw : wx < 2 ^ 30) {e : Nat} (he : word t.mem P (8 * Crt.sEnt) = off P e) :
    WP isa nextEnt t fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sEnt)) (off P (e + 8 * (wx + 2))) ∧
      Keep [.x3, .x4] t t' :=
  VG.Proof.Bignum.AArch64.nextEnt_ok hc.toC hw he

/-- `toEnt a`: entry `j`, at `sEnt`, `:= [a]`. -/
theorem toEnt_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) {a j : Nat} (ha : a < 8) (hj : j < 32)
    (he : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + j))) :
    WP isa (seqs (toEnt a)) t fun t' => wv t'.mem P (slot wx (8 + j)) wx = wv t.mem P (slot wx a) wx ∧
      Outside P (slot wx (8 + j)) (8 * wx) t.mem t'.mem ∧ Keep mmRegs t t' :=
  VG.Proof.Bignum.AArch64.toEnt_ok hc.toC hw hw' ha hj he

/-- The selection's start: `sEnt := sTab`, `sJ := 0`. -/
theorem selInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) (ht : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)) :
    WP isa (.block [ldh .x3 Crt.sTab, sth .x3 Crt.sEnt, movi .x3 0, sth .x3 Crt.sJ]) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx 8))).writeW (off P (8 * Crt.sJ))
        (BitVec.ofNat 64 0) ∧ Keep [.x3] t t' :=
  VG.Proof.Bignum.AArch64.selInit_ok hc.toC ht

/-- The instructions that start reading entry `j`: its mask and the
selection's bases. -/
def selHead : List Instr :=
  [ldh .x3 Crt.sJ, ldh .x4 Crt.sNib, .logic .eor .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4, movi .x7 0] ++
    borrowMask ++ [ldh .x12 sW, ldh .x16 Crt.sEnt, ldh .x17 (sArr Crt.aT), mov .x14 .x12]

theorem selHead_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) {j v : Nat} (hj : j < 32) (hv : v < 32)
    (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hE : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + j))) :
    WP isa (.block selHead) t fun t' =>
      (t'.gpr .x15 = mask (decide (j = v)) ∧ t'.gpr .x14 = BitVec.ofNat 64 wx ∧
      t'.gpr .x16 = off P (slot wx (8 + j)) ∧ t'.gpr .x17 = off P (slot wx Crt.aT) ∧ t'.mem = t.mem) ∧
      Keep [.x3, .x4, .x7, .x12, .x14, .x15, .x16, .x17] t t' :=
  VG.Proof.Bignum.AArch64.selHeadN_ok hc.toC (by decide) hj hv hJ hN hE

/-- The entry's index up, and `x4 := j + 1 - 32`. -/
theorem selEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : TableCtx t P wx minv X Xc) {j : Nat} (hj : j < 32) (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j) :
    WP isa (.block [ldh .x3 Crt.sJ, .addImm .x .x3 .x3 1, sth .x3 Crt.sJ, .subImm .x .x4 .x3 32]) t fun t' =>
      (t'.mem = t.mem.writeW (off P (8 * Crt.sJ)) (BitVec.ofNat 64 (j + 1)) ∧
      ((t'.gpr .x4).toNat ≠ 0 ↔ j + 1 ≠ 32)) ∧ Keep [.x3, .x4] t t' :=
  VG.Proof.Bignum.AArch64.selEndN_ok hc.toC (by decide) hj hJ

/-- After `j` entries of the selection of entry `v` from `t₀`. -/
structure TabSelInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc v : Nat) (j : Nat) (t : State) :
    Prop where
  ctx : TableCtx t P wx minv X Xc
  nib : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + j))
  idx : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j
  val : wv t.mem P (slot wx Crt.aT) wx =
    if v < j then wv t₀.mem P (slot wx (8 + v)) wx else wv t₀.mem P (slot wx Crt.aT) wx
  frm : Frm P (selRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- The selection's loop body, as a list. -/
def selBody : List (Prog isa) :=
  [.block selHead, selLoop, nextEnt,
    .block [ldh .x3 Crt.sJ, .addImm .x .x3 .x3 1, sth .x3 Crt.sJ, .subImm .x .x4 .x3 32]]

theorem tabSelect_eq : VG.Impl.Rsa.AArch64.WindowFive.tabSelect32 = [.block [ldh .x3 Crt.sTab, sth .x3 Crt.sEnt, movi .x3 0, sth .x3 Crt.sJ],
    .loop (seqs selBody) (.nonzero .x .x4)] := rfl

/-- Entry `j` of the selection. -/
theorem selStep_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v j : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 32) (hj : j < 32) (hI : TabSelInv t₀ P wx minv X Xc v j t) :
    WP isa (seqs selBody) t fun t' =>
      TabSelInv t₀ P wx minv X Xc v (j + 1) t' ∧ ((t'.gpr .x4).toNat ≠ 0 ↔ j + 1 ≠ 32) :=
  WP.mono (VG.Proof.Bignum.AArch64.selStepN_ok hw hw' (by decide) hv hj
    ⟨hI.ctx.toC, hI.nib, hI.ent, hI.idx, hI.val, hI.frm, hI.keep⟩)
    fun _ ⟨h, hz⟩ => ⟨⟨TableCtx.ofC h.ctx, h.nib, h.ent, h.idx, h.val, h.frm, h.keep⟩, hz⟩

/-- The selection: `[aT] := T_v`. -/
theorem tabSel_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : TableCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 32)
    (ht : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (seqs VG.Impl.Rsa.AArch64.WindowFive.tabSelect32) t fun t' => TableCtx t' P wx minv X Xc ∧
      wv t'.mem P (slot wx Crt.aT) wx = wv t.mem P (slot wx (8 + v)) wx ∧
      Frm P (selRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  rw [tabSelect_eq]
  exact WP.mono (VG.Proof.Bignum.AArch64.tabSelN_ok hc.toC hw hw' (by decide) hv ht hN)
    fun _ ⟨c, v, f, k⟩ => ⟨TableCtx.ofC c, v, f, k⟩

end VG.Proof.Bignum.AArch64.WindowFive
