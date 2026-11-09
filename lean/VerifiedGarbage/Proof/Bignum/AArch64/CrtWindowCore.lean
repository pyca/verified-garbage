module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTableCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab

/-! A complete five-bit arithmetic window, generic over the proved table
selector so the scalar fallback and vector path share its arithmetic proof. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem TableCtx.base {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (h : TableCtx s P w mi X Xc) : CExpCtx s P w mi X Xc := by
  refine ⟨h.good, ?_, h.n, h.inv, h.x⟩
  simpa [off] using
    h.scrT.sub (o := 0) (n := slot w 8 + tabBytes w)
      (by unfold tabBytes CrtWindowFive.tabBytes32; omega)
      (by unfold slot hdrBytes; omega)

/-- An internal proof interface, retaining the current write set and ABI
obligations. It is not a new public specification or trusted declaration. -/
structure Selector where
  code : Prog isa
  ok : ∀ {t : State} {P : Addr} {wx : Nat} {mi : BitVec 64} {X Xc v : Nat},
    TableCtx t P wx mi X Xc → 2 ≤ wx → wx < 2 ^ 30 → v < 32 →
    word t.mem P (8 * Crt.sTab) = off P (slot wx 8) →
    word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v →
    WP isa code t fun t' => TableCtx t' P wx mi X Xc ∧
      wv t'.mem P (slot wx Crt.aT) wx = wv t.mem P (slot wx (8 + v)) wx ∧
      Frm P (selRanges wx) t.mem t'.mem ∧ Keep mmRegs t t'
  ct : RelCT isa (Two SelP) code (fun _ _ => True)

def Selector.scalar : Selector :=
  ⟨seqs VG.Impl.Rsa.AArch64.WindowFive.tabSelect32, tabSel_ok, tabSel_ct⟩

theorem selection_keeps_y {P : Addr} {w : Nat} {m m' : Mem}
    (hf : Frm P (selRanges w) m m') (hn : P.toNat + slot w 8 ≤ 2 ^ 64) :
    wv m' P (slot w aY) w = wv m P (slot w aY) w := by
  have hs := slot_sep (w := w) (show aY ≠ Crt.aT by decide)
  have hy := slot_le (w := w) (show aY < 8 by decide)
  exact hf.wv_eq (fun r hr => by
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only; omega
    · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot w aY (show 31 < 32 by decide); omega
    · simp only [Crt.sJ, sFn]; have := hdr_lt_slot w aY (show 31 < 32 by decide); omega) (by omega)

end VG.Proof.Bignum.AArch64.WindowFive
