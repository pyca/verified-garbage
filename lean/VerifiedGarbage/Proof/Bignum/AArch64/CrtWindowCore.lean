module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTableCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp

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

/-- Five squares and one selected product give `x^(32 E + v) R`, while
the table and all caller-owned header slots remain available. -/
theorem windowCore_ok (M : Mont) (S : Selector) {t : State} {P : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x E v : Nat} {Q : Prop}
    (hc : TableCtx t P w mi X Xc) (ht : CrtWindowFive.CTab t.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv t.mem P (slot w aY) w < X)
    (hyv : Q → wv t.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hv : v < 32) (hnib : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.windowCore M.mm S.code) t fun u =>
      TableCtx u P w mi X Xc ∧ CrtWindowFive.CTab u.mem P w X Q x ∧
      wv u.mem P (slot w aY) w < X ∧
      (Q → wv u.mem P (slot w aY) w % X = x ^ (32 * E + v) * 2 ^ (64 * w) % X) ∧
      Frm P (crtWinRanges w) t.mem u.mem ∧ Keep mmRegs t u ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ →
        word u.mem P (8 * k) = word t.mem P (8 * k)) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.windowCore
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (crtSquares_ok M 4 hc.base hw hw' hR hy hyv)
    fun a ⟨_, hya, hva, hha, fa, ka⟩ => ?_
  have ca := hc.of_win fa ka.wr (ka.gpr .x0 (by decide))
  have ta := ht.of_win fa hc.scrT.nowrap
  simp only [seqs]
  refine WP.seq (WP.mono (S.ok ca hw hw' hv ta.tab
    (by rw [hha _ (by decide)]; exact hnib)) fun b ⟨cb, htb, fb, kb⟩ => ?_)
  have fb' := fb.mono (selRanges_sub w)
  have tb := ta.of_win fb' ca.scrT.nowrap
  have ey := selection_keeps_y fb ca.good.scr.nowrap
  refine WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := 32 * E) (v := v) cb.base hw hw' hR
    (by rw [htb]; exact ta.lt v hv)
    (by intro hQ; rw [ey]; exact hva hQ)
    (by intro hQ; rw [htb]; exact ta.val hQ v hv))
    fun c ⟨_, hyc, hvc, hhc, fc, kc⟩ => ?_
  refine ⟨cb.of_win fc kc.wr (kc.gpr .x0 (by decide)), tb.of_win fc cb.scrT.nowrap,
    hyc, hvc, (fa.trans fb').trans fc, ((ka.trans kb).trans kc).mono (by decide), ?_⟩
  intro k hk he hj
  rw [hhc k hk, fb.word_eq (fun r hr => by
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := hdr_lt_slot w Crt.aT hk; simp only; omega
    · simp only; omega
    · simp only; omega) (by
      have := hdr_lt_slot w 8 hk
      have := ca.good.scr.nowrap
      omega), hha k hk]

end VG.Proof.Bignum.AArch64.WindowFive
