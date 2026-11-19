module

import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivPre
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Bignum.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.CrtPRanges
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.X86_64.R2

/-! ### `Bignum.X86_64.PrivPre.R2`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_precompute` on x86-64: `R_X² mod X`

In a prime's workspace, `R² mod n = 2^(128 w) mod n` reduced chunk by chunk
(`redc_ok`: `[aY] R_X^K ≡ 2^(128 w) (mod X)` when `X` divides `n`), then
`r2X`: while `A = 64 w_X k + 128 w_X < 128 w`, one more reduction
(`fixIter_ok`), then `A - 128 w` doublings, which leave `R_X² mod X` in `aY`
(`fix_end`, `r2X_ok`, `r2At_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (r2X r2At r2Phase dbl link bW chunkWords fixStart fixStep fixStepB fixSub)

/-- What `r2X` changes in a prime's workspace. -/
def r2Ranges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx aY, 8 * (wx + 2)), (slot wx aAcc, 8 * (wx + 2)), (slot wx aTmp, 8 * (wx + 2)), (8 * sRem, 8),
    (8 * sD, 8)]

theorem r2Ranges_ok (wx : Nat) : ∀ r ∈ r2Ranges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  obtain a1 := slot_le (w := wx) (show aY < 8 by decide)
  obtain a2 := slot_le (w := wx) (show aAcc < 8 by decide)
  obtain a3 := slot_le (w := wx) (show aTmp < 8 by decide)
  obtain b1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  obtain b2 := hdr_lt_slot wx aAcc (show 31 < 32 by decide)
  obtain b3 := hdr_lt_slot wx aTmp (show 31 < 32 by decide)
  obtain b4 := hdr_lt_slot wx 0 (show 31 < 32 by decide)
  obtain b5 := slot_le (w := wx) (show 0 < 8 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [sRem, sD, sFn] <;> omega_arith

/-- The arrays `X` and 1 are outside what `r2X` changes. -/
theorem r2Ranges_arr (wx : Nat) {j : Nat} (hj : j = aN ∨ j = aOne) :
    ∀ r ∈ r2Ranges wx, slot wx j + 8 * wx ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  obtain hj8 : j < 8 := by rcases hj with rfl | rfl <;> decide
  obtain s1 := slot_sep (w := wx) (show j ≠ aY by rcases hj with rfl | rfl <;> decide)
  obtain s2 := slot_sep (w := wx) (show j ≠ aAcc by rcases hj with rfl | rfl <;> decide)
  obtain s3 := slot_sep (w := wx) (show j ≠ aTmp by rcases hj with rfl | rfl <;> decide)
  obtain b := hdr_lt_slot wx j (show 31 < 32 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [sRem, sD, sFn] at * <;> omega_arith

/-- `X` and 1 are kept by what keeps `r2X`'s ranges. -/
theorem xvals_r2 {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat} (hv : XVals s B o wx mx X)
    (hn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64) (hw : 1 ≤ wx) (f : Frm (off B o) (r2Ranges wx) s.mem t.mem) :
    XVals t B o wx mx X := by
  obtain rN := r2Ranges_arr wx (j := aN) (Or.inl rfl)
  obtain rO := r2Ranges_arr wx (j := aOne) (Or.inr rfl)
  obtain lN := slot_le (w := wx) (show aN < 8 by decide)
  obtain lO := slot_le (w := wx) (show aOne < 8 by decide)
  exact ⟨by rw [f.wv_eq rN (by omega_using [hn, lN])]; exact hv.n,
    by rw [f.word_eq (fun r h => by have := rN r h; omega_using [hw, this]) (by omega_using [hn, lN])]; exact hv.inv,
    by rw [f.wv_eq rO (by omega_using [hn, lO])]; exact hv.one⟩

theorem ofNat_dbl (a : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 a = BitVec.ofNat 64 (2 * a) := by
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem ofNat_sub' {a b : Nat} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [ha, hb]),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega_using [ha, hb]),
    Nat.mod_eq_of_lt (by omega_using [ha])]

section Blocks
variable {s : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64}

theorem hdr_ld (hc : SubCtx s B Z o w wx mx) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 :=
  hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_using [this])

theorem nW_ld (hc : SubCtx s B Z o w wx mx) : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 :=
  hc.scr.ld (by have := hdr_lt_slot w 8 (show sW < 32 by decide); have := hc.lo; have := hc.hi; omega_arith)

theorem sD_st (hc : SubCtx s B Z o w wx mx) : InRegions s.wr (off (off B o) (8 * sD)) 8 :=
  hc.good.scr.st (by have := hdr_lt_slot wx 8 (show sD < 32 by decide); omega_using [this])

/-- `link`: `r12 := B`. -/
theorem link_ok (hc : SubCtx s B Z o w wx mx) :
    WP isa (.block link) s fun t => t.gpr .r12 = B ∧ t.mem = s.mem ∧ Keep [.r12] s t := by
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = B ∧ t.mem = s.mem)
    (by xrun [link, State.ea, hdr, hc.rdi, hdrOff, hdr_ld hc (show sLink < 32 by decide), hc.link]) rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- `chunkWords`' first block: `rax := w_X`, `r12 := B`. -/
theorem chunkA_ok (hc : SubCtx s B Z o w wx mx) :
    WP isa (.block (([.mov .rax (.mem (hdr sW))] : List Instr) ++ link)) s fun t => t.gpr .rax = BitVec.ofNat 64 wx ∧
      t.gpr .r12 = B ∧ t.mem = s.mem ∧ Keep [.rax, .r12] s t := by
  refine WP.mono (WP.keep [.rax, .r12] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 wx ∧ t.gpr .r12 = B ∧
      t.mem = s.mem) (by
    xrun [link, List.cons_append, List.nil_append, State.ea, hdr, hc.rdi, hdrOff, hdr_ld hc (show sW < 32 by decide), hc.hdr.hw,
      hdr_ld hc (show sLink < 32 by decide), hc.link]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

/-- `chunkWords`' second block: `r12 := w`, `rcx := 0`. -/
theorem chunkB_ok (hc : SubCtx s B Z o w wx mx) (h12 : s.gpr .r12 = B) :
    WP isa (.block [.mov .r12 (.mem (Crt.ws .r12 sW)), .mov32 .rcx (.imm 0)]) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧ Keep [.r12, .rcx] s t := by
  refine WP.mono (WP.keep [.r12, .rcx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, Crt.ws, h12, hdrOff, nW_ld hc, hc.nw]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

/-- `fixStart`'s first block: `rcx := 64 rcx + 128 w_X`, `r12 := B`. -/
theorem fsA_ok (hc : SubCtx s B Z o w wx mx) {c : Nat} (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hax : s.gpr .rax = BitVec.ofNat 64 wx) :
    WP isa (.block (dbl .rcx 6 ++ dbl .rax 7 ++ ([.alu .add .rcx (.reg .rax)] : List Instr) ++ link)) s fun t =>
      t.gpr .rcx = BitVec.ofNat 64 (64 * c + 128 * wx) ∧ t.gpr .r12 = B ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .r12] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .r12] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (64 * c + 128 * wx) ∧
      t.gpr .r12 = B ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  simp only [dbl, link, List.replicate, List.cons_append, List.nil_append]
  xrun [State.ea, hdr, hc.rdi, hdrOff, hcx, hax, ← BitVec.ofNat_add, hdr_ld hc (show sLink < 32 by decide), hc.link]
  exact congrArg _ (by omega_using [])

/-- `fixStart`'s second block: `[sD] := rcx = A`, and `A < 128 w` in the carry. -/
theorem fsB_ok (hc : SubCtx s B Z o w wx mx) (h12 : s.gpr .r12 = B) {A : Nat}
    (hcx : s.gpr .rcx = BitVec.ofNat 64 A) (hb : A < 2 ^ 64) (hw : w < 2 ^ 20) :
    WP isa (.block (bW ++ ([.store (hdr sD) .rcx, .alu .cmp .rcx (.reg .r12)] : List Instr))) s fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * sD)) (BitVec.ofNat 64 A) ∧
      t.cf = some (decide (A < 128 * w)) ∧ Keep [.rcx, .r12] s t := by
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * sD)) (BitVec.ofNat 64 A) ∧
      t.cf = some (decide (A < 128 * w))) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  simp only [bW, dbl, List.replicate, List.cons_append, List.nil_append]
  xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, h12, nW_ld hc, hc.nw, ← BitVec.ofNat_add, hcx, sD_st hc]
  refine decide_eq_decide.mpr ?_
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega_using [hw])]
  omega_using []

/-- `fixStep`'s second block: `[sD] := A + 64 w_X`, and `A + 64 w_X < 128 w` in the carry. -/
theorem stB_ok (hc : SubCtx s B Z o w wx mx) (h12 : s.gpr .r12 = B) {A : Nat}
    (hA : word s.mem (off B o) (8 * sD) = BitVec.ofNat 64 A) (hb : A + 64 * wx < 2 ^ 64) (hw : w < 2 ^ 20) :
    WP isa (.block fixStepB) s fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * sD)) (BitVec.ofNat 64 (A + 64 * wx)) ∧
      t.cf = some (decide (A + 64 * wx < 128 * w)) ∧ Keep [.rcx, .r12] s t := by
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * sD)) (BitVec.ofNat 64 (A + 64 * wx)) ∧
      t.cf = some (decide (A + 64 * wx < 128 * w))) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  simp only [fixStepB, bW, dbl, List.replicate, List.cons_append, List.nil_append]
  xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, h12, nW_ld hc, hc.nw, hdr_ld hc (show sW < 32 by decide),
    hc.hdr.hw, hdr_ld hc (show sD < 32 by decide), hA, ← BitVec.ofNat_add, sD_st hc]
  refine ⟨congrArg _ (congrArg _ (by omega_using [])), decide_eq_decide.mpr ?_⟩
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb]), Nat.mod_eq_of_lt (by omega_using [hw])]
  omega_using []

/-- `fixSub`'s first block: `rcx := [sD] = A`, `r12 := B`. -/
theorem subA_ok (hc : SubCtx s B Z o w wx mx) {A : Nat} (hA : word s.mem (off B o) (8 * sD) = BitVec.ofNat 64 A) :
    WP isa (.block (([.mov .rcx (.mem (hdr sD))] : List Instr) ++ link)) s fun t => t.gpr .rcx = BitVec.ofNat 64 A ∧
      t.gpr .r12 = B ∧ t.mem = s.mem ∧ Keep [.rcx, .r12] s t := by
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 A ∧ t.gpr .r12 = B ∧
      t.mem = s.mem) (by
    xrun [link, List.cons_append, List.nil_append, State.ea, hdr, hc.rdi, hdrOff, hdr_ld hc (show sD < 32 by decide), hA,
      hdr_ld hc (show sLink < 32 by decide), hc.link]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

/-- `fixSub`'s second block: `rcx := A - 128 w`, zero exactly when `A = 128 w`. -/
theorem subB_ok (hc : SubCtx s B Z o w wx mx) (h12 : s.gpr .r12 = B) {A : Nat}
    (hcx : s.gpr .rcx = BitVec.ofNat 64 A) (hb : A < 2 ^ 64) (hAw : 128 * w ≤ A) (hw : w < 2 ^ 20) :
    WP isa (.block (bW ++ ([.alu .sub .rcx (.reg .r12)] : List Instr))) s fun t => t.gpr .rcx = BitVec.ofNat 64 (A - 128 * w) ∧
      t.zf = some (decide (A = 128 * w)) ∧ t.mem = s.mem ∧ Keep [.rcx, .r12] s t := by
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (A - 128 * w) ∧
      t.zf = some (decide (A = 128 * w)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  obtain e : BitVec.ofNat 64 (2 * (2 * (2 * (2 * (2 * (2 * (2 * w))))))) = BitVec.ofNat 64 (128 * w) :=
    congrArg _ (by omega_using [])
  obtain e2 : (BitVec.ofNat 64 (A - 128 * w) == 0) = decide (A = 128 * w) := by
    rw [← ofNat_sub' hb hAw]; exact ofNat_sub_beq hb (by omega_using [hw])
  simp only [bW, dbl, List.replicate, List.cons_append, List.nil_append]
  xrun [State.ea, Crt.ws, h12, hdrOff, nW_ld hc, hc.nw, hcx, ofNat_dbl, e, ofNat_sub' hb hAw, e2]

end Blocks

/-- `chunkWords`: `rax := w_X`, `r12 := w`, `rcx := K w_X`. -/
theorem chunk_ok {s : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} (hc : SubCtx s B Z o w wx mx)
    (hwx : 1 ≤ wx) (hwxw : wx ≤ w) (hw : w < 2 ^ 20) :
    WP isa (seqs chunkWords) s fun t => t.gpr .rax = BitVec.ofNat 64 wx ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rcx = BitVec.ofNat 64 ((w + wx - 1) / wx * wx) ∧ t.mem = s.mem ∧ Keep [.rax, .r12, .rcx] s t := by
  unfold chunkWords
  simp only [seqs]
  refine WP.seq (WP.mono (chunkA_ok hc) fun s₁ ⟨h1, h2, hm₁, k₁⟩ => ?_)
  obtain hc₁ := hc.of_frm (rs := []) (by rw [hm₁]; exact fun _ _ => rfl) (by simp) k₁.2.2 (k₁.gpr (by decide))
  refine WP.seq (WP.mono (chunkB_ok hc₁ h2) fun s₂ ⟨h3, h4, hm₂, k₂⟩ => ?_)
  obtain h1' : s₂.gpr .rax = BitVec.ofNat 64 wx := (k₂.gpr (by decide)).trans h1
  refine WP.mono (kLoop_ok hwx (by omega_using [hwx, hwxw]) (by omega_using [hwxw, hw]) h1' h3 h4) fun t ⟨hcx, hm', k⟩ =>
    ⟨(k.gpr (by decide)).trans h1', (k.gpr (by decide)).trans h3, hcx, (hm'.trans hm₂).trans hm₁,
      ((k₁.trans k₂).trans k).mono (by decide)⟩

/-- `fixStart`: `[sD] := A = 64 rcx + 128 w_X`, and `A < 128 w` in the carry. -/
theorem fixStart_ok {s : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} (hc : SubCtx s B Z o w wx mx)
    {c : Nat} (hcx : s.gpr .rcx = BitVec.ofNat 64 c) (hax : s.gpr .rax = BitVec.ofNat 64 wx)
    (hb : 64 * c + 128 * wx < 2 ^ 64) (hw : w < 2 ^ 20) :
    WP isa (seqs fixStart) s fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * sD)) (BitVec.ofNat 64 (64 * c + 128 * wx)) ∧
      t.cf = some (decide (64 * c + 128 * wx < 128 * w)) ∧ Keep [.rax, .rcx, .r12] s t := by
  unfold fixStart
  simp only [seqs]
  refine WP.seq (WP.mono (fsA_ok hc hcx hax) fun s₁ ⟨h1, h2, hm₁, k₁⟩ => ?_)
  obtain hc₁ := hc.of_frm (rs := []) (by rw [hm₁]; exact fun _ _ => rfl) (by simp) k₁.2.2 (k₁.gpr (by decide))
  refine WP.mono (fsB_ok hc₁ h2 h1 hb hw) fun t ⟨hm, hcf, k⟩ => ⟨by rw [hm, hm₁], hcf, (k₁.trans k).mono (by decide)⟩

/-- `fixStep`: `[sD] := A + 64 w_X`, and `A + 64 w_X < 128 w` in the carry. -/
theorem fixStep_ok {s : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} (hc : SubCtx s B Z o w wx mx)
    {A : Nat} (hA : word s.mem (off B o) (8 * sD) = BitVec.ofNat 64 A) (hb : A + 64 * wx < 2 ^ 64)
    (hw : w < 2 ^ 20) :
    WP isa fixStep s fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * sD)) (BitVec.ofNat 64 (A + 64 * wx)) ∧
      t.cf = some (decide (A + 64 * wx < 128 * w)) ∧ Keep [.rcx, .r12] s t := by
  unfold fixStep
  refine WP.seq (WP.mono (link_ok hc) fun s₁ ⟨h1, hm₁, k₁⟩ => ?_)
  obtain hc₁ := hc.of_frm (rs := []) (by rw [hm₁]; exact fun _ _ => rfl) (by simp) k₁.2.2 (k₁.gpr (by decide))
  refine WP.mono (stB_ok hc₁ h1 (by rw [hm₁]; exact hA) hb hw) fun t ⟨hm, hcf, k⟩ =>
    ⟨by rw [hm, hm₁], hcf, (k₁.trans k).mono (by decide)⟩

/-- `fixSub`: `rcx := A - 128 w`, zero exactly when `A = 128 w`. -/
theorem fixSub_ok {s : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} (hc : SubCtx s B Z o w wx mx)
    {A : Nat} (hA : word s.mem (off B o) (8 * sD) = BitVec.ofNat 64 A) (hb : A < 2 ^ 64) (hAw : 128 * w ≤ A)
    (hw : w < 2 ^ 20) :
    WP isa (seqs fixSub) s fun t => t.gpr .rcx = BitVec.ofNat 64 (A - 128 * w) ∧
      t.zf = some (decide (A = 128 * w)) ∧ t.mem = s.mem ∧ Keep [.rcx, .r12] s t := by
  unfold fixSub
  simp only [seqs]
  refine WP.seq (WP.mono (subA_ok hc hA) fun s₁ ⟨h1, h2, hm₁, k₁⟩ => ?_)
  obtain hc₁ := hc.of_frm (rs := []) (by rw [hm₁]; exact fun _ _ => rfl) (by simp) k₁.2.2 (k₁.gpr (by decide))
  refine WP.mono (subB_ok hc₁ h2 h1 hb hAw hw) fun t ⟨h, hz, hm, k⟩ =>
    ⟨h, hz, hm.trans hm₁, (k₁.trans k).mono (by decide)⟩

/-- What holds from `fixStart` on: `[sD] = A = 64 w_X k + 128 w_X` and
`[aY] R_X^k ≡ 2^(128 w)` when `Pr`. -/
structure FInv (Pr : Prop) (s t : State) (B : Addr) (Z o w wx : Nat) (mx : BitVec 64) (X k : Nat) : Prop where
  c : SubCtx t B Z o w wx mx
  v : XVals t B o wx mx X
  lt : wv t.mem (off B o) (slot wx aY) wx < X
  y : Pr → wv t.mem (off B o) (slot wx aY) wx * 2 ^ (64 * (k * wx)) % X = 2 ^ (128 * w) % X
  d : word t.mem (off B o) (8 * sD) = BitVec.ofNat 64 (64 * (k * wx) + 128 * wx)
  frm : Frm (off B o) (r2Ranges wx) s.mem t.mem
  keep : Keep mmRegs s t

/-- A store to `[sD]` keeps `r2X`'s context. -/
theorem sD_store {s t : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X : Nat} (hc : SubCtx s B Z o w wx mx)
    (hv : XVals s B o wx mx X) (hwx : 1 ≤ wx) {v : BitVec 64} (hm : t.mem = s.mem.writeW (off (off B o) (8 * sD)) v)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) :
    SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧ Frm (off B o) (r2Ranges wx) s.mem t.mem ∧
      word t.mem (off B o) (8 * sD) = v := by
  have hn := hc.good.scr.nowrap
  obtain f : Frm (off B o) (r2Ranges wx) s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [sD, sFn]; omega_using [])) (by simp [r2Ranges])
  exact ⟨hc.of_frm f (r2Ranges_ok wx) hwr hdi, xvals_r2 hv hn (by omega_using [hwx]) f, f, by rw [hm, word_writeW_self]⟩

/-- `FInv` once `[sD] := A` is stored, from `[aY] R_X^k ≡ 2^(128 w)` when `Pr`. -/
theorem finv_store {Pr : Prop} {s t : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X k : Nat}
    {rs : List Reg} (hc : SubCtx s B Z o w wx mx) (hv : XVals s B o wx mx X) (hwx : 1 ≤ wx)
    (hy : wv s.mem (off B o) (slot wx aY) wx < X)
    (hR : Pr → wv s.mem (off B o) (slot wx aY) wx * 2 ^ (64 * (k * wx)) % X = 2 ^ (128 * w) % X)
    (hm : t.mem = s.mem.writeW (off (off B o) (8 * sD)) (BitVec.ofNat 64 (64 * (k * wx) + 128 * wx)))
    (k' : Keep rs s t) (hrs : ∀ r ∈ rs, r ∈ mmRegs) (hdi : .rdi ∉ rs) : FInv Pr s t B Z o w wx mx X k := by
  obtain ⟨hc', hv', f', hd'⟩ := sD_store hc hv hwx hm k'.2.2 (k'.gpr hdi)
  obtain hy' : wv t.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
    rw [hm]
    have := hdr_lt_slot wx aY (show sD < 32 by decide)
    have := slot_le (w := wx) (show aY < 8 by decide)
    have := hc.good.scr.nowrap
    exact (writeW_outside _ _ _ (by simp only [sD, sFn]; omega_using [])).wv (by omega_arith) (by omega_arith)
  exact ⟨hc', hv', by rw [hy']; exact hy, fun hp => by rw [hy']; exact hR hp, hd', f', k'.mono hrs⟩

/-- After the reduction of one more step: `[aY] R_X^(k+1) ≡ 2^(128 w)` when
`Pr`, and `[sD]` still `A`. -/
structure FMid (Pr : Prop) (s t : State) (B : Addr) (Z o w wx : Nat) (mx : BitVec 64) (X k : Nat) : Prop where
  c : SubCtx t B Z o w wx mx
  v : XVals t B o wx mx X
  lt : wv t.mem (off B o) (slot wx aY) wx < X
  y : Pr → wv t.mem (off B o) (slot wx aY) wx * 2 ^ (64 * ((k + 1) * wx)) % X = 2 ^ (128 * w) % X
  d : word t.mem (off B o) (8 * sD) = BitVec.ofNat 64 (64 * (k * wx) + 128 * wx)
  frm : Frm (off B o) (r2Ranges wx) s.mem t.mem
  keep : Keep mmRegs s t

/-- `FMid` past a step that keeps the memory and the registers but `rs`. -/
theorem FMid.step {Pr : Prop} {s t t' : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X k : Nat}
    {rs : List Reg} (h : FMid Pr s t B Z o w wx mx X k) (hm : t'.mem = t.mem) (k' : Keep rs t t')
    (hrs : ∀ r ∈ rs, r ∈ mmRegs) (hdi : .rdi ∉ rs) : FMid Pr s t' B Z o w wx mx X k :=
  ⟨h.c.of_frm (rs := []) (by rw [hm]; exact fun _ _ => rfl) (by simp) k'.2.2 (k'.gpr hdi),
    ⟨by rw [hm]; exact h.v.n, by rw [hm]; exact h.v.inv, by rw [hm]; exact h.v.one⟩, by rw [hm]; exact h.lt,
    fun hp => by rw [hm]; exact h.y hp, by rw [hm]; exact h.d, by rw [hm]; exact h.frm,
    (h.keep.trans k').mono fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · exact hrs r hr⟩

/-- `FInv` past a step that keeps the memory and the registers but `rs`. -/
theorem FInv.step {Pr : Prop} {s t t' : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X k : Nat}
    {rs : List Reg} (h : FInv Pr s t B Z o w wx mx X k) (hm : t'.mem = t.mem) (k' : Keep rs t t')
    (hrs : ∀ r ∈ rs, r ∈ mmRegs) (hdi : .rdi ∉ rs) : FInv Pr s t' B Z o w wx mx X k :=
  ⟨h.c.of_frm (rs := []) (by rw [hm]; exact fun _ _ => rfl) (by simp) k'.2.2 (k'.gpr hdi),
    ⟨by rw [hm]; exact h.v.n, by rw [hm]; exact h.v.inv, by rw [hm]; exact h.v.one⟩, by rw [hm]; exact h.lt,
    fun hp => by rw [hm]; exact h.y hp, by rw [hm]; exact h.d, by rw [hm]; exact h.frm,
    (h.keep.trans k').mono fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · exact hrs r hr⟩

/-- One more reduction: `[aY] := [aY] R_X⁻¹ mod X`. -/
theorem mulY_ok (M : Mont) {Pr : Prop} {s t : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X k : Nat}
    (hI : FInv Pr s t B Z o w wx mx X k) (hX1 : 1 < X) (hwx2 : 2 ≤ wx) (hw : w < 2 ^ 20) (hwxw : wx ≤ w) :
    WP isa (M.mm aY aY aOne) t fun t₁ => FMid Pr s t₁ B Z o w wx mx X k := by
  have hc := hI.c
  have hv := hI.v
  have hg := hc.good
  have hn := hg.scr.nowrap
  refine WP.mono (M.mm_ok hg (Nat.le_refl _) hwx2 (by omega_using [hw, hwxw]) (o := aY) (a := aY) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv.inv (by rw [hv.n, hv.one]; exact hX1))
    fun t₁ ⟨_, hlt, hval, harr, k₁⟩ => ?_
  obtain f₁a : Frm (off B o) [(slot wx aY, 8 * (wx + 2)), (slot wx aAcc, 8 * (wx + 2)),
      (slot wx aTmp, 8 * (wx + 2))] t.mem t₁.mem := Frm.of_arrays harr (by simp)
  obtain f₁ : Frm (off B o) (r2Ranges wx) t.mem t₁.mem := f₁a.mono fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rcases h with rfl | rfl | rfl <;> simp
  obtain hd₁ : word t₁.mem (off B o) (8 * sD) = BitVec.ofNat 64 (64 * (k * wx) + 128 * wx) := by
    obtain b1 := hdr_lt_slot wx aY (show sD < 32 by decide)
    obtain b2 := hdr_lt_slot wx aAcc (show sD < 32 by decide)
    obtain b3 := hdr_lt_slot wx aTmp (show sD < 32 by decide)
    rw [f₁a.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Or.inl (by dsimp only; omega_arith))
      (by simp only [sD, sFn]; omega_using [])]
    exact hI.d
  rw [hv.n] at hlt hval
  rw [hv.one, Nat.mul_one] at hval
  refine ⟨hc.of_frm f₁ (r2Ranges_ok wx) k₁.2.2 (k₁.gpr (by decide)), xvals_r2 hv hn (by omega_using [hwx2]) f₁, hlt,
    fun hp => ?_, hd₁, hI.frm.trans f₁, (hI.keep.trans k₁).mono (by decide)⟩
  rw [show 64 * ((k + 1) * wx) = 64 * (k * wx) + 64 * wx by rw [Nat.add_mul, Nat.one_mul, Nat.mul_add], Nat.pow_add,
    ← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_mod, hval, ← Nat.mul_mod]
  exact hI.y hp

/-- `fixStep`'s second block, after the reduction: `[sD] := A + 64 w_X`. -/
theorem stepFin_ok {Pr : Prop} {s t : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X k : Nat}
    (hI : FMid Pr s t B Z o w wx mx X k) (h12 : t.gpr .r12 = B) (hwx : 1 ≤ wx) (hw : w < 2 ^ 20)
    (hA : 64 * (k * wx) + 128 * wx < 128 * w) :
    WP isa (.block fixStepB) t fun t' => FInv Pr s t' B Z o w wx mx X (k + 1) ∧
      t'.cf = some (decide (64 * ((k + 1) * wx) + 128 * wx < 128 * w)) := by
  refine WP.mono (stB_ok hI.c h12 hI.d (by omega_using [hw, hA]) hw) fun t' ⟨hm', hcf, k'⟩ => ?_
  obtain ⟨hc', hv', f', hd'⟩ := sD_store hI.c hI.v hwx hm' k'.2.2 (k'.gpr (by decide))
  obtain hy' : wv t'.mem (off B o) (slot wx aY) wx = wv t.mem (off B o) (slot wx aY) wx := by
    rw [hm']
    have := hdr_lt_slot wx aY (show sD < 32 by decide)
    have := slot_le (w := wx) (show aY < 8 by decide)
    have := hI.c.good.scr.nowrap
    exact (writeW_outside _ _ _ (by simp only [sD, sFn]; omega_using [])).wv (by omega_arith) (by omega_arith)
  refine ⟨⟨hc', hv', by rw [hy']; exact hI.lt, fun hp => by rw [hy']; exact hI.y hp, by rw [hd']; exact congrArg _ (by
      have := Nat.add_one_mul k wx; omega_using [this]), hI.frm.trans f', (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  rw [hcf]; exact congrArg _ (decide_eq_decide.mpr (by have := Nat.add_one_mul k wx; omega_using [this]))

/-- One more reduction: `[aY] := [aY] R_X⁻¹ mod X` and `[sD] := A + 64 w_X`. -/
theorem fixIter_ok (M : Mont) {Pr : Prop} {s t : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X k : Nat}
    (hI : FInv Pr s t B Z o w wx mx X k) (hX1 : 1 < X) (hwx2 : 2 ≤ wx) (hwxw : wx ≤ w)
    (hw : w < 2 ^ 20) (hA : 64 * (k * wx) + 128 * wx < 128 * w) :
    WP isa (.seq (M.mm aY aY aOne) fixStep) t fun t' => FInv Pr s t' B Z o w wx mx X (k + 1) ∧
      t'.cf = some (decide (64 * ((k + 1) * wx) + 128 * wx < 128 * w)) := by
  refine WP.seq (WP.mono (mulY_ok M hI hX1 hwx2 hw hwxw) fun t₁ h₁ => ?_)
  unfold fixStep
  refine WP.seq (WP.mono (link_ok h₁.c) fun t₂ ⟨h12, hm₂, k₂⟩ => ?_)
  exact stepFin_ok (h₁.step hm₂ k₂ (by decide) (by decide)) h12 (by omega_using [hwx2]) hw hA

/-- The arithmetic of the end: from `y R^k ≡ 2^(128 w)` and `c + 128 w = 64 w_X k + 128 w_X`,
`2^c y ≡ 2^(128 w_X)`. -/
theorem fix_end {X y k c w wx : Nat} (hXodd : X % 2 = 1)
    (h : y * 2 ^ (64 * (k * wx)) % X = 2 ^ (128 * w) % X) (hA : c + 128 * w = 64 * (k * wx) + 128 * wx) :
    2 ^ c * y % X = 2 ^ (128 * wx) % X := by
  apply VG.Proof.Bignum.mont_cancel (VG.Proof.Bignum.coprime_pow2 hXodd (64 * (k * wx)))
  rw [Nat.mul_assoc, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add, hA, Nat.add_comm]

/-- `r2X`: from `[aY] R_X^K ≡ 2^(128 w) (mod X)` when `Pr`, `[aY] := R_X² mod X`
when `Pr`, in the prime's workspace, keeping `X`, 1 and the workspace. -/
theorem r2X_ok (M : Mont) {Pr : Prop} {s : State} {B : Addr} {Z o w wx : Nat} {mx : BitVec 64} {X : Nat}
    (hc : SubCtx s B Z o w wx mx) (hv : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1) (hwx2 : 2 ≤ wx)
    (hwxw : wx ≤ w) (hw : w < 2 ^ 20) (hy : wv s.mem (off B o) (slot wx aY) wx < X)
    (hR : Pr → wv s.mem (off B o) (slot wx aY) wx * 2 ^ (64 * ((w + wx - 1) / wx * wx)) % X = 2 ^ (128 * w) % X) :
    WP isa (seqs (r2X M.mm)) s fun t => SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Pr → wv t.mem (off B o) (slot wx aY) wx = 2 ^ (128 * wx) % X) ∧ Frm (off B o) (r2Ranges wx) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hn := hg.scr.nowrap
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) (show 1 ≤ wx by omega_using [hwx2])
  generalize hK : (w + wx - 1) / wx = K at hR hK1 hK2
  unfold r2X
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [chunkWords]) (by simp [fixStart]) ?_
  refine WP.mono (chunk_ok hc (by omega_using [hwx2]) hwxw hw) fun s₁ ⟨hax₁, _, hcx₁, hm₁, k₁⟩ => ?_
  rw [hK] at hcx₁
  obtain hc₁ := hc.of_frm (rs := r2Ranges wx) (by rw [hm₁]; exact fun _ _ => rfl) (r2Ranges_ok wx) k₁.2.2
    (k₁.gpr (by decide))
  obtain hv₁ := xvals_r2 hv hn (by omega_using [hwx2]) (by rw [hm₁]; exact fun _ _ => rfl)
  refine wp_seqs_append (by simp [fixStart]) (by simp) ?_
  refine WP.mono (fixStart_ok hc₁ hcx₁ hax₁ (by omega_using [hwxw, hw, hK2]) hw) fun s₂ ⟨hm₂, hcf₂, k₂⟩ => ?_
  obtain ⟨hc₂, hv₂, f₂, hd₂⟩ := sD_store hc₁ hv₁ (by omega_using [hwx2]) hm₂ k₂.2.2 (k₂.gpr (by decide))
  obtain hI₂ : FInv Pr s s₂ B Z o w wx mx X K := by
    obtain hy₂ : wv s₂.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
      rw [hm₂, hm₁]
      have := hdr_lt_slot wx aY (show sD < 32 by decide)
      have := slot_le (w := wx) (show aY < 8 by decide)
      exact (writeW_outside _ _ _ (by simp only [sD, sFn]; omega_using [])).wv (by omega_arith) (by omega_using [hn, this])
    refine ⟨hc₂, hv₂, by rw [hy₂]; exact hy, fun hp => by rw [hy₂]; exact hR hp,
      by rw [hd₂], ?_, (k₁.trans k₂).mono (by decide)⟩
    obtain f₁ : Frm (off B o) (r2Ranges wx) s.mem s₁.mem := by rw [hm₁]; exact fun _ _ => rfl
    exact f₁.trans f₂
  -- The extra reductions, while `A < 128 w`.
  obtain hloop : WP isa (.ite .b (.loop (.seq (M.mm aY aY aOne) fixStep) .b) (.block [])) s₂ fun t =>
      ∃ k, 128 * w ≤ 64 * (k * wx) + 128 * wx ∧ 64 * (k * wx) + 128 * wx ≤ 128 * w + 64 * (K * wx) + 128 * wx ∧
        FInv Pr s t B Z o w wx mx X k := by
    by_cases hb : 64 * (K * wx) + 128 * wx < 128 * w
    · refine WP.ite true (by simp [eval, hcf₂, hb]) (fun _ => ?_) (by simp)
      refine WP.loop (M := isa) (fun n t => ∃ k, n = 128 * w - (64 * (k * wx) + 128 * wx) ∧
          64 * (k * wx) + 128 * wx < 128 * w ∧ FInv Pr s t B Z o w wx mx X k) ?_ _ s₂
        ⟨K, rfl, by omega_using [hb], hI₂⟩
      rintro n t ⟨k, rfl, hk, hI⟩
      refine WP.mono (fixIter_ok M hI hX1 hwx2 hwxw hw hk) fun t' ⟨hI', hcf'⟩ => ?_
      by_cases hb' : 64 * ((k + 1) * wx) + 128 * wx < 128 * w
      · exact .inr ⟨by simp [eval, hcf', hb'], _, by have := Nat.add_one_mul k wx; omega_using [hwx2, hk, this], k + 1, rfl, hb', hI'⟩
      · exact .inl ⟨by simp [eval, hcf', hb'], k + 1, by omega_using [hb'], by have := Nat.add_one_mul k wx; omega_using [hk, this], hI'⟩
    · exact WP.ite false (by simp [eval, hcf₂, hb]) (by simp) (fun _ => WP.block_nil
        ⟨K, by omega_using [hb], by omega_using [], hI₂⟩)
  refine wp_seqs_append (by simp) (by simp [fixSub]) ?_
  refine WP.mono hloop fun s₃ ⟨k, hk1, hk2, hI₃⟩ => ?_
  -- `rcx := A - 128 w`, the doublings left.
  refine wp_seqs_append (by simp [fixSub]) (by simp) ?_
  refine WP.mono (fixSub_ok hI₃.c hI₃.d (by omega_using [hwxw, hw, hK2, hk2]) hk1 hw) fun s₄ ⟨hcx₄, hz₄, hm₄, k₄⟩ => ?_
  obtain hc₄ := hI₃.c.of_frm (rs := r2Ranges wx) (by rw [hm₄]; exact fun _ _ => rfl) (r2Ranges_ok wx) k₄.2.2
    (k₄.gpr (by decide))
  obtain hv₄ := xvals_r2 hI₃.v hn (by omega_using [hwx2]) (by rw [hm₄]; exact fun _ _ => rfl)
  obtain f₄ : Frm (off B o) (r2Ranges wx) s.mem s₄.mem := by rw [hm₄]; exact hI₃.frm
  obtain hk₄ : Keep mmRegs s s₄ := (hI₃.keep.trans k₄).mono (by decide)
  by_cases hz : 64 * (k * wx) + 128 * wx = 128 * w
  · refine WP.ite true (by simp [eval, hz₄, hz]) (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨hc₄, hv₄, by rw [hm₄]; exact hI₃.lt, fun hp => ?_, f₄, hk₄⟩
    rw [hm₄, ← Nat.mod_eq_of_lt hI₃.lt, ← Nat.one_mul (wv _ _ _ _), ← Nat.pow_zero 2]
    exact fix_end hXodd (hI₃.y hp) (by omega_using [hz])
  refine WP.ite false (by simp [eval, hz₄, hz]) (by simp) (fun _ => ?_)
  have hg₄ := hc₄.good
  refine WP.mono (doubles_ok hg₄.scr hg₄.rdi hg₄.hdr (Nat.le_refl _) hwx2 (by omega_using [hwxw, hw]) (mo := aN) (acc := aAcc)
    (tmp := aTmp) (o := aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (sl := sRem) (by decide) (by decide)
    (c := 64 * (k * wx) + 128 * wx - 128 * w) (by omega_using [hk1, hz]) (by omega_using [hwxw, hw, hK2, hk2]) hcx₄
    (by rw [hv₄.n, hm₄]; exact hI₃.lt)) fun t ⟨hyt, ft, _, kt⟩ => ?_
  obtain f₅ : Frm (off B o) (r2Ranges wx) s₄.mem t.mem := ft.mono fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rcases h with rfl | rfl | rfl | rfl <;> simp
  obtain hct := hc₄.of_frm f₅ (r2Ranges_ok wx) kt.2.2 (kt.gpr (by decide))
  obtain hvt := xvals_r2 hv₄ hn (by omega_using [hwx2]) f₅
  rw [hv₄.n] at hyt
  refine ⟨hct, hvt, by rw [hyt]; exact Nat.mod_lt _ (by omega_using [hX1]), fun hp => ?_, f₄.trans f₅, (hk₄.trans kt).mono (by decide)⟩
  rw [hyt, hm₄]
  exact fix_end hXodd (hI₃.y hp) (by omega_using [hk1])

/-- `r2At sl`: into the prime's workspace (its base in slot `sl`), `R² mod n`
reduced chunk by chunk into `aY`, `r2X`, and back. -/
theorem r2At_ok (M : Mont) {s : State} {B : Addr} {Z w o wx : Nat} {minv mx : BitVec 64} {N X sl : Nat}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw20 : w < 2 ^ 20) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hwx2 : 2 ≤ wx) (hwxw : wx ≤ w) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx)
    (hN : NVals s B w minv N) (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hXodd : X % 2 = 1) :
    WP isa (seqs (r2At M.mm sl)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (X ∣ N → wv t.mem (off B o) (slot wx aY) wx = 2 ^ (128 * wx) % X) ∧
      Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain ho64 : o < 2 ^ 64 := by omega
  obtain hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  unfold r2At
  simp only [List.append_assoc]
  -- Into the prime's workspace.
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl) fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_
  obtain hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo (hi_of_wsTab hhi)
  obtain hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  -- `[aXc] R_X^K ≡ R² mod n (mod X)`.
  refine wp_seqs_append (by simp [redc]) (by simp [copyArr]) ?_
  refine WP.mono (redc_ok M hc₁ hX₁ hwx2 hwxw (by omega) hX1 (j := aR2) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, hv₂, f₂, k₂⟩ => ?_
  refine wp_seqs_append (by simp [copyArr]) (by simp [r2X]) ?_
  refine WP.mono (copyArr_ok hc₂.good (Nat.le_refl _) (by omega) (by omega) (o := aY) (a := aXc)
    (by decide) (by decide) (by decide)) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_
  obtain f₃ : Frm (off B o) (r2Ranges wx) s₂.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot wx aY) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp [r2Ranges])
  obtain hc₃ := hc₂.of_frm f₃ (r2Ranges_ok wx) k₃.2.2 (k₃.gpr (by decide))
  obtain hX₃ := xvals_r2 hX₂ hc₂.good.scr.nowrap (by omega) f₃
  refine wp_seqs_append (by simp [r2X]) (by simp) ?_
  refine WP.mono (r2X_ok M (Pr := X ∣ N) hc₃ hX₃ hX1 hXodd hwx2 hwxw hw20 (by rw [hv₃]; exact hlt₂) (fun hd => by
      rw [hv₃, show 64 * ((w + wx - 1) / wx * wx) = 64 * wx * ((w + wx - 1) / wx) by
        rw [Nat.mul_assoc, Nat.mul_comm wx], hv₂, hm₁, ← Nat.mod_mod_of_dvd _ hd, hN.r2, Nat.mod_mod_of_dvd _ hd, ← Nat.pow_add]
      exact congrArg (· % X) (congrArg _ (by omega))))
    fun s₄ ⟨hc₄, hX₄, hlt₄, hy₄, f₄, k₄⟩ => ?_
  -- Back to the modulus'.
  obtain hl₄ : InRegions (s₄.rd ++ s₄.wr) (off (off B o) (8 * sLink)) 8 :=
    hc₄.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₄.mem)
    (by xrun [leave, State.ea, hdr, hc₄.rdi, hdrOff, hl₄, hc₄.link]) rfl) fun t ⟨⟨hdi, hm⟩, k₅⟩ => ?_
  obtain fx : Frm B [xRange o wx] s₁.mem t.mem := by
    rw [hm]
    exact ((f₂.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)).trans
      (f₃.to_x (r2Ranges_ok wx) hoL (List.mem_singleton_self _))).trans
      (f₄.to_x (r2Ranges_ok wx) hoL (List.mem_singleton_self _))
  obtain fx' : Frm B [xRange o wx] s.mem t.mem := by rw [← hm₁]; exact fx
  obtain kall := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  obtain hb : ∀ d, d + 8 ≤ o → word t.mem B d = word s.mem B d := fun d hd => fx'.x_below hd ho64
  have hH := hg.hdr
  refine ⟨⟨hs.congr kall.2.2, hdi, ?_⟩, by rw [hm]; exact hc₄.ws,
    ⟨by rw [hm]; exact hX₄.n, by rw [hm]; exact hX₄.inv, by rw [hm]; exact hX₄.one⟩, by rw [hm]; exact hlt₄,
    fun hp => by rw [hm]; exact hy₄ hp, fx'.mono fun r h => List.mem_append_right _ h, ⟨fun r hr => ?_, kall.2⟩⟩
  · exact ⟨(hb _ (by unfold sW; omega)).trans hH.hw, (hb _ (by unfold sMinv; omega)).trans hH.hminv,
      fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (hH.harr j hj)⟩
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by revert hr h; cases r <;> decide)

/-- After `R_p² mod p` and `R_q² mod q`: `n`'s values, the mask, and the
primes' `aY`. -/
structure R2Done (σ t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  msk : word t.mem B (8 * sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  py : M = true → wv t.mem (off B (offP w)) (slot (wsWords pl) aY) (wsWords pl) = 2 ^ (128 * wsWords pl) % P
  qy : M = true → wv t.mem (off B (offQ w pl)) (slot (wsWords ql) aY) (wsWords ql) = 2 ^ (128 * wsWords ql) % Q
  hfix : HFix B σ.mem t.mem
  iscr : InScr B Z σ.mem t.mem
  keep : Keep mmRegs σ t

/-- After `R_p² mod p`: as after the checks, and `p`'s `aY`. -/
structure R2Mid (σ t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  msk : word t.mem B (8 * sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  py : M = true → wv t.mem (off B (offP w)) (slot (wsWords pl) aY) (wsWords pl) = 2 ^ (128 * wsWords pl) % P
  qxv : XVals t B (offQ w pl) (wsWords ql) mq (if M then Q else 3)
  hfix : HFix B σ.mem t.mem
  iscr : InScr B Z σ.mem t.mem
  keep : Keep mmRegs σ t

/-- `R_p² mod p`, from what the checks leave. -/
theorem r2P_ok (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (r2At M.mm sWsP)) t₀ fun t => R2Mid s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain hw8 : 8 ≤ (k + 7) / 8 := by omega_using [hk1]
  obtain hw28 : (k + 7) / 8 < 2 ^ 20 := by omega_using [hk2]
  obtain hpw : pl < 8 * ((k + 7) / 8) := by omega_using [hpl2]
  generalize (k + 7) / 8 = w at *
  obtain ⟨hMk', hP', -⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  obtain hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_using []
  obtain hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_using []
  obtain hwpw : wsWords pl ≤ w := wsWords_le (by omega_using [hpw]) (by omega_using [hw8])
  obtain hloP : slot w 8 ≤ offP w := Nat.le_refl _
  obtain hhiP : offP w + slot (wsWords pl) 8 + wsTab (wsWords pl) ≤ Z := by unfold offQ at hZq; unfold offP; omega_using [hZq]
  have hPQ : offP w + slot (wsWords pl) 8 + wsTab (wsWords pl) = offQ w pl := rfl
  obtain hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hn, hloP, hhiP]
  refine WP.mono (r2At_ok M hr.good (by omega_using [hw8]) (by omega_using [hw28]) hloP hhiP hwp2 hwpw (by decide)
    hr.wsP hr.pws hr.nv hr.pxv hP'.1 hP'.2)
    fun t₁ ⟨hg₁, hpws₁, _, _, hpy₁, f₁, k₁⟩ => ?_
  obtain f₁' : Frm B (pRanges w ++ [xRange (offP w) (wsWords pl)]) t₀.mem t₁.mem :=
    f₁.mono fun r hr => (List.mem_append.mp hr).elim
      (fun h' => List.mem_append_left _ (List.mem_append_left _ h')) (fun h' => List.mem_append_right _ h')
  obtain hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ sCnt → word t₁.mem B (8 * i) = word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => Frm.gx_hdr f₁ hloP hi h1 h2
  obtain hq₁ : ∀ d, offQ w pl ≤ d → d + 8 ≤ Z → word t₁.mem B d = word t₀.mem B d := fun d hd hd' =>
    f₁'.word_eq (fun r hr => Or.inr (by have := pxR_bound hloP r hr; omega_using [hPQ, hd, this])) (by omega_using [hn, hd'])
  obtain hqw : ∀ i < 32, word t₁.mem (off B (offQ w pl)) (8 * i) = word t₀.mem (off B (offQ w pl)) (8 * i) :=
    fun i hi => by rw [word_off, word_off]; exact hq₁ _ (by omega_using []) (by omega_using [hZq, hQ8, hi])
  obtain hqv : ∀ d m, d + 8 * m ≤ slot (wsWords ql) 8 → wv t₁.mem (off B (offQ w pl)) d m =
      wv t₀.mem (off B (offQ w pl)) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hq₁ _ (by omega_using []) (by omega_using [hZq, hd, hi])
  obtain lN := slot_le (w := wsWords ql) (show aN < 8 by decide)
  obtain lO := slot_le (w := wsWords ql) (show aOne < 8 by decide)
  exact ⟨hg₁, hr.nv.of_frm f₁ hloP hz (by omega_using [hw8]),
    by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.msk,
    by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP,
    by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ,
    hpws₁, hr.qws.of_words fun i hi => hqw i (by omega_using [hi]),
    fun hm => by
      obtain ⟨_, hpq, _⟩ := hMk' hm
      have := hpy₁ ⟨Q, by simp only [hm, ↓reduceIte]; exact hpq.symm⟩
      simpa only [hm, ↓reduceIte] using this,
    ⟨by rw [hqv _ _ (by omega_using [lN])]; exact hr.qxv.n,
      by rw [word_off, hq₁ _ (by omega_using []) (by omega_using [hZq, lN]), ← word_off]; exact hr.qxv.inv,
      by rw [hqv _ _ (by omega_using [lO])]; exact hr.qxv.one⟩,
    hr.hfix.trans fun i hi hf => by
      obtain h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
      obtain h2 : i ≠ sCnt := by rintro rfl; revert hf; decide
      exact hb₁ i hi h1 h2,
    hr.iscr.trans (InScr.of_frm f₁' fun r hr => by have := pxR_bound hloP r hr; omega_using [hhiP, this]),
    (hr.keep.trans k₁).mono (by decide)⟩

/-- `R_q² mod q`, after `p`'s. -/
theorem r2Q_ok (M : Mont) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : R2Mid s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (r2At M.mm sWsQ)) t₁ fun t => R2Done s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain hw8 : 8 ≤ (k + 7) / 8 := by omega_using [hk1]
  obtain hw28 : (k + 7) / 8 < 2 ^ 20 := by omega_using [hk2]
  obtain hqw' : ql < 8 * ((k + 7) / 8) := by omega_using [hql2]
  generalize (k + 7) / 8 = w at *
  obtain ⟨hMk', -, hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  obtain hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_using []
  obtain hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_using []
  obtain hwqw : wsWords ql ≤ w := wsWords_le (by omega_using [hqw']) (by omega_using [hw8])
  obtain hloQ : slot w 8 ≤ offQ w pl := by unfold offQ; omega_using []
  obtain hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZq, hn, hloQ]
  refine WP.mono (r2At_ok M hr.good (by omega_using [hw8]) (by omega_using [hw28]) hloQ hZq hwq2 hwqw (by decide)
    hr.wsQ hr.qws hr.nv hr.qxv hQ'.1 hQ'.2)
    fun t ⟨hg, hqws, _, _, hqy, f₂, k₂⟩ => ?_
  obtain f₂' : Frm B (pRanges w ++ [xRange (offQ w pl) (wsWords ql)]) t₁.mem t.mem :=
    f₂.mono fun r hr => (List.mem_append.mp hr).elim
      (fun h' => List.mem_append_left _ (List.mem_append_left _ h')) (fun h' => List.mem_append_right _ h')
  obtain hb : ∀ i < 32, i ≠ Crt.sD → i ≠ sCnt → word t.mem B (8 * i) = word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => Frm.gx_hdr f₂ hloQ hi h1 h2
  -- `p`'s workspace, below `q`'s, is kept.
  obtain hpk : ∀ d, slot w 8 ≤ d → d + 8 ≤ offQ w pl → word t.mem B d = word t₁.mem B d := fun d hd hd' =>
    f₂'.word_eq (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact Or.inr (by have := pRanges_le w r hr; omega_using [hd, this])
      · rw [List.mem_singleton.mp hr]; exact Or.inl (by simp only [xRange]; omega_using [hd'])) (by omega_using [hZq, hn, hd'])
  obtain hpv : ∀ d m, d + 8 * m ≤ slot (wsWords pl) 8 → wv t.mem (off B (offP w)) d m =
      wv t₁.mem (off B (offP w)) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpk _ (by unfold offP; omega_using []) (by unfold offP offQ; omega_using [hd, hi])
  obtain hpw : ∀ i < 32, word t.mem (off B (offP w)) (8 * i) = word t₁.mem (off B (offP w)) (8 * i) :=
    fun i hi => by rw [word_off, word_off]; exact hpk _ (by unfold offP; omega_using []) (by unfold offP offQ; omega_using [hP8, hi])
  refine ⟨hg, hr.nv.of_frm f₂ hloQ hz (by omega_using [hw8]),
    by rw [hb _ (by decide) (by decide) (by decide)]; exact hr.msk,
    by rw [hb _ (by decide) (by decide) (by decide)]; exact hr.wsP,
    by rw [hb _ (by decide) (by decide) (by decide)]; exact hr.wsQ,
    hr.pws.of_words fun i hi => hpw i (by omega_using [hi]), hqws,
    fun hm => by
      rw [hpv _ _ (by have := slot_le (w := wsWords pl) (show aY < 8 by decide); omega_using [this])]; exact hr.py hm,
    fun hm => by
      obtain ⟨_, hpq, _⟩ := hMk' hm
      have := hqy ⟨P, by simp only [hm, ↓reduceIte]; rw [← hpq, Nat.mul_comm]⟩
      simpa only [hm, ↓reduceIte] using this,
    hr.hfix.trans fun i hi hf => by
      obtain h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
      obtain h2 : i ≠ sCnt := by rintro rfl; revert hf; decide
      exact hb i hi h1 h2,
    hr.iscr.trans (InScr.of_frm f₂' fun r hr => by have := pxR_bound hloQ r hr; omega_using [hZq, this]),
    (hr.keep.trans k₂).mono (by decide)⟩

/-- `r2Phase`, from what the checks leave. -/
theorem r2Phase_ok (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (r2Phase M.mm)) t₀ fun t => R2Done s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk :=
  wp_seqs_append (by simp [r2At]) (by simp [r2At])
    (WP.mono (r2P_ok M h hv hr hMk) fun _ hm => r2Q_ok M h hv hm hMk)

end VG.Proof.Bignum.X86_64.PrivPre

end

end

/-!
# `vg_rsa_private_precompute` on x86-64: the masked copies

`copyMasked` copies `w` words from `rsi` to `rbx`, each and-ed with `r15`
(`copyMasked_ok`); `outArr j` copies the current workspace's array `j` so to
`rbx`, and moves `rbx` past it (`outArr_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (copyMasked outArr outAt out)
open VG.Impl.Rsa.X86_64 (eightW)

/-- After copying `j` words from `S + eS` to `D + eD`, each and-ed with
`v`. -/
structure MCopyInv (s₀ : State) (S D : Addr) (eS eD : Nat) (v : BitVec 64) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  done : ∀ i < j, word t.mem D (eD + 8 * i) = word s₀.mem S (eS + 8 * i) &&& v
  frame : Outside D eD (8 * j) s₀.mem t.mem

theorem copyMaskedStep_ok {s₀ : State} {S D : Addr} {eS eD w : Nat} {v : BitVec 64}
    (hsi : s₀.gpr .rsi = off S eS) (hbx : s₀.gpr .rbx = off D eD) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (h15 : s₀.gpr .r15 = v) (hw : w < 2 ^ 32) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s₀.rd ++ s₀.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s₀.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b))
    {j : Nat} (hj : j < w) {t : State} (hI : MCopyInv s₀ S D eS eD v j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax] :
        List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ MCopyInv s₀ S D eS eD v (j + 1) t' := by
  obtain tsi : t.gpr .rsi = off S eS := (hI.keep.gpr (by decide)).trans hsi
  obtain tbx : t.gpr .rbx = off D eD := (hI.keep.gpr (by decide)).trans hbx
  obtain t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain t15 : t.gpr .r15 = v := (hI.keep.gpr (by decide)).trans h15
  obtain hld : InRegions (t.rd ++ t.wr) (off S (eS + 8 * j)) 8 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  obtain hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.2.2]; exact hwr j hj
  obtain hv : word t.mem S (eS + 8 * j) = word s₀.mem S (eS + 8 * j) :=
    Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega_using [hj, this])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (word s₀.mem S (eS + 8 * j) &&& v)) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tsi hI.r14, addr0 tbx hI.r14, hld, hst, hv, t15]
  obtain t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  obtain t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_using [hw, hj]) (by omega_using [hw])) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), h14, fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega_using [hD, hj])).word (by omega_using [hi]) (by omega_arith)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega_using [hD, hj]) x (by omega_using [hx'])]
    exact hI.frame x (by omega_using [hx'])

/-- `copyMasked`: the `w` words at `S + eS`, each and-ed with `v` (in
`r15`), to `D + eD`, which they do not overlap, changing only those. -/
theorem copyMasked_ok {s : State} {S D : Addr} {eS eD w : Nat} {v : BitVec 64}
    (hsi : s.gpr .rsi = off S eS) (hbx : s.gpr .rbx = off D eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (h15 : s.gpr .r15 = v) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s.rd ++ s.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b)) :
    WP isa copyMasked s fun t =>
      (∀ i < w, word t.mem D (eD + 8 * i) = word s.mem S (eS + 8 * i) &&& v) ∧
      Outside D eD (8 * w) s.mem t.mem ∧ Keep [.rax, .r14] s t := by
  obtain h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      MCopyInv s S D eS eD v 0 t := fun t h14 hm k _ =>
    ⟨k.mono (by decide), h14, fun i hi => absurd hi (Nat.not_lt_zero _),
      by rw [hm]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_using [hw]) hw' (MCopyInv s S D eS eD v) h0
    (fun j _ hj t hI => copyMaskedStep_ok hsi hbx h12 h15 (by omega_using [hw']) hD hrd hwr hsep hj hI)) fun t hI => ?_
  exact ⟨hI.done, hI.frame, hI.keep⟩
/-- `x = p + (x - p)`. -/
theorem eq_add_ofs (p x : Addr) : x = p + BitVec.ofNat 64 (ofs p x) := by
  unfold ofs
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- A byte of a workspace at `o` is one of the working space. -/
theorem ofs_lt_of_sub {B x : Addr} {o n Z : Nat} (ho : o + n ≤ Z) (hZ : B.toNat + Z ≤ 2 ^ 64)
    (hx : ofs (off B o) x < n) : ofs B x < Z := by
  obtain e := eq_add_ofs (off B o) x
  generalize ofs (off B o) x = m at hx e
  rw [e, ofs_off B (by omega_using [ho, hZ, hx])]; omega_using [ho, hx]

theorem times8 (r : BitVec 64) {L : Nat} (h : r = BitVec.ofNat 64 L) :
    r + r + (r + r) + (r + r + (r + r)) = BitVec.ofNat 64 (L * 8) := by
  subst h; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_using []

theorem off_add_ofNat (D : Addr) (e a : Nat) : off D e + BitVec.ofNat 64 a = off D (e + a) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- `outArr j`: the array `j` of the workspace at `X`, each word and-ed with
`v` (in `r15`), to `D + eD`, and `rbx` past it. -/
theorem outArr_ok {s : State} {X D : Addr} {Zx wx eD : Nat} {mx v : BitVec 64} {j : Nat}
    (hg : Good s X Zx wx mx) (hZ : slot wx 8 ≤ Zx) (hj : j < 8) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31)
    (hbx : s.gpr .rbx = off D eD) (h15 : s.gpr .r15 = v) (hD : eD + 8 * wx ≤ 2 ^ 64)
    (hwr : ∀ i < wx, InRegions s.wr (off D (eD + 8 * i)) 8)
    (hsep : ∀ i < wx, ∀ b < 8, ofs D (off X (slot wx j + 8 * i) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * wx ≤ ofs D (off X (slot wx j + 8 * i) + BitVec.ofNat 64 b)) :
    WP isa (seqs (outArr j)) s fun t =>
      (∀ i < wx, word t.mem D (eD + 8 * i) = word s.mem X (slot wx j + 8 * i) &&& v) ∧
      Outside D eD (8 * wx) s.mem t.mem ∧ t.gpr .rbx = off D (eD + 8 * wx) ∧
      Keep [.rax, .r14, .r12, .rsi, .rbx] s t := by
  have hn := hg.scr.nowrap
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off X (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_using [hZ, this])
  obtain sj := Nat.le_trans (slot_le (w := wx) hj) hZ
  unfold outArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rsi = off X (slot wx j) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr j) (by unfold sArr; omega_using [hj]),
      hg.hdr.hw, hg.hdr.harr j hj]) rfl) fun s₁ ⟨⟨h12, hsi, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (copyMasked_ok (S := X) (eS := slot wx j) hsi ((k₁.gpr (by decide)).trans hbx) h12
    ((k₁.gpr (by decide)).trans h15) hw hw' hD
    (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact hg.scr.ld (d := slot wx j + 8 * i) (by omega_using [sj, hi]))
    (fun i hi => by rw [k₁.2.2]; exact hwr i hi) hsep) fun s₂ ⟨hd₂, ho₂, k₂⟩ => ?_)
  obtain h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 wx := (k₂.gpr (by decide)).trans h12
  obtain hbx₂ : s₂.gpr .rbx = off D eD := ((k₁.trans k₂).gpr (by decide)).trans hbx
  refine WP.mono (WP.keep [.rax, .rbx] (Q := fun t => t.gpr .rbx = off D (eD + 8 * wx) ∧ t.mem = s₂.mem)
    (by
      xrun [eightW, List.cons_append, List.nil_append, h12₂, hbx₂, times8 _ h12₂, off_add_ofNat]
      rw [times8 _ rfl, off_add_ofNat]; congr 2; omega_using []) rfl) fun t ⟨⟨hbx', hm⟩, k₃⟩ => ?_
  refine ⟨fun i hi => by rw [hm, hd₂ i hi, hm₁], by rw [hm, ← hm₁]; exact ho₂, hbx',
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- A word of the working space's array is outside `pre`, which nothing
of the working space overlaps. -/
theorem sep_of {B D : Addr} {Z L8 eD n o d : Nat} (hS : ∀ x, ofs B x < Z → L8 ≤ ofs D x)
    (hn : eD + n ≤ L8) (hd : o + d + 8 ≤ Z) (hZ : B.toNat + Z ≤ 2 ^ 64) :
    ∀ b < 8, ofs D (off (off B o) d + BitVec.ofNat 64 b) < eD ∨
      eD + n ≤ ofs D (off (off B o) d + BitVec.ofNat 64 b) := fun b hb => by
  have := hS (off (off B o) d + BitVec.ofNat 64 b) (by rw [off_off, ofs_off B (by omega_using [hd, hZ, hb])]; omega_using [hd, hb])
  omega_using [hn, this]

/-- `outAt sl`: into the prime's workspace (its base in slot `sl`), its
`aY` masked to `D + eD`, and back. -/
theorem outAt_ok {s : State} {B D : Addr} {Z w o wx eD L8 : Nat} {minv mx v : BitVec 64} {sl : Nat}
    (hg : Good s B Z w minv) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 ≤ Z) (hwx : 1 ≤ wx) (hwx' : wx < 2 ^ 31)
    (hsl : sl < 32) (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx)
    (hbx : s.gpr .rbx = off D eD) (h15 : s.gpr .r15 = v) (hD : eD + 8 * wx ≤ L8) (hL : D.toNat + L8 ≤ 2 ^ 64)
    (hwr : (⟨D, L8⟩ : Region) ∈ s.wr) (hS : ∀ x, ofs B x < Z → L8 ≤ ofs D x) :
    WP isa (seqs (outAt sl)) s fun t =>
      (∀ i < wx, word t.mem D (eD + 8 * i) = word s.mem (off B o) (slot wx aY + 8 * i) &&& v) ∧
      Outside D eD (8 * wx) s.mem t.mem ∧ t.gpr .rbx = off D (eD + 8 * wx) ∧ t.gpr .rdi = B ∧
      t.gpr .r15 = v ∧ Keep [.rax, .r14, .r12, .rsi, .rbx, .rdi] s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain lY := slot_le (w := wx) (show aY < 8 by decide)
  unfold outAt
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [outArr]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl) fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_
  obtain hg₁ : Good s₁ (off B o) (slot wx 8) wx mx :=
    ⟨(hs.congr k₁.2.2).sub (by omega) (by omega), hdi₁, by rw [hm₁]; exact hws.hdr⟩
  refine wp_seqs_append (by simp [outArr]) (by simp) ?_
  refine WP.mono (outArr_ok hg₁ (Nat.le_refl _) (show aY < 8 by decide) hwx hwx' (D := D) (eD := eD)
    ((k₁.gpr (by decide)).trans hbx) ((k₁.gpr (by decide)).trans h15) (by omega)
    (fun i hi => ⟨_, by rw [k₁.2.2]; exact hwr, Offset.contains_base D (by omega) (by omega)⟩)
    (fun i hi => sep_of hS (by omega) (by omega) hn)) fun s₂ ⟨hd₂, ho₂, hbx₂, k₂⟩ => ?_
  obtain hl₂ : InRegions (s₂.rd ++ s₂.wr) (off (off B o) (8 * sLink)) 8 := by
    rw [k₂.2.1, k₂.2.2]; exact hg₁.scr.ld (by unfold sLink sFn; omega)
  obtain hlk : word s₂.mem (off B o) (8 * sLink) = B := by
    refine Eq.trans ?_ hws.link
    rw [← hm₁]
    exact Mem.readW_congr fun b hb => ho₂ _ (by
      have := hS (off (off B o) (8 * sLink) + BitVec.ofNat 64 b) (by rw [off_off, ofs_off B (by unfold sLink sFn; omega)]; unfold sLink sFn; omega)
      omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₂.mem)
    (by xrun [Crt.leave, State.ea, hdr, (k₂.gpr (by decide)).trans hdi₁, hdrOff, hl₂, hlk]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  refine ⟨fun i hi => by rw [hm, hd₂ i hi, hm₁], by rw [hm, ← hm₁]; exact ho₂,
    by rw [k₃.gpr (by decide)]; exact hbx₂, hdi, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact h15

/-- Memory that changes only within `pre` keeps the working space. -/
theorem scr_of_outside {B D : Addr} {Z L8 e n : Nat} {m m' : Mem} (h : Outside D e n m m')
    (hS : ∀ x, ofs B x < Z → L8 ≤ ofs D x) (hn : e + n ≤ L8) : ∀ x, ofs B x < Z → m' x = m x :=
  fun x hx => h x (Or.inr (by have := hS x hx; omega_using [hn, this]))

theorem word_of_scr {B : Addr} {Z d : Nat} {m m' : Mem} (h : ∀ x, ofs B x < Z → m' x = m x)
    (hd : d + 8 ≤ Z) (hZ : B.toNat + Z ≤ 2 ^ 64) : word m' B d = word m B d :=
  Mem.readW_congr fun i hi => h _ (by rw [ofs_off B (d := d) (i := i) (by omega_using [hd, hZ, hi])]; omega_using [hd, hi])

theorem Good.of_scr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hm : ∀ x, ofs B x < Z → t.mem x = s.mem x) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = B) : Good t B Z w minv := by
  have hn := hg.scr.nowrap
  obtain hh : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    word_of_scr hm (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this]) hn
  exact ⟨hg.scr.congr hwr, hdi, ⟨ (hh _ (by decide)).trans hg.hdr.hw,
    (hh _ (by decide)).trans hg.hdr.hminv, fun j hj => (hh _ (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj)⟩⟩

/-- What `out` leaves: `pre`'s four parts, each word and-ed with the mask,
the mask's low bit returned and the saved registers restored. -/
structure OutPost (t u : State) (B D : Addr) (w wp wq L8 : Nat) (op oq : Nat) (M : Bool) : Prop where
  segN : ∀ i < w, word u.mem D (8 * i) = word t.mem B (slot w aN + 8 * i) &&& mask M
  segR : ∀ i < w, word u.mem D (8 * w + 8 * i) = word t.mem B (slot w aR2 + 8 * i) &&& mask M
  segP : ∀ i < wp, word u.mem D (16 * w + 8 * i) = word t.mem (off B op) (slot wp aY + 8 * i) &&& mask M
  segQ : ∀ i < wq, word u.mem D (16 * w + 8 * wp + 8 * i) =
    word t.mem (off B oq) (slot wq aY + 8 * i) &&& mask M
  rax : u.gpr .rax = BitVec.ofNat 64 M.toNat
  saved : ∀ i < 6, u.gpr (saved.getD i .rax) = word t.mem B (8 * i)
  frame : ∀ x, L8 ≤ ofs D x → u.mem x = t.mem x
  rsp : u.gpr .rsp = t.gpr .rsp

/-- `out`, from what `r2Phase` leaves, with `pre` (`L8` bytes at `D`, apart
from the working space) in `sOut`. -/
theorem out_ok {σ t : State} {B D : Addr} {Z w pl ql L8 : Nat} {minv mp mq : BitVec 64} {N P Q : Nat}
    {M : Bool} (hR : R2Done σ t B Z w pl ql minv mp mq N P Q M) (hw : 1 ≤ w) (hw' : w < 2 ^ 20)
    (hpl : pl < 2 ^ 20) (hql : ql < 2 ^ 20)
    (hZq : offQ w pl + slot (wsWords ql) 8 + wsTab (wsWords ql) ≤ Z) (hO : word t.mem B (8 * sOut) = D)
    (hL8 : L8 = 8 * (2 * w + wsWords pl + wsWords ql)) (hL : D.toNat + L8 ≤ 2 ^ 64)
    (hwr : (⟨D, L8⟩ : Region) ∈ t.wr) (hS : ∀ x, ofs B x < Z → L8 ≤ ofs D x) :
    WP isa (seqs out) t fun u => OutPost t u B D w (wsWords pl) (wsWords ql) L8 (offP w) (offQ w pl) M := by
  have hg := hR.good
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_using []
  obtain hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_using []
  obtain hwp : wsWords pl < 2 ^ 20 := by unfold wsWords; omega_using [hpl]
  obtain hwq : wsWords ql < 2 ^ 20 := by unfold wsWords; omega_using [hql]
  obtain hZ : slot w 8 ≤ Z := by unfold offQ at hZq; omega_using [hZq]
  obtain hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  obtain hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_using []
  obtain hhiP : offP w + slot (wsWords pl) 8 ≤ Z := by unfold offQ at hZq; unfold offP; omega_using [hZq]
  obtain hhiQ : offQ w pl + slot (wsWords ql) 8 ≤ Z := by omega_using [hZq]
  obtain hloQ : slot w 8 ≤ offQ w pl := by unfold offQ; omega_using []
  obtain hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [h8, hZ, hi])
  unfold out
  simp only [List.append_assoc]
  -- `rbx := pre`, `r15 := ` the mask.
  refine wp_seqs_append (by simp) (by simp [outArr]) ?_
  refine WP.mono (WP.keep [.rbx, .r15] (Q := fun u => u.gpr .rbx = off D 0 ∧ u.gpr .r15 = mask M ∧ u.mem = t.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sOut (by decide), hl sMask (by decide), hO, hR.msk]) rfl)
    fun s₀ ⟨⟨hbx₀, h15₀, hm₀⟩, k₀⟩ => ?_
  obtain hg₀ : Good s₀ B Z w minv := Good.of_scr hg hZ (fun x _ => by rw [hm₀]) k₀.2.2 ((k₀.gpr (by decide)).trans hg.rdi)
  obtain hwr₀ : (⟨D, L8⟩ : Region) ∈ s₀.wr := by rw [k₀.2.2]; exact hwr
  -- `n`.
  refine wp_seqs_append (by simp [outArr]) (by simp [outArr]) ?_
  refine WP.mono (outArr_ok hg₀ hZ (show aN < 8 by decide) hw (by omega_using [hw']) hbx₀ h15₀ (by omega_using [hw'])
    (fun i hi => ⟨_, hwr₀, Offset.contains_base D (by omega_using [hL8, hi]) (by omega_using [hw', hi])⟩)
    (fun i hi => by
      have := slot_le (w := w) (show aN < 8 by decide)
      have := sep_of (o := 0) (d := slot w aN + 8 * i) hS (eD := 0) (n := 8 * w) (by omega_using [hL8]) (by omega_using [hZ, hi, this]) hn
      simpa [off_off] using this)) fun s₁ ⟨hd₁, ho₁, hbx₁, k₁⟩ => ?_
  obtain hsc₁ := scr_of_outside ho₁ hS (by omega_using [hL8])
  obtain hg₁ := Good.of_scr hg₀ hZ hsc₁ k₁.2.2 ((k₁.gpr (by decide)).trans hg₀.rdi)
  obtain hwr₁ : (⟨D, L8⟩ : Region) ∈ s₁.wr := by rw [k₁.2.2]; exact hwr₀
  obtain h15₁ : s₁.gpr .r15 = mask M := (k₁.gpr (by decide)).trans h15₀
  -- `R² mod n`.
  refine wp_seqs_append (by simp [outArr]) (by simp [outAt]) ?_
  refine WP.mono (outArr_ok hg₁ hZ (show aR2 < 8 by decide) hw (by omega_using [hw']) (eD := 0 + 8 * w) hbx₁ h15₁ (by omega_using [hw'])
    (fun i hi => ⟨_, hwr₁, Offset.contains_base D (by omega_using [hL8, hi]) (by omega_using [hw', hi])⟩)
    (fun i hi => by
      have := slot_le (w := w) (show aR2 < 8 by decide)
      have := sep_of (o := 0) (d := slot w aR2 + 8 * i) hS (eD := 0 + 8 * w) (n := 8 * w) (by omega_using [hL8]) (by omega_using [hZ, hi, this]) hn
      simpa [off_off] using this)) fun s₂ ⟨hd₂, ho₂, hbx₂, k₂⟩ => ?_
  obtain hsc₂ := scr_of_outside ho₂ hS (by omega_using [hL8])
  obtain hg₂ := Good.of_scr hg₁ hZ hsc₂ k₂.2.2 ((k₂.gpr (by decide)).trans hg₁.rdi)
  obtain hwr₂ : (⟨D, L8⟩ : Region) ∈ s₂.wr := by rw [k₂.2.2]; exact hwr₁
  obtain h15₂ : s₂.gpr .r15 = mask M := (k₂.gpr (by decide)).trans h15₁
  obtain hsc02 : ∀ x, ofs B x < Z → s₂.mem x = t.mem x := fun x hx => by rw [hsc₂ x hx, hsc₁ x hx, hm₀]
  obtain hwd : ∀ d, d + 8 ≤ Z → word s₂.mem B d = word t.mem B d := fun d hd => word_of_scr hsc02 hd hn
  -- `R_p² mod p`.
  refine wp_seqs_append (by simp [outAt]) (by simp [outAt]) ?_
  refine WP.mono (outAt_ok hg₂ (Nat.le_refl _) hhiP (by omega_using [hwp2]) (by omega_using [hwp]) (by decide)
    (by rw [hwd _ (by unfold sWsP sFn; omega_using [h8, hZ])]; exact hR.wsP)
    (hR.pws.of_words fun i hi => by rw [word_off, word_off]; exact hwd _ (by unfold offP; omega_using [hZq, hQ8, hloQ, hi]))
    (eD := 0 + 8 * w + 8 * w) (by rw [hbx₂]) h15₂ (by omega_using [hL8]) hL hwr₂ hS) fun s₃ ⟨hd₃, ho₃, hbx₃, hdi₃, h15₃, k₃⟩ => ?_
  obtain hsc₃ := scr_of_outside ho₃ hS (by omega_using [hL8])
  obtain hg₃ := Good.of_scr hg₂ hZ hsc₃ k₃.2.2 hdi₃
  obtain hwr₃ : (⟨D, L8⟩ : Region) ∈ s₃.wr := by rw [k₃.2.2]; exact hwr₂
  obtain hsc03 : ∀ x, ofs B x < Z → s₃.mem x = t.mem x := fun x hx => by rw [hsc₃ x hx, hsc02 x hx]
  obtain hwd₃ : ∀ d, d + 8 ≤ Z → word s₃.mem B d = word t.mem B d := fun d hd => word_of_scr hsc03 hd hn
  -- `R_q² mod q`.
  refine wp_seqs_append (by simp [outAt]) (by simp) ?_
  refine WP.mono (outAt_ok hg₃ hloQ hhiQ (by omega_using [hwq2]) (by omega_using [hwq]) (by decide)
    (by rw [hwd₃ _ (by unfold sWsQ sFn; omega_using [h8, hZ])]; exact hR.wsQ)
    (hR.qws.of_words fun i hi => by rw [word_off, word_off]; exact hwd₃ _ (by omega_using [hZq, hQ8, hi]))
    (eD := 0 + 8 * w + 8 * w + 8 * wsWords pl) (by rw [hbx₃]) h15₃ (by omega_using [hL8]) hL hwr₃ hS)
    fun s₄ ⟨hd₄, ho₄, _, hdi₄, _, k₄⟩ => ?_
  obtain hsc₄ := scr_of_outside ho₄ hS (by omega_using [hL8])
  obtain hsc04 : ∀ x, ofs B x < Z → s₄.mem x = t.mem x := fun x hx => by rw [hsc₄ x hx, hsc03 x hx]
  obtain hwd₄ : ∀ d, d + 8 ≤ Z → word s₄.mem B d = word t.mem B d := fun d hd => word_of_scr hsc04 hd hn
  obtain hl₄ : ∀ i < 32, InRegions (s₄.rd ++ s₄.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k₄.2.1, k₄.2.2, k₃.2.1, k₃.2.2, k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2, k₀.2.1, k₀.2.2]; exact hl i hi
  -- The result and the saved registers.
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun u =>
      u.gpr .rax = BitVec.ofNat 64 M.toNat ∧ u.gpr .rbx = word t.mem B (8 * 0) ∧
      u.gpr .rbp = word t.mem B (8 * 1) ∧ u.gpr .r12 = word t.mem B (8 * 2) ∧
      u.gpr .r13 = word t.mem B (8 * 3) ∧ u.gpr .r14 = word t.mem B (8 * 4) ∧
      u.gpr .r15 = word t.mem B (8 * 5) ∧ u.mem = s₄.mem) (by
    xrun [exit_eq, List.cons_append, List.nil_append, State.ea, hdr, hdi₄, hdrOff, hl₄ sMask (by decide),
      hwd₄ (8 * sMask) (by unfold sMask sFn; omega_using [h8, hZ]), hR.msk, mask_and1, hl₄ 0 (by decide), hl₄ 1 (by decide),
      hl₄ 2 (by decide), hl₄ 3 (by decide), hl₄ 4 (by decide), hl₄ 5 (by decide), hwd₄ (8 * 0) (by omega_using [h8, hZ]),
      hwd₄ (8 * 1) (by omega_using [h8, hZ]), hwd₄ (8 * 2) (by omega_using [h8, hZ]), hwd₄ (8 * 3) (by omega_using [h8, hZ]), hwd₄ (8 * 4) (by omega_using [h8, hZ]),
      hwd₄ (8 * 5) (by omega_using [h8, hZ])]) rfl)
    fun u ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₅⟩ => ?_
  -- Each part of `pre`, kept by the later copies.
  have o12 := ho₂
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hax, fun i hi => ?_, fun x hx => ?_, ?_⟩
  · rw [hm, ho₄.word (by omega_using [hi]) (by omega_using [hw', hi]), ho₃.word (by omega_using [hi]) (by omega_using [hw', hi]), ho₂.word (by omega_using [hi]) (by omega_using [hw', hi]),
      show 8 * i = 0 + 8 * i by omega_using [], hd₁ i hi, hm₀, Nat.zero_add]
  · rw [hm, ho₄.word (by omega_using [hi]) (by omega_using [hw', hi]), ho₃.word (by omega_using [hi]) (by omega_using [hw', hi]),
      show 8 * w + 8 * i = 0 + 8 * w + 8 * i by omega_using [], hd₂ i hi, word_of_scr (fun x hx => by rw [hsc₁ x hx, hm₀])
        (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_using [hZ, hi, this]) hn]
  · rw [hm, ho₄.word (by omega_using [hi]) (by omega_using [hw', hwp, hi]), show 16 * w + 8 * i = 0 + 8 * w + 8 * w + 8 * i by omega_using [], hd₃ i hi,
      word_off, word_off, hwd _ (by have := slot_le (w := wsWords pl) (show aY < 8 by decide); have := hhiP; simp only [offP] at *; omega_arith)]
    rfl
  · rw [hm, show 16 * w + 8 * wsWords pl + 8 * i = 0 + 8 * w + 8 * w + 8 * wsWords pl + 8 * i by omega_using [], hd₄ i hi,
      word_off, word_off, hwd₃ _ (by have := slot_le (w := wsWords ql) (show aY < 8 by decide); omega_using [hZq, hi, this])]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · rw [hm, ho₄ x (Or.inr (by omega_using [hL8, hx])), ho₃ x (Or.inr (by omega_using [hL8, hx])), ho₂ x (Or.inr (by omega_using [hL8, hx])),
      ho₁ x (Or.inr (by omega_using [hL8, hx])), hm₀]
  · have kk := (((k₀.trans k₁).trans k₂).trans k₃).trans (k₄.trans k₅)
    exact kk.gpr (by decide)

end VG.Proof.Bignum.X86_64.PrivPre
