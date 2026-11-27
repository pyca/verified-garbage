module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
public import VerifiedGarbage.Impl.Ffdh.RISCV64.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Ffdh.RISCV64.CheckPrivate

/-!
# `vg_ffdh_check_private` on RISC-V

## The front

`kpContract`: `vg_ffdh_check_private(domain = a0, domain_len = a1,
p_len = a2, y = a3, y_len = a4, x = a5, x_len = a6, scratch = a7,
scratch_len)`, the last on the stack. `cxOf`: the exchange's public data
(`XD`), with g as the peer, the working space its first `slot w 24` bytes and
`out` the bytes after them, which nothing writes. `cpFront_ok`: `cpFront`
saves the callee-saved registers, stores the header's words 0–4 and sets up
as `vg_ffdh_derive_public`'s front does, with `Derive.AR`'s registers.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.CheckPrivate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.CheckPrivate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.Derive (AR off_off)
open VG.Proof.Bignum (slot)
open VG.Impl.Dsa.RISCV64 (save)

/-! ## The function -/

/-- The argument on the stack: `scratch_len`. -/
abbrev kpStack (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- The status. -/
def kpStatus (s : State) : Nat :=
  Spec.Ffdh.privateStatus
    (Spec.Ffdh.domainOf (s.gpr .a2).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat))

/-- What timing may depend on: the domain, y and the status. -/
def kpLeak (s : State) : List Nat :=
  (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat).map (·.toNat) ++
    (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat).map (·.toNat) ++ [kpStatus s]

/-- `vg_ffdh_check_private`, on the registers and the stack. -/
def kpContract : Contract isa where
  pre s :=
    let dom : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let y : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let x : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
    let scr : Region := ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩
    s.rd = [dom, y, x, kpStack s] ∧ s.wr = [scr] ∧
      dom.Disjoint scr ∧ y.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint (kpStack s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .a2).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .a2).toNat (s.gpr .a1).toNat ∧
      (s.gpr .a4).toNat = (s.gpr .a2).toNat ∧ 1 ≤ (s.gpr .a6).toNat ∧ (s.gpr .a6).toNat ≤ (s.gpr .a2).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .a2).toNat ≤ (stackArg s 0).toNat ∧
      (s.gpr .a7).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    Spec.Ffdh.domainValid (s.gpr .a2).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) = true →
      ((t.gpr .a0).setWidth 32).toNat = kpStatus s
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ kpLeak s₁ = kpLeak s₂

/-- The bytes of the exchange's working space: its 24 arrays. -/
abbrev cpZ (k : Nat) : Nat := slot ((k + 7) / 8) 24

/-- The exchange's public data: the working space its first `cpZ` bytes,
`out` the bytes after them, g as the peer. -/
def cxOf (s : State) : XD :=
  ⟨off (s.gpr .a7) (cpZ (s.gpr .a2).toNat), s.gpr .a0, (s.gpr .a1).toNat, (s.gpr .a2).toNat, s.gpr .a5,
    (s.gpr .a6).toNat, off (s.gpr .a0) (s.gpr .a2).toNat, s.gpr .a7, cpZ (s.gpr .a2).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat⟩

/-- A working space within a larger one. -/
theorem scr_shrink {s : State} {B : Addr} {Z Z' : Nat} (h : Scr s B Z) (hZ : Z' ≤ Z) : Scr s B Z' :=
  let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := h.wr
  ⟨⟨B₀, o, L, hm, hb, by omega_arith, hL'⟩, by have := h.nowrap; omega_arith, h.al⟩

/-- An address within `k` bytes past `Z` bytes at `S` is at least `Z` past `S`. -/
theorem ofs_past {S y : Addr} {Z k : Nat} (hn : S.toNat + Z + k ≤ 2 ^ 64) (h : ofs (off S Z) y < k) :
    Z ≤ ofs S y := by
  simp only [ofs, off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h ⊢
  have hS := S.isLt
  have hy := y.isLt
  rw [Nat.mod_eq_of_lt (a := Z) (by omega_arith), Nat.mod_eq_of_lt (a := S.toNat + Z) (by omega_arith)] at h
  omega_arith

/-! ## The front -/

/-- The header's words 1–4 and the moved arguments. -/
theorem chdr_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 40 ≤ Z) (h6 : s.gpr .s6 = S) :
    WP isa (.block cpHdr) s fun t =>
      (word t.mem S 32 = s.gpr .a3 ∧ word t.mem S 8 = s.gpr .a5 ∧ word t.mem S 16 = s.gpr .a6 ∧
        word t.mem S 24 = s.gpr .a0 + s.gpr .a2 ∧ t.gpr .a2 = s.gpr .a0 ∧ t.gpr .a3 = s.gpr .a1 ∧
        t.gpr .a4 = s.gpr .a2 ∧ t.gpr .s7 = s.gpr .a0 ∧ t.gpr .s8 = s.gpr .a2 ∧ t.gpr .a1 = s.gpr .a2 ∧
        Outside S 0 40 s.mem t.mem) ∧ Keep [.a2, .a3, .a4, .t2, .s7, .s8, .a1] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  have i32 := hs.st (d := 32) (n := 8) (by omega_arith)
  have i8 := hs.st (d := 8) (n := 8) (by omega_arith)
  have i16 := hs.st (d := 16) (n := 8) (by omega_arith)
  have i24 := hs.st (d := 24) (n := 8) (by omega_arith)
  have l32 := hs.al8 (d := 32) (by omega_arith) (by decide)
  have l8 := hs.al8 (d := 8) (by omega_arith) (by decide)
  have l16 := hs.al8 (d := 16) (by omega_arith) (by decide)
  have l24 := hs.al8 (d := 24) (by omega_arith) (by decide)
  have o0 := writeW_outside s.mem S (d := 32) (s.gpr .a3) (by omega_arith)
  have o1 := writeW_outside (s.mem.writeW (off S 32) (s.gpr .a3)) S (d := 8) (s.gpr .a5) (by omega_arith)
  have o2 := writeW_outside ((s.mem.writeW (off S 32) (s.gpr .a3)).writeW (off S 8) (s.gpr .a5)) S (d := 16)
    (s.gpr .a6) (by omega_arith)
  have o3 := writeW_outside (((s.mem.writeW (off S 32) (s.gpr .a3)).writeW (off S 8) (s.gpr .a5)).writeW
    (off S 16) (s.gpr .a6)) S (d := 24) (s.gpr .a0 + s.gpr .a2) (by omega_arith)
  refine WP.mono (WP.keep [.a2, .a3, .a4, .t2, .s7, .s8, .a1] (Q := fun t => t.mem = (((s.mem.writeW (off S 32)
      (s.gpr .a3)).writeW (off S 8) (s.gpr .a5)).writeW (off S 16) (s.gpr .a6)).writeW (off S 24)
        (s.gpr .a0 + s.gpr .a2) ∧ t.gpr .a2 = s.gpr .a0 ∧ t.gpr .a3 = s.gpr .a1 ∧ t.gpr .a4 = s.gpr .a2 ∧
      t.gpr .s7 = s.gpr .a0 ∧ t.gpr .s8 = s.gpr .a2 ∧ t.gpr .a1 = s.gpr .a2) ?_ (by rfl) (by rfl))
    fun t ⟨⟨tm, t2, t3, t4, t7, t8, t1⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_, t2, t3, t4, t7, t8, t1, ?_⟩, kt⟩
  · unfold cpHdr
    brun [h6', i32, i8, i16, i24, l32, l8, l16, l24]
    simp [off]
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith),
      o1.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (((o0.mono (by omega_arith) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))).trans (o3.mono (by omega_arith) (by omega_arith))

theorem out_addr (S : Addr) (w : Nat) :
    BitVec.ofNat 64 24 * BitVec.ofNat 64 (8 * w + 16) + off S (slot w 0) = off S (slot w 24) := by
  have e : slot w 24 = 24 * (8 * w + 16) + slot w 0 := by unfold slot hdrBytes; omega_arith
  rw [e, off, off, ← BitVec.ofNat_mul, BitVec.ofNat_add]
  ac_rfl

/-- `cpOut`: the exchange's `out` into `s10` and the header's word 0. -/
theorem cout_ok {s : State} {S : Addr} {Z w : Nat} (hs : Scr s S Z) (hZ : 8 ≤ Z) (h6 : s.gpr .s6 = S)
    (h7 : s.gpr .a7 = off S (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * w + 16)) :
    WP isa (.block cpOut) s fun t =>
      (t.gpr .s10 = off S (slot w 24) ∧ word t.mem S 0 = off S (slot w 24) ∧ Outside S 0 8 s.mem t.mem) ∧
        Keep [.t2, .s10] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  have i0 := hs.st (d := 0) (n := 8) (by omega_arith)
  have l0 := hs.al8 (d := 0) (by omega_arith) (by decide)
  have o0 := writeW_outside s.mem S (d := 0) (off S (slot w 24)) (by omega_arith)
  refine WP.mono (WP.keep [.t2, .s10] (Q := fun t => t.mem = s.mem.writeW (off S 0) (off S (slot w 24)) ∧
      t.gpr .s10 = off S (slot w 24)) ?_ (by rfl) (by rfl))
    fun t ⟨⟨tm, t10⟩, kt⟩ => ⟨⟨t10, by rw [tm]; exact word_writeW_self _ _ _ _, by rw [tm]; exact o0⟩, kt⟩
  unfold cpOut
  brun [h6', h7, h5, i0, l0, Dsa.RISCV64.exec_li_lit (show 24 < 2048 by decide), out_addr]

/-- The registers the front writes. -/
def frontRegs : List Reg := [.t2, .s6, .a2, .a3, .a4, .s7, .s8, .a1, .a7, .s5, .s10, .s11, .t0]

/-- `cpFront`: `Base`, `AR`, y's address in the header's word 4, the
registers saved, and only the header changed. -/
theorem cpFront_ok {s : State} (h : kpContract.pre s) :
    WP isa (.block cpFront) s fun t =>
      Base (cxOf s) t ∧ AR (cxOf s) t ∧ word t.mem (s.gpr .a7) 32 = s.gpr .a3 ∧
        SavedAt (s.gpr .a7) t.mem s ∧
        Keep frontRegs s t ∧ Outside (s.gpr .a7) 0 256 s.mem t.mem := by
  obtain ⟨hrd, hwr, dDS, dYS, dXS, dSA, nwD, nwY, nwX, nwS, ⟨hk, hk'⟩, hL,
    hyl, hx1, hxk, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [cxOf]
  generalize hSd : s.gpr .a7 = S at hwr dDS dYS dXS dSA nwS alS ⊢
  generalize hZd : (stackArg s 0).toNat * 8 = Z at hwr dDS dYS dXS dSA nwS ⊢
  have hZ : 256 + 128 * (s.gpr .a2).toNat ≤ Z := by omega_arith
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS alS
  have hwd : ((s.gpr .a2).toNat + 7) / 8 * 8 ≤ (s.gpr .a2).toNat + 7 := Nat.div_mul_le_self _ _
  have hcz : cpZ (s.gpr .a2).toNat + (s.gpr .a2).toNat ≤ Z := by unfold cpZ slot hdrBytes; omega_arith
  unfold cpFront
  rw [show ∀ a b c d e : List Instr, a ++ b ++ c ++ d ++ e = (a ++ b) ++ (c ++ (d ++ e)) from fun a b c d e => by
    simp only [List.append_assoc]]
  refine WP.block_append (WP.mono (pre_ok .a7 hSd hs (by omega_arith)) fun s₂ ⟨h6₂, sv₂, k12, hsavO⟩ => ?_)
  refine WP.block_append (WP.mono (chdr_ok (hs.congr k12.2.2) (by omega_arith) h6₂)
    fun s₃ ⟨⟨w32, w8, w16, w24, b2, b3, b4, b7, b8, b1, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.block_append (WP.mono (Pub.setup_ok (O := s.gpr .a0) (k := (s.gpr .a2).toNat)
    ((k13.gpr (by decide)))
    (by rw [b1, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    ((k3.gpr (by decide)).trans h6₂) hk') fun s₄ ⟨⟨_, j11, j0, j5, j7, jm⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  refine WP.mono (cout_ok (hs.congr k14.2.2) (by omega_arith) ((k4.gpr (by decide)).trans ((k3.gpr (by decide)).trans h6₂))
    j7 j5) fun t ⟨⟨t10, tw0, ot⟩, k5⟩ => ?_
  have k := k14.trans k5
  have hrdt : t.rd ++ t.wr = s.rd ++ s.wr := by rw [k.2.1, k.2.2]
  -- Memory: the saved registers' words and the header's words 0–4.
  have hO : Outside S 0 256 s.mem t.mem := by
    rw [jm] at ot
    exact (hsavO.trans (o3.mono (Nat.le_refl _) (by omega_arith))).trans (ot.mono (Nat.le_refl _) (by omega_arith))
  have hOZ : Outside S 0 Z s.mem t.mem := hO.mono (Nat.le_refl _) (by omega_arith)
  have hb : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs S y < Z → off Q i ≠ y) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep =>
    Pub.bytes_apart (o := 0) (n := Z) hOZ (by omega_arith) hsep
  have hw3 : ∀ d, 8 ≤ d → d + 8 ≤ 40 → word t.mem S d = word s₃.mem S d := fun d h1 h2 => by
    rw [ot.word (Or.inr h1) (by omega_arith), jm]
  have hLk : 2 * (s.gpr .a2).toNat ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 3 * (s.gpr .a2).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have sepD' := Pub.ne_of_disjoint dDS (Nat.le_of_lt (s.gpr .a1).isLt)
  have sepX' := Pub.ne_of_disjoint dXS (Nat.le_of_lt (s.gpr .a6).isLt)
  have sepD : ∀ i < (s.gpr .a1).toNat, ∀ y, ofs S y < cpZ (s.gpr .a2).toNat → off (s.gpr .a0) i ≠ y :=
    fun i hi y hy => sepD' i hi y (Nat.lt_of_lt_of_le hy (by omega_arith))
  have rdD : ∀ i < (s.gpr .a1).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a0) i) 1 := by
    rw [hrdt]; exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  have rdX : ∀ i < (s.gpr .a6).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a5) i) 1 := by
    rw [hrdt]; exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  have hst : Scr t S Z := hs.congr k.2.2
  have hzz : cpZ (s.gpr .a2).toNat ≤ Z := by omega_arith
  have hnw' : S.toNat + cpZ (s.gpr .a2).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 := by omega_arith
  refine ⟨⟨⟨scr_shrink hst hzz, hk, hk', hLk, Nat.le_refl _, ?_, fun i hi => ?_,
      fun y hy => ofs_past hnw' hy,
      rdD, sepD, fun i hi => by rw [off_off]; exact rdD _ (by change i < (s.gpr .a2).toNat at hi; omega_arith),
      fun i hi => by rw [off_off]; exact sepD _ (by change i < (s.gpr .a2).toNat at hi; omega_arith),
      rdX, fun i hi y hy => sepX' i hi y (Nat.lt_of_lt_of_le hy (by omega_arith)), hx1, hxk,
      (by rw [hb _ _ sepD']), ?_, ?_, ?_, ?_⟩,
    by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide)]; exact h6₂,
    (k5.gpr (by decide)).trans j7,
    by rw [k5.gpr (by decide), j5, Nat.mul_add], (k5.gpr (by decide)).trans j0,
    by rw [k5.gpr (by decide), k4.gpr (by decide), b7, k12.gpr (by decide)]; simp [off],
    by rw [k5.gpr (by decide), k4.gpr (by decide), b8, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [t10]; simp [off], (k5.gpr (by decide)).trans j11⟩,
    ⟨by rw [k5.gpr (by decide), k4.gpr (by decide), b2, k12.gpr (by decide)],
      by rw [k5.gpr (by decide), k4.gpr (by decide), b3, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [k5.gpr (by decide), k4.gpr (by decide), b4, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [k.gpr (by decide)],
      by rw [k.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩,
    by rw [hw3 32 (by decide) (by decide), w32, k12.gpr (by decide)], ?_, k.mono (by decide), hO⟩
  · show (off S (cpZ (s.gpr .a2).toNat)).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := cpZ _) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [off_off]
    exact hst.st (by change i < (s.gpr .a2).toNat at hi; omega_arith)
  · rw [tw0]; simp [off, cpZ]
  · rw [hw3 8 (by decide) (by decide), w8, k12.gpr (by decide)]; simp [off]
  · rw [hw3 16 (by decide) (by decide), w16, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hw3 24 (by decide) (by decide), w24, k12.gpr (by decide), k12.gpr (by decide)]; simp [off]
  · refine SavedAt.mono ?_ ot (by decide)
    rw [jm]; exact sv₂.mono o3 (by decide)


/-! ## The comparison -/

/-- y: its address in the header's word 4, its `k` bytes readable and apart
from the working space. -/
structure YE (x : XD) (Yc : Addr) (s : State) : Prop where
  w : word s.mem x.S 32 = Yc
  rd : ∀ i < x.k, InRegions (s.rd ++ s.wr) (off Yc i) 1
  sep : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off Yc i ≠ y

theorem YE.keep {x : XD} {Yc : Addr} {s t : State} (h : YE x Yc s) (hc : Ctx x s) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hm : Arr x s.mem t.mem) : YE x Yc t := by
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  unfold slot hdrBytes at hZ
  exact ⟨by rw [Outside.word hm (Or.inl (by omega_arith)) (by omega_arith)]; exact h.w, by rw [hrd, hwr]; exact h.rd,
    h.sep⟩

/-- What the comparison leaves, from `s` after the power. -/
def CPost (x : XD) (Yc : Addr) (s t : State) : Prop :=
  t.gpr .a0 = BitVec.ofNat 64 (if (1 < wordsVal s.mem x.S (slot x.w 4) x.w ∧
      wordsVal s.mem x.S (slot x.w 4) x.w < x.p - 1) ∧
    wordsVal s.mem x.S (slot x.w 4) x.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yc x.k) then 1 else 0) ∧
  t.gpr .s6 = x.S ∧ Arr x s.mem t.mem

theorem both_bv (a b : Bool) :
    BitVec.ofNat 64 1 &&& (bmask a &&& (BitVec.allOnes 64 &&& bmask b)) =
      BitVec.ofNat 64 (if (a && b) = true then 1 else 0) := by
  cases a <;> cases b <;> decide

/-- `zMask`, y's address from the header, y into array 8, `eqMask`, and the
status. -/
theorem cmp_split {x : XD} {Yc : Addr} {s : State} (hc : Ctx x s) (hr : RW x s) (hy : YE x Yc s)
    (hp : wordsVal s.mem x.S (slot x.w 0) x.w = x.p) (hodd : x.p % 2 = 1)
    (hzp : wordsVal s.mem x.S (slot x.w 4) x.w < x.p) :
    WP isa zMask s fun s₁ => RW x s₁ ∧ WP isa (.block ldY) s₁ fun s₂ => (RW x s₂ ∧ s₂.gpr .s7 = Yc) ∧
      WP isa (.seq loadY (.seq (eqMask 4 8) (.block both))) s₂ (CPost x Yc s) := by
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have hkw : x.k ≤ 8 * x.w := by omega_arith
  have e : ∀ j, slot x.w j = hdrBytes + j * (8 * (x.w + 2)) := fun _ => rfl
  have e0 := e 0; have e4 := e 4; have e5 := e 5; have e8 := e 8; have e24 := e 24
  have hh : hdrBytes = 256 := rfl
  obtain ⟨h6, h7, h5, h0, h11⟩ := id hr
  generalize hz : wordsVal s.mem x.S (slot x.w 4) x.w = z at hzp ⊢
  refine WP.mono (zMask_ok hc.scr h7 h5 h0 (by omega_arith) hw' (by omega_arith) (by rw [hp]; exact hodd))
    fun s₁ ⟨⟨a9, o1⟩, k1⟩ => ⟨hr.keep k1 (by decide), ?_⟩
  rw [hz, hp] at a9
  have ar1 : Arr x s.mem s₁.mem := arr_of o1 (by omega_arith) (by omega_arith)
  have hc1 := hc.keep k1.2.1 k1.2.2 ar1
  have rw1 : RW x s₁ := hr.keep k1 (by decide)
  have hy1 := hy.keep hc k1.2.1 k1.2.2 ar1
  refine WP.mono (ldh_ok hc1 rw1.1 .s7 (d := 32) (by decide) (by decide)) fun s₂ ⟨⟨a7', m2⟩, k2⟩ =>
    ⟨⟨rw1.keep k2 (by decide), by rw [a7']; exact hy1.w⟩, ?_⟩
  have rw2 : RW x s₂ := rw1.keep k2 (by decide)
  have hc2 := hc1.same k2 m2
  -- y into array 8.
  unfold loadY
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a7) (by decide) rw2.2.1 rw2.2.2.1 8) fun s₃ ⟨⟨b7, m3⟩, k3⟩ => ?_
  refine WP.mono (WP.keep [.s8] (Q := fun u => u.gpr .s8 = BitVec.ofNat 64 x.k ∧ u.mem = s₃.mem)
    (by brun [(k3.gpr (r := .s11) (by decide)).trans rw2.2.2.2.2, add_ofNat_zero]) (by rfl) (by rfl))
    fun s₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  have k24 := k3.trans k4
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  refine WP.seq (WP.mono (loadN_ok (dA := slot x.w 8) (hc2.scr.congr k24.2.2) ((k4.gpr (by decide)).trans b7)
    (by rw [k24.gpr (by decide), a7']; simp [hy1.w, off]) a8 ((k24.gpr (by decide)).trans rw2.2.2.2.1)
    (by omega_arith) hkw hw' (by omega_arith) (slot_al _ 8) (by omega_arith)
    (by rw [k24.2.1, k24.2.2, k2.2.1, k2.2.2]; exact hy1.rd) hy1.sep) fun s₅ ⟨yv, o5, k5⟩ => ?_)
  have k25 := k24.trans k5
  refine WP.mono (WP.keep [.a7, .s4] (Q := fun u => u.gpr .a7 = off x.S (slot x.w 0) ∧
    u.gpr .s4 = BitVec.allOnes 64 ∧ u.mem = s₅.mem)
    (by brun [(k25.gpr (r := .s6) (by decide)).trans rw2.1, hdrBytes, add_ofNat_zero, li_m1]
        simp [slot, hdrBytes, off]) (by rfl) (by rfl)) fun s₆ ⟨⟨a76, a46, m6⟩, k6⟩ => ?_
  have k26 := k25.trans k6
  refine WP.seq (WP.mono (eqMask_ok (j := 4) (k := 8) (hc2.scr.congr k26.2.2) a76
    ((k26.gpr (by decide)).trans rw2.2.2.1) ((k26.gpr (by decide)).trans rw2.2.2.2.1) (by omega_arith) hw'
    (by omega_arith) (by omega_arith)) fun s₇ ⟨⟨b4, m7⟩, k7⟩ => ?_)
  have z6 : wordsVal s₆.mem x.S (slot x.w 4) x.w = z := by
    rw [m6, Outside.wordsVal o5 (by omega_arith) (by omega_arith), hm4,
      Outside.wordsVal o1 (by omega_arith) (by omega_arith), hz]
  have y6 : wordsVal s₆.mem x.S (slot x.w 8) x.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yc x.k) := by
    rw [m6, yv, hm4, Pub.bytes_apart (Z := x.Z) ar1 (by omega_arith) hy.sep]
  rw [a46, z6, y6] at b4
  have h9 : s₇.gpr .s9 = bmask (decide (z ≠ 0 ∧ z ≠ 1 ∧ z ≠ x.p - 1)) :=
    ((k6.gpr (by decide)).trans ((k5.gpr (by decide)).trans (k24.gpr (by decide)) |>.trans (k2.gpr (by decide)))).trans a9 |>
      fun h => (k7.gpr (by decide)).trans h
  refine WP.mono (WP.keep [.s9, .a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 1 &&& (s₇.gpr .s9 &&& s₇.gpr .s4) ∧
    u.mem = s₇.mem) (by unfold both; brun [Dsa.RISCV64.exec_li_lit (show 1 < 2048 by decide)]) (by rfl) (by rfl))
    fun t ⟨⟨ta, tm⟩, kt⟩ => ⟨?_, (kt.gpr (by decide)).trans ((k7.gpr (by decide)).trans
      ((k26.gpr (by decide)).trans ((k2.gpr (by decide)).trans rw1.1))), ?_⟩
  · rw [ta, h9, b4, both_bv, hz]
    have hb : decide (z ≠ 0 ∧ z ≠ 1 ∧ z ≠ x.p - 1) = decide (1 < z ∧ z < x.p - 1) := by
      apply decide_eq_decide.mpr; omega_arith
    rw [hb]
    congr 1
    by_cases h1 : 1 < z ∧ z < x.p - 1 <;> by_cases h2 : z = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yc x.k) <;>
      simp [h1, h2]
  · rw [tm, m7, m6]
    have o5' : Arr x s₄.mem s₅.mem := arr_of o5 (by omega_arith) (by omega_arith)
    rw [hm4] at o5'
    exact ar1.trans o5'

/-! ## The status -/

open VG.Spec.Ffdh in
/-- `privateStatus` for a valid domain of `L = 2 k` or `3 k` octets at `D`. -/
theorem privateStatus_dom {m : Mem} {D : Addr} {k L : Nat} (hk : 0 < k) (hL : L = 2 * k ∨ L = 3 * k)
    (hv : domainValid k (Spec.Rsa.bytesAt m D L) = true) (y x : Nat) :
    privateStatus (domainOf k (Spec.Rsa.bytesAt m D L)) y x =
      if ¬ (0 < x ∧ x < Derive.bnd m D k L (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k))) then 2 else
        if (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) <
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) - 1) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) = y
        then 1 else 0 := by
  have hpv : parametersValid (domainOf k (Spec.Rsa.bytesAt m D L)) = true := by
    unfold domainValid at hv
    simp only [Bool.and_eq_true] at hv
    exact hv.1
  have h2k : 2 * k ≤ L := by omega_arith
  have hpw := Proof.Ffdh.publicValid_power hpv x
  rw [Proof.Ffdh.privateStatus_eq hpv, Derive.privateValid_dom hk hL]
  rw [Proof.Ffdh.domainOf_p m D h2k, Proof.Ffdh.domainOf_g m D h2k] at hpw ⊢
  have e : (publicValid ⟨domainOf k (Spec.Rsa.bytesAt m D L), y⟩ = true ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) = y) ↔
      ((1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) - 1) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) = y) := by
    constructor
    · rintro ⟨hp, he⟩
      subst he
      exact ⟨hpw.mp hp, rfl⟩
    · rintro ⟨hp, he⟩
      subst he
      exact ⟨hpw.mpr hp, rfl⟩
  by_cases h : 0 < x ∧ x < Derive.bnd m D k L (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k))
  · simp only [h, and_self, decide_true, Bool.true_eq_false, ↓reduceIte, not_true_eq_false]
    simp only [e]
  · simp [h]

open VG.Spec.Ffdh in
/-- The status is 2 exactly when x is out of range. -/
theorem privateStatus_two (a : Parameters) (y x : Nat) : privateStatus a y x = 2 ↔ privateValid a x = false := by
  unfold privateStatus
  cases privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> simp

end VG.Proof.Ffdh.RISCV64.CheckPrivate

/-!
## `vg_ffdh_check_private` on RISC-V: correctness

`checkPrivate` runs the front (`cpFront_ok`), loads and checks p
(`loadP_X`), and for a valid p checks x's range (`xRange_ok`): out of range
the status is 2, otherwise `g^x mod p` is computed as the exchange computes
its shared value and compared (`good_ok`); then it restores the
registers (`kp_correct`).
-/

namespace VG.Proof.Ffdh.RISCV64.CheckPrivate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive VG.Impl.Ffdh.RISCV64.CheckPrivate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd xRange_ok off_off)
open VG.Proof.Bignum (slot)
open VG.Impl.Dsa.RISCV64 (restore)

/-- `g^x mod p`, from the bytes of g and x in `m`. -/
abbrev gx (x : XD) (m : Mem) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.Y x.k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.X x.xl) % x.p

/-- What the branches leave, from `s` after p's check. -/
def KPost (x : XD) (Yc : Addr) (s t : State) : Prop :=
  (Spec.Rsa.modulusValid x.p x.k = true →
    t.gpr .a0 = BitVec.ofNat 64 (if ¬ (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p) then 2 else
      if (1 < gx x s.mem ∧ gx x s.mem < x.p - 1) ∧ gx x s.mem = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yc x.k)
      then 1 else 0)) ∧
  t.gpr .s6 = x.S ∧ Arr x s.mem t.mem

/-- x in range: `g^x mod p`, compared. -/
theorem good_ok {x : XD} {Yc : Addr} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0) (hy : YE x Yc s) :
    WP isa cpGood s fun t =>
      t.gpr .a0 = BitVec.ofNat 64 (if (1 < gx x s.mem ∧ gx x s.mem < x.p - 1) ∧
        gx x s.mem = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yc x.k) then 1 else 0) ∧
      t.gpr .s6 = x.S ∧ Arr x s.mem t.mem := by
  have hv := h.2.2.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv h.1.ctx.k64
  have hc := h.1.ctx
  have hZ := hc.hZ
  unfold slot hdrBytes at hZ
  unfold cpGood exPre cpCmp
  refine WP.seq (WP.seq (WP.mono (WP.rdwr (exPre_split h hz)) fun s₁ ⟨⟨_, h1⟩, r1, w1, _⟩ =>
    WP.mono (WP.rdwr h1) fun s₅ ⟨⟨_, h5⟩, r5, w5, _⟩ =>
      WP.seq (WP.mono (WP.rdwr h5) fun s₆ ⟨pp, r6, w6, _⟩ => ?_)))
  have hy6 : YE x Yc s₆ := hy.keep hc (by rw [r6, r5, r1]) (by rw [w6, w5, w1]) pp.arr
  refine WP.seq (WP.mono (cmp_split pp.ctx pp.regs hy6 pp.p hf.1
    (by rw [pp.z]; exact Nat.mod_lt _ (by omega_arith))) fun s₇ ⟨_, h7⟩ =>
      WP.seq (WP.mono h7 fun s₈ ⟨_, h8⟩ => WP.mono h8 fun t op => ?_))
  obtain ⟨ta, t6, at'⟩ := op
  refine ⟨?_, t6, pp.arr.trans at'⟩
  rw [ta, pp.z, Pub.bytes_apart (Z := x.Z) pp.arr (by omega_arith) hy.sep]

/-- After p's check: the body for a valid p, else the status 0. -/
theorem branch_ok {x : XD} {Yc : Addr} {s : State} (h : X4 x s) (ha : AR x s) (hy : YE x Yc s) :
    WP isa (.ite (.zero .s0) cpBody (.block [.li .a0 0])) s (KPost x Yc s) := by
  have hZ := h.1.ctx.hZ
  unfold slot hdrBytes at hZ
  refine WP.ite (s.gpr .s0 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hz : s.gpr .s0 = 0 := by simpa using hb
    have hv := h.2.2.mp hz
    unfold cpBody
    refine WP.seq (WP.mono (WP.rdwr (xRange_ok h hv ha)) fun s₁ ⟨⟨h1, z1, m1, a1⟩, r1, w1, _⟩ => ?_)
    have hY : ∀ n (Q : Addr), (∀ i < n, ∀ y, ofs x.S y < x.Z → off Q i ≠ y) →
        Spec.Rsa.bytesAt s₁.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun n Q hq =>
      Pub.bytes_apart (Z := x.Z) a1 (by omega_arith) hq
    refine WP.ite (s₁.gpr .s9 == 0) (Steps.eval_zero _ _) (fun h9 => ?_) (fun h9 => ?_)
    · have h9' : s₁.gpr .s9 = 0 := by simpa using h9
      rw [m1] at h9'
      have hr : ¬ (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p) := fun hr => by
        rw [decide_eq_true hr] at h9'; exact absurd h9' (by decide)
      refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 2 ∧ t.mem = s₁.mem)
        (by brun [Dsa.RISCV64.exec_li_lit (show 2 < 2048 by decide)]) (by rfl) (by rfl))
        fun t ⟨⟨ta, tm⟩, kt⟩ => ⟨fun _ => ?_, (kt.gpr (by decide)).trans h1.1.s6, by rw [tm]; exact a1⟩
      simp only [ta, hr, not_false_eq_true, ↓reduceIte]
    · have h9' : s₁.gpr .s9 ≠ 0 := by simpa using h9
      rw [m1] at h9'
      have hr : 0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p := by
        by_contra hr; rw [decide_eq_false hr] at h9'; exact h9' rfl
      refine WP.mono (good_ok h1 z1 (hy.keep h.1.ctx r1 w1 a1)) fun t ⟨ta, t6, at'⟩ =>
        ⟨fun _ => ?_, t6, a1.trans at'⟩
      have e : gx x s₁.mem = gx x s.mem := by simp only [gx]; rw [hY _ _ h1.1.ctx.sepY, hY _ _ h1.1.ctx.sepX]
      rw [ta, e, hY _ _ hy.sep]
      simp only [hr, and_self, not_true_eq_false, ↓reduceIte]
  · have hz : s.gpr .s0 ≠ 0 := by simpa using hb
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.mem = s.mem) (by brun [exec_li]) (by rfl) (by rfl))
      fun t ⟨tm, kt⟩ => ⟨fun hv => absurd (h.2.2.mpr hv) hz, (kt.gpr (by decide)).trans h.1.s6,
        by rw [tm]; exact Outside.refl _ _ _ _⟩

theorem ret_status (n : Nat) (hn : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

theorem kp_correct (s : State) (h : kpContract.pre s) :
    ∃ tr t, Exec isa checkPrivate s tr t ∧ abiPreserved s t ∧ kpContract.post s t := by
  show WP isa checkPrivate s fun t => abiPreserved s t ∧ kpContract.post s t
  refine abi_of ?_
  have hpre := h
  obtain ⟨hrd, hwr, dDS, dYS, dXS, dSA, nwD, nwY, nwX, nwS, ⟨hk, hk'⟩, hL,
    hyl, hx1, hxk, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hLk : 2 * (s.gpr .a2).toNat ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 3 * (s.gpr .a2).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have hwd : ((s.gpr .a2).toNat + 7) / 8 * 8 ≤ (s.gpr .a2).toNat + 7 := Nat.div_mul_le_self _ _
  have hcz : cpZ (s.gpr .a2).toNat ≤ (stackArg s 0).toNat * 8 := by unfold cpZ slot hdrBytes; omega_arith
  unfold checkPrivate
  refine WP.seq (WP.mono (WP.rdwr (cpFront_ok hpre)) fun s₃ ⟨⟨hb3, ha3, hw32, hsv, k3, o3⟩, r3, w3, _⟩ => ?_)
  have e24 : cpZ (s.gpr .a2).toNat = 256 + 24 * (8 * (((s.gpr .a2).toNat + 7) / 8 + 2)) := rfl
  have hy3 : YE (cxOf s) (s.gpr .a3) s₃ := ⟨hw32, fun i hi => by
      change i < (s.gpr .a2).toNat at hi
      rw [r3, w3]
      exact rd_of_mem (L := (s.gpr .a4).toNat) (by rw [hrd]; simp) (by change _ ≤ _; omega_arith) (BitVec.isLt _) i hi,
    fun i hi y hy => Pub.ne_of_disjoint dYS (Nat.le_of_lt (s.gpr .a4).isLt) i
      (by change i < (s.gpr .a2).toNat at hi; omega_arith) y (Nat.lt_of_lt_of_le hy hcz)⟩
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadP_X hb3) (by rfl)))
    fun s₄ ⟨⟨⟨h4, a4⟩, k4⟩, r4, w4, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (branch_ok h4 (ha3.keep k4) (hy3.keep hb3.ctx r4 w4 a4)))
    fun t₅ ⟨⟨tpost, t6, am⟩, r5, w5, _⟩ => ?_)
  have hc := hb3.ctx
  have hnS := nwS
  change Outside (s.gpr .a7) 256 (cpZ (s.gpr .a2).toNat - 256) s₃.mem s₄.mem at a4
  change Outside (s.gpr .a7) 256 (cpZ (s.gpr .a2).toNat - 256) s₄.mem t₅.mem at am
  -- The saved registers' words.
  have hs5 : Scr t₅ (s.gpr .a7) (cpZ (s.gpr .a2).toNat) := hc.scr.congr (by rw [w5, w4])
  refine WP.mono (restoreS_ok hs5 (by omega_arith) t6 ((hsv.mono a4 (Or.inr (by decide))).mono am (Or.inr (by decide))))
    fun u ⟨urs, u0, _⟩ => ⟨urs, ?_⟩
  · intro hdv
    -- The memory apart from the working space, before the branch.
    have hOZ : Outside (s.gpr .a7) 0 (cpZ (s.gpr .a2).toNat) s.mem s₄.mem :=
      (o3.mono (Nat.le_refl _) (by omega_arith)).trans (a4.mono (by omega_arith) (by omega_arith))
    have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .a7) y < cpZ (s.gpr .a2).toNat → off Q i ≠ y) →
        Spec.Rsa.bytesAt s₄.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq =>
      Pub.bytes_apart (o := 0) hOZ (by omega_arith) hq
    have bG : Spec.Rsa.bytesAt s₄.mem (cxOf s).Y (cxOf s).k =
        Spec.Rsa.bytesAt s.mem (off (s.gpr .a0) (s.gpr .a2).toNat) (s.gpr .a2).toNat := hsep _ _ hc.sepY
    have bX : Spec.Rsa.bytesAt s₄.mem (cxOf s).X (cxOf s).xl =
        Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat := hsep _ _ hc.sepX
    have bY : Spec.Rsa.bytesAt s₄.mem (s.gpr .a3) (cxOf s).k =
        Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat := by
      rw [hyl]; exact hsep _ _ hy3.sep
    have bB : bnd s₄.mem (cxOf s).D (cxOf s).k (cxOf s).L (cxOf s).p =
        bnd s.mem (s.gpr .a0) (s.gpr .a2).toNat (s.gpr .a1).toNat (cxOf s).p := by
      unfold bnd
      by_cases hq : (cxOf s).L = 3 * (cxOf s).k
      · have hq' : (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat := hq
        rw [ite_eq_left hq, ite_eq_left hq', hsep _ _ fun i hi => by
          change i < (s.gpr .a2).toNat at hi
          have h' := hc.sepD (2 * (s.gpr .a2).toNat + i) (by change _ < (s.gpr .a1).toNat; omega_arith)
          rw [← off_off] at h'; exact h']
        rfl
      · rw [ite_eq_right hq, ite_eq_right (show ¬ (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat from hq)]
    have hmod := Proof.Ffdh.domainValid_mod hdv
    have hpe : (Spec.Ffdh.domainOf (s.gpr .a2).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)).p =
        (cxOf s).p := by
      rw [Proof.Ffdh.domainOf_p _ _ hLk.1]
      show _ = Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat).take (s.gpr .a2).toNat)
      rw [Proof.Ffdh.take_bytesAt _ _ (by omega_arith)]
    have hpD : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a2).toNat) = (cxOf s).p := by
      rw [← hpe, Proof.Ffdh.domainOf_p _ _ hLk.1]
    rw [hpe] at hmod
    have ta := tpost hmod
    simp only [gx] at ta
    simp only [bG, bX, bB, bY] at ta
    have hL' : (s.gpr .a1).toNat = 2 * (s.gpr .a2).toNat ∨ (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat := hL
    show _ = Spec.Ffdh.privateStatus _ _ _
    rw [privateStatus_dom (by omega_arith) hL' hdv, u0, ta]
    simp only [hpD]
    rw [ret_status _ (by split <;> [decide; split <;> decide])]

end VG.Proof.Ffdh.RISCV64.CheckPrivate

/-!
## `vg_ffdh_check_private` on RISC-V: constant time

As `vg_ffdh_derive_public`'s (`Derive/CT.lean`), whose predicates on its data
`DD` (the exchange's public data and x's range, which the status reveals)
this carries with y's address `Yc` and the facts on it (`YE`, the data
`CD`); after the power, the comparison's own predicates (`K6`–`K8`) fix the
registers it uses as addresses and counts, y's address among them.
-/

namespace VG.Proof.Ffdh.RISCV64.CheckPrivate

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive VG.Impl.Ffdh.RISCV64.CheckPrivate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd xRange_ok off_off DD inRange Inv W Z4 RB pins_W pins_Z4 lp_W pins_RB
  pins_TI two_x)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- The public data of a run: `vg_ffdh_derive_public`'s, and y's address. -/
structure CD where
  d : DD
  Yc : Addr

def kdOf (s : State) : CD := ⟨⟨cxOf s, inRange (cxOf s) s.mem⟩, s.gpr .a3⟩

/-- `Φ` of `vg_ffdh_derive_public`'s data, with y's facts. -/
def V (Φ : DD → State → Prop) (c : CD) (s : State) : Prop := Φ c.d s ∧ YE c.d.x c.Yc s

theorem pins_V {Φ : DD → State → Prop} {rs : List Reg} (h : Pins Φ rs) : Pins (V Φ) rs :=
  fun c _ _ h₁ h₂ => h c.d _ _ h₁.1 h₂.1

/-! ## The predicates -/

def Q0 (c : CD) (s : State) : Prop := kpContract.pre s ∧ kdOf s = c

/-- Before the comparison's load of y's address. -/
def K8 (a : XD × Addr) (s : State) : Prop :=
  (RW a.1 s ∧ s.gpr .s7 = a.2) ∧ WP isa (.seq loadY (.seq (eqMask 4 8) (.block both))) s (CF a.1)

/-- After `zMask`. -/
def K7 (a : XD × Addr) (s : State) : Prop := RW a.1 s ∧ WP isa (.block ldY) s (K8 a)

/-- After the power. -/
def K6 (a : XD × Addr) (s : State) : Prop := RW a.1 s ∧ WP isa zMask s (K7 a)

/-- Before the power. -/
def K5 (a : XD × Addr) (s : State) : Prop := R5 a.1 s ∧ WP isa ModExp.powWinFn s (K6 a)

/-- After the peer's address. -/
def K1 (a : XD × Addr) (s : State) : Prop :=
  R1 a.1 s ∧ WP isa (.seq PublicChecked.loadX (.seq r2 (.block [.load .d .s9 .s6 8, .load .d .s10 .s6 16]))) s
    (K5 a)

/-! ## Pins -/

theorem pins_Q0 : Pins Q0 [.a7] := by
  rintro c s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact (congrArg (fun c => c.d.x.S) h₁).trans (congrArg (fun c => c.d.x.S) h₂).symm

theorem pins_K1 : Pins K1 [.a6, .s6, .a7, .s5, .t0, .s11] := pins_of (fun a => rwVal a.1) fun a s h r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr
  · exact h.1.1
  · exact rw_vals h.1.2 r (by simpa using hr)

theorem pins_K5 : Pins K5 [.s9, .s10, .s6, .a7, .s5, .t0, .s11] := pins_of (fun a => rwVal a.1) fun a s h r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · exact h.1.1
  · exact h.1.2.1
  · exact rw_vals h.1.2.2 r (by simpa using hr)

theorem pins_K6 : Pins K6 [.s6, .a7, .s5, .t0, .s11] := pins_of (fun a => rwVal a.1) fun _ _ h => rw_vals h.1

theorem pins_K7 : Pins K7 [.s6, .a7, .s5, .t0, .s11] := pins_of (fun a => rwVal a.1) fun _ _ h => rw_vals h.1

theorem pins_K8 : Pins K8 [.s7, .s6, .a7, .s5, .t0, .s11] :=
  pins_of (fun a r => if r = .s7 then a.2 else rwVal a.1 r) fun a s h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · exact h.1.2
    · have hne : r ≠ .s7 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
      exact rw_vals h.1.1 r (by simpa using hr)

/-! ## The steps, by correctness -/

theorem front_V {c : CD} {s : State} (h : Q0 c s) : WP isa (.block cpFront) s (V (W Base) c) := by
  obtain ⟨hpre, rfl⟩ := h
  have hpre' := hpre
  obtain ⟨hrd, -, -, dYS, -, -, -, -, -, -, ⟨hk, -⟩, -, hyl, -, -, hsl, -, -⟩ := hpre'
  simp only [Spec.Rsa.scratchWords] at hsl
  have hwd : ((s.gpr .a2).toNat + 7) / 8 * 8 ≤ (s.gpr .a2).toNat + 7 := Nat.div_mul_le_self _ _
  have hcz : cpZ (s.gpr .a2).toNat ≤ (stackArg s 0).toNat * 8 := by unfold cpZ slot hdrBytes; omega_arith
  refine WP.mono (WP.rdwr (cpFront_ok hpre)) fun t ⟨⟨hb, ha, hw32, _, _, o⟩, r, w, _⟩ =>
    ⟨⟨hb, ha, ?_⟩, hw32, fun i hi => ?_, fun i hi y hy => Pub.ne_of_disjoint dYS (Nat.le_of_lt (s.gpr .a4).isLt) i
      (by change i < (s.gpr .a2).toNat at hi; omega_arith) y (Nat.lt_of_lt_of_le hy hcz)⟩
  · have hZ := hb.ctx.hZ
    unfold slot hdrBytes at hZ
    have hn : 0 + 256 ≤ (cxOf s).Z := by omega_arith
    have hi : Derive.Inv (kdOf s).d s := by unfold Derive.Inv kdOf; dsimp only
    exact Derive.Inv.keep (s := s) (t := t) hi hb.ctx o hn
  · change i < (s.gpr .a2).toNat at hi
    change InRegions _ (off (s.gpr .a3) i) 1
    rw [r, w]
    exact rd_of_mem (L := (s.gpr .a4).toNat) (by rw [hrd]; simp) (by omega_arith) (BitVec.isLt _) i hi

/-- A piece of `loadP`, which writes only `a0`, `s0`, `t3`–`t5` and arrays. -/
theorem lp_V {Φ Ψ : XD → State → Prop} {c : Prog isa} {cd : CD} {s : State}
    (hc : ∀ x s, Φ x s → Ctx x s) (h : V (W Φ) cd s)
    (hw : WP isa c s fun t => (Ψ cd.d.x t ∧ Arr cd.d.x s.mem t.mem) ∧ Keep [.a0, .s0, .t3, .t4, .t5] s t) :
    WP isa c s (V (W Ψ) cd) :=
  WP.mono (WP.and (lp_W hc h.1 hw) (WP.rdwr hw)) fun _ ⟨h', ⟨⟨_, a⟩, _⟩, r, w, _⟩ =>
    ⟨h', h.2.keep (hc _ _ h.1.1) r w a⟩

theorem TVc {a : XD × Addr} {s : State} (h : (X4 a.1 s ∧ s.gpr .s0 = 0) ∧ YE a.1 a.2 s) :
    WP isa (.block [.load .d .a6 .s6 24]) s (K1 a) := by
  obtain ⟨⟨h4, hz⟩, hy⟩ := h
  have hv := h4.2.2.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv h4.1.ctx.k64
  refine WP.mono (WP.rdwr (exPre_split h4 hz)) fun s₁ ⟨⟨r1, w1⟩, rd1, wr1, _⟩ => ⟨r1,
    WP.mono (WP.rdwr w1) fun s₅ ⟨⟨r5, w5⟩, rd5, wr5, _⟩ => ⟨r5,
      WP.mono (WP.rdwr w5) fun s₆ ⟨pp, rd6, wr6, _⟩ => ⟨pp.regs, ?_⟩⟩⟩
  have hy6 : YE a.1 a.2 s₆ := hy.keep h4.1.ctx (by rw [rd6, rd5, rd1]) (by rw [wr6, wr5, wr1]) pp.arr
  exact WP.mono (cmp_split pp.ctx pp.regs hy6 pp.p hf.1 (by rw [pp.z]; exact Nat.mod_lt _ (by omega_arith)))
    fun s₇ ⟨r7, w7⟩ => ⟨r7, WP.mono w7 fun s₈ ⟨r8, w8⟩ => ⟨r8, WP.mono w8 fun t op => op.2.1⟩⟩

/-! ## Constant time -/

/-- x in range: the exchange's power, then the comparison. -/
theorem good_rel : RelCT isa (Two fun (a : XD × Addr) s => (X4 a.1 s ∧ s.gpr .s0 = 0) ∧ YE a.1 a.2 s) cpGood
    (Two fun (a : XD × Addr) s => CF a.1 s) := by
  unfold cpGood exPre cpCmp
  exact RelCT.seq (RelCT.seq (two_post (two_taint _ (fun a s₁ s₂ h₁ h₂ =>
        pins_base (Φ := X4) (fun _ _ h => h.1) a.1 s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide)) fun _ _ h => TVc h)
    (two_post (two_taint _ pins_K1 (by taint_decide)) fun _ _ h => h.2))
    (RelCT.seq (two_post (two_taint _ pins_K5 (by taint_decide)) fun _ _ h => h.2)
      (RelCT.seq (two_post (two_taint _ pins_K6 (by taint_decide)) fun _ _ h => h.2)
        (RelCT.seq (two_post (two_taint _ pins_K7 (by taint_decide)) fun _ _ h => h.2)
          (two_post (two_taint _ pins_K8 (by taint_decide)) fun _ _ h => h.2))))

theorem two_a {Φ : XD → State → Prop} {s₁ s₂ : State} (h : Two (fun (a : XD × Addr) s => Φ a.1 s) s₁ s₂) :
    Two Φ s₁ s₂ :=
  let ⟨a, h₁, h₂, hsp⟩ := h
  ⟨a.1, h₁, h₂, hsp⟩

theorem two_c {Φ : XD → State → Prop} {s₁ s₂ : State} (h : Two (fun (c : CD) s => Φ c.d.x s) s₁ s₂) :
    Two Φ s₁ s₂ :=
  let ⟨c, h₁, h₂, hsp⟩ := h
  ⟨c.d.x, h₁, h₂, hsp⟩

theorem pins_TB : Pins (fun c s => V RB c s ∧ s.gpr .s9 = 0) baseRegs :=
  fun c s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) c.d.x s₁ s₂ h₁.1.1.1 h₂.1.1.1

theorem TB {c : CD} {s : State} (h : V RB c s ∧ s.gpr .s9 = 0) : WP isa (.block [.li .a0 2]) s (CF c.d.x) :=
  WP.mono (WP.keep [.a0] (Q := fun _ => True) (by brun [Dsa.RISCV64.exec_li_lit (show 2 < 2048 by decide)]; exact ⟨_, rfl⟩)
    (by rfl) (by rfl)) fun _ ⟨_, kt⟩ => (kt.gpr (by decide)).trans h.1.1.1.1.s6

/-- After p's check, for a valid p. -/
theorem body_rel : RelCT isa (Two (V Z4)) cpBody (Two CF) := by
  unfold cpBody
  refine RelCT.seq (R := Two (V RB)) (two_post (two_taint _ (pins_V pins_Z4) (by taint_decide)) fun c s h => ?_) ?_
  rotate_left
  · refine RelCT.ite (fun s₁ s₂ ⟨c, h₁, h₂, _⟩ => ?_)
      (RelCT.mono (two_post (Φ := fun c s => V RB c s ∧ s.gpr .s9 = 0)
        (two_taint _ pins_TB (by taint_decide))
        (Ψ := fun c s => CF c.d.x s) fun _ _ h => TB h)
        (fun s₁ s₂ ⟨⟨c, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => two_c h)
      (RelCT.mono good_rel (fun s₁ s₂ ⟨⟨c, h₁, h₂, hsp⟩, _⟩ =>
        ⟨(c.d.x, c.Yc), ⟨⟨h₁.1.1, h₁.1.2.1⟩, h₁.2⟩, ⟨⟨h₂.1.1, h₂.1.2.1⟩, h₂.2⟩, hsp⟩) fun _ _ h => two_a h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.1.2.2, h₂.1.2.2]
    · rw [Steps.eval_zero] at hc
      have h9 : s₁.gpr .s9 = 0 := by simpa using hc
      exact ⟨c, ⟨h₁, h9⟩, ⟨h₂, h₂.1.2.2.mpr (h₁.1.2.2.mp h9)⟩, hsp⟩
  · obtain ⟨⟨⟨h4, ha, hi⟩, hz⟩, hy⟩ := h
    have hv := h4.2.2.mp hz
    refine WP.mono (WP.rdwr (xRange_ok h4 hv ha)) fun t ⟨⟨t4, t0, t9, at'⟩, r, w, _⟩ =>
      ⟨⟨t4, t0, ?_⟩, hy.keep h4.1.ctx r w at'⟩
    rw [t9]
    have hi' : inRange c.d.x s.mem = c.d.v := hi
    unfold inRange at hi'
    rw [hi']
    cases c.d.v <;> decide

theorem pins_TIc : Pins (fun c s => V (W X4) c s ∧ s.gpr .s0 ≠ 0) baseRegs :=
  fun c s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) c.d.x s₁ s₂ h₁.1.1.1 h₂.1.1.1

theorem kp_rel : RelCT isa (Two Q0) checkPrivate fun _ _ => True := by
  unfold checkPrivate
  refine RelCT.seq (R := Two (V (W Base))) (two_post (two_taint _ pins_Q0 (by taint_decide)) fun _ _ h => front_V h)
    (RelCT.seq (R := Two (V (W X4))) ?_ (RelCT.seq (R := Two CF) ?_ (two_taint _ pins_CF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_V (pins_W (pins_base fun _ _ h => h))) (by taint_decide))
        fun _ _ h => lp_V (fun _ _ h => h.ctx) h (WP.keep _ (loadN_X h.1.1) (by rfl)))
      (RelCT.seq (two_post (two_taint _ (pins_V (pins_W (pins_base (Φ := X2) fun _ _ h => h.1))) (by taint_decide))
          fun _ _ h => lp_V (fun _ _ h => h.1.ctx) h (WP.keep _ (WP.mono (check1_X h.1.1) fun t ⟨h3, m⟩ =>
            ⟨h3, by rw [m]; exact Outside.refl _ _ _ _⟩) (by rfl)))
        (two_post (two_taint _ (pins_V (pins_W pins_X3)) (by taint_decide)) fun _ _ h =>
          lp_V (fun _ _ h => h.1.ctx) h
            (WP.keep _ (WP.mono (check2_X h.1.1) fun t ⟨h4, m⟩ => ⟨h4, by rw [m]; exact Outside.refl _ _ _ _⟩) (by rfl))))
  · refine RelCT.ite (fun s₁ s₂ ⟨c, h₁, h₂, _⟩ => ?_)
      (RelCT.mono body_rel (fun s₁ s₂ ⟨⟨c, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
      (RelCT.mono (two_post (Φ := fun c s => V (W X4) c s ∧ s.gpr .s0 ≠ 0)
        (two_taint _ pins_TIc (by taint_decide)) (Ψ := fun c s => CF c.d.x s) fun _ _ h => TI ⟨h.1.1.1, h.2⟩)
        (fun s₁ s₂ ⟨⟨c, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => two_c h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.1.1.2.2, h₂.1.1.2.2]
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 = 0 := by simpa using hc
      exact ⟨c, ⟨⟨h₁.1, h0⟩, h₁.2⟩, ⟨⟨h₂.1, h₂.1.1.2.2.mpr (h₁.1.1.2.2.mp h0)⟩, h₂.2⟩, hsp⟩
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 ≠ 0 := by simpa using hc
      exact ⟨c, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 (h₁.1.1.2.2.mpr (h₂.1.1.2.2.mp e))⟩, hsp⟩

/-- `inRange` as `privateValid` of the domain. -/
theorem inRange_eq {s : State} (h : kpContract.pre s) :
    inRange (cxOf s) s.mem = Spec.Ffdh.privateValid (Spec.Ffdh.domainOf (s.gpr .a2).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := h
  have hL' : (s.gpr .a1).toNat = 2 * (s.gpr .a2).toNat ∨ (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat := hL
  rw [Derive.privateValid_dom (by omega_arith) hL']
  have hp : (cxOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a2).toNat) := by
    show Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat).take (s.gpr .a2).toNat) = _
    rw [Proof.Ffdh.take_bytesAt _ _ (by rcases hL' with h | h <;> omega_arith)]
  unfold inRange
  rw [hp]
  rfl

theorem kdOf_eq {s t : State} (hs : kpContract.pre s) (ht : kpContract.pre t) (hp : kpContract.pub s t) :
    kdOf s = kdOf t := by
  obtain ⟨_, h0, h1, h2, h3, h4, h5, h6, h7, a0, hb⟩ := hp
  simp only [kpLeak] at hb
  obtain ⟨e12, e3⟩ := List.append_inj hb (by
    simp only [List.length_append, List.length_map, VG.Proof.Bignum.bytesAt_length, h1, h4])
  obtain ⟨e1, -⟩ := List.append_inj e12 (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h1])
  have eb : Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a0) (t.gpr .a1).toNat :=
    (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
  have ex : cxOf s = cxOf t := by
    simp only [cxOf]
    rw [eb]
    simp only [h0, h1, h2, h5, h6, h7]
  have ev : inRange (cxOf s) s.mem = inRange (cxOf t) t.mem := by
    rw [inRange_eq hs, inRange_eq ht]
    have ek := List.cons.inj e3 |>.1
    simp only [kpStatus] at ek
    rw [eb, h2] at ek
    rw [eb, h2]
    generalize Spec.Ffdh.domainOf (t.gpr .a2).toNat (Spec.Rsa.bytesAt t.mem (t.gpr .a0) (t.gpr .a1).toNat) = a at ek ⊢
    have := (privateStatus_two a _ _).symm.trans ((iff_of_eq (congrArg (· = 2) ek)).trans (privateStatus_two a _ _))
    cases h₁ : Spec.Ffdh.privateValid a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)) <;>
      cases h₂ : Spec.Ffdh.privateValid a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (t.gpr .a5) (t.gpr .a6).toNat)) <;>
      simp_all
  unfold kdOf
  rw [ev, ex, h3]

theorem kp_ct : ConstantTime isa kpContract.pre kpContract.pub checkPrivate :=
  RelCT.constantTime (kp_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨kdOf s, ⟨hs, rfl⟩, ⟨ht, (kdOf_eq hs ht hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.RISCV64.CheckPrivate

/-!
## `vg_ffdh_check_private` on RISC-V: verified against the shared contract

`kpContract` states the shared contract on the registers and the stack
(`kp_implies`); with correctness (`kp_correct`) and constant time (`kp_ct`),
`checkPrivate` is verified (`checkPrivate_verified`).
-/

namespace VG.Proof.Ffdh.RISCV64.CheckPrivate

open VG VG.RISCV64

theorem kpStackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting `kpContract.pre`: a 512-bit p without q, the domain at
`0x2000`, y at `0x3100`, x at `0x3000`, the working space at `0x4000`, and the
stack argument at `0x9000`. -/
def kpSatState : State where
  gpr r := match r with
    | .a0 => 0x2000 | .a1 => 128 | .a2 => 64 | .a3 => 0x3100 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9000 then 0x20 else bif Nat.beq a.toNat 0x9001 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3100, 64⟩, ⟨0x3000, 1⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x4000, 8448⟩]

theorem kp_implies : kpContract.Implies (Spec.Ffdh.checkPrivateContract RISCV64.abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | sig_disjoint_symm
      | omega
      | (sig_simp_only [Nat.mul_comm] at *
         first | with_reducible assumption | sig_disjoint_symm)
      | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_false,
          Bool.cond_true, Sig.conj_cons, List.nil_append, List.cons_append] at *
         simp_all only [kpStack])
  post := by
    sig_implies_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs,
      kpContract, kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs,
      kpContract, kpStackArgs_one, kpLeak, kpStatus, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs,
      kpContract, kpStackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [kpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSatState

/-- `vg_ffdh_check_private`. -/
theorem checkPrivate_verified :
    Verified RISCV64.target Impl.Ffdh.RISCV64.CheckPrivate.checkPrivate (Spec.Ffdh.checkPrivateContract RISCV64.abi 0) :=
  Verified.of_correct kp_correct kp_ct kp_implies

end VG.Proof.Ffdh.RISCV64.CheckPrivate
