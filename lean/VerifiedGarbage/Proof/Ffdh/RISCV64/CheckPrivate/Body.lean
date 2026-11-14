module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
public import VerifiedGarbage.Impl.Ffdh.RISCV64.CheckPrivate
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.RISCV64.Li

/-!
# `vg_ffdh_check_private` on RISC-V: the front

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
open VG.Proof.Bignum.RISCV64.Pub (savW savR)

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
  brun [h6', h7, h5, i0, l0, fin64_exec_li_lit (show 24 < 2048 by decide), out_addr]

/-- The registers the front writes. -/
def frontRegs : List Reg := [.t0, .s6, .a2, .a3, .a4, .t2, .s7, .s8, .a1, .a7, .s5, .s10, .s11]

/-- `cpFront`: `Base`, `AR`, y's address in the header's word 4, the
callee-saved registers saved, and only the header changed. -/
theorem cpFront_ok {s : State} (h : kpContract.pre s) :
    WP isa (.block cpFront) s fun t =>
      Base (cxOf s) t ∧ AR (cxOf s) t ∧ word t.mem (s.gpr .a7) 32 = s.gpr .a3 ∧
        (∀ i < 12, t.mem.readW (off (savW (s.gpr .a7)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
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
  simp only [List.append_assoc]
  have h1 : WP isa (.block ([.addi .t0 .a7 0] : List Instr)) s fun t =>
      (t.gpr .t0 = S ∧ t.mem = s.mem) ∧ Keep [.t0] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [hSd, add_ofNat_zero]
  refine WP.block_append (WP.mono h1 fun s₁ ⟨⟨a0', m1⟩, k1⟩ => ?_)
  have hin : ∀ i < 12, InRegions s₁.wr (off (savW (s₁.gpr .t0)) (8 * i)) 8 := fun i hi => by
    rw [a0', k1.2.2, hwr]
    show InRegions _ (S + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.block_append (WP.mono (Pub.save_ok s₁ hin (fun i hi => by
    rw [a0']; exact Pub.sav_al alS (by omega_arith) hi)) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have h6₂ : s₂.gpr .s6 = S := hS.s6.trans a0'
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
  have hsavO : Outside S 0 256 s.mem s₂.mem := fun y hy => by
    rw [← m1]
    refine hS.frame y fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [a0'] at hc
    have hc' := (Offset.sub_base (n := 96) (k := 256) S (d := 128) (by omega_arith)) _ hc
    simp only [Region.Contains] at hc'
    simp only [ofs] at hy
    omega_arith
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
  · intro i hi
    have e : off (savW S) (8 * i) = off S (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [e]
    show word t.mem S (128 + 8 * i) = _
    rw [ot.word (Or.inr (by omega_arith)) (by omega_arith), jm, o3.word (Or.inr (by omega_arith)) (by omega_arith)]
    show s₂.mem.readW (off S (128 + 8 * i)) 64 = _
    rw [← e, ← a0', hS.saved i hi, k1.gpr fun h => Pub.saved_ne_t0 i hi (List.mem_singleton.mp h)]

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
    u.mem = s₇.mem) (by unfold both; brun [fin64_exec_li_lit (show 1 < 2048 by decide)]) (by rfl) (by rfl))
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
