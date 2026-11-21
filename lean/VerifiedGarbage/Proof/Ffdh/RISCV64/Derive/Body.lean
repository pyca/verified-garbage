module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Power
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ZMask
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Derive
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.RISCV64.Li

/-!
# `vg_ffdh_derive_public` on RISC-V: the front and x's range

`dpContract`: `vg_ffdh_derive_public(y = a0, y_len = a1, domain = a2,
domain_len = a3, p_len = a4, x = a5, x_len = a6, scratch = a7, scratch_len)`,
the last on the stack. `dxOf`: the exchange's public data (`XD`), with `y` as
`out` and g (`domain + p_len`) as the peer. `dpFront_ok`: `dpFront` saves the
callee-saved registers, stores the header's words 0–3 and sets up as the
exchange's front does. `xRange_ok`: with p in array 0, `xRange` leaves in
`s9` the mask of `0 < x < bnd`, the registers of `Base` back, and `s0 = 0`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Derive

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-! ## The function -/

/-- The argument on the stack: `scratch_len`. -/
abbrev dpStack (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- What timing may depend on: the domain and the status. -/
def dpLeak (s : State) : List Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat
  dom.map (·.toNat) ++ [Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (s.gpr .a4).toNat dom)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat))]

/-- `vg_ffdh_derive_public`, on the registers and the stack. -/
def dpContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let dom : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let x : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
    let scr : Region := ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩
    s.rd = [dom, x, dpStack s] ∧ s.wr = [out, scr] ∧
      out.Disjoint dom ∧ out.Disjoint x ∧ out.Disjoint scr ∧ out.Disjoint (dpStack s) ∧
      dom.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint (dpStack s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .a4).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .a4).toNat (s.gpr .a3).toNat ∧
      (s.gpr .a1).toNat = (s.gpr .a4).toNat ∧ 1 ≤ (s.gpr .a6).toNat ∧ (s.gpr .a6).toNat ≤ (s.gpr .a4).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 0).toNat ∧
      (s.gpr .a7).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat
    let a := Spec.Ffdh.domainOf (s.gpr .a4).toNat dom
    let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
    Spec.Ffdh.domainValid (s.gpr .a4).toNat dom = true →
      ((t.gpr .a0).setWidth 32).toNat = Spec.Ffdh.keyStatus a x ∧
        if Spec.Ffdh.keyStatus a x = 1 then
          Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a4).toNat =
            Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (s.gpr .a4).toNat
        else Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a4).toNat = List.replicate (s.gpr .a4).toNat 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ dpLeak s₁ = dpLeak s₂

/-- The exchange's public data: `y` as `out`, g as the peer. -/
def dxOf (s : State) : XD :=
  ⟨s.gpr .a0, s.gpr .a2, (s.gpr .a3).toNat, (s.gpr .a4).toNat, s.gpr .a5, (s.gpr .a6).toNat,
    off (s.gpr .a2) (s.gpr .a4).toNat, s.gpr .a7, (stackArg s 0).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat⟩

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-! ## The front -/

/-- `y`, x, `x_len` and g's address into the header's words 0–3 at `S`
(`s6`), the domain into `s7` and `p_len` into `s8` and `a1`. -/
theorem dhdr_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 32 ≤ Z) (h6 : s.gpr .s6 = S) :
    WP isa (.block ([.store .d .a0 .s6 0, .store .d .a5 .s6 8, .store .d .a6 .s6 16, .add .t2 .a2 .a4,
      .store .d .t2 .s6 24, .addi .s7 .a2 0, .addi .s8 .a4 0, .addi .a1 .a4 0] : List Instr)) s fun t =>
      (word t.mem S 0 = s.gpr .a0 ∧ word t.mem S 8 = s.gpr .a5 ∧ word t.mem S 16 = s.gpr .a6 ∧
        word t.mem S 24 = s.gpr .a2 + s.gpr .a4 ∧ t.gpr .s7 = s.gpr .a2 ∧ t.gpr .s8 = s.gpr .a4 ∧
        t.gpr .a1 = s.gpr .a4 ∧ Outside S 0 32 s.mem t.mem) ∧ Keep [.t2, .s7, .s8, .a1] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  have i0 := hs.st (d := 0) (n := 8) (by omega_arith)
  have i8 := hs.st (d := 8) (n := 8) (by omega_arith)
  have i16 := hs.st (d := 16) (n := 8) (by omega_arith)
  have i24 := hs.st (d := 24) (n := 8) (by omega_arith)
  have l0 := hs.al8 (d := 0) (by omega_arith) (by decide)
  have l8 := hs.al8 (d := 8) (by omega_arith) (by decide)
  have l16 := hs.al8 (d := 16) (by omega_arith) (by decide)
  have l24 := hs.al8 (d := 24) (by omega_arith) (by decide)
  have o0 := writeW_outside s.mem S (d := 0) (s.gpr .a0) (by omega_arith)
  have o1 := writeW_outside (s.mem.writeW (off S 0) (s.gpr .a0)) S (d := 8) (s.gpr .a5) (by omega_arith)
  have o2 := writeW_outside ((s.mem.writeW (off S 0) (s.gpr .a0)).writeW (off S 8) (s.gpr .a5)) S (d := 16)
    (s.gpr .a6) (by omega_arith)
  have o3 := writeW_outside (((s.mem.writeW (off S 0) (s.gpr .a0)).writeW (off S 8) (s.gpr .a5)).writeW
    (off S 16) (s.gpr .a6)) S (d := 24) (s.gpr .a2 + s.gpr .a4) (by omega_arith)
  refine WP.mono (WP.keep [.t2, .s7, .s8, .a1] (Q := fun t => t.mem = (((s.mem.writeW (off S 0) (s.gpr .a0)).writeW
      (off S 8) (s.gpr .a5)).writeW (off S 16) (s.gpr .a6)).writeW (off S 24) (s.gpr .a2 + s.gpr .a4) ∧
      t.gpr .s7 = s.gpr .a2 ∧ t.gpr .s8 = s.gpr .a4 ∧ t.gpr .a1 = s.gpr .a4) ?_ (by rfl) (by rfl))
    fun t ⟨⟨tm, t7, t8, t1⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_, t7, t8, t1, ?_⟩, kt⟩
  · brun [h6', i0, i8, i16, i24, l0, l8, l16, l24]
    exact ⟨BitVec.add_zero _, BitVec.add_zero _⟩
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

/-- The registers the front writes. -/
def frontRegs : List Reg := [.t0, .s6, .t2, .s7, .s8, .a1, .a7, .s5, .s10, .s11]

/-- `dpFront`: `Base`, the callee-saved registers saved, and only the header
changed. -/
theorem dpFront_ok {s : State} (h : dpContract.pre s) :
    WP isa (.block dpFront) s fun t =>
      Base (dxOf s) t ∧
        (∀ i < 12, t.mem.readW (off (savW (s.gpr .a7)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
        Keep frontRegs s t ∧ Outside (s.gpr .a7) 0 256 s.mem t.mem := by
  obtain ⟨hrd, hwr, dOD, dOX, dOS, dOA, dDS, dXS, dSA, nwO, nwD, nwX, nwS, ⟨hk, hk'⟩, hL,
    hol, hx1, hxk, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [dxOf]
  generalize hSd : s.gpr .a7 = S at hwr dOS dDS dXS dSA nwS alS ⊢
  generalize hZd : (stackArg s 0).toNat * 8 = Z at hwr dOS dDS dXS dSA nwS ⊢
  have hZ : 256 + 128 * (s.gpr .a4).toNat ≤ Z := by omega_arith
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS alS
  unfold dpFront
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
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.block_append (WP.mono (Pub.save_ok s₁ hin (fun i hi => by
    rw [a0']; exact Pub.sav_al alS (by omega_arith) hi)) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have h6₂ : s₂.gpr .s6 = S := hS.s6.trans a0'
  refine WP.block_append (WP.mono (dhdr_ok (hs.congr k12.2.2) (by omega_arith) h6₂)
    fun s₃ ⟨⟨w0, w8, w16, w24, b7, b8, b1, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.mono (Pub.setup_ok (O := s.gpr .a0) (k := (s.gpr .a4).toNat) ((k13.gpr (by decide)))
    (by rw [b1, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    ((k3.gpr (by decide)).trans h6₂) hk') fun t ⟨⟨j10, j11, j0, j5, j7, jm⟩, k4⟩ => ?_
  have k := k13.trans k4
  have hrdt : t.rd ++ t.wr = s.rd ++ s.wr := by rw [k.2.1, k.2.2]
  -- Memory: the saved registers' words and the header's words 0–3.
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
    rw [jm]; exact hsavO.trans (o3.mono (Nat.le_refl _) (by omega_arith))
  have hOZ : Outside S 0 Z s.mem t.mem := hO.mono (Nat.le_refl _) (by omega_arith)
  have hb : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs S y < Z → off Q i ≠ y) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep =>
    Pub.bytes_apart (o := 0) (n := Z) hOZ (by omega_arith) hsep
  have hw3 : ∀ d, d + 8 ≤ 32 → word t.mem S d = word s₃.mem S d := fun d _ => by rw [jm]
  have hLk : 2 * (s.gpr .a4).toNat ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 3 * (s.gpr .a4).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have sepD := Pub.ne_of_disjoint dDS (Nat.le_of_lt (s.gpr .a3).isLt)
  have rdD : ∀ i < (s.gpr .a3).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a2) i) 1 := by
    rw [hrdt]; exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  have rdX : ∀ i < (s.gpr .a6).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a5) i) 1 := by
    rw [hrdt]; exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  refine ⟨⟨⟨hs.congr k.2.2, hk, hk', hLk, ?_, by rw [← hol]; exact nwO, fun i hi => ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩,
      by rw [k.2.2, hwr]; simp, Offset.contains_base _ (by change i < (s.gpr .a4).toNat at hi; omega_arith)
        (by change i < (s.gpr .a4).toNat at hi; omega_arith)⟩,
      fun y hy => Pub.sep_of_disjoint dOS y (by rw [hol]; exact hy),
      rdD, sepD, fun i hi => by rw [off_off]; exact rdD _ (by change i < (s.gpr .a4).toNat at hi; omega_arith),
      fun i hi => by rw [off_off]; exact sepD _ (by change i < (s.gpr .a4).toNat at hi; omega_arith),
      rdX, Pub.ne_of_disjoint dXS (Nat.le_of_lt (s.gpr .a6).isLt), hx1, hxk,
      (by rw [hb _ _ sepD]), ?_, ?_, ?_, ?_⟩,
    by rw [k4.gpr (by decide), k3.gpr (by decide)]; exact h6₂, j7,
    by rw [j5, Nat.mul_add], j0, by rw [k4.gpr (by decide), b7, k12.gpr (by decide)]; simp [off],
    by rw [k4.gpr (by decide), b8, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [j10]; simp [off], j11⟩, ?_, k.mono (by decide), hO⟩
  · show slot (((s.gpr .a4).toNat + 7) / 8) 24 ≤ Z
    unfold slot hdrBytes; omega_arith
  · rw [hw3 0 (by decide), w0, k12.gpr (by decide)]; simp [off]
  · rw [hw3 8 (by decide), w8, k12.gpr (by decide)]; simp [off]
  · rw [hw3 16 (by decide), w16, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hw3 24 (by decide), w24, k12.gpr (by decide), k12.gpr (by decide)]; simp [off]
  · intro i hi
    have e : off (savW S) (8 * i) = off S (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [e]
    show word t.mem S (128 + 8 * i) = _
    rw [jm, o3.word (Or.inr (by omega_arith)) (by omega_arith)]
    show s₂.mem.readW (off S (128 + 8 * i)) 64 = _
    rw [← e, ← a0', hS.saved i hi, k1.gpr fun h => Pub.saved_ne_t0 i hi (List.mem_singleton.mp h)]

/-! ## x's range -/

/-- The bound on x: q (the `k` octets at `D + 2 k`) if `L = 3 k`, else
`p − 1`. -/
def bnd (m : Mem) (D : Addr) (k L p : Nat) : Nat :=
  if L = 3 * k then Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D (2 * k)) k) else p - 1

/-- The argument registers the range reads: the domain, its length, `p_len`,
x and `x_len`. -/
structure AR (x : XD) (s : State) : Prop where
  a2 : s.gpr .a2 = x.D
  a3 : s.gpr .a3 = BitVec.ofNat 64 x.L
  a4 : s.gpr .a4 = BitVec.ofNat 64 x.k
  a5 : s.gpr .a5 = x.X
  a6 : s.gpr .a6 = BitVec.ofNat 64 x.xl

theorem AR.keep {x : XD} {s t : State} {rs : List Reg} (h : AR x s) (k : Keep rs s t)
    (hr : ∀ r ∈ [Reg.a2, .a3, .a4, .a5, .a6], r ∉ rs := by decide) : AR x t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  exact ⟨(k.gpr hr.1).trans h.a2, (k.gpr hr.2.1).trans h.a3, (k.gpr hr.2.2.1).trans h.a4,
    (k.gpr hr.2.2.2.1).trans h.a5, (k.gpr hr.2.2.2.2).trans h.a6⟩

/-- `xLoad`: x's `xl` octets into array 4, its word `w` zero. -/
theorem xLoad_ok {x : XD} {s : State} (hb : Base x s) (ha : AR x s) :
    WP isa xLoad s fun t =>
      (wordsVal t.mem x.S (slot x.w 4) x.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
        word t.mem x.S (slot x.w 4 + 8 * x.w) = 0 ∧ Outside x.S (slot x.w 4) (8 * (x.w + 1)) s.mem t.mem ∧
        t.gpr .a7 = off x.S (slot x.w 0)) ∧
      Keep [.s11, .a6, .a0, .a1, .a7, .s0, .s7, .s8, .t3, .t4, .t5] s t := by
  have hc := hb.ctx
  have hZ := hc.hZ
  have hk' := hc.k1024
  have hxl := hc.xlk
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have e : ∀ j, slot x.w j = hdrBytes + j * (8 * (x.w + 2)) := fun _ => rfl
  have e8 := e 8; have e24 := e 24
  have hh : hdrBytes = 256 := rfl
  unfold xLoad
  refine WP.seq (WP.mono (WP.keep [.s11, .a6] (Q := fun t => t.gpr .s11 = BitVec.ofNat 64 x.xl ∧
    t.gpr .a6 = x.X ∧ t.mem = s.mem) (by brun [ha.a5, ha.a6, add_ofNat_zero]) (by rfl) (by rfl))
    fun s₁ ⟨⟨a11, a6, m1⟩, k1⟩ => ?_)
  have hc1 := hc.same k1 m1
  refine WP.mono (Pub.loadX_ok hc1.scr ((k1.gpr (by decide)).trans hb.s6) a6 a11 ((k1.gpr (by decide)).trans hb.a7)
    ((k1.gpr (by decide)).trans hb.s5) ((k1.gpr (by decide)).trans hb.t0) hc.xl1 (by omega_arith) (by omega_arith)
    (by omega_arith) hc1.rdX hc1.sepX) fun t ⟨⟨v, z, o, a7, _⟩, kt⟩ => ⟨⟨?_, z, ?_, a7⟩, (k1.trans kt).mono (by decide)⟩
  · rw [v, m1]
  · rw [m1] at o; exact o

theorem q_addr (D : Addr) (k : Nat) :
    BitVec.ofNat 64 k + BitVec.ofNat 64 k + D = off (off D (2 * k)) 0 := by
  rw [off, off, add_ofNat_zero, BitVec.add_comm _ D, ← BitVec.ofNat_add, Nat.two_mul]

/-- `xBound`: `a7 :=` array 1 with q's `k` octets (at `D + 2 k`) if `L = 3 k`,
else array 6 with `p − 1`. -/
theorem xBound_ok {x : XD} {s : State} (hc : Ctx x s) (h7 : s.gpr .a7 = off x.S (slot x.w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (x.w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 x.w)
    (ha2 : s.gpr .a2 = x.D) (ha4 : s.gpr .a4 = BitVec.ofNat 64 x.k)
    (ht2 : (s.gpr .t2 == 0) = decide (x.L = 3 * x.k)) (hp : wordsVal s.mem x.S (slot x.w 0) x.w = x.p)
    (hodd : x.p % 2 = 1) :
    WP isa xBound s fun t =>
      (∃ j, (j = 1 ∨ j = 6) ∧ t.gpr .a7 = off x.S (slot x.w j) ∧
          wordsVal t.mem x.S (slot x.w j) x.w = bnd s.mem x.D x.k x.L x.p ∧
          Outside x.S (slot x.w j) (8 * x.w) s.mem t.mem) ∧
        Keep [.a7, .s7, .s8, .a0, .s0, .t3, .t4, .t5] s t := by
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hL := hc.hL
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have e : ∀ j, slot x.w j = hdrBytes + j * (8 * (x.w + 2)) := fun _ => rfl
  have e1 := e 1; have e6 := e 6; have e24 := e 24
  have hh : hdrBytes = 256 := rfl
  unfold xBound
  refine WP.ite (s.gpr .t2 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [ht2, decide_eq_true_eq] at hb
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (Pub.base_ok (rd := .a7) (by decide) h7 h5 1) fun s₁ ⟨⟨b7, m1⟩, k1⟩ => ?_
    refine WP.mono (WP.keep [.s7, .s8] (Q := fun t => t.gpr .s7 = off (off x.D (2 * x.k)) 0 ∧
      t.gpr .s8 = BitVec.ofNat 64 x.k ∧ t.mem = s₁.mem)
      (by brun [(k1.gpr (r := .a2) (by decide)).trans ha2, (k1.gpr (r := .a4) (by decide)).trans ha4,
        add_ofNat_zero, q_addr]) (by rfl) (by rfl)) fun s₂ ⟨⟨a7', a8, m2⟩, k2⟩ => ?_
    have k12 := k1.trans k2
    refine WP.mono (loadN_ok (dA := slot x.w 1) (hc.scr.congr k12.2.2) ((k2.gpr (by decide)).trans b7) a7' a8
      ((k12.gpr (by decide)).trans h0) (by omega_arith) (by omega_arith) hw' (by omega_arith) (slot_al _ 1)
      (by omega_arith) (fun i hi => ?_) (fun i hi => ?_)) fun t ⟨tv, to, tk⟩ =>
        ⟨⟨1, Or.inl rfl, (tk.gpr (by decide)).trans ((k2.gpr (by decide)).trans b7), ?_, ?_⟩,
          (k12.trans tk).mono (by decide)⟩
    · rw [k12.2.1, k12.2.2, off_off]; exact hc.rdD _ (by omega_arith)
    · rw [off_off]; exact hc.sepD _ (by omega_arith)
    · rw [tv, m2, m1]; unfold bnd; rw [ite_eq_left hb]
    · rw [m2, m1] at to; exact to
  · have hq : ¬ x.L = 3 * x.k := by rw [ht2] at hb; simpa using hb
    refine WP.seq (WP.mono (pMinus1_ok hc.scr h7 h5 h0 (by omega_arith) hw' (by omega_arith)
      (by rw [hp]; exact hodd)) fun s₁ ⟨⟨v6, o1⟩, k1⟩ => ?_)
    refine WP.mono (Pub.base_ok (rd := .a7) (by decide) ((k1.gpr (by decide)).trans h7)
      ((k1.gpr (by decide)).trans h5) 6) fun t ⟨⟨b7, mt⟩, kt⟩ =>
        ⟨⟨6, Or.inr rfl, b7, ?_, by rw [mt]; exact o1⟩, (k1.trans kt).mono (by decide)⟩
    rw [mt, v6, hp]; unfold bnd; rw [ite_eq_right hq]

/-- `subMod64`'s mask, for `T` with its word `w` zero: all ones exactly when
`T < M`. -/
theorem lt_mask {A M D w c : Nat} (hc : c ≤ 1) (hD : D < 2 ^ (64 * w)) (h : D + M = A + 2 ^ (64 * w) * c) :
    (if (0 : BitVec 64).toNat < c then BitVec.allOnes 64 else 0) = bmask (decide (A < M)) := by
  rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl
  · have : ¬ A < M := by omega_arith
    simp [this]; rfl
  · have : A < M := by omega_arith
    simp [this]; rfl

/-- The registers `xCmp` writes. -/
def cmpRegs : List Reg := [.a0, .a7, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s7, .s8, .s9, .s11]

/-- `xCmp`, x in array 4 (`a5`) with its word `w` zero, the bound in array
`j` (`a7`) and array 3 (`a6`) the temporary: `s9 :=` the mask of
`0 < x < bound`, and the registers of `Base` back. -/
theorem xCmp_ok {x : XD} {s : State} {j : Nat} (hj : j = 1 ∨ j = 6) (hc : Ctx x s) (h6 : s.gpr .s6 = x.S)
    (h7 : s.gpr .a7 = off x.S (slot x.w j)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (x.w + 2)))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 x.w) (ha5 : s.gpr .a5 = off x.S (slot x.w 4))
    (ha6 : s.gpr .a6 = off x.S (slot x.w 3)) (ha2 : s.gpr .a2 = x.D) (ha4 : s.gpr .a4 = BitVec.ofNat 64 x.k)
    (htop : word s.mem x.S (slot x.w 4 + 8 * x.w) = 0) :
    WP isa xCmp s fun t =>
      (t.gpr .s9 = bmask (decide (wordsVal s.mem x.S (slot x.w 4) x.w < wordsVal s.mem x.S (slot x.w j) x.w) &&
          !decide (wordsVal s.mem x.S (slot x.w 4) x.w = 0)) ∧
        t.gpr .a7 = off x.S (slot x.w 0) ∧ t.gpr .s7 = off x.D 0 ∧ t.gpr .s8 = BitVec.ofNat 64 x.k ∧
        t.gpr .s11 = BitVec.ofNat 64 x.k ∧ t.gpr .s0 = 0 ∧
        Outside x.S (slot x.w 3) (3 * (8 * (x.w + 2))) s.mem t.mem) ∧ Keep cmpRegs s t := by
  have hs := hc.scr
  have hnw := hs.nowrap
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have e : ∀ j, slot x.w j = hdrBytes + j * (8 * (x.w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e24 := e 24
  have hh : hdrBytes = 256 := rfl
  have hjM : slot x.w j + 8 * x.w ≤ x.Z := by rcases hj with rfl | rfl <;> omega_arith
  have hjT : slot x.w 3 + 8 * x.w ≤ slot x.w j ∨ slot x.w j + 8 * x.w ≤ slot x.w 3 := by
    rcases hj with rfl | rfl <;> omega_arith
  have hj4 : slot x.w 4 + 8 * x.w ≤ slot x.w j ∨ slot x.w j + 8 * x.w ≤ slot x.w 4 := by
    rcases hj with rfl | rfl <;> omega_arith
  generalize hA : wordsVal s.mem x.S (slot x.w 4) x.w = A
  generalize hM : wordsVal s.mem x.S (slot x.w j) x.w = M
  unfold xCmp
  -- The mask of `x < bound`.
  refine WP.seq (WP.mono (subMod64_ok (w := x.w) (dA := slot x.w 4) (dT := slot x.w 3) (dM := slot x.w j) hs ha5 ha6 h7
    h0 (by omega_arith) hw' (slot_al _ 4) (slot_al _ 3) (slot_al _ j) (by omega_arith) (by omega_arith) hjM
    (by omega_arith) hjT) fun s₁ ⟨⟨c, hc1, hD, h4⟩, o1, k1⟩ => ?_)
  rw [htop] at h4
  rw [hA, hM] at hD
  have hlt : s₁.gpr .s4 = bmask (decide (A < M)) := by
    rw [h4]
    exact lt_mask hc1 (wordsVal_lt _ _ _ _) hD
  -- 0 into array 5.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.a7, .s9] (Q := fun t => t.gpr .a7 = off x.S (slot x.w 0) ∧
    t.gpr .s9 = bmask (decide (A < M)) ∧ t.mem = s₁.mem)
    (by brun [(k1.gpr (r := .s6) (by decide)).trans h6, hlt, hdrBytes, add_ofNat_zero]; simp [slot, hdrBytes, off])
    (by rfl) (by rfl)) fun s₂ ⟨⟨a72, a92, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) a72 ((k12.gpr (by decide)).trans h5) 5)
    fun s₃ ⟨⟨b3, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k13.2.2) b3 ((k13.gpr (by decide)).trans h0) (by omega_arith) hw'
    (slot_al _ 5) (by omega_arith)) fun s₄ ⟨⟨_, z4, o4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  refine WP.seq (WP.mono (WP.keep [.s4] (Q := fun u => u.gpr .s4 = BitVec.allOnes 64 ∧ u.mem = s₄.mem)
    (by brun [li_m1]) (by rfl) (by rfl)) fun s₅ ⟨⟨a45, m5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have g7 : s₅.gpr .a7 = off x.S (slot x.w 0) := ((k3.trans k4).trans k5).gpr (by decide) |>.trans a72
  -- The mask of `x = 0`.
  refine WP.seq (WP.mono (eqMask_ok (j := 4) (k := 5) (hs.congr k15.2.2) g7 ((k15.gpr (by decide)).trans h5)
    ((k15.gpr (by decide)).trans h0) (by omega_arith) hw' (by omega_arith) (by omega_arith))
    fun s₆ ⟨⟨b4, m6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  have a4' : wordsVal s₅.mem x.S (slot x.w 4) x.w = A := by
    rw [m5, Outside.wordsVal o4 (by omega_arith) (by omega_arith), m3, m2,
      Outside.wordsVal o1 (by omega_arith) (by omega_arith), hA]
  have z5 : wordsVal s₅.mem x.S (slot x.w 5) x.w = 0 := by rw [m5]; exact Pub.wsv_zero z4
  rw [a45, ones_and, a4', z5] at b4
  rw [xFin, show ([.logicImm .xor .s4 .s4 (-1), .logic .and .s9 .s9 .s4, .addi .s7 .a2 0, .addi .s8 .a4 0,
    .addi .s11 .a4 0, .li .s0 0] : List Instr) = ([.logicImm .xor .s4 .s4 (-1), .logic .and .s9 .s9 .s4] : List Instr) ++
    ([.addi .s7 .a2 0, .addi .s8 .a4 0, .addi .s11 .a4 0, .li .s0 0] : List Instr) from rfl, WP.block_append_iff]
  refine WP.mono (blkC_ok (((k3.trans k4).trans (k5.trans k6)).gpr (by decide) |>.trans a92) b4)
    fun s₇ ⟨⟨c9, m7⟩, k7⟩ => ?_
  have k17 := k16.trans k7
  refine WP.mono (WP.keep [.s7, .s8, .s11, .s0] (Q := fun u => u.gpr .s7 = off x.D 0 ∧
    u.gpr .s8 = BitVec.ofNat 64 x.k ∧ u.gpr .s11 = BitVec.ofNat 64 x.k ∧ u.gpr .s0 = 0 ∧ u.mem = s₇.mem)
    (by brun [(k17.gpr (r := .a2) (by decide)).trans ha2, (k17.gpr (r := .a4) (by decide)).trans ha4, add_ofNat_zero,
      fin64_exec_li_zero]) (by rfl) (by rfl)) fun t ⟨⟨t7, t8, t11, t0', mt⟩, kt⟩ =>
    ⟨⟨(kt.gpr (by decide)).trans c9, ?_, t7, t8, t11, t0', ?_⟩, (k17.trans kt).mono (by decide)⟩
  · exact (kt.gpr (by decide)).trans ((k7.gpr (by decide)).trans ((k6.gpr (by decide)).trans g7))
  · rw [mt, m7, m6, m5]
    exact ((o1.mono (Nat.le_refl _) (by omega_arith)).trans
      (by rw [m3, m2] at o4; exact o4.mono (by omega_arith) (by omega_arith)))

theorem sub_3k_zero {L k : Nat} (hL : L < 2 ^ 63) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 L - off (BitVec.ofNat 64 k) (k + k) == 0) = decide (L = 3 * k) := by
  rw [off, ← BitVec.ofNat_add]
  by_cases h : L = 3 * k
  · rw [h, show k + (k + k) = 3 * k by omega_arith, BitVec.sub_self]; simp
  · rw [decide_eq_false h]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega_arith

theorem range_mask (A M : Nat) :
    (decide (A < M) && !decide (A = 0)) = decide (0 < A ∧ A < M) := by
  by_cases h : A = 0 <;> by_cases h' : A < M <;> simp [h, h'] <;> omega_arith

/-- `xRange`: with p (valid) in array 0, `s9 :=` the mask of `0 < x < bnd`;
`X4` again, with `s0 = 0`, and only arrays changed. -/
theorem xRange_ok {x : XD} {s : State} (h : X4 x s) (hv : Spec.Rsa.modulusValid x.p x.k = true) (ha : AR x s) :
    WP isa xRange s fun t => X4 x t ∧ t.gpr .s0 = 0 ∧
      t.gpr .s9 = bmask (decide (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p)) ∧ Arr x s.mem t.mem := by
  obtain ⟨hb, hp, -⟩ := h
  have hc := hb.ctx
  have hf := VG.Proof.Bignum.valid_facts hv hc.k64
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hL := hc.hL
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have e : ∀ j, slot x.w j = hdrBytes + j * (8 * (x.w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e6 := e 6; have e24 := e 24
  have hh : hdrBytes = 256 := rfl
  unfold xRange
  refine WP.seq (WP.mono (xLoad_ok hb ha) fun s₁ ⟨⟨v1, z1, o1, a71⟩, k1⟩ => ?_)
  have ar1 : Arr x s.mem s₁.mem := arr_of o1 (by omega_arith) (by omega_arith)
  have hc1 := hc.keep k1.2.1 k1.2.2 ar1
  -- The comparison's arrays, and whether there is q.
  refine WP.seq ?_
  unfold xPrep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) a71 ((k1.gpr (by decide)).trans hb.s5) 4)
    fun s₂ ⟨⟨b5, m2⟩, k2⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k2.gpr (by decide)).trans a71)
    ((k1.trans k2).gpr (by decide) |>.trans hb.s5) 3) fun s₃ ⟨⟨b6, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  refine WP.mono (WP.keep [.t2] (Q := fun t => (t.gpr .t2 == 0) = decide (x.L = 3 * x.k) ∧ t.mem = s₃.mem)
    (by brun [(k13.gpr (r := .a3) (by decide)).trans ha.a3, (k13.gpr (r := .a4) (by decide)).trans ha.a4]
        exact sub_3k_zero (by omega_arith) (by omega_arith)) (by rfl) (by rfl)) fun s₄ ⟨⟨t24, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  have hc4 := hc1.keep (k2.trans (k3.trans k4)).2.1 (k2.trans (k3.trans k4)).2.2 (by rw [hm4]; exact Outside.refl _ _ _ _)
  have p4 : wordsVal s₄.mem x.S (slot x.w 0) x.w = x.p := by
    rw [hm4, Outside.wordsVal o1 (by omega_arith) (by omega_arith), hp]
  -- The bound.
  refine WP.seq (WP.mono (xBound_ok hc4 ((k2.trans (k3.trans k4)).gpr (by decide) |>.trans a71)
    (k14.gpr (by decide) |>.trans hb.s5) (k14.gpr (by decide) |>.trans hb.t0) (k14.gpr (by decide) |>.trans ha.a2)
    (k14.gpr (by decide) |>.trans ha.a4) t24 p4 hf.1) fun s₅ ⟨⟨j, hj, a75, v5, o5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have hjZ : slot x.w j + 8 * x.w ≤ slot x.w 4 ∨ slot x.w 4 + 8 * (x.w + 1) ≤ slot x.w j := by
    rcases hj with rfl | rfl <;> omega_arith
  have hj256 : 256 ≤ slot x.w j ∧ slot x.w j + 8 * x.w ≤ x.Z := by rcases hj with rfl | rfl <;> omega_arith
  have ar5 : Arr x s₄.mem s₅.mem := arr_of o5 hj256.1 hj256.2
  have hc5 := hc4.keep k5.2.1 k5.2.2 ar5
  have top5 : word s₅.mem x.S (slot x.w 4 + 8 * x.w) = 0 := by
    rw [Outside.word o5 (by rcases hj with rfl | rfl <;> omega_arith) (by omega_arith), hm4]; exact z1
  have x5 : wordsVal s₅.mem x.S (slot x.w 4) x.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) := by
    rw [Outside.wordsVal o5 (by rcases hj with rfl | rfl <;> omega_arith) (by omega_arith), hm4, v1]
  have bnd4 : bnd s₄.mem x.D x.k x.L x.p = bnd s.mem x.D x.k x.L x.p := by
    unfold bnd
    by_cases hq : x.L = 3 * x.k
    · rw [ite_eq_left hq, ite_eq_left hq, hm4, Pub.bytes_apart (Z := x.Z) ar1 (by omega_arith) fun i hi => by
        have h' := hc.sepD (2 * x.k + i) (by omega_arith); rw [← off_off] at h'; exact h']
    · rw [ite_eq_right hq, ite_eq_right hq]
  -- The masks.
  refine WP.mono (xCmp_ok hj hc5 (k15.gpr (by decide) |>.trans hb.s6) a75 (k15.gpr (by decide) |>.trans hb.s5)
    (k15.gpr (by decide) |>.trans hb.t0) ((k3.trans (k4.trans k5)).gpr (by decide) |>.trans b5)
    ((k4.trans k5).gpr (by decide) |>.trans b6) (k15.gpr (by decide) |>.trans ha.a2)
    (k15.gpr (by decide) |>.trans ha.a4) top5) fun t ⟨⟨t9, t7, ts7, ts8, ts11, ts0, ot⟩, kt⟩ => ?_
  have art : Arr x s₅.mem t.mem := arr_of ot (by omega_arith) (by omega_arith)
  have arT : Arr x s.mem t.mem := (ar1.trans (by rw [← hm4]; exact ar5)).trans art
  have kT := k15.trans kt
  refine ⟨⟨⟨hc.keep kT.2.1 kT.2.2 arT, (kT.gpr (by decide)).trans hb.s6, t7, (kT.gpr (by decide)).trans hb.s5,
    (kT.gpr (by decide)).trans hb.t0, ts7.trans hb.s7.symm |>.trans hb.s7, ts8.trans hb.s8.symm |>.trans hb.s8,
    (kT.gpr (by decide)).trans hb.s10, ts11⟩, ?_, ⟨fun _ => hv, fun _ => ts0⟩⟩, ts0, ?_, arT⟩
  · rw [Outside.wordsVal ot (by omega_arith) (by omega_arith), Outside.wordsVal o5 (by rcases hj with rfl | rfl <;> omega_arith)
      (by omega_arith), p4]
  · rw [t9, x5, v5, bnd4, range_mask]

/-! ## The status -/

open VG.Spec.Ffdh in
/-- `privateValid` of a domain of `L = 2 k` or `3 k` octets at `D`. -/
theorem privateValid_dom {m : Mem} {D : Addr} {k L : Nat} (hk : 0 < k) (hL : L = 2 * k ∨ L = 3 * k) (x : Nat) :
    privateValid (domainOf k (Spec.Rsa.bytesAt m D L)) x =
      decide (0 < x ∧ x < bnd m D k L (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k))) := by
  unfold privateValid bnd
  rcases hL with rfl | rfl
  · rw [Proof.Ffdh.domainOf_q2 m D hk, ite_eq_right (show ¬ (2 * k = 3 * k) by omega_arith),
      Proof.Ffdh.domainOf_p m D (by omega_arith)]
    simp
  · rw [Proof.Ffdh.domainOf_q3 m D k, ite_eq_left rfl]
    simp [off]

open VG.Spec.Ffdh in
/-- `keyStatus` for a valid domain of `L = 2 k` or `3 k` octets at `D`. -/
theorem keyStatus_dom {m : Mem} {D : Addr} {k L : Nat} (hk : 0 < k) (hL : L = 2 * k ∨ L = 3 * k)
    (hv : domainValid k (Spec.Rsa.bytesAt m D L) = true) (x : Nat) :
    keyStatus (domainOf k (Spec.Rsa.bytesAt m D L)) x =
      if ¬ (0 < x ∧ x < bnd m D k L (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k))) then 2 else
        if 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k) ^ x % Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) <
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) - 1 then 1 else 3 := by
  have hpv : parametersValid (domainOf k (Spec.Rsa.bytesAt m D L)) = true := by
    unfold domainValid at hv
    simp only [Bool.and_eq_true] at hv
    exact hv.1
  have h2k : 2 * k ≤ L := by omega_arith
  simp only [Proof.Ffdh.KeyScalar.keyStatus_eq hpv, Proof.Ffdh.publicValid_power hpv, privateValid_dom hk hL]
  simp only [Proof.Ffdh.domainOf_p m D h2k, Proof.Ffdh.domainOf_g m D h2k]
  by_cases h : 0 < x ∧ x < bnd m D k L (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k))
  · simp [h, off]
  · simp [h]

open VG.Spec.Ffdh in
/-- The status is 2 exactly when x is out of range. -/
theorem keyStatus_two (a : Parameters) (x : Nat) : keyStatus a x = 2 ↔ privateValid a x = false := by
  unfold keyStatus
  cases privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> simp

/-! ## Out of range -/

/-- x out of range: zeros to `y`, the status 2. -/
theorem bad_ok {x : XD} {s : State} (hb : Base x s) (h9 : s.gpr .s9 = 0) :
    WP isa dpBad s fun t =>
      (Spec.Rsa.bytesAt t.mem x.O x.k = List.replicate x.k 0 ∧ t.gpr .a0 = BitVec.ofNat 64 2) ∧
      t.gpr .s6 = x.S ∧ Outside x.O 0 x.k s.mem t.mem := by
  have hc := hb.ctx
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have e : ∀ j, slot x.w j = hdrBytes + j * (8 * (x.w + 2)) := fun _ => rfl
  have e8 := e 8; have e24 := e 24
  unfold dpBad
  refine WP.seq (WP.mono (Pub.output_ok (b := false) hc.scr hc.outW hc.nwO hb.a7 hb.s5 hb.s11 hb.s10
    (by rw [h9]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) hc.sepO) fun t ⟨⟨ob, ot, _⟩, kt⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 2 ∧ u.mem = t.mem)
    (by brun [fin64_exec_li_lit (show 2 < 2048 by decide)]) (by rfl) (by rfl)) fun u ⟨⟨ua, um⟩, ku⟩ =>
      ⟨⟨by rw [um]; exact Pub.zero_bytes fun i hi => by rw [ob i hi]; rfl, ua⟩,
        (ku.gpr (by decide)).trans ((kt.gpr (by decide)).trans hb.s6), by rw [um]; exact ot⟩

end VG.Proof.Ffdh.RISCV64.Derive
