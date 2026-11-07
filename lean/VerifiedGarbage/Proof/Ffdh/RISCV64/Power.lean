module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Fn
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubSave
public import VerifiedGarbage.Impl.Ffdh.RISCV64
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
import VerifiedGarbage.Proof.Bignum.RISCV64.Double64
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore

/-!
# FFDH's exchange on RISC-V: up to the power

The public data of a run (`XD`, `xdOf`): the pointers and lengths and the
domain's octets. `Ctx`: what holds from `setup` on, but for the registers:
the working space, the buffers apart from it, the domain's octets and the
header's words 0–3 (`out`, x, `x_len` and the peer). `Base`: `Ctx` and the
registers `setup` leaves. `front_ok`: `exFront` loads the working space's
address from the stack (`loadS1_ok`), saves the callee-saved registers in
its header, stores the header's words 0–3 (`hdr_ok`) and sets up the
registers.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)

/-- The public data of an exchange: `out`, the domain and its length, p's
length, x's address and length, the peer, the working space and its size in
bytes, and the domain's octets. -/
structure XD where
  O : Addr
  D : Addr
  L : Nat
  k : Nat
  X : Addr
  xl : Nat
  Y : Addr
  S : Addr
  Z : Nat
  db : List Byte

/-- The words of p. -/
abbrev XD.w (x : XD) : Nat := (x.k + 7) / 8

/-- p. -/
abbrev XD.p (x : XD) : Nat := Spec.Rsa.os2ip (x.db.take x.k)

def xdOf (s : State) : XD :=
  ⟨s.gpr .a0, s.gpr .a2, (s.gpr .a3).toNat, (s.gpr .a4).toNat, s.gpr .a5, (s.gpr .a6).toNat, s.gpr .a7,
    stackArg s 1, (stackArg s 2).toNat * 8, Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat⟩

/-- What holds from `setup` on, but for the registers. -/
structure Ctx (x : XD) (s : State) : Prop where
  scr : Scr s x.S x.Z
  k64 : 64 ≤ x.k
  k1024 : x.k ≤ 1024
  hL : 2 * x.k ≤ x.L ∧ x.L ≤ 3 * x.k
  hZ : slot x.w 24 ≤ x.Z
  nwO : x.O.toNat + x.k ≤ 2 ^ 64
  outW : ∀ i < x.k, InRegions s.wr (off x.O i) 1
  sepO : ∀ y, ofs x.O y < x.k → x.Z ≤ ofs x.S y
  rdD : ∀ i < x.L, InRegions (s.rd ++ s.wr) (off x.D i) 1
  sepD : ∀ i < x.L, ∀ y, ofs x.S y < x.Z → off x.D i ≠ y
  rdY : ∀ i < x.k, InRegions (s.rd ++ s.wr) (off x.Y i) 1
  sepY : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off x.Y i ≠ y
  rdX : ∀ i < x.xl, InRegions (s.rd ++ s.wr) (off x.X i) 1
  sepX : ∀ i < x.xl, ∀ y, ofs x.S y < x.Z → off x.X i ≠ y
  xl1 : 1 ≤ x.xl
  xlk : x.xl ≤ x.k
  bD : Spec.Rsa.bytesAt s.mem x.D x.L = x.db
  hO : word s.mem x.S 0 = off x.O 0
  hX : word s.mem x.S 8 = off x.X 0
  hXL : word s.mem x.S 16 = BitVec.ofNat 64 x.xl
  hY : word s.mem x.S 24 = x.Y

/-- The arrays: memory from byte 256 of the working space on. -/
abbrev Arr (x : XD) (m m' : Mem) : Prop := Outside x.S 256 (x.Z - 256) m m'

theorem Ctx.keep {x : XD} {s t : State} (h : Ctx x s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : Arr x s.mem t.mem) : Ctx x t := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have h24 : 256 ≤ slot x.w 24 := by unfold slot hdrBytes; omega_arith
  have hw : ∀ d, d + 8 ≤ 256 → word t.mem x.S d = word s.mem x.S d := fun d hd =>
    Outside.word hm (Or.inl hd) (by omega_arith)
  exact ⟨h.scr.congr hwr, h.k64, h.k1024, h.hL, h.hZ, h.nwO, by rw [hwr]; exact h.outW, h.sepO,
    by rw [hrd, hwr]; exact h.rdD, h.sepD, by rw [hrd, hwr]; exact h.rdY, h.sepY,
    by rw [hrd, hwr]; exact h.rdX, h.sepX, h.xl1, h.xlk,
    by rw [Pub.bytes_apart hm (by omega_arith) h.sepD]; exact h.bD,
    by rw [hw 0 (by decide)]; exact h.hO, by rw [hw 8 (by decide)]; exact h.hX,
    by rw [hw 16 (by decide)]; exact h.hXL, by rw [hw 24 (by decide)]; exact h.hY⟩

theorem Ctx.same {x : XD} {s t : State} {rs : List Reg} (h : Ctx x s) (k : Keep rs s t) (hm : t.mem = s.mem) :
    Ctx x t := h.keep k.2.1 k.2.2 (by rw [hm]; exact Outside.refl _ _ _ _)

/-- `Ctx` and the registers `setup` leaves. -/
structure Base (x : XD) (s : State) : Prop where
  ctx : Ctx x s
  s6 : s.gpr .s6 = x.S
  a7 : s.gpr .a7 = off x.S (slot x.w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (x.w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 x.w
  s7 : s.gpr .s7 = off x.D 0
  s8 : s.gpr .s8 = BitVec.ofNat 64 x.k
  s10 : s.gpr .s10 = off x.O 0
  s11 : s.gpr .s11 = BitVec.ofNat 64 x.k

/-- The registers `Base` fixes. -/
def baseRegs : List Reg := [.s6, .a7, .s5, .t0, .s7, .s8, .s10, .s11]

theorem Base.keep {x : XD} {s t : State} {rs : List Reg} (h : Base x s) (k : Keep rs s t)
    (hm : Arr x s.mem t.mem) (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : Base x t := by
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  exact ⟨h.ctx.keep k.2.1 k.2.2 hm, (k.gpr hr.1).trans h.s6, (k.gpr hr.2.1).trans h.a7,
    (k.gpr hr.2.2.1).trans h.s5, (k.gpr hr.2.2.2.1).trans h.t0, (k.gpr hr.2.2.2.2.1).trans h.s7,
    (k.gpr hr.2.2.2.2.2.1).trans h.s8, (k.gpr hr.2.2.2.2.2.2.1).trans h.s10,
    (k.gpr hr.2.2.2.2.2.2.2).trans h.s11⟩

theorem Base.same {x : XD} {s t : State} {rs : List Reg} (h : Base x s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : Base x t :=
  h.keep k (by rw [hm]; exact Outside.refl _ _ _ _) hr

/-! ## The front -/

/-- The second argument on the stack, `scratch`, into `t0`. -/
theorem loadS1_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8) (ha : s.sp.toNat % 16 = 0) :
    WP isa (.block ([.addSp .t0 8, .load .d .t0 .t0 0] : List Instr)) s fun t =>
      (t.gpr .t0 = stackArg s 1 ∧ t.mem = s.mem) ∧ Keep [.t0] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [stackArgAddr, Nat.reduceMul] at h
  have ha' : (s.sp + BitVec.ofNat 64 8 + BitVec.ofNat 64 0).toNat % 8 = 0 := by
    rw [add_ofNat_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero]; exact h
  have ha'' : (s.sp + BitVec.ofNat 64 8).toNat % 8 = 0 := by rw [add_ofNat_zero] at ha'; exact ha'
  brun [exec_addSp (show 8 < 2048 by decide), add_ofNat_zero, h, h', ha', ha'']
  simp [stackArg, stackArgAddr]

/-- `out`, x, `x_len` and the peer into the header's words 0–3 at `S`
(`s6`), the domain into `s7` and `p_len` into `s8` and `a1`. -/
theorem hdr_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 32 ≤ Z) (h6 : s.gpr .s6 = S) :
    WP isa (.block ([.store .d .a0 .s6 0, .store .d .a5 .s6 8, .store .d .a6 .s6 16, .store .d .a7 .s6 24,
      .addi .s7 .a2 0, .addi .s8 .a4 0, .addi .a1 .a4 0] : List Instr)) s fun t =>
      (word t.mem S 0 = s.gpr .a0 ∧ word t.mem S 8 = s.gpr .a5 ∧ word t.mem S 16 = s.gpr .a6 ∧
        word t.mem S 24 = s.gpr .a7 ∧ t.gpr .s7 = s.gpr .a2 ∧ t.gpr .s8 = s.gpr .a4 ∧ t.gpr .a1 = s.gpr .a4 ∧
        Outside S 0 32 s.mem t.mem) ∧ Keep [.s7, .s8, .a1] s t := by
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
    (off S 16) (s.gpr .a6)) S (d := 24) (s.gpr .a7) (by omega_arith)
  refine WP.mono (WP.keep [.s7, .s8, .a1] (Q := fun t => t.mem = (((s.mem.writeW (off S 0) (s.gpr .a0)).writeW
      (off S 8) (s.gpr .a5)).writeW (off S 16) (s.gpr .a6)).writeW (off S 24) (s.gpr .a7) ∧
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

theorem rd_of_mem {s : State} {A : Addr} {L n : Nat} (h : (⟨A, L⟩ : Region) ∈ s.rd) (hn : n ≤ L)
    (hL : L < 2 ^ 64) :
    ∀ i < n, InRegions (s.rd ++ s.wr) (off A i) 1 := fun i hi =>
  ⟨_, List.mem_append_left _ h, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The registers the front writes. -/
def frontRegs : List Reg := [.t0, .s6, .s7, .s8, .a1, .a7, .s5, .s10, .s11]

/-- `exFront`: `Base`, the callee-saved registers saved, and only the header
changed. -/
theorem front_ok {s : State} (h : fnContract.pre s) :
    WP isa (.block exFront) s fun t =>
      Base (xdOf s) t ∧
        (∀ i < 12, t.mem.readW (off (savW (stackArg s 1)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
        Keep frontRegs s t ∧ Outside (stackArg s 1) 0 256 s.mem t.mem := by
  obtain ⟨hrd, hwr, dOD, dOX, dOP, dOS, dOA, dDS, dXS, dPS, dSA, nwO, nwD, nwX, nwP, nwS, ⟨hk, hk'⟩, hL,
    hol, hpl, hx1, hxk, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [xdOf]
  generalize hSd : stackArg s 1 = S at hwr dOS dDS dXS dPS dSA nwS alS ⊢
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hwr dOS dDS dXS dPS dSA nwS ⊢
  have hZ : 256 + 128 * (s.gpr .a4).toNat ≤ Z := by omega_arith
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS alS
  have hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * 1)) 8
    simp only [Nat.mul_zero, Nat.mul_one, add_ofNat_zero]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  unfold exFront
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadS1_ok s hA1 alsp) fun s₁ ⟨⟨a0', m1⟩, k1⟩ => ?_)
  rw [hSd] at a0'
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
  refine WP.block_append (WP.mono (hdr_ok (hs.congr k12.2.2) (by omega_arith) h6₂)
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
  have rdY : ∀ i < (s.gpr .a4).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a7) i) 1 := by
    rw [hrdt]
    exact rd_of_mem (L := (stackArg s 0).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hpl.symm) (BitVec.isLt _)
  have rdX : ∀ i < (s.gpr .a6).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a5) i) 1 := by
    rw [hrdt]; exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  refine ⟨⟨⟨hs.congr k.2.2, hk, hk', hLk, ?_, by rw [← hol]; exact nwO, fun i hi => ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩,
      by rw [k.2.2, hwr]; simp, Offset.contains_base _ (by change i < (s.gpr .a4).toNat at hi; omega_arith)
        (by change i < (s.gpr .a4).toNat at hi; omega_arith)⟩,
      fun y hy => Pub.sep_of_disjoint dOS y (by rw [hol]; exact hy),
      rdD, sepD, rdY,
      fun i hi => Pub.ne_of_disjoint dPS (Nat.le_of_lt (stackArg s 0).isLt) i (by
        change i < (s.gpr .a4).toNat at hi; omega_arith),
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
  · rw [hw3 24 (by decide), w24, k12.gpr (by decide)]
  · intro i hi
    have e : off (savW S) (8 * i) = off S (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [e]
    show word t.mem S (128 + 8 * i) = _
    rw [jm, o3.word (Or.inr (by omega_arith)) (by omega_arith)]
    show s₂.mem.readW (off S (128 + 8 * i)) 64 = _
    rw [← e, ← a0', hS.saved i hi, k1.gpr fun h => Pub.saved_ne_t0 i hi (List.mem_singleton.mp h)]

end VG.Proof.Ffdh.RISCV64

/-!
## FFDH's exchange on RISC-V: p, its check and `R² mod p`

`loadN_X`, `check1_X`, `check2_X`: p into array 0 (`X2`), then whether it
is a valid modulus, in `s0` (`X4`). `r2t_ok`: `Precompute.r2`, `R² mod p`
in array 1, also leaving `-p⁻¹ mod 2⁶⁴` in `t1`.
-/

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

theorem take_len {x : XD} (h : 2 * x.k ≤ x.L) {s : State} (hc : Ctx x s) : (x.db.take x.k).length = x.k := by
  rw [List.length_take, ← hc.bD, VG.Proof.Bignum.bytesAt_length]; omega_arith

theorem take_byte {x : XD} {s : State} (hc : Ctx x s) {i : Nat} (hi : i < x.k) :
    s.mem (off x.D i) = (x.db.take x.k)[i]'(by rw [take_len hc.hL.1 hc]; exact hi) := by
  have hL := hc.hL
  simp only [← hc.bD, List.getElem_take, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]

theorem bytes_p {x : XD} {s : State} (hc : Ctx x s) :
    Spec.Rsa.bytesAt s.mem x.D x.k = x.db.take x.k := by
  rw [← hc.bD, Proof.Ffdh.take_bytesAt _ _ (by have := hc.hL; omega_arith)]

/-- After `loadN`: p in array 0. -/
def X2 (x : XD) (s : State) : Prop := Base x s ∧ wordsVal s.mem x.S (slot x.w 0) x.w = x.p

/-- After `check1`. -/
def X3 (x : XD) (s : State) : Prop :=
  Base x s ∧ wordsVal s.mem x.S (slot x.w 0) x.w = x.p ∧
    s.gpr .t4 = BitVec.ofNat 64 ((x.db.take x.k).getD 0 0).toNat ∧
    (s.gpr .s0 = 0 ↔ ((x.db.take x.k).getD (x.k - 1) 0).toNat % 2 = 1)

/-- After `check2`: whether p is valid, in `s0`. -/
def X4 (x : XD) (s : State) : Prop :=
  Base x s ∧ wordsVal s.mem x.S (slot x.w 0) x.w = x.p ∧
    (s.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid x.p x.k = true)

theorem getD_of_lt' {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem loadN_X {x : XD} {s : State} (h : Base x s) :
    WP isa Precompute.loadN s fun t => X2 x t ∧ Arr x s.mem t.mem := by
  have hc := h.ctx
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hL := hc.hL
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have e0 : slot x.w 0 = 256 := by simp [slot, hdrBytes]
  have e24 : slot x.w 24 = 256 + 24 * (8 * (x.w + 2)) := by simp [slot, hdrBytes]
  refine WP.mono (loadN_ok (dA := slot x.w 0) hc.scr h.a7 h.s7 h.s8 h.t0 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (slot_al _ 0) (by omega_arith)
    (fun i hi => hc.rdD i (by omega_arith)) (fun i hi => hc.sepD i (by omega_arith))) fun t ⟨hv, out, k⟩ => ?_
  have hm : Arr x s.mem t.mem := out.mono (by omega_arith) (by omega_arith)
  exact ⟨⟨h.keep k hm, by rw [hv, bytes_p hc]⟩, hm⟩

theorem check1_X {x : XD} {s : State} (h : X2 x s) :
    WP isa (.block Precompute.check1) s fun t => X3 x t ∧ t.mem = s.mem := by
  obtain ⟨hb, hp⟩ := h
  have hc := hb.ctx
  have hl := take_len hc.hL.1 hc
  have hk := hc.k64
  refine WP.mono (check1_ok (N := x.D) (nb := x.db.take x.k) hb.s7 hb.s8 hk hl
    (fun i hi => hc.rdD i (by have := hc.hL; omega_arith)) fun i hi => take_byte hc hi)
    fun t ⟨⟨i0, i4, im⟩, k⟩ => ⟨⟨hb.same k im, by rw [im]; exact hp,
      by rw [i4, getD_of_lt' (by omega_arith)], by rw [i0, getD_of_lt' (by omega_arith)]⟩, im⟩

theorem check2_X {x : XD} {s : State} (h : X3 x s) :
    WP isa Precompute.check2 s fun t => X4 x t ∧ t.mem = s.mem := by
  obtain ⟨hb, hp, h4, h0⟩ := h
  have hc := hb.ctx
  have hl := take_len hc.hL.1 hc
  have hk := hc.k64
  refine WP.mono (check2_ok (nb := x.db.take x.k) hb.s8 hk hc.k1024 hl (by rw [h0, getD_of_lt' (by omega_arith)])
    (by rw [h4, getD_of_lt' (by omega_arith)])) fun t ⟨a, m, k⟩ => ⟨⟨hb.same k m, by rw [m]; exact hp, a⟩, m⟩

/-- `loadP`: p into array 0, and whether it is valid in `s0`. -/
theorem loadP_X {x : XD} {s : State} (h : Base x s) : WP isa loadP s fun t => X4 x t ∧ Arr x s.mem t.mem := by
  unfold loadP Precompute.check
  refine WP.seq (WP.mono (loadN_X h) fun s₁ ⟨h1, a1⟩ => ?_)
  refine WP.seq (WP.mono (check1_X h1) fun s₂ ⟨h2, m2⟩ => ?_)
  refine WP.mono (check2_X h2) fun t ⟨h4, m4⟩ => ⟨h4, ?_⟩
  rw [m4, m2]; exact a1

/-- `Precompute.r2`: `x := R² mod n = 2^(128 w) mod n` in array 1, for an odd
`n` of `w` words, at least `2^(64 (w − 1))`, in array 0, changing only arrays
1–3, with `-n⁻¹ mod 2⁶⁴` in `t1`. -/
theorem r2t_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hN : 2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa Impl.Bignum.RISCV64.Precompute.r2 s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        ((Mont.word s.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
        Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep r2Regs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hlow : (Mont.word s.mem B (slot w 0)).toNat % 2 = 1 := by
    rw [fios_wordsVal_pred _ _ _ (show 1 ≤ w by omega)] at hodd
    omega
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd ⊢
  replace hN : 2 ^ (64 * (w - 1)) < N := Nat.lt_of_le_of_ne hN fun h => by
    rw [← h, show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left] at hodd
    exact absurd hodd (by decide)
  have hN0 : 0 < N := by omega
  unfold Impl.Bignum.RISCV64.Precompute.r2
  refine WP.seq (WP.mono (r2HiDbl_ok hs h5 h6 h7 h2 ht0 hw hw' (by omega) hNd hN) fun s₃ ⟨x3, o3, k3⟩ => ?_)
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by rw [Outside.wordsVal o3 (by omega) (by omega), hNd]
  have w3 : Mont.word s₃.mem B (slot w 0) = Mont.word s.mem B (slot w 0) := Outside.word o3 (by omega) (by omega)
  refine WP.seq (WP.mono (minv_ok (hs.congr k3.2.2) ((k3.gpr (by decide)).trans h7) (slot_al8 w 0) (by omega)
    (by rw [w3]; exact hlow)) fun s₄ ⟨⟨i4, m4⟩, k4⟩ => ?_)
  have i4' : ((Mont.word s.mem B (slot w 0)).toNat * (s₄.gpr .t1).toNat + 1) % 2 ^ 64 = 0 := by
    rw [← w3]; exact i4
  have k34 := k3.trans k4
  rw [← m4] at x3 n3 w3
  refine WP.mono (r2Squares_ok (N := N) (hs.congr k34.2.2) hw hw' hZ ((k34.gpr (by decide)).trans h2)
    ((k34.gpr (by decide)).trans h5) ((k34.gpr (by decide)).trans h6) ((k34.gpr (by decide)).trans h7)
    ((k34.gpr (by decide)).trans ht0) (by rw [m4]; exact i4) n3 hodd
    (by rw [x3]; exact Nat.mod_lt _ hN0) (by rw [x3, Nat.mod_mod, Nat.pow_add]))
    fun t ⟨tx, to, tk⟩ => ⟨⟨tx, by rw [tk.gpr (by decide)]; exact i4',
      Outside.trans (by rw [m4]; exact o3) to⟩, (k34.trans tk).mono (by decide)⟩

end VG.Proof.Ffdh.RISCV64

/-!
## FFDH's exchange on RISC-V: `z = y^x mod p`

`exPre_split`: from a valid p in array 0 (`X4`), `exPre` loads the peer's
address (`R1`), the peer into array 4 (`loadX_ok`), `R² mod p` into array 1
and `-p⁻¹ mod 2⁶⁴` into `t1` (`r2t_ok`), and x's address and length (`R5`);
then `ModExp.powWin` leaves `z = y^x mod p` in array 4 (`PowPost`).
-/

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- The working space's registers. -/
def RW (x : XD) (s : State) : Prop :=
  s.gpr .s6 = x.S ∧ s.gpr .a7 = off x.S (slot x.w 0) ∧ s.gpr .s5 = BitVec.ofNat 64 (8 * (x.w + 2)) ∧
    s.gpr .t0 = BitVec.ofNat 64 x.w ∧ s.gpr .s11 = BitVec.ofNat 64 x.k

/-- After `exPre`'s first load: the peer's address, for `loadX`. -/
def R1 (x : XD) (s : State) : Prop := s.gpr .a6 = x.Y ∧ RW x s

/-- After `exPre`: x's address and length, for the power. -/
def R5 (x : XD) (s : State) : Prop := s.gpr .s9 = off x.X 0 ∧ s.gpr .s10 = BitVec.ofNat 64 x.xl ∧ RW x s

/-- What the power leaves, from `s` before `exPre`. -/
structure PowPost (x : XD) (s t : State) : Prop where
  ctx : Ctx x t
  regs : RW x t
  z : wordsVal t.mem x.S (slot x.w 4) x.w =
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) % x.p
  p : wordsVal t.mem x.S (slot x.w 0) x.w = x.p
  arr : Arr x s.mem t.mem

theorem RW.keep {x : XD} {s t : State} {rs : List Reg} (h : RW x s) (k : Keep rs s t)
    (hr : ∀ r ∈ [Reg.s6, .a7, .s5, .t0, .s11], r ∉ rs := by decide) : RW x t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  exact ⟨(k.gpr hr.1).trans h.1, (k.gpr hr.2.1).trans h.2.1, (k.gpr hr.2.2.1).trans h.2.2.1,
    (k.gpr hr.2.2.2.1).trans h.2.2.2.1, (k.gpr hr.2.2.2.2).trans h.2.2.2.2⟩

theorem arr_of {x : XD} {m m' : Mem} {o n : Nat} (h : Outside x.S o n m m') (ho : 256 ≤ o) (hn : o + n ≤ x.Z) :
    Arr x m m' := h.mono ho (by omega_arith)

theorem Arr.trans {x : XD} {m₁ m₂ m₃ : Mem} (a : Arr x m₁ m₂) (b : Arr x m₂ m₃) : Arr x m₁ m₃ := Outside.trans a b

/-- A header word into a register. -/
theorem ldh_ok {s : State} {x : XD} (hc : Ctx x s) (h6 : s.gpr .s6 = x.S) (r : Reg) {d : Nat} (hd : d + 8 ≤ 256)
    (hd8 : d % 8 = 0) :
    WP isa (.block [.load .d r .s6 d]) s fun t => (t.gpr r = word s.mem x.S d ∧ t.mem = s.mem) ∧ Keep [r] s t := by
  have hZ := hc.hZ
  have h24 : 256 ≤ slot x.w 24 := by unfold slot hdrBytes; omega_arith
  have h6' : s.gpr .s6 = off x.S 0 := by rw [h6]; simp [off]
  have hst : WP isa (.block [.load .d r .s6 d]) s fun t => t = s.write r (word s.mem x.S d) := by
    brun [h6', Nat.zero_add, hc.scr.ld (d := d) (n := 8) (by omega_arith), hc.scr.al8 (d := d) (by omega_arith) hd8,
      show d < 2048 by omega_arith]
  refine WP.mono hst fun t e => ?_
  subst e
  exact ⟨⟨by simp [gpr_write], by gsimp⟩, Keep.write _ _ _⟩

/-- `exPre`, with the registers it leaves for `loadX` and for the power, and
then the power. -/
theorem exPre_split {x : XD} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0) :
    WP isa (.block [.load .d .a6 .s6 24]) s fun s₁ => R1 x s₁ ∧
      WP isa (.seq PublicChecked.loadX (.seq r2 (.block [.load .d .s9 .s6 8, .load .d .s10 .s6 16]))) s₁
        fun s₅ => R5 x s₅ ∧ WP isa ModExp.powWin s₅ (PowPost x s) := by
  obtain ⟨hb, hp, h0⟩ := h
  have hc := hb.ctx
  have hv := h0.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv hc.k64
  have hk := hc.k64
  have hk' := hc.k1024
  have hxl := hc.xlk
  have hZ := hc.hZ
  have hn := hc.scr.nowrap
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have hw8 : 8 ≤ x.w := by omega_arith
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have hkw : x.k ≤ 8 * x.w := by omega_arith
  rw [← hwd] at hf
  have e : ∀ j, slot x.w j = hdrBytes + j * (8 * (x.w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8; have e24 := e 24
  have hh : hdrBytes = 256 := rfl
  have rw0 : RW x s := ⟨hb.s6, hb.a7, hb.s5, hb.t0, hb.s11⟩
  refine WP.mono (ldh_ok hc hb.s6 .a6 (d := 24) (by decide) (by decide)) fun s₁ ⟨⟨a6, m1⟩, k1⟩ =>
    ⟨⟨a6.trans hc.hY, rw0.keep k1⟩, ?_⟩
  have hc1 := hc.same k1 m1
  -- The peer into array 4.
  refine WP.seq (WP.mono (Pub.loadX_ok hc1.scr ((k1.gpr (by decide)).trans hb.s6) (a6.trans hc.hY)
    ((k1.gpr (by decide)).trans hb.s11) ((k1.gpr (by decide)).trans hb.a7) ((k1.gpr (by decide)).trans hb.s5)
    ((k1.gpr (by decide)).trans hb.t0) (by omega_arith) hkw hw' (by omega_arith) hc1.rdY hc1.sepY)
    fun s₂ ⟨⟨y2, _, o2, a72, _⟩, k2⟩ => ?_)
  rw [m1] at y2 o2
  have ar2 : Arr x s.mem s₂.mem := arr_of o2 (by omega_arith) (by omega_arith)
  have hc2 := hc.keep (k1.trans k2).2.1 (k1.trans k2).2.2 ar2
  have k12 := k1.trans k2
  have p2 : wordsVal s₂.mem x.S (slot x.w 0) x.w = x.p := by
    rw [Outside.wordsVal o2 (by omega_arith) (by omega_arith), hp]
  -- `R² mod p` and `-p⁻¹ mod 2⁶⁴`.
  unfold r2
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) a72 ((k12.gpr (by decide)).trans hb.s5) 1)
    fun s₃ ⟨⟨b2, m3⟩, k3⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k3.gpr (by decide)).trans a72)
    ((k12.trans k3).gpr (by decide) |>.trans hb.s5) 2) fun s₄ ⟨⟨b5, m4⟩, k4⟩ => ?_
  have k24 := (k12.trans k3).trans k4
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k3.trans k4).gpr (by decide) |>.trans a72)
    (k24.gpr (by decide) |>.trans hb.s5) 3) fun s₅ ⟨⟨b6, m5⟩, k5⟩ => ?_
  have k25 := k24.trans k5
  have hm5 : s₅.mem = s₂.mem := by rw [m5, m4, m3]
  have g7 : s₅.gpr .a7 = off x.S (slot x.w 0) := ((k3.trans k4).trans k5).gpr (by decide) |>.trans a72
  have g0 : s₅.gpr .t0 = BitVec.ofNat 64 x.w := k25.gpr (by decide) |>.trans hb.t0
  refine WP.mono (r2t_ok (hc2.scr.congr (k3.trans (k4.trans k5)).2.2) ((k4.trans k5).gpr (by decide) |>.trans b2)
    ((k5.gpr (by decide)).trans b5) b6 g7 g0 (by omega_arith) hw' (by omega_arith)
    (by rw [hm5, p2]; exact hf.2.2) (by rw [hm5, p2]; exact hf.1)) fun s₆ ⟨⟨rr6, inv6, o6⟩, k6⟩ => ?_
  rw [hm5, p2] at rr6
  rw [hm5] at inv6 o6
  have k26 := k25.trans k6
  have ar6 : Arr x s₂.mem s₆.mem := arr_of o6 (by omega_arith) (by omega_arith)
  have hc6 := hc2.keep ((k3.trans (k4.trans k5)).trans k6).2.1 ((k3.trans (k4.trans k5)).trans k6).2.2 ar6
  have rw6 : RW x s₆ := ⟨(k26.gpr (by decide)).trans hb.s6, (k6.gpr (by decide)).trans g7,
    (k26.gpr (by decide)).trans hb.s5, (k26.gpr (by decide)).trans hb.t0, (k26.gpr (by decide)).trans hb.s11⟩
  have p6 : wordsVal s₆.mem x.S (slot x.w 0) x.w = x.p := by
    rw [Outside.wordsVal o6 (by omega_arith) (by omega_arith), p2]
  have y6 : wordsVal s₆.mem x.S (slot x.w 4) x.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) := by
    rw [Outside.wordsVal o6 (by omega_arith) (by omega_arith), y2]
  have w6 : Mont.word s₆.mem x.S (slot x.w 0) = Mont.word s₂.mem x.S (slot x.w 0) :=
    Outside.word o6 (by omega_arith) (by omega_arith)
  -- x's address and length.
  rw [show ([.load .d .s9 .s6 8, .load .d .s10 .s6 16] : List Instr) =
    ([.load .d .s9 .s6 8] : List Instr) ++ ([.load .d .s10 .s6 16] : List Instr) from rfl, WP.block_append_iff]
  refine WP.mono (ldh_ok hc6 rw6.1 .s9 (d := 8) (by decide) (by decide)) fun s₇ ⟨⟨a9, m7⟩, k7⟩ => ?_
  have hc7 := hc6.same k7 m7
  refine WP.mono (ldh_ok hc7 ((k7.gpr (by decide)).trans rw6.1) .s10 (d := 16) (by decide) (by decide))
    fun s₈ ⟨⟨a10, m8⟩, k8⟩ => ?_
  have hc8 := hc7.same k8 m8
  have k78 := k7.trans k8
  have rw8 : RW x s₈ := rw6.keep k78 (by decide)
  have hm8 : s₈.mem = s₆.mem := by rw [m8, m7]
  refine ⟨⟨by rw [k8.gpr (by decide), a9]; exact hc6.hX, by rw [a10, m7]; exact hc6.hXL, rw8⟩, ?_⟩
  -- The power.
  refine WP.mono (Win.powWin_ok (D := x.X) (L := x.xl) hc8.scr (by omega_arith) hw' hZ rw8.2.1 rw8.2.2.1
    rw8.2.2.2.1 (by rw [k78.gpr (by decide), hm8, w6]; exact inv6) (by rw [hm8, p6]; exact hf.2.1)
    (by rw [hm8, p6]; exact hf.1) (by rw [hm8, p6, rr6]; exact Nat.mod_lt _ (by omega_arith))
    (by rw [k8.gpr (by decide), a9]; exact hc6.hX) (by rw [a10, m7]; exact hc6.hXL) hc.xl1 (by omega_arith)
    hc8.rdX hc8.sepX) fun t ⟨⟨hpow, ot⟩, kt⟩ => ?_
  have art : Arr x s₈.mem t.mem := arr_of ot (by omega_arith) (by omega_arith)
  have ar6' : Arr x s.mem s₆.mem := ar2.trans ar6
  have ar8 : Arr x s.mem s₈.mem := by rw [hm8]; exact ar6'
  refine ⟨hc8.keep kt.2.1 kt.2.2 art, rw8.keep kt (by decide), ?_, ?_, ar8.trans art⟩
  · rw [hpow (by rw [hm8, rr6, p6, ← Nat.pow_add]; congr 2; omega_arith), hm8, y6, p6,
      Pub.bytes_apart (o := 256) (n := x.Z - 256) ar6' (by omega_arith) hc.sepX]
  · rw [Outside.wordsVal ot (by omega_arith) (by omega_arith), hm8, p6]

end VG.Proof.Ffdh.RISCV64
