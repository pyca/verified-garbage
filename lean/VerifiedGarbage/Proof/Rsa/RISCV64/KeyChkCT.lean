module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkBase
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkBase
meta import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
meta import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Rsa.RISCV64.KeyChkFn`, which this module and modules that import it used -/

section

/-! ### `Rsa.RISCV64.KeyChkFront`, which only this module used -/

section

/-!
# The checks of an RSA key on RISC-V: the entry, the set-up and the exit

As on PPC64LE (`Proof/Rsa/PPC64LE/KcFrame.lean`, `KcEntry.lean`,
`KcSetup.lean`, `KcBody.lean`). `KPre s0 B Z K oS na`: what the proofs use of
either function's precondition: the working space (`Z` bytes at `B`, the
stack argument `oS`), writable and apart from the `na` stack arguments, and
`n_len = K` in `a1`. `KBase B Z s0 s`: memory outside the working space is
`s0`'s, the header's first twelve words hold the saved registers, and the
working space's base is in `s11`.

`tail_ok`: the entry after the arguments are moved: `e` read and checked
and `n` checked, `t0 = 0` exactly when both are valid. `setup_ok`,
`ldStep_ok`, `eArr_ok`: the arrays set up and the numbers read (`LdS`);
`Stg.base`: the checks keep `KBase`; `ret_ok`: the mask returned.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs saved mov load setW zeroArrays save)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)
open VG.Proof.Bignum.RISCV64.Pub (sat)

/-- What the proofs use of the precondition. -/
structure KPre (s0 : State) (B : Addr) (Z K oS na : Nat) : Prop where
  wr : (⟨B, Z⟩ : Region) ∈ s0.wr
  nowrap : B.toNat + Z ≤ 2 ^ 64
  al : B.toNat % 8 = 0
  zk : 8 * (16 * K + 32) ≤ Z
  k64 : 64 ≤ K
  k1024 : K ≤ 1024
  sp : s0.sp.toNat + 8 * na ≤ 2 ^ 64
  sp16 : s0.sp.toNat % 16 = 0
  args : (⟨stackArgAddr s0 0, 8 * na⟩ : Region) ∈ s0.rd
  disj : (⟨B, Z⟩ : Region).Disjoint ⟨stackArgAddr s0 0, 8 * na⟩
  base : stackArg s0 oS = B
  hoS : oS < na
  a1 : (s0.gpr .a1).toNat = K

structure KBase (B : Addr) (Z : Nat) (s0 s : State) : Prop where
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  frame : ∀ x, Z ≤ ofs B x → s.mem x = s0.mem x
  hdr : ∀ i < 12, word s.mem B (8 * i) = s0.gpr (saved i)
  s11 : s.gpr .s11 = B

theorem KBase.of_regs {B : Addr} {Z : Nat} {s0 s t : State} (h : KBase B Z s0 s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hr : .s11 ∉ rs := by decide) : KBase B Z s0 t :=
  ⟨k.2.1.trans h.rd, k.2.2.trans h.wr, fun x hx => by rw [hm]; exact h.frame x hx,
    fun i hi => by rw [hm]; exact h.hdr i hi, (k.gpr hr).trans h.s11⟩

/-- A step that writes only arrays and slots from 96 on keeps `KBase`. -/
theorem KBase.of_frame {B : Addr} {Z : Nat} {s0 s t : State} (h : KBase B Z s0 s) {w : Nat}
    {js ds : List Nat} (k : Keys.Frame B w js ds s.mem t.mem)
    (hjs : ∀ j ∈ js, arr w j + S w ≤ Z) (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ Keys.hdr) (hZ : Keys.hdr ≤ Z)
    {rs : List Reg} (kr : Keep rs s t) (hr : .s11 ∉ rs := by decide) : KBase B Z s0 t := by
  refine ⟨kr.2.1.trans h.rd, kr.2.2.trans h.wr, fun x hx => ?_, fun i hi => ?_, (kr.gpr hr).trans h.s11⟩
  · rw [← h.frame x hx]
    exact k.out (Z := Z) hjs (fun d hd => by have := hds d hd; omega_using [hZ, this]) hx
  · rw [← h.hdr i hi]
    have e := k.words (d := 8 * i) (k := 1) (fun j _ => by have := hdr_le_arr w j; simp only [hdr_eq] at this; omega_using [hi, this])
      (fun d hd => by have := hds d hd; omega_using [hi, this]) (by omega_using [hi])
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at e
    exact BitVec.eq_of_toNat_eq e

theorem past_of_disjoint {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr}
    (ha : r.Contains a 1) : Z ≤ ofs B a := by
  have := hd a ha
  simp only [Region.Contains] at this
  simp only [ofs]; omega_using [this]

/-! ## The entry, after the arguments are moved -/

/-- What `e` and `n` are read and checked into. -/
def tail : Prog isa :=
  .seq VG.Impl.Bignum.RISCV64.PublicChecked.readE
    (.seq (.block (VG.Impl.Bignum.RISCV64.PublicChecked.checkE ++ [mov .a5 .s9, mov .a4 .s7, mov .s7 .s1, mov .s8 .s2]))
      (.seq VG.Impl.Bignum.RISCV64.Precompute.check (.block [.addi .t0 .a5 1, .logic .or .t0 .t0 .s0])))

theorem entry_eq (oS : Nat) (moves : List Instr) : entry oS moves = .seq (.block (save oS ++ moves)) tail := rfl

/-- The registers the tail changes. -/
abbrev tailRegs : List Reg := [.a4, .a5, .s7, .t2, .t3, .t4, .s9, .s8, .s0, .t5, .t0]

theorem or_one_ne (x : BitVec 64) : BitVec.ofNat 64 1 ||| x ≠ 0 := by
  intro h
  have := congrArg (fun y => y.getLsbD 0) h
  simp at this

theorem mask_add_one (b : Bool) (x : BitVec 64) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) + BitVec.ofNat 64 1) ||| x = 0 ↔
      (b = true ∧ x = 0) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 0 + BitVec.ofNat 64 1 = BitVec.ofNat 64 1 by decide]
    exact or_one_ne x
  · simp only [↓reduceIte, true_and]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 + BitVec.ofNat 64 1 = 0 by decide]
    simp

theorem exponentValid_sat (v : Nat) : Spec.Rsa.exponentValid (sat v) = Spec.Rsa.exponentValid v := by
  unfold sat
  by_cases h : v < 2 ^ 33
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [Nat.min_eq_right (by omega_using [h])]
    have h2 : (decide (v < 2 ^ 33)) = false := decide_eq_false h
    simp only [Spec.Rsa.exponentValid, h2, Bool.and_false]
    decide

theorem tail_ok {v : State} {E N : Addr} {L K : Nat} (h4 : v.gpr .a4 = off E 0)
    (h5 : v.gpr .a5 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L ≤ 1024)
    (hrdE : ∀ i < L, InRegions (v.rd ++ v.wr) (off E i) 1) (h1 : v.gpr .s1 = off N 0)
    (h2 : v.gpr .s2 = BitVec.ofNat 64 K) (hK : 64 ≤ K) (hK' : K ≤ 1024)
    (hrdN : ∀ i < K, InRegions (v.rd ++ v.wr) (off N i) 1) :
    WP isa tail v fun t =>
      (t.gpr .t0 = 0 ↔ (Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem E L)) = true ∧
        Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem N K)) K = true)) ∧
      t.gpr .a4 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem E L))) <<< 31 ∧
      t.mem = v.mem ∧ Keep tailRegs v t := by
  unfold tail
  refine WP.seq (WP.mono (Pub.readE_ok h4 h5 hL (by omega_using [hL']) hrdE) fun u ⟨⟨u7, um⟩, ku⟩ => ?_)
  have hsat : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem E L)) ≤ 2 ^ 33 := by unfold sat; omega_using []
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.checkE_ok u7 hsat) fun x ⟨⟨x9, x7, xm⟩, kx⟩ => ?_
  have g1 : x.gpr .s1 = off N 0 := by rw [kx.gpr (by decide), ku.gpr (by decide), h1]
  have g2 : x.gpr .s2 = BitVec.ofNat 64 K := by rw [kx.gpr (by decide), ku.gpr (by decide), h2]
  refine WP.mono (WP.keep [.a5, .a4, .s7, .s8] (Q := fun y => y.gpr .a5 = x.gpr .s9 ∧ y.gpr .a4 = x.gpr .s7 ∧
    y.gpr .s7 = off N 0 ∧ y.gpr .s8 = BitVec.ofNat 64 K ∧ y.mem = x.mem) (by
      brun [mov, g1, g2, add_ofNat_zero']) (by rfl) (by rfl)) fun y ⟨⟨y5, y4, y7, y8, ym⟩, ky⟩ => ?_
  have kvy := (ku.trans (kx.trans ky))
  have hrd' : ∀ i < K, InRegions (y.rd ++ y.wr) (off N i) 1 := fun i hi => by
    rw [kvy.2.1, kvy.2.2]; exact hrdN i hi
  have yv : y.mem = v.mem := ym.trans (xm.trans um)
  refine WP.seq (WP.mono (check_ok (nb := Spec.Rsa.bytesAt v.mem N K) y7 y8 hK hK' (by simp [Spec.Rsa.bytesAt])
    hrd' (fun i hi => by simp [Spec.Rsa.bytesAt, yv])) fun z ⟨z0, zm, kz⟩ => ?_)
  have z5 : z.gpr .a5 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if Spec.Rsa.exponentValid (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem E L))) then 1 else 0) := by
    rw [kz.gpr (by decide), y5, x9]
  refine WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = (z.gpr .a5 + BitVec.ofNat 64 1) ||| z.gpr .s0 ∧
    t.mem = z.mem) (by brun []) (by rfl) (by rfl)) fun t ⟨⟨t0, tm⟩, kt⟩ => ?_
  refine ⟨?_, ?_, by rw [tm, zm, yv], ?_⟩
  · rw [t0, z5, mask_add_one, exponentValid_sat, z0]
  · rw [kt.gpr (by decide), kz.gpr (by decide), y4, x7]
  · exact ((((ku.trans kx).trans ky).trans kz).trans kt).mono (by decide)

/-- The tail's block after `readE`: `e` checked, and the moves to `check`. -/
theorem tB_ok {u : State} {E : Nat} {N : Addr} {K : Nat} (u7 : u.gpr .s7 = BitVec.ofNat 64 E) (hE : E ≤ 2 ^ 33)
    (g1 : u.gpr .s1 = off N 0) (g2 : u.gpr .s2 = BitVec.ofNat 64 K) :
    WP isa (.block (VG.Impl.Bignum.RISCV64.PublicChecked.checkE ++
        [mov .a5 .s9, mov .a4 .s7, mov .s7 .s1, mov .s8 .s2])) u fun y =>
      (y.gpr .a5 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if Spec.Rsa.exponentValid E then 1 else 0) ∧
        y.gpr .a4 = BitVec.ofNat 64 E <<< 31 ∧ y.gpr .s7 = off N 0 ∧ y.gpr .s8 = BitVec.ofNat 64 K ∧
        y.mem = u.mem) ∧ Keep [.s7, .s9, .t2, .t3, .t4, .a5, .a4, .s7, .s8] u y := by
  rw [WP.block_append_iff]
  refine WP.mono (Pub.checkE_ok u7 hE) fun x ⟨⟨x9, x7, xm⟩, kx⟩ => ?_
  have g1' : x.gpr .s1 = off N 0 := by rw [kx.gpr (by decide), g1]
  have g2' : x.gpr .s2 = BitVec.ofNat 64 K := by rw [kx.gpr (by decide), g2]
  refine WP.mono (WP.keep [.a5, .a4, .s7, .s8] (Q := fun y => y.gpr .a5 = x.gpr .s9 ∧ y.gpr .a4 = x.gpr .s7 ∧
    y.gpr .s7 = off N 0 ∧ y.gpr .s8 = BitVec.ofNat 64 K ∧ y.mem = x.mem) (by
      brun [mov, g1', g2', add_ofNat_zero']) (by rfl) (by rfl)) fun y ⟨⟨y5, y4, y7, y8, ym⟩, ky⟩ =>
    ⟨⟨y5.trans x9, y4.trans x7, y7, y8, ym.trans xm⟩, kx.trans ky⟩

/-- The tail's last block: `t0 := (a5 + 1) | s0`. -/
theorem tE_ok (z : State) :
    WP isa (.block [.addi .t0 .a5 1, .logic .or .t0 .t0 .s0]) z fun t =>
      (t.gpr .t0 = (z.gpr .a5 + BitVec.ofNat 64 1) ||| z.gpr .s0 ∧ t.mem = z.mem) ∧ Keep [.t0] z t :=
  WP.keep [.t0] (by brun []) (by rfl) (by rfl)

/-! ## The set-up -/

/-- `w = ⌈K / 8⌉`. -/
abbrev kw (K : Nat) : Nat := (K + 7) / 8

theorem KPre.ws {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) :
    arr (kw K) nArr ≤ Z ∧ 8 ≤ kw K ∧ kw K ≤ 128 ∧ K ≤ 8 * kw K := by
  have := h.zk; have := h.k64; have := h.k1024
  simp only [arr, S, nArr, hdr_eq, kw]
  omega_arith

/-- `setup`: `w` and the stride, and every word of the arrays 0. -/
theorem setup_ok {s0 s : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na) (h : KBase B Z s0 s)
    (h2 : s.gpr .s2 = BitVec.ofNat 64 K) :
    WP isa setup s fun t => KBase B Z s0 t ∧ Ws t B Z (kw K) nArr ∧
      (∀ j < nArr, wordsVal t.mem B (arr (kw K) j) (kw K + 2) = 0) ∧
      Keep (.s9 :: .s10 :: opRegs) s t := by
  obtain ⟨fits, hw8, hw, -⟩ := hp.ws
  have nw := hp.nowrap
  have hs : Scr s B Z := Scr.of_mem (by rw [h.wr]; exact hp.wr) nw hp.al
  rw [setup, WP.seq_iff]
  refine WP.mono (setW_ok h2 (by have := hp.k1024; omega_using [this])) fun u ⟨⟨u9, u10, um⟩, ku⟩ => ?_
  have hu : Ws u B Z (kw K) nArr :=
    ⟨hs.congr ku.2.2, fits, by omega_using [hw8], by omega_using [hw], u9, u10, (ku.gpr (by decide)).trans h.s11⟩
  refine WP.mono (zeroArrays_ok hu (c := nArr) (by decide) (Nat.le_refl _) (by decide))
    fun t ⟨ht, z, zz, kt⟩ => ⟨?_, ht, zz, (ku.trans kt).mono (by decide)⟩
  refine (h.of_regs ku um).of_frame z (fun j hj => hu.arr_fit (List.mem_range.mp hj)) (by simp)
    hu.hdr_le kt

/-- What the reading of the numbers keeps. -/
structure LdS (B : Addr) (Z K : Nat) (s0 : State) (A : Nat → Nat) (t : State) : Prop where
  base : KBase B Z s0 t
  ws : Ws t B Z (kw K) nArr
  arrs : Arrs t.mem B (kw K) A (List.range nArr)
  top : ∀ j < nArr, word t.mem B (arr (kw K) j + 8 * kw K) = 0

/-- `setup`'s arrays: every one 0. -/
theorem LdS.of_setup {B : Addr} {Z K : Nat} {s0 t : State} (b : KBase B Z s0 t) (w : Ws t B Z (kw K) nArr)
    (z : ∀ j < nArr, wordsVal t.mem B (arr (kw K) j) (kw K + 2) = 0) :
    LdS B Z K s0 (fun _ => 0) t := by
  refine ⟨b, w, fun j hj => ?_, fun j hj => ?_⟩
  · have := wordsVal_zero_part (a := 0) (c := kw K) (z j (List.mem_range.mp hj)) (by omega_using [])
    simpa using this
  · have := wordsVal_zero_part (a := kw K) (c := 1) (z j hj) (by omega_using [])
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at this
    exact BitVec.eq_of_toNat_eq (by simpa using this)

theorem bytes_frame {B : Addr} {Z : Nat} {s0 t : State} (h : KBase B Z s0 t) {P : Addr} {L : Nat}
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨B, Z⟩) (hPw : P.toNat + L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem P L = Spec.Rsa.bytesAt s0.mem P L := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun c hc => h.frame _ (past_of_disjoint hd ?_)
  have := List.mem_range.mp hc
  exact Offset.contains_base _ (by omega_using [this]) (by omega_using [hPw, this])

/-- `load j src len`: array `j`, 0, := the `L` bytes at `P`. -/
theorem ldStep_ok {B : Addr} {Z K : Nat} {s0 t : State} {A : Nat → Nat} (hI : LdS B Z K s0 A t) {j : Nat}
    (hj : j < nArr) (hA : A j = 0) {src len : Reg} (hl1 : len ≠ .t1)
    {P : Addr} {L : Nat} (hP : t.gpr src = P) (hL : t.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 8 * kw K) (hrd : (⟨P, L⟩ : Region) ∈ s0.rd) (hd : (⟨P, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (hPw : P.toNat + L ≤ 2 ^ 64) :
    WP isa (load j src len) t fun u =>
      LdS B Z K s0 (upd A j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L))) u ∧ Keep [.t0, .t1, .t3, .t5] t u := by
  have h := hI.ws
  have hS : S (kw K) = 8 * (kw K + 2) := rfl
  have fit : ∀ i < nArr, arr (kw K) i + S (kw K) ≤ 2 ^ 64 := fun i hi => h.fit64 hi
  have hc : ∀ i < L, (⟨P, L⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hPw, hi])
  refine WP.mono (load_ok h hj (by decide) hl1 hP hL hL1 hLw
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [hI.base.rd]; exact hrd), hc i hi⟩)
    (fun i hi x hx e => by have := past_of_disjoint hd (hc i hi); rw [e] at this; omega_using [hx, this])
    ((hI.arrs.get (List.mem_range.mpr hj)).trans hA))
    fun v ⟨hv, k, val, kv, o⟩ => ⟨⟨hI.base.of_frame k (by simpa using h.arr_fit hj) (by simp) h.hdr_le kv,
      hv, fun i hi => ?_, fun i hi => ?_⟩, kv⟩
  · by_cases e : i = j
    · subst e
      rw [upd_self, val, bytes_frame hI.base hd hPw]
    · rw [upd_ne _ _ e, k.num (by simpa using Ne.symm e) (by simp) (fit _ (List.mem_range.mp hi))]
      exact hI.arrs.get hi
  · have fi := fit i hi
    by_cases e : i = j
    · subst e; rw [o.word (by omega_using []) (by omega_using [hS, fi])]; exact hI.top _ hi
    · have := arr_disj (w := kw K) e
      rw [o.word (by omega_using [hS, this]) (by omega_using [hS, fi])]; exact hI.top _ hi

theorem shl_shr31 {E : Nat} (hE : E < 2 ^ 33) : (BitVec.ofNat 64 E <<< 31) >>> 31 = BitVec.ofNat 64 E := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega_using [hE]),
    Nat.mod_eq_of_lt (show E * 2 ^ 31 < 2 ^ 64 by omega_using [hE]), Nat.mul_div_cancel _ (by decide)]

/-- `eArr`: `e`, below `2^33`, from `a4 = e · 2^31` into its array, which is 0. -/
theorem eArr_ok {B : Addr} {Z K : Nat} {s0 t : State} {A : Nat → Nat} (hI : LdS B Z K s0 A t)
    (hA : A aE = 0) {E : Nat} (h4 : t.gpr .a4 = BitVec.ofNat 64 E <<< 31) (hE : E < 2 ^ 33) :
    WP isa (.block eArr) t fun u => LdS B Z K s0 (upd A aE E) u ∧ Keep opRegs t u := by
  have h := hI.ws
  have hS : S (kw K) = 8 * (kw K + 2) := rfl
  have fit : ∀ i < nArr, arr (kw K) i + S (kw K) ≤ 2 ^ 64 := fun i hi => h.fit64 hi
  have fE := h.arr_fit (j := aE) (by decide)
  have nw := h.nowrap
  have fit0 := fit aE (by decide)
  unfold eArr
  refine ptr_ok h (r := .t0) (by decide) (by decide) (show aE < 2048 by decide) ?_
  have hm : WP isa (.block [.shift .srl .d .t5 .a4 31, .store .d .t5 .t0 0])
      (t.write .t0 (off B (arr (kw K) aE))) fun u =>
        u.mem = t.mem.writeW (off B (arr (kw K) aE)) (BitVec.ofNat 64 E) ∧ Keep [.t0, .t5] t u := by
    refine WP.mono (WP.keep [.t5] (Q := fun u => u.mem = t.mem.writeW (off B (arr (kw K) aE))
      (BitVec.ofNat 64 E)) ?_ (by rfl) (by rfl)) fun u ⟨m, k⟩ => ⟨m, ((Keep.write _ _ _).trans k).mono (by decide)⟩
    brun [h4, shl_shr31 hE, h.scr.st (d := arr (kw K) aE) (n := 8) (by omega_using [hS, fE]),
      h.scr.al8 (d := arr (kw K) aE) (by omega_using [hS, fE]) (arr_al _ _)]
  refine WP.mono hm fun u ⟨um, ku⟩ => ?_
  have lw := low_write (m := t.mem) (B := B) h.wpos fit0 (BitVec.ofNat 64 E)
  have o := writeW_outside t.mem B (d := arr (kw K) aE) (BitVec.ofNat 64 E) (by omega_using [hS, fE, nw])
  rw [← um] at lw o
  obtain ⟨k, val⟩ := lw
  have z : num t.mem B (kw K) aE = 0 := (hI.arrs.get (List.mem_range.mpr (by decide))).trans hA
  have ku' : Keep opRegs t u := ku.mono (by decide)
  refine ⟨⟨hI.base.of_frame k (by simpa using fE) (by simp) h.hdr_le ku', h.of_keep ku', fun j hj => ?_,
    fun j hj => ?_⟩, ku'⟩
  · by_cases e : j = aE
    · subst e
      rw [upd_self, val, z]
      simp only [BitVec.toNat_ofNat, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
      omega_using [hE]
    · rw [upd_ne _ _ e, k.num (by simpa using Ne.symm e) (by simp) (fit _ (List.mem_range.mp hj))]
      exact hI.arrs.get hj
  · by_cases e : j = aE
    · subst e
      have := h.wpos
      rw [o.word (by omega_using [this]) (by omega_using [hS, fE, nw])]
      exact hI.top _ hj
    · rw [k.word (by omega_using []) (by simpa using Ne.symm e) (by simp) (fit _ hj)]
      exact hI.top _ hj

end VG.Proof.Rsa.RISCV64.KeyCheck

end

end

/-!
# The checks of an RSA key on RISC-V: a function, from its parts

`fn_ok`: `KeyCheck.fn` from the precondition (`KPre`): `save`, the moves of
the arguments (whatever they establish, `MV`), the entry's checks of `e` and
`n` (`tail_ok`), then the valid branch (given), or 0 returned, and the
registers restored. `ldSp_ok`: a stack argument loaded through `t0 = sp`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs saved save restore)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Bignum.RISCV64.Pub (sat)

theorem stackArgAddr_eq (s : State) (i : Nat) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) := by
  unfold stackArgAddr
  rw [Nat.mul_zero]
  exact (congrArg (· + BitVec.ofNat 64 (8 * i)) (add_ofNat_zero' s.sp)).symm

/-- The stack argument `i` is readable. -/
theorem KPre.arg_rd {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) {i : Nat}
    (hi : i < na) : InRegions (s0.rd ++ s0.wr) (stackArgAddr s0 i) 8 := by
  have hs := h.sp
  refine ⟨_, List.mem_append_left _ h.args, ?_⟩
  rw [stackArgAddr_eq s0 i]
  exact Offset.contains_base (d := 8 * i) (n := 8) (k := 8 * na) (stackArgAddr s0 0) (by omega_using [hi]) (by omega_using [hi, hs])

theorem KPre.arg_al {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) {i : Nat}
    (hi : i < na) : (stackArgAddr s0 i).toNat % 8 = 0 := by
  have hs := h.sp
  have h16 := h.sp16
  have e : (stackArgAddr s0 i).toNat = s0.sp.toNat + 8 * i := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hi, hs]
  rw [e]; omega_using [h16]

/-- A stack argument loaded through `t0 = sp`. -/
theorem ldSp_ok {u : State} (h0 : u.gpr .t0 = u.sp) {r : Reg} {i o : Nat} (ho : o = 8 * i) (hi : 8 * i < 2048)
    (hin : InRegions (u.rd ++ u.wr) (stackArgAddr u i) 8) (hal : (stackArgAddr u i).toNat % 8 = 0)
    {rest : List Instr} {Q : State → Prop} (k : WP isa (.block rest) (u.write r (stackArg u i)) Q) :
    WP isa (.block (.load .d r .t0 o :: rest)) u Q := by
  subst ho
  have e : u.gpr .t0 + BitVec.ofNat 64 (8 * i) = stackArgAddr u i := by rw [h0]; rfl
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d hi (by rw [e]; exact hal) (by rw [e]; exact hin), ?_⟩
  rw [e]
  exact k

/-- `save`'s state, as `KBase`. -/
theorem KBase.of_saved {s0 u : State} {B : Addr} {Z : Nat} (h : Saved s0 B u) (hZ : 96 ≤ Z) :
    KBase B Z s0 u :=
  ⟨h.keep.2.1, h.keep.2.2, fun x hx => h.out x (Or.inr (by omega_using [hZ, hx])), h.saved, h.s11⟩

/-- The registers the code may change, but `ra`. -/
abbrev fnRegs : List Reg := [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7,
  .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .t3, .t4, .t5, .t6]

theorem fn_ok {s0 : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na) (hoS : 8 * oS < 2048)
    {moves : List Instr} {loads body : List (Prog isa)} {E N : Addr} {L : Nat} {ok : Bool}
    {MV : State → Prop}
    (hm : ∀ u, Saved s0 B u → WP isa (.block moves) u fun v => MV v ∧ v.mem = u.mem ∧ v.rd = u.rd ∧
      v.wr = u.wr ∧ v.gpr .s11 = u.gpr .s11 ∧ v.gpr .a4 = off E 0 ∧ v.gpr .a5 = BitVec.ofNat 64 L ∧
      v.gpr .s1 = off N 0 ∧ v.gpr .s2 = BitVec.ofNat 64 K)
    (hL : 1 ≤ L) (hL' : L ≤ 1024) (hE : (⟨E, L⟩ : Region) ∈ s0.rd) (dE : (⟨E, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (wE : E.toNat + L ≤ 2 ^ 64) (hN : (⟨N, K⟩ : Region) ∈ s0.rd) (dN : (⟨N, K⟩ : Region).Disjoint ⟨B, Z⟩)
    (wN : N.toNat + K ≤ 2 ^ 64)
    (hok : ok = true → Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem E L)) = true ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem N K)) K = true)
    (hv : ∀ v t, MV v → Keep tailRegs v t → KBase B Z s0 t →
      t.gpr .a4 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem E L))) <<< 31 →
      Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem E L)) = true →
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem N K)) K = true →
      WP isa (seqs (([setup, .block eArr] : List (Prog isa)) ++ loads ++ body ++ ([.block ret] : List (Prog isa)))) t fun u =>
        KBase B Z s0 u ∧ u.gpr .a0 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    WP isa (fn (8 * oS) moves loads body) s0 fun t =>
      (∀ i < 12, t.gpr (saved i) = s0.gpr (saved i)) ∧ t.gpr .a0 = BitVec.ofNat 64 (if ok then 1 else 0) := by
  have hZ : 96 ≤ Z := by have := hp.zk; omega_using [this]
  have hs : Scr s0 (stackArg s0 oS) Z := by rw [hp.base]; exact Scr.of_mem hp.wr hp.nowrap hp.al
  unfold fn
  rw [entry_eq]
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s0 hoS (hp.arg_rd hp.hoS) (hp.arg_al hp.hoS) hs hZ) fun u hu => ?_
  rw [hp.base] at hu
  have bu := KBase.of_saved hu hZ
  refine WP.mono (hm u hu) fun v ⟨mv, vm, vrd, vwr, v11, v4, v5, v1, v2⟩ => ?_
  have bv : KBase B Z s0 v := ⟨vrd.trans bu.rd, vwr.trans bu.wr, fun x hx => by rw [vm]; exact bu.frame x hx,
    fun i hi => by rw [vm]; exact bu.hdr i hi, v11.trans bu.s11⟩
  have rdv : ∀ {P : Addr} {M : Nat}, (⟨P, M⟩ : Region) ∈ s0.rd → P.toNat + M ≤ 2 ^ 64 → ∀ i < M,
      InRegions (v.rd ++ v.wr) (off P i) 1 := fun hP wP i hi =>
    ⟨_, List.mem_append_left _ (by rw [bv.rd]; exact hP), Offset.contains_base _ (by omega_using [hi]) (by omega_using [wP, hi])⟩
  refine WP.mono (tail_ok v4 v5 hL hL' (rdv hE wE) v1 v2 hp.k64 hp.k1024 (rdv hN wN))
    fun t ⟨t0, t4, tm, kt⟩ => ?_
  rw [bytes_frame bv dE wE, bytes_frame bv dN wN] at t0
  rw [bytes_frame bv dE wE] at t4
  have bt := bv.of_regs kt tm
  have fin : ∀ u, KBase B Z s0 u → u.gpr .a0 = BitVec.ofNat 64 (if ok then 1 else 0) →
      WP isa (.block restore) u fun x =>
        (∀ i < 12, x.gpr (saved i) = s0.gpr (saved i)) ∧ x.gpr .a0 = BitVec.ofNat 64 (if ok then 1 else 0) := by
    intro u bu' a0
    have hsu : Scr u B Z := Scr.of_mem (by rw [bu'.wr]; exact hp.wr) hp.nowrap hp.al
    refine WP.mono (restore_ok u hsu hZ bu'.s11 bu'.hdr) fun x ⟨xs, xo, _⟩ => ⟨xs, ?_⟩
    rw [xo .a0 (by decide), a0]
  refine WP.seq ?_
  refine WP.ite _ (Steps.eval_zero t .t0) (fun hz => ?_) (fun hz => ?_)
  · have hz' : t.gpr .t0 = 0 := by simpa using hz
    obtain ⟨ev, mv'⟩ := t0.mp hz'
    exact WP.mono (hv v t mv kt bt t4 ev mv') fun u ⟨bu', a0⟩ => fin u bu' a0
  · have hz' : t.gpr .t0 ≠ 0 := by simpa using hz
    have hok' : ok = false := by
      cases e : ok
      · rfl
      · exact absurd (t0.mpr (hok e)) hz'
    refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 0 ∧ u.mem = t.mem) (by
      have e : exec (.li .a0 0) t = some (t.write .a0 (BitVec.ofNat 64 0)) := by
        rw [exec_li (by decide)]; rfl
      brun [ret0, e]) (by rfl) (by rfl)) fun u ⟨⟨a0, um⟩, ku⟩ => fin u (bt.of_regs ku um) ?_
    rw [a0, hok']; rfl

/-- The checks keep `KBase`. -/
theorem Stg.base {g : Geo} {s0 sS t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g sS A live c t) (hb : KBase g.B g.Z s0 sS) : KBase g.B g.Z s0 t :=
  hb.of_frame h.frame (fun j hj => h.ws.arr_fit (List.mem_range.mp hj)) (by decide) h.ws.hdr_le h.regs

/-- `ret`: the mask's bit in `a0`. -/
theorem ret_ok {g : Geo} {sS t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g sS A live c t) :
    WP isa (.block ret) t fun u => (u.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0) ∧ u.mem = t.mem) ∧
      Keep [.a0] t u := by
  have hs := h.ws.scr
  have hz := h.ws.hdr_le
  have e : word t.mem g.B sMask = BitVec.ofNat 64 (if c then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by cases c <;> decide)]
    exact h.mask
  have ea : t.gpr .s11 + BitVec.ofNat 64 sMask = off g.B sMask := by rw [h.ws.s11]
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .s11 + BitVec.ofNat 64 sMask) 8 := by
    rw [ea]; exact hs.ld (d := sMask) (n := 8) (by simp only [hdr_eq] at hz; unfold sMask; omega_using [hz])
  have hal : (t.gpr .s11 + BitVec.ofNat 64 sMask).toNat % 8 = 0 := by
    rw [ea]; exact hs.al8 (d := sMask) (by simp only [hdr_eq] at hz; unfold sMask; omega_using [hz]) (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (by decide) hal hin, WP.block_nil ?_⟩
  rw [ea]
  exact ⟨by rw [gpr_write_self]; exact e, rfl⟩

end VG.Proof.Rsa.RISCV64.KeyCheck

end

end

/-!
# The checks of an RSA key on RISC-V: constant time

As on PPC64LE (`Proof/Rsa/PPC64LE/KcVerified.lean`): two runs with the same
public data (`D`: the arguments, the stack arguments, `n` and `e`) are
related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each step, both
satisfying the same predicate for the same data, which fixes the registers
the next piece's addresses and branches read; the pieces by the taint
analysis, what each run satisfies after each by correctness (`two_post`).
The taint analysis treats memory as secret, so the code is cut after each
load whose value an address or a branch reads: the working space's address,
the stack arguments, `n`'s first byte, and whether `e` and `n` are valid,
which the one branch tests (`RelCT.ite`). `fn_rel`: `KeyCheck.fn`, from the
function's own pieces (the moves, the valid branch).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
  VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs saved save restore mov)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Bignum.RISCV64.Pub (sat)

/-! ## `save`, in two parts -/

/-- The stores of `save`, and the base into `s11`. -/
def save2 : List Instr :=
  (List.range 12).flatMap (fun i => [.store .d (saved i) .t0 (8 * i)]) ++ [mov .s11 .t0]

theorem save_eq (o : Nat) (moves : List Instr) :
    save o ++ moves = ([.addSp .t0 0, .load .d .t0 .t0 o] : List Instr) ++ (save2 ++ moves) := by
  simp only [save, save2, List.append_assoc]

/-- `save`'s first part: the working space's address, the stack argument `i`, into `t0`. -/
theorem save1_ok (s₀ : State) {i : Nat} (hi : 8 * i < 2048)
    (hin : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ i) 8) (hal : (stackArgAddr s₀ i).toNat % 8 = 0) :
    WP isa (.block [.addSp .t0 0, .load .d .t0 .t0 (8 * i)]) s₀ fun s =>
      (s.gpr .t0 = stackArg s₀ i ∧ s.mem = s₀.mem ∧ s.sp = s₀.sp) ∧ Keep [.t0] s₀ s := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  obtain e : s₀.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * i) = stackArgAddr s₀ i := by
    rw [add_ofNat_zero']; rfl
  obtain ha : ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).gpr .t0 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
    rw [gpr_write_self, e]; exact hal
  obtain hin' : InRegions ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).rd ++ (s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).wr)
      ((s₀.write .t0 (s₀.sp + BitVec.ofNat 64 0)).gpr .t0 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [gpr_write_self, e]; exact hin
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addSp (show 0 < 2048 by decide),
    exec_load_d hi ha hin', Option.some.injEq, exists_eq_left', gpr_write_self, e, mem_write, sp_write,
    and_true]
  first | rfl | exact ⟨rfl, rfl⟩

/-- `save`'s second part: the registers saved. -/
theorem save2_ok (s₀ : State) {B : Addr} {Z : Nat} (hs : Scr s₀ B Z) (hZ : 96 ≤ Z) {s₁ : State}
    (h : (s₁.gpr .t0 = B ∧ s₁.mem = s₀.mem ∧ s₁.sp = s₀.sp) ∧ Keep [.t0] s₀ s₁) :
    WP isa (.block save2) s₁ (Saved s₀ B) := by
  obtain ⟨⟨i0, im, isp⟩, k₁⟩ := h
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀ B)
    (fun k s hk h => save_step s₀ hs hZ hk h) 12 (Nat.le_refl _) s₁
    ⟨k₁, i0, isp, by rw [im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s h => ?_)
  have hw : s.gpr .t0 = B := h.t0
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
    BitVec.ofInt_ofNat, add_ofNat_zero', Option.some.injEq, exists_eq_left', hw]
  refine ⟨(h.keep.trans (Keep.write _ _ _)).mono (by decide), h.sp, ?_, ?_, h.out, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (by decide)]; exact hw
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-! ## Two runs -/

/-- `t0` holds 0 exactly when `e` and `n` are valid, after the tail. -/
theorem t0_iff (b : Bool) (x : BitVec 64) {P : Prop} (h : x = 0 ↔ P) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) + BitVec.ofNat 64 1) ||| x = 0 ↔
      (b = true ∧ P) := by
  rw [mask_add_one, h]

/-! ## A function's pieces -/

/-- What the constant-time proof of a key check needs to know of the
function: its precondition and public data, its working space and the
arguments its entry reads, and what its moves establish. -/
structure KC (β : Type) where
  Pre : State → Prop
  D : State → β
  B : State → Addr
  Z : State → Nat
  K : State → Nat
  E : State → Addr
  L : State → Nat
  N : State → Addr
  MV : State → State → Prop

variable {β : Type} (F : KC β)

abbrev KC.eN (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (F.E s0) (F.L s0))
abbrev KC.nB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (F.N s0) (F.K s0)
abbrev KC.ev (s0 : State) : Prop := Spec.Rsa.exponentValid (F.eN s0) = true
abbrev KC.mv (s0 : State) : Prop := Spec.Rsa.modulusValid (Spec.Rsa.os2ip (F.nB s0)) (F.K s0) = true
abbrev KC.mask (s0 : State) : BitVec 64 :=
  BitVec.ofNat 64 0 - BitVec.ofNat 64 (if Spec.Rsa.exponentValid (sat (F.eN s0)) then 1 else 0)

def KC.C0 (a : β) (s : State) : Prop := F.Pre s ∧ F.D s = a

/-- After the moves. -/
def KC.M2 (s0 v : State) : Prop :=
  F.MV s0 v ∧ KBase (F.B s0) (F.Z s0) s0 v ∧ v.gpr .a4 = off (F.E s0) 0 ∧
    v.gpr .a5 = BitVec.ofNat 64 (F.L s0) ∧ v.gpr .s1 = off (F.N s0) 0 ∧ v.gpr .s2 = BitVec.ofNat 64 (F.K s0)

def KC.S1 (a : β) (t : State) : Prop :=
  ∃ s0, F.C0 a s0 ∧ (t.gpr .t0 = F.B s0 ∧ t.mem = s0.mem ∧ t.sp = s0.sp) ∧ Keep [.t0] s0 t

def KC.S2 (a : β) (v : State) : Prop := ∃ s0, F.C0 a s0 ∧ F.M2 s0 v

def KC.S3 (a : β) (u : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ (u.gpr .s7 = BitVec.ofNat 64 (sat (F.eN s0)) ∧ u.mem = v.mem) ∧
    Keep tailRegs v u

def KC.S4 (a : β) (y : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ (y.gpr .a5 = F.mask s0 ∧ y.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s0)) <<< 31 ∧
    y.gpr .s7 = off (F.N s0) 0 ∧ y.gpr .s8 = BitVec.ofNat 64 (F.K s0) ∧ y.mem = v.mem) ∧ Keep tailRegs v y

def KC.S5 (a : β) (z : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ ((z.gpr .s0 = 0 ↔ ((F.nB s0).getD (F.K s0 - 1) 0).toNat % 2 = 1) ∧
    z.gpr .t4 = BitVec.ofNat 64 ((F.nB s0).getD 0 0).toNat ∧ z.gpr .a5 = F.mask s0 ∧
    z.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s0)) <<< 31 ∧ z.gpr .s8 = BitVec.ofNat 64 (F.K s0) ∧ z.mem = v.mem) ∧
    Keep tailRegs v z

def KC.S6 (a : β) (z : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ ((z.gpr .s0 = 0 ↔ F.mv s0) ∧ z.gpr .a5 = F.mask s0 ∧
    z.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s0)) <<< 31 ∧ z.mem = v.mem) ∧ Keep tailRegs v z

def KC.S7 (a : β) (t : State) : Prop :=
  ∃ s0 v, F.C0 a s0 ∧ F.M2 s0 v ∧ ((t.gpr .t0 = 0 ↔ F.ev s0 ∧ F.mv s0) ∧
    t.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s0)) <<< 31 ∧ t.mem = v.mem) ∧ Keep tailRegs v t

def KC.S8 (a : β) (u : State) : Prop := ∃ s0, F.C0 a s0 ∧ KBase (F.B s0) (F.Z s0) s0 u

/-- What the function's own proofs give. -/
structure KC.Ok (oS na : Nat) (moves : List Instr) (T : List (Prog isa)) (mvRegs : List Reg) : Prop where
  hk : ∀ s, F.Pre s → KPre s (F.B s) (F.Z s) (F.K s) oS na
  hm : ∀ s, F.Pre s → ∀ u, Saved s (F.B s) u → WP isa (.block moves) u fun v => F.MV s v ∧ v.mem = u.mem ∧
    v.rd = u.rd ∧ v.wr = u.wr ∧ v.gpr .s11 = u.gpr .s11 ∧ v.gpr .a4 = off (F.E s) 0 ∧
    v.gpr .a5 = BitVec.ofNat 64 (F.L s) ∧ v.gpr .s1 = off (F.N s) 0 ∧ v.gpr .s2 = BitVec.ofNat 64 (F.K s)
  hL : ∀ s, F.Pre s → 1 ≤ F.L s ∧ F.L s ≤ 1024
  hE : ∀ s, F.Pre s → (⟨F.E s, F.L s⟩ : Region) ∈ s.rd ∧ (⟨F.E s, F.L s⟩ : Region).Disjoint ⟨F.B s, F.Z s⟩ ∧
    (F.E s).toNat + F.L s ≤ 2 ^ 64
  hN : ∀ s, F.Pre s → (⟨F.N s, F.K s⟩ : Region) ∈ s.rd ∧ (⟨F.N s, F.K s⟩ : Region).Disjoint ⟨F.B s, F.Z s⟩ ∧
    (F.N s).toNat + F.K s ≤ 2 ^ 64
  hv : ∀ s, F.Pre s → ∀ v t, F.MV s v → Keep tailRegs v t → KBase (F.B s) (F.Z s) s t →
    t.gpr .a4 = BitVec.ofNat 64 (sat (F.eN s)) <<< 31 → F.ev s → F.mv s →
    WP isa (seqs T) t fun u => KBase (F.B s) (F.Z s) s u
  hsame : ∀ s t, F.Pre s → F.Pre t → F.D s = F.D t → F.B s = F.B t ∧ F.E s = F.E t ∧ F.N s = F.N t ∧
    F.L s = F.L t ∧ F.K s = F.K t ∧ Spec.Rsa.bytesAt s.mem (F.E s) (F.L s) = Spec.Rsa.bytesAt t.mem (F.E t) (F.L t) ∧
    F.nB s = F.nB t ∧ ∀ r ∈ argRegs, s.gpr r = t.gpr r
  hmv : ∀ s t v w, F.Pre s → F.Pre t → F.D s = F.D t → F.MV s v → F.MV t w → ∀ r ∈ mvRegs, v.gpr r = w.gpr r
  hmr : ∀ r ∈ mvRegs, r ∉ tailRegs

theorem KC.M2.base {F : KC β} {s0 v t : State} (h : F.M2 s0 v) (k : Keep tailRegs v t) (hm : t.mem = v.mem) :
    KBase (F.B s0) (F.Z s0) s0 t := h.2.1.of_regs k hm

theorem KC.M2.bytesE {F : KC β} {oS na : Nat} {moves : List Instr} {T : List (Prog isa)} {mvRegs : List Reg} {s0 v : State} (H : F.Ok oS na moves T mvRegs) (h0 : F.Pre s0) (h : F.M2 s0 v) :
    Spec.Rsa.bytesAt v.mem (F.E s0) (F.L s0) = Spec.Rsa.bytesAt s0.mem (F.E s0) (F.L s0) :=
  bytes_frame h.2.1 (H.hE s0 h0).2.1 (H.hE s0 h0).2.2

theorem KC.M2.bytesN {F : KC β} {oS na : Nat} {moves : List Instr} {T : List (Prog isa)} {mvRegs : List Reg} {s0 v : State} (H : F.Ok oS na moves T mvRegs) (h0 : F.Pre s0) (h : F.M2 s0 v) :
    Spec.Rsa.bytesAt v.mem (F.N s0) (F.K s0) = F.nB s0 :=
  bytes_frame h.2.1 (H.hN s0 h0).2.1 (H.hN s0 h0).2.2

theorem argRegs_ne_t0 : ∀ r ∈ argRegs, r ∉ ([.t0] : List Reg) := by decide

theorem zero_of_eval {s : State} (h : isa.eval (.zero .t0) s = some true) : s.gpr .t0 = 0 := by
  rw [Steps.eval_zero] at h; simpa using h

/-- `KeyCheck.fn` is constant time, from the function's pieces. -/
theorem fn_rel {oS na : Nat} {moves : List Instr} {loads body : List (Prog isa)} {mvRegs : List Reg}
    (H : F.Ok oS na moves (([setup, .block eArr] : List (Prog isa)) ++ loads ++ body ++ ([.block ret] : List (Prog isa))) mvRegs) (hoS : 8 * oS < 2048)
    {hc1 hc2 hc3 : VG.Taint.Hint taint.T}
    (hS1 : (taint.check (Taint.ofRegs []) (.block [.addSp .t0 0, .load .d .t0 .t0 (8 * oS)]) hc1).isSome = true)
    (hS2 : (taint.check (Taint.ofRegs (.t0 :: argRegs)) (.block (save2 ++ moves)) hc2).isSome = true)
    (hT : (taint.check (Taint.ofRegs (.s11 :: mvRegs))
      (seqs (([setup, .block eArr] : List (Prog isa)) ++ loads ++ body ++ ([.block ret] : List (Prog isa)))) hc3).isSome = true) :
    RelCT isa (Two F.C0) (fn (8 * oS) moves loads body) fun _ _ => True := by
  obtain same : ∀ {a : β} {x y : State}, F.C0 a x → F.C0 a y → F.B x = F.B y ∧ F.E x = F.E y ∧ F.N x = F.N y ∧
      F.L x = F.L y ∧ F.K x = F.K y ∧
      Spec.Rsa.bytesAt x.mem (F.E x) (F.L x) = Spec.Rsa.bytesAt y.mem (F.E y) (F.L y) ∧
      F.nB x = F.nB y ∧ ∀ r ∈ argRegs, x.gpr r = y.gpr r :=
    fun hx hy => H.hsame _ _ hx.1 hy.1 (hx.2.trans hy.2.symm)
  obtain sameEv : ∀ {a : β} {x y : State}, F.C0 a x → F.C0 a y → (F.ev x ↔ F.ev y) := fun hx hy => by
    obtain ⟨-, -, -, -, -, he, -⟩ := same hx hy
    simp only [KC.ev, KC.eN, he]
  obtain sameMv : ∀ {a : β} {x y : State}, F.C0 a x → F.C0 a y → (F.mv x ↔ F.mv y) := fun hx hy => by
    obtain ⟨-, -, -, -, hk, -, hn, -⟩ := same hx hy
    simp only [KC.mv, hk, hn]
  obtain rdOf : ∀ {s0 v : State}, F.Pre s0 → KBase (F.B s0) (F.Z s0) s0 v → ∀ {P : Addr} {M : Nat},
      (⟨P, M⟩ : Region) ∈ s0.rd → P.toNat + M ≤ 2 ^ 64 → ∀ i < M, InRegions (v.rd ++ v.wr) (off P i) 1 :=
    fun _ bv _ _ hP wP i hi =>
      ⟨_, List.mem_append_left _ (by rw [bv.rd]; exact hP), Offset.contains_base _ (by omega_using [hi]) (by omega_using [wP, hi])⟩
  unfold fn
  rw [entry_eq, save_eq]
  refine RelCT.seq (R := Two F.S7) (RelCT.seq (R := Two F.S2) (RelCT.block_append
    (RelCT.seq (R := Two F.S1) ?_ ?_)) ?_) ?_
  · -- `save`'s first part.
    refine two_post (two_taint _ (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil) hS1) fun a s c0 => ?_
    obtain hp := H.hk s c0.1
    exact WP.mono (save1_ok s hoS (hp.arg_rd hp.hoS) (hp.arg_al hp.hoS)) fun t ⟨⟨t0, tm, tsp⟩, k⟩ =>
      ⟨s, c0, ⟨t0.trans hp.base, tm, tsp⟩, k⟩
  · -- `save`'s second part and the moves.
    refine two_post (two_taint _ ?_ hS2) fun a s ⟨s0, c0, ht⟩ => ?_
    · rintro a s₁ s₂ ⟨x, hx, ⟨tx, -, -⟩, kx⟩ ⟨y, hy, ⟨ty, -, -⟩, ky⟩ r hr
      obtain hs := same hx hy
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [tx, ty, hs.1]
      · rw [kx.gpr (argRegs_ne_t0 r hr), ky.gpr (argRegs_ne_t0 r hr), hs.2.2.2.2.2.2.2 r hr]
    obtain hp := H.hk s0 c0.1
    obtain hZ : 96 ≤ F.Z s0 := by have := hp.zk; omega_using [this]
    rw [WP.block_append_iff]
    refine WP.mono (save2_ok s0 (Scr.of_mem hp.wr hp.nowrap hp.al) hZ ht) fun u hu => ?_
    obtain bu := KBase.of_saved hu hZ
    exact WP.mono (H.hm s0 c0.1 u hu) fun v ⟨mv, vm, vrd, vwr, v11, v4, v5, v1, v2⟩ =>
      ⟨s0, c0, mv, ⟨vrd.trans bu.rd, vwr.trans bu.wr, fun x hx => by rw [vm]; exact bu.frame x hx,
        fun i hi => by rw [vm]; exact bu.hdr i hi, v11.trans bu.s11⟩, v4, v5, v1, v2⟩
  · -- The tail.
    unfold tail
    rw [show VG.Impl.Bignum.RISCV64.Precompute.check =
      .seq (.block VG.Impl.Bignum.RISCV64.Precompute.check1) VG.Impl.Bignum.RISCV64.Precompute.check2 from rfl]
    refine RelCT.seq (R := Two F.S3) ?_ (RelCT.seq (R := Two F.S4) ?_
      (RelCT.seq (R := Two F.S6) (RelCT.seq (R := Two F.S5) ?_ ?_) ?_))
    · -- `readE`.
      refine two_post (two_taint [.a4, .a5] ?_ (by taint_decide)) fun a v ⟨s0, c0, m⟩ => ?_
      · rintro a s₁ s₂ ⟨x, hx, mx⟩ ⟨y, hy, my⟩ r hr
        obtain hs := same hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [mx.2.2.1, my.2.2.1, hs.2.1]
        · rw [mx.2.2.2.1, my.2.2.2.1, hs.2.2.2.1]
      obtain hL := H.hL s0 c0.1
      obtain hE := H.hE s0 c0.1
      refine WP.mono (Pub.readE_ok m.2.2.1 m.2.2.2.1 hL.1 (by omega_using [hL]) (rdOf c0.1 m.2.1 hE.1 hE.2.2))
        fun u ⟨⟨u7, um⟩, ku⟩ => ⟨s0, v, c0, m, ⟨by rw [u7, m.bytesE H c0.1], um⟩, ku.mono (by decide)⟩
    · -- `e` checked, and the moves to `check`.
      refine two_post (two_taint [.s1, .s2] ?_ (by taint_decide)) fun a u ⟨s0, v, c0, m, ⟨u7, um⟩, ku⟩ => ?_
      · rintro a s₁ s₂ ⟨x, vx, hx, mx, -, kx⟩ ⟨y, vy, hy, my, -, ky⟩ r hr
        obtain hs := same hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [kx.gpr (by decide), ky.gpr (by decide), mx.2.2.2.2.1, my.2.2.2.2.1, hs.2.2.1]
        · rw [kx.gpr (by decide), ky.gpr (by decide), mx.2.2.2.2.2, my.2.2.2.2.2, hs.2.2.2.2.1]
      obtain hsat : sat (F.eN s0) ≤ 2 ^ 33 := by unfold sat; omega_using []
      refine WP.mono (tB_ok u7 hsat ((ku.gpr (by decide)).trans m.2.2.2.2.1) ((ku.gpr (by decide)).trans m.2.2.2.2.2))
        fun y ⟨⟨y5, y4, y7, y8, ym⟩, ky⟩ => ⟨s0, v, c0, m, ⟨y5, y4, y7, y8, ym.trans um⟩, (ku.trans ky).mono (by decide)⟩
    · -- `check`'s first part.
      refine two_post (two_taint [.s7, .s8] ?_ (by taint_decide)) fun a y ⟨s0, v, c0, m, ⟨y5, y4, y7, y8, ym⟩, ky⟩ => ?_
      · rintro a s₁ s₂ ⟨x, vx, hx, mx, ⟨-, -, x7, x8, -⟩, -⟩ ⟨y, vy, hy, my, ⟨-, -, z7, z8, -⟩, -⟩ r hr
        obtain hs := same hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [x7, z7, hs.2.2.1]
        · rw [x8, z8, hs.2.2.2.2.1]
      obtain hp := H.hk s0 c0.1
      obtain hN := H.hN s0 c0.1
      have hk := hp.k64
      obtain hlen : (F.nB s0).length = F.K s0 := by simp [KC.nB, Spec.Rsa.bytesAt]
      obtain hrd : ∀ i < F.K s0, InRegions (y.rd ++ y.wr) (off (F.N s0) i) 1 := fun i hi => by
        rw [ky.2.1, ky.2.2]; exact rdOf c0.1 m.2.1 hN.1 hN.2.2 i hi
      obtain eb := m.bytesN H c0.1
      refine WP.mono (check1_ok (nb := F.nB s0) y7 y8 hk hlen hrd fun i hi => by
          rw [← Pre.getD_of_lt (by omega_using [hlen, hi]), ym, ← eb]
          simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi])
        fun z ⟨⟨z0, z4, zm⟩, kz⟩ => ⟨s0, v, c0, m, ⟨by rw [z0, Pre.getD_of_lt (by omega_using [hk, hlen])],
          by rw [z4, Pre.getD_of_lt (by omega_using [hk, hlen])], by rw [kz.gpr (by decide), y5], by rw [kz.gpr (by decide), y4],
          by rw [kz.gpr (by decide), y8], zm.trans ym⟩, (ky.trans kz).mono (by decide)⟩
    · -- `check`'s second part.
      refine two_post (two_taint [.t4, .s8] ?_ (by taint_decide))
        fun a z ⟨s0, v, c0, m, ⟨z0, z4, z5, z4', z8, zm⟩, kz⟩ => ?_
      · rintro a s₁ s₂ ⟨x, vx, hx, mx, ⟨-, x4, -, -, x8, -⟩, -⟩ ⟨y, vy, hy, my, ⟨-, y4, -, -, y8, -⟩, -⟩ r hr
        obtain hs := same hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [x4, y4, hs.2.2.2.2.2.2.1]
        · rw [x8, y8, hs.2.2.2.2.1]
      obtain hp := H.hk s0 c0.1
      have hk := hp.k64
      have hk' := hp.k1024
      obtain hlen : (F.nB s0).length = F.K s0 := by simp [KC.nB, Spec.Rsa.bytesAt]
      refine WP.mono (check2_ok (nb := F.nB s0) z8 hk hk' hlen (by rw [z0, Pre.getD_of_lt (by omega_using [hk, hlen])])
        (by rw [z4, Pre.getD_of_lt (by omega_using [hk, hlen])])) fun x ⟨x0, xm, kx⟩ =>
          ⟨s0, v, c0, m, ⟨x0, by rw [kx.gpr (by decide), z5], by rw [kx.gpr (by decide), z4'], xm.trans zm⟩,
            (kz.trans kx).mono (by decide)⟩
    · -- The tail's last block.
      refine two_post (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide))
        fun a z ⟨s0, v, c0, m, ⟨z0, z5, z4, zm⟩, kz⟩ => ?_
      refine WP.mono (tE_ok z) fun t ⟨⟨t0, tm⟩, kt⟩ => ⟨s0, v, c0, m, ⟨?_, by rw [kt.gpr (by decide), z4],
        tm.trans zm⟩, (kz.trans kt).mono (by decide)⟩
      rw [t0, z5, t0_iff _ _ z0, exponentValid_sat]
  · -- The branch and the exit.
    refine RelCT.seq (R := Two F.S8) (RelCT.ite ?_ ?_ ?_) ?_
    · rintro s₁ s₂ ⟨a, ⟨x, vx, hx, mx, ⟨x0, -, -⟩, -⟩, ⟨y, vy, hy, my, ⟨y0, -, -⟩, -⟩, -⟩
      rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, x0, y0, sameEv hx hy, sameMv hx hy]
    · -- The valid branch.
      refine RelCT.mono (two_post (Φ := fun a s => F.S7 a s ∧ s.gpr .t0 = 0) (two_taint _ ?_ hT) ?_) ?_ fun _ _ h => h
      · rintro a s₁ s₂ ⟨⟨x, vx, hx, mx, ⟨-, -, xm⟩, kx⟩, -⟩ ⟨⟨y, vy, hy, my, ⟨-, -, ym⟩, ky⟩, -⟩ r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [(mx.base kx xm).s11, (my.base ky ym).s11, (same hx hy).1]
        · rw [kx.gpr (H.hmr r hr), ky.gpr (H.hmr r hr)]
          exact H.hmv _ _ _ _ hx.1 hy.1 (hx.2.trans hy.2.symm) mx.1 my.1 r hr
      · rintro a t ⟨⟨s0, v, c0, m, ⟨t0, t4, tm⟩, kt⟩, hz⟩
        obtain ⟨ev, mv⟩ := t0.mp hz
        exact WP.mono (H.hv s0 c0.1 v t m.1 kt (m.base kt tm) t4 ev mv) fun u hu => ⟨s0, c0, hu⟩
      · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩
        obtain z1 := zero_of_eval hc
        obtain ⟨x, vx, hx, mx, ⟨x0, x4, xm⟩, kx⟩ := h₁
        obtain ⟨y, vy, hy, my, ⟨y0, y4, ym⟩, ky⟩ := h₂
        obtain ⟨ev, mv⟩ := x0.mp z1
        exact ⟨a, ⟨⟨x, vx, hx, mx, ⟨x0, x4, xm⟩, kx⟩, z1⟩,
          ⟨⟨y, vy, hy, my, ⟨y0, y4, ym⟩, ky⟩,
            y0.mpr ⟨(sameEv hx hy).mp ev, (sameMv hx hy).mp mv⟩⟩, hsp⟩
    · -- The other branch.
      refine RelCT.mono (two_post (Φ := F.S7) (two_taint [] (fun _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
        (by taint_decide)) ?_) (fun _ _ h => h.1) fun _ _ h => h
      rintro a t ⟨s0, v, c0, m, ⟨-, -, tm⟩, kt⟩
      obtain bt := m.base kt tm
      refine WP.mono (WP.keep [.a0] (Q := fun u => u.mem = t.mem) (by
        obtain e : exec (.li .a0 0) t = some (t.write .a0 (BitVec.ofNat 64 0)) := by
          rw [exec_li (by decide)]; rfl
        brun [ret0, e]) (by rfl) (by rfl)) fun u ⟨um, ku⟩ => ⟨s0, c0, bt.of_regs ku um⟩
    · -- `restore`.
      refine two_taint [.s11] ?_ (by taint_decide)
      rintro a s₁ s₂ ⟨x, hx, bx⟩ ⟨y, hy, by'⟩ r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [bx.s11, by'.s11, (same hx hy).1]

end VG.Proof.Rsa.RISCV64.KeyCheck
