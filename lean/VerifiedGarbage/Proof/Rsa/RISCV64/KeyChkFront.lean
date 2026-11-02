module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkBase
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
open VG.Impl.Rsa.RISCV64.Keys (seqs saved mov load setW zeroArrays)
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
    (hjs : ∀ j ∈ js, arr w j + S w ≤ Z) (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ hdr) (hZ : hdr ≤ Z)
    {rs : List Reg} (kr : Keep rs s t) (hr : .s11 ∉ rs := by decide) : KBase B Z s0 t := by
  refine ⟨kr.2.1.trans h.rd, kr.2.2.trans h.wr, fun x hx => ?_, fun i hi => ?_, (kr.gpr hr).trans h.s11⟩
  · rw [← h.frame x hx]
    exact k.out (Z := Z) hjs (fun d hd => by have := hds d hd; omega) hx
  · rw [← h.hdr i hi]
    have e := k.words (d := 8 * i) (k := 1) (fun j _ => by have := hdr_le_arr w j; simp only [hdr_eq] at this; omega)
      (fun d hd => by have := hds d hd; omega) (by omega)
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at e
    exact BitVec.eq_of_toNat_eq e

theorem past_of_disjoint {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr}
    (ha : r.Contains a 1) : Z ≤ ofs B a := by
  have := hd a ha
  simp only [Region.Contains] at this
  simp only [ofs]; omega

/-! ## The entry, after the arguments are moved -/

/-- What `e` and `n` are read and checked into. -/
def tail : Prog isa :=
  .seq PublicChecked.readE
    (.seq (.block (PublicChecked.checkE ++ [mov .a5 .s9, mov .a4 .s7, mov .s7 .s1, mov .s8 .s2]))
      (.seq Precompute.check (.block [.addi .t0 .a5 1, .logic .or .t0 .t0 .s0])))

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
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 + BitVec.ofNat 64 1 = 0 by decide, BitVec.zero_or]

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
  refine WP.seq (WP.mono (Pub.readE_ok h4 h5 hL (by omega) hrdE) fun u ⟨⟨u7, um⟩, ku⟩ => ?_)
  have hsat : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem E L)) ≤ 2 ^ 33 := by unfold sat; omega
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
  · rw [t0, z5, mask_add_one, Pub.exponentValid_sat, z0]
  · rw [kt.gpr (by decide), kz.gpr (by decide), y4, x7]
  · exact ((((ku.trans kx).trans ky).trans kz).trans kt).mono (by decide)

/-! ## The set-up -/

/-- `w = ⌈K / 8⌉`. -/
abbrev kw (K : Nat) : Nat := (K + 7) / 8

theorem KPre.ws {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) :
    arr (kw K) nArr ≤ Z ∧ 8 ≤ kw K ∧ kw K ≤ 128 ∧ K ≤ 8 * kw K := by
  have := h.zk; have := h.k64; have := h.k1024
  simp only [arr, S, nArr, hdr_eq, kw]
  omega

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
  refine WP.mono (setW_ok h2 (by have := hp.k1024; omega)) fun u ⟨⟨u9, u10, um⟩, ku⟩ => ?_
  have hu : Ws u B Z (kw K) nArr :=
    ⟨hs.congr ku.2.2, fits, by omega, by omega, u9, u10, (ku.gpr (by decide)).trans h.s11⟩
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
  · have := wordsVal_zero_part (a := 0) (c := kw K) (z j (List.mem_range.mp hj)) (by omega)
    simpa using this
  · have := wordsVal_zero_part (a := kw K) (c := 1) (z j hj) (by omega)
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at this
    exact BitVec.eq_of_toNat_eq (by simpa using this)

theorem bytes_frame {B : Addr} {Z : Nat} {s0 t : State} (h : KBase B Z s0 t) {P : Addr} {L : Nat}
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨B, Z⟩) (hPw : P.toNat + L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem P L = Spec.Rsa.bytesAt s0.mem P L := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun c hc => h.frame _ (past_of_disjoint hd ?_)
  have := List.mem_range.mp hc
  exact Offset.contains_base _ (by omega) (by omega)

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
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (load_ok h hj (by decide) hl1 hP hL hL1 hLw
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [hI.base.rd]; exact hrd), hc i hi⟩)
    (fun i hi x hx e => by have := past_of_disjoint hd (hc i hi); rw [e] at this; omega)
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
    · subst e; rw [o.word (by omega) (by omega)]; exact hI.top _ hi
    · have := arr_disj (w := kw K) e
      rw [o.word (by omega) (by omega)]; exact hI.top _ hi

theorem shl_shr31 {E : Nat} (hE : E < 2 ^ 33) : (BitVec.ofNat 64 E <<< 31) >>> 31 = BitVec.ofNat 64 E := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show E * 2 ^ 31 < 2 ^ 64 by omega), Nat.mul_div_cancel _ (by decide)]

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
    brun [h4, shl_shr31 hE, h.scr.st (d := arr (kw K) aE) (n := 8) (by omega),
      h.scr.al8 (d := arr (kw K) aE) (by omega) (arr_al _ _)]
  refine WP.mono hm fun u ⟨um, ku⟩ => ?_
  have lw := low_write (m := t.mem) (B := B) h.wpos fit0 (BitVec.ofNat 64 E)
  have o := writeW_outside t.mem B (d := arr (kw K) aE) (BitVec.ofNat 64 E) (by omega)
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
      omega
    · rw [upd_ne _ _ e, k.num (by simpa using Ne.symm e) (by simp) (fit _ (List.mem_range.mp hj))]
      exact hI.arrs.get hj
  · by_cases e : j = aE
    · subst e
      have := h.wpos
      rw [o.word (by omega) (by omega)]
      exact hI.top _ hj
    · rw [k.word (by omega) (by simpa using Ne.symm e) (by simp) (fit _ hj)]
      exact hI.top _ hj

end VG.Proof.Rsa.RISCV64.KeyCheck
