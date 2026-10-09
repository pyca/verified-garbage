import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import VerifiedGarbage.Proof.Bignum.CrtExp

-- Reduce vector updates before comparing unchanged fields of whole states.
attribute [local instance_reducible] VG.X86_64.State.setXmm


/-!
# RSA with the CRT on x86-64: gathering a table entry with SSE2

A pass of the table selection (`Crt.gatherPass`, `Impl/Rsa/X86_64/Crt.lean`)
holds eight entries' bases in registers and their masks in `xmm8`–`xmm15`,
and replaces each pair of words of `[rbx]` by
`OR_j (T_j & mask_j) | ([rbx] & xmm7)` (`gPair_ok`), over the words below
`2 ⌈w / 2⌉`, one more than `w` when `w` is odd (`gLoop_ok`). With the masks
of `8 p + j = v`, `gacc_eq` says what that is: entry `v` if it is among the
eight, and 0 otherwise.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.X86_64.RegUpd (xmm_setXmm_self xmm_setXmm_of_ne gpr_setXmm mem_setXmm rd_setXmm wr_setXmm)

/-! ## The arithmetic -/

theorem gath_and_mask (x : BitVec 64) (c : Bool) : x &&& mask c = if c then x else 0 := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes]; rfl

/-- `OR_(j ≤ n) (e j & mask (k + j = v))`, as a pass accumulates it. -/
def gacc (e : Nat → BitVec 64) (k v : Nat) : Nat → BitVec 64
  | 0 => e 0 &&& mask (decide (k + 0 = v))
  | n + 1 => gacc e k v n ||| (e (n + 1) &&& mask (decide (k + (n + 1) = v)))

/-- The pass's value: `e (v - k)` if `v` is among its entries, 0 otherwise. -/
theorem gacc_eq (e : Nat → BitVec 64) (k v n : Nat) :
    gacc e k v n = if k ≤ v ∧ v ≤ k + n then e (v - k) else 0 := by
  induction n with
  | zero =>
    simp only [gacc, gath_and_mask]
    by_cases h : k + 0 = v
    · subst h; simp
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, show ¬ (k ≤ v ∧ v ≤ k + 0) by omega]
  | succ n ih =>
    simp only [gacc, ih, gath_and_mask]
    by_cases h : k ≤ v ∧ v ≤ k + n
    · simp [h, show ¬ k + (n + 1) = v by omega, show k ≤ v ∧ v ≤ k + (n + 1) by omega]
    · by_cases h' : k + (n + 1) = v
      · subst h'
        simp [show ¬ (k + (n + 1) ≤ k + n) by omega]
      · simp [h', show ¬ (k ≤ v ∧ v ≤ k + (n + 1)) by omega, show ¬ (k ≤ v ∧ v ≤ k + n) by omega]

/-- Quadword `q` of a 128-bit value. -/
abbrev q128 (v : BitVec 128) (q : Nat) : BitVec 64 := qword v q

theorem q128_low (x : BitVec 64) : q128 ((0 : BitVec 64) ++ x) 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [q128, qword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add]
  rw [BitVec.getLsbD_append]; simp [hi]

theorem q128_pair (x : BitVec 64) {q : Nat} (hq : q < 2) : q128 (x ++ x) q = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [q128, qword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]
  rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl
  · simp [hi]
  · simp [show ¬ 64 * 1 + i < 64 by omega]

theorem q128_xor (a b : BitVec 128) (q : Nat) : q128 (a ^^^ b) q = q128 a q ^^^ q128 b q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [q128, qword, hi]

theorem q128_and (a b : BitVec 128) (q : Nat) : q128 (a &&& b) q = q128 a q &&& q128 b q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [q128, qword, hi]

/-- The mask in both quadwords: `punpcklqdq` of `movq`. -/
theorem q128_dup (x : BitVec 64) {q : Nat} (hq : q < 2) :
    q128 (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ x) ((0 : BitVec 64) ++ x)) q = x := by
  simp only [XBinOp.eval]
  rw [show qword ((0 : BitVec 64) ++ x) 0 = x from q128_low x]
  exact q128_pair x hq

/-- Quadword `q` of a 16-byte read. -/
theorem q128_read (m : Mem) (a : Addr) {q : Nat} (hq : q < 2) :
    q128 (m.readW a 128) q = m.readW (a + BitVec.ofNat 64 (8 * q)) 64 := by
  have e := readW_extract m a (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * (8 * q) = 64 * q by omega, show 8 * 8 = 64 by rfl] at e
  exact e

/-- A 16-byte write, read back a quadword at a time. -/
theorem read_write128 (m : Mem) (a : Addr) (v : BitVec 128) {q : Nat} (hq : q < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * q)) 64 = q128 v q := by
  have e := readW_writeW_inside m a v (k := 8 * q) (n := 8) (by omega) (by decide)
  rw [show 8 * (8 * q) = 64 * q by omega, show 8 * 8 = 64 by rfl] at e
  exact e

theorem q128_or (a b : BitVec 128) (q : Nat) : q128 (a ||| b) q = q128 a q ||| q128 b q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [q128, qword, hi]

theorem off_add_eq (B : Addr) (a d : Nat) : off B a + BitVec.ofNat 64 d = off B (a + d) := off_off B a d

theorem inRegions16 {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) {d : Nat} (hd : d + 16 ≤ Z) :
    InRegions (s.rd ++ s.wr) (off B d) 16 ∧ InRegions s.wr (off B d) 16 := by
  obtain ⟨r, hr, hc⟩ := hs.region hd (by decide)
  exact ⟨⟨r, List.mem_append_right _ hr, hc⟩, ⟨r, hr, hc⟩⟩

/-- A 16-byte write changes only its bytes. -/
theorem writeW128_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 2 ^ 64) :
    Outside base d 16 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply (n := 16)
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## A pair of words -/

/-- `xmm0 |= [b + 8 r14] & x`: quadword `q` of `xmm0` ORed with word `2 i + q`
of the array at `e` under quadword `q` of `x`. -/
theorem gOr_ok {s : State} {B : Addr} {Z e i : Nat} (hs : Scr s B Z) {b : Reg} {x : XReg}
    (hx1 : x ≠ .xmm1) (hb : s.gpr b = off B e)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * i)) (he : e + 16 * i + 16 ≤ Z) :
    WP isa (.block (Crt.gatherOr b x)) s fun t =>
      (∀ q < 2, q128 (t.xmm .xmm0) q =
        q128 (s.xmm .xmm0) q ||| (word s.mem B (e + 16 * i + 8 * q) &&& q128 (s.xmm x) q)) ∧
      (∀ y, y ≠ .xmm0 → y ≠ .xmm1 → t.xmm y = s.xmm y) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have hn := hs.nowrap
  obtain ⟨iA, -⟩ := inRegions16 hs (d := e + 16 * i) he
  have eA : s.ea (ix b .r14) = off B (e + 16 * i) := by rw [ea_ix0 s hb h14]; congr 1; omega
  unfold Crt.gatherOr
  rw [WP.block_cons_iff]
  refine ⟨s.setXmm .xmm1 (s.mem.readW (off B (e + 16 * i)) 128),
    by simp only [exec, eA, State.load128, iA, ite_true, Option.map_some], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  simp only [XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne _ _ hx1, xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm0 = .xmm1 by decide),
    gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, XBinOp.eval, and_true]
  refine ⟨fun q hq => ?_, fun y h0 h1 => ?_⟩
  · rw [q128_or, q128_and, q128_read _ _ hq, off_add_eq]
  · rw [xmm_setXmm_of_ne _ _ h0, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h1]

/-- `xmm0 := [rcx + 8 r14] & xmm8`. -/
theorem gFirst_ok {s : State} {B : Addr} {Z e i : Nat} (hs : Scr s B Z) (hb : s.gpr .rcx = off B e)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * i)) (he : e + 16 * i + 16 ≤ Z) :
    WP isa (.block Crt.gatherFirst) s fun t =>
      (∀ q < 2, q128 (t.xmm .xmm0) q = word s.mem B (e + 16 * i + 8 * q) &&& q128 (s.xmm .xmm8) q) ∧
      (∀ y, y ≠ .xmm0 → y ≠ .xmm1 → t.xmm y = s.xmm y) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have hn := hs.nowrap
  obtain ⟨iA, -⟩ := inRegions16 hs (d := e + 16 * i) he
  have eA : s.ea (ix .rcx .r14) = off B (e + 16 * i) := by rw [ea_ix0 s hb h14]; congr 1; omega
  unfold Crt.gatherFirst
  rw [WP.block_cons_iff]
  refine ⟨s.setXmm .xmm0 (s.mem.readW (off B (e + 16 * i)) 128),
    by simp only [exec, eA, State.load128, iA, ite_true, Option.map_some], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  simp only [XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm8 = .xmm0 by decide),
    gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, XBinOp.eval, and_true]
  refine ⟨fun q hq => ?_, fun y h0 _ => ?_⟩
  · rw [q128_and, q128_read _ _ hq, off_add_eq]
  · rw [xmm_setXmm_of_ne _ _ h0, xmm_setXmm_of_ne _ _ h0]

/-- The pair's store, and the next pair: `ZF` after the last of `n`. -/
theorem gStore_ok {s : State} {B : Addr} {Z e i n : Nat} (hs : Scr s B Z) (hb : s.gpr .rbx = off B e)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * i)) (h13 : s.gpr .r13 = BitVec.ofNat 64 (2 * n)) (hin : i < n)
    (hn : 2 * n < 2 ^ 64) (he : e + 16 * i + 16 ≤ Z) :
    WP isa (.block Crt.gatherStore) s fun t =>
      t.mem = s.mem.writeW (off B (e + 16 * i)) (s.xmm .xmm0) ∧ t.gpr .r14 = BitVec.ofNat 64 (2 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = n)) ∧ (∀ r, r ≠ .r14 → t.gpr r = s.gpr r) ∧ t.xmm = s.xmm ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hn' := hs.nowrap
  obtain ⟨-, sO⟩ := inRegions16 hs (d := e + 16 * i) he
  have eO : s.ea (ix .rbx .r14) = off B (e + 16 * i) := by rw [ea_ix0 s hb h14]; congr 1; omega
  let s₁ : State := { s with mem := s.mem.writeW (off B (e + 16 * i)) (s.xmm .xmm0) }
  unfold Crt.gatherStore
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [exec, eO, State.store128, sO, ite_true]; rfl, ?_⟩
  have hadd : BitVec.ofNat 64 (2 * i) + 2 = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, BitVec.ofNat_add]; rfl
  have hcmp : (BitVec.ofNat 64 (2 * (i + 1)) - BitVec.ofNat 64 (2 * n) == 0) = decide (i + 1 = n) := by
    rw [ofNat_sub_beq (by omega) hn]; exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 (2 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = n)) ∧ t.mem = s₁.mem ∧ t.xmm = s₁.xmm)
    (by xrun [show s₁.gpr = s.gpr from rfl, h14, h13, hadd, hcmp]; rfl) rfl)
    fun t ⟨⟨h14', hz, hm, hx⟩, k⟩ => ⟨hm, h14', hz, fun r hr => k.1 r (by simpa using hr), hx, k.2.1, k.2.2⟩



/-! ## A pass's registers -/

/-- The bases of a pass's eight entries. -/
def gReg : Nat → Reg
  | 0 => .rcx | 1 => .rdx | 2 => .rsi | 3 => .rbp | 4 => .r8 | 5 => .r9 | 6 => .r10 | _ => .rax

/-- Their masks. -/
def gX : Nat → XReg
  | 0 => .xmm8 | 1 => .xmm9 | 2 => .xmm10 | 3 => .xmm11 | 4 => .xmm12 | 5 => .xmm13 | 6 => .xmm14 | _ => .xmm15

theorem gReg_ne : ∀ k < 8, gReg k ≠ .r14 := by decide

theorem gX_ne : ∀ k < 8, gX k ≠ .xmm0 ∧ gX k ≠ .xmm1 ∧ gX k ≠ .xmm7 := by decide

/-- The registers of pass `p` over the entries from `8 p` (entry `j` is the
array `8 + j`), to select entry `v`. -/
structure GRegs (B : Addr) (wx p v : Nat) (s : State) : Prop where
  base : ∀ k < 8, s.gpr (gReg k) = off B (slot wx (8 + 8 * p + k))
  bx : s.gpr .rbx = off B (slot wx Crt.aT)
  r13 : s.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2))
  msk : ∀ k < 8, ∀ q < 2, q128 (s.xmm (gX k)) q = mask (decide (8 * p + k = v))
  keep : ∀ q < 2, q128 (s.xmm .xmm7) q = mask (decide (p = 1))

theorem GRegs.congr {B : Addr} {wx p v : Nat} {s t : State} (h : GRegs B wx p v s)
    (hg : ∀ r, r ≠ .r14 → t.gpr r = s.gpr r) (hx : ∀ y, y ≠ .xmm0 → y ≠ .xmm1 → t.xmm y = s.xmm y) :
    GRegs B wx p v t :=
  ⟨fun k hk => (hg _ (gReg_ne k hk)).trans (h.base k hk), (hg _ (by decide)).trans h.bx,
    (hg _ (by decide)).trans h.r13,
    fun k hk q hq => by rw [hx _ (gX_ne k hk).1 (gX_ne k hk).2.1]; exact h.msk k hk q hq,
    fun q hq => by rw [hx _ (by decide) (by decide)]; exact h.keep q hq⟩

/-- Pair `i` of an entry is within the table. -/
theorem gEnt_le (wx : Nat) {j i : Nat} (hj : j < 16) (hi : i < (wx + 1) / 2) :
    slot wx (8 + j) + 16 * i + 16 ≤ slot wx 8 + tabBytes wx := by
  have := ent_le wx hj; omega

/-- Pair `i` of `[aT]` is within its array. -/
theorem gT_le (wx : Nat) {i : Nat} (hi : i < (wx + 1) / 2) :
    slot wx Crt.aT + 16 * i + 16 ≤ slot wx 8 + tabBytes wx := by
  have := slot_succ wx Crt.aT
  have := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  omega

/-- After the entries `8 p` to `8 p + n` of pair `i`, from `s`. -/
structure GathAccI (s : State) (B : Addr) (wx p v i n : Nat) (t : State) : Prop where
  acc : ∀ q < 2, q128 (t.xmm .xmm0) q = gacc (fun j => word s.mem B (slot wx (8 + 8 * p + j) + 16 * i + 8 * q)) (8 * p) v n
  xmm : ∀ y, y ≠ .xmm0 → y ≠ .xmm1 → t.xmm y = s.xmm y
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem gAcc0 {s : State} {B : Addr} {wx p v i : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx)) (hG : GRegs B wx p v s)
    (hp : p < 2) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * i)) (hi : i < (wx + 1) / 2) :
    WP isa (.block Crt.gatherFirst) s (GathAccI s B wx p v i 0) := by
  have hb := hG.base 0 (by decide)
  rw [Nat.add_zero] at hb
  refine WP.mono (gFirst_ok hs hb h14 (gEnt_le wx (j := 8 * p) (by omega) hi)) fun t ⟨hx0, hx, hg, hm, hrd, hwr⟩ =>
    ⟨fun q hq => ?_, hx, hg, hm, hrd, hwr⟩
  rw [hx0 q hq, show s.xmm .xmm8 = s.xmm (gX 0) from rfl, hG.msk 0 (by decide) q hq]
  rfl

theorem gAcc_step {s t : State} {B : Addr} {wx p v i n : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx))
    (hG : GRegs B wx p v s) (hp : p < 2) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * i)) (hi : i < (wx + 1) / 2)
    (hn : n < 7) (hA : GathAccI s B wx p v i n t) :
    WP isa (.block (Crt.gatherOr (gReg (n + 1)) (gX (n + 1)))) t (GathAccI s B wx p v i (n + 1)) := by
  have hb : t.gpr (gReg (n + 1)) = off B (slot wx (8 + 8 * p + (n + 1))) := by
    rw [hA.gpr]; exact hG.base _ (by omega)
  have hnx := gX_ne (n + 1) (by omega)
  refine WP.mono (gOr_ok (hs.congr hA.wr) hnx.2.1 (Nat.add_assoc 8 (8 * p) (n + 1) ▸ hb) (by rw [hA.gpr]; exact h14)
      (gEnt_le wx (j := 8 * p + (n + 1)) (by omega) hi))
    fun t' ⟨hx0, hx, hg, hm, hrd, hwr⟩ => ⟨fun q hq => ?_, fun y h0 h1 => (hx y h0 h1).trans (hA.xmm y h0 h1),
      hg.trans hA.gpr, hm.trans hA.mem, hrd.trans hA.rd, hwr.trans hA.wr⟩
  rw [hx0 q hq, hA.acc q hq, hA.xmm _ hnx.1 hnx.2.1, hG.msk _ (by omega) q hq, hA.mem, ← Nat.add_assoc]
  rfl

/-- Pair `i` of a pass: `[aT] := ([aT] & keep) | OR_j (T_(8p+j) & mask_j)`. -/
theorem gPair_ok {s : State} {B : Addr} {wx p v i : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx))
    (hG : GRegs B wx p v s) (hp : p < 2) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * i)) (hi : i < (wx + 1) / 2)
    (hw' : wx < 2 ^ 30) :
    WP isa (seqs Crt.gatherBody) s fun t =>
      (∃ V, t.mem = s.mem.writeW (off B (slot wx Crt.aT + 16 * i)) V ∧ ∀ q < 2, q128 V q =
        gacc (fun j => word s.mem B (slot wx (8 + 8 * p + j) + 16 * i + 8 * q)) (8 * p) v 7 |||
          (word s.mem B (slot wx Crt.aT + 16 * i + 8 * q) &&& mask (decide (p = 1)))) ∧
      t.gpr .r14 = BitVec.ofNat 64 (2 * (i + 1)) ∧ t.zf = some (decide (i + 1 = (wx + 1) / 2)) ∧
      (∀ r, r ≠ .r14 → t.gpr r = s.gpr r) ∧ (∀ y, y ≠ .xmm0 → y ≠ .xmm1 → t.xmm y = s.xmm y) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  simp only [Crt.gatherBody, seqs]
  refine WP.seq (WP.mono (gAcc0 hs hG hp h14 hi) fun t₀ a₀ => ?_)
  refine WP.seq (WP.mono (gAcc_step (n := 0) hs hG hp h14 hi (by decide) a₀) fun t₁ a₁ => ?_)
  refine WP.seq (WP.mono (gAcc_step (n := 1) hs hG hp h14 hi (by decide) a₁) fun t₂ a₂ => ?_)
  refine WP.seq (WP.mono (gAcc_step (n := 2) hs hG hp h14 hi (by decide) a₂) fun t₃ a₃ => ?_)
  refine WP.seq (WP.mono (gAcc_step (n := 3) hs hG hp h14 hi (by decide) a₃) fun t₄ a₄ => ?_)
  refine WP.seq (WP.mono (gAcc_step (n := 4) hs hG hp h14 hi (by decide) a₄) fun t₅ a₅ => ?_)
  refine WP.seq (WP.mono (gAcc_step (n := 5) hs hG hp h14 hi (by decide) a₅) fun t₆ a₆ => ?_)
  refine WP.seq (WP.mono (gAcc_step (n := 6) hs hG hp h14 hi (by decide) a₆) fun t₇ a₇ => ?_)
  have hT := gT_le wx hi
  refine WP.seq (WP.mono (gOr_ok (hs.congr a₇.wr) (x := .xmm7) (by decide) (by rw [a₇.gpr]; exact hG.bx)
    (by rw [a₇.gpr]; exact h14) hT) fun t₈ ⟨hx0, hx, hg, hm, hrd, hwr⟩ => ?_)
  have hn := hs.nowrap
  refine WP.mono (gStore_ok (hs.congr (hwr.trans a₇.wr)) (by rw [hg, a₇.gpr]; exact hG.bx)
    (by rw [hg, a₇.gpr]; exact h14) (by rw [hg, a₇.gpr]; exact hG.r13) hi (by omega) hT)
    fun t ⟨hm', h14', hz, hg', hx', hrd', hwr'⟩ => ⟨⟨t₈.xmm .xmm0, by rw [hm', hm, a₇.mem], fun q hq => ?_⟩, h14', hz,
      fun r hr => by rw [hg' r hr, hg, a₇.gpr], fun y h0 h1 => by rw [hx', hx y h0 h1, a₇.xmm y h0 h1],
      by rw [hrd', hrd, a₇.rd], by rw [hwr', hwr, a₇.wr]⟩
  rw [hx0 q hq, a₇.acc q hq, a₇.xmm _ (by decide) (by decide), hG.keep q hq, a₇.mem]

theorem gacc_congr {e e' : Nat → BitVec 64} {k v n : Nat} (h : ∀ j ≤ n, e j = e' j) : gacc e k v n = gacc e' k v n := by
  induction n with
  | zero => simp only [gacc, h 0 (Nat.le_refl _)]
  | succ n ih => simp only [gacc, ih fun j hj => h j (by omega), h (n + 1) (Nat.le_refl _)]

/-! ## A pass -/

/-- Word `k` of `[aT]` after pass `p`, from memory `m`. -/
def gval (m : Mem) (B : Addr) (wx p v k : Nat) : BitVec 64 :=
  gacc (fun j => word m B (slot wx (8 + 8 * p + j) + 8 * k)) (8 * p) v 7 |||
    (word m B (slot wx Crt.aT + 8 * k) &&& mask (decide (p = 1)))

/-- After `i` pairs of a pass from `s`. -/
structure GathInv (s : State) (B : Addr) (wx p v : Nat) (i : Nat) (t : State) : Prop where
  r14 : t.gpr .r14 = BitVec.ofNat 64 (2 * i)
  gpr : ∀ r, r ≠ .r14 → t.gpr r = s.gpr r
  xmm : ∀ y, y ≠ .xmm0 → y ≠ .xmm1 → t.xmm y = s.xmm y
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : Outside B (slot wx Crt.aT) (16 * ((wx + 1) / 2)) s.mem t.mem
  val : ∀ k < 2 * ((wx + 1) / 2), word t.mem B (slot wx Crt.aT + 8 * k) =
    if k < 2 * i then gval s.mem B wx p v k else word s.mem B (slot wx Crt.aT + 8 * k)

/-- A pass's loop: every pair of `[aT]` below `2 ⌈w / 2⌉`. -/
theorem gLoop_ok {s : State} {B : Addr} {wx p v : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx))
    (hG : GRegs B wx p v s) (hp : p < 2) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * 0)) (hw : 1 ≤ wx)
    (hw' : wx < 2 ^ 30) :
    WP isa (.loop (seqs Crt.gatherBody) .ne) s (GathInv s B wx p v ((wx + 1) / 2)) := by
  have hn := hs.nowrap
  have hTa := slot_succ wx Crt.aT
  have hT8 := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  refine wp_upto (a := 0) (N := (wx + 1) / 2) (by omega) (GathInv s B wx p v) (fun j _ hj t hI => ?_) (fun t h => h)
    ⟨h14, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, fun k _ => by simp⟩
  refine WP.mono (gPair_ok (hs.congr hI.wr) (hG.congr hI.gpr hI.xmm) hp hI.r14 hj hw')
    fun t' ⟨⟨V, hm, hV⟩, h14', hz, hg, hx, hrd, hwr⟩ => ⟨hz, ?_⟩
  have o' : Outside B (slot wx Crt.aT + 16 * j) 16 t.mem t'.mem := by
    rw [hm]; exact writeW128_outside _ _ _ (by omega)
  refine ⟨h14', fun r hr => (hg r hr).trans (hI.gpr r hr), fun y h0 h1 => (hx y h0 h1).trans (hI.xmm y h0 h1),
    hrd.trans hI.rd, hwr.trans hI.wr, hI.out.trans (o'.mono (by omega) (by omega)), fun k hk => ?_⟩
  by_cases hlo : k < 2 * j
  · rw [o'.word (by omega) (by omega), hI.val k hk]
    simp only [hlo, show k < 2 * (j + 1) by omega, ↓reduceIte]
  by_cases hhi : 2 * j + 2 ≤ k
  · rw [o'.word (by omega) (by omega), hI.val k hk]
    simp only [hlo, show ¬ k < 2 * (j + 1) by omega, ↓reduceIte]
  obtain ⟨q, hq, rfl⟩ : ∃ q, q < 2 ∧ k = 2 * j + q := ⟨k - 2 * j, by omega, by omega⟩
  simp only [show 2 * j + q < 2 * (j + 1) by omega, ↓reduceIte]
  rw [show slot wx Crt.aT + 8 * (2 * j + q) = slot wx Crt.aT + 16 * j + 8 * q by omega, hm]
  show (t.mem.writeW (off B (slot wx Crt.aT + 16 * j)) V).readW (off B (slot wx Crt.aT + 16 * j + 8 * q)) 64 = _
  rw [show off B (slot wx Crt.aT + 16 * j + 8 * q) = off B (slot wx Crt.aT + 16 * j) + BitVec.ofNat 64 (8 * q) from
    (off_add_eq _ _ _).symm, read_write128 _ _ _ hq, hV q hq]
  have hT : word t.mem B (slot wx Crt.aT + 16 * j + 8 * q) = word s.mem B (slot wx Crt.aT + 8 * (2 * j + q)) := by
    rw [show slot wx Crt.aT + 16 * j + 8 * q = slot wx Crt.aT + 8 * (2 * j + q) by omega, hI.val _ hk]
    simp only [hlo, ↓reduceIte]
  unfold gval
  rw [hT, gacc_congr fun j' hj' => ?_]
  have := ent_le wx (j := 8 * p + j') (by omega)
  have := slot_mono wx (show 8 ≤ 8 + (8 * p + j') by omega)
  rw [show 8 + 8 * p + j' = 8 + (8 * p + j') by omega, hI.out.word (by omega) (by omega)]
  congr 1
  omega

/-- `x := r14` in both quadwords: `movq`, `punpcklqdq`. -/
theorem dupX_ok {s : State} (x : XReg) :
    WP isa (.block [.xop (.movq x .r14), .xop (.bin .punpcklqdq x x)]) s fun t =>
      (∀ q < 2, q128 (t.xmm x) q = s.gpr .r14) ∧ (∀ y, y ≠ x → t.xmm y = s.xmm y) ∧ t.gpr = s.gpr ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  simp only [XOp.exec, xmm_setXmm_self, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, and_true]
  exact ⟨fun q hq => q128_dup _ hq, fun y hy => by rw [xmm_setXmm_of_ne _ _ hy, xmm_setXmm_of_ne _ _ hy]⟩

end VG.Proof.Bignum.X86_64
