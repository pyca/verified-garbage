module

public import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
public import VerifiedGarbage.Proof.Ed25519.Canonical64
public import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mem
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ed25519.AArch64.CombDigit
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# The comb's entry, selected in registers

`combDigitS` leaves the digit's magnitude in `x2` and its sign's mask in `x1`
(`combDigitS_ok`). `combEntry` loads every candidate of the digit's table in
pairs of words and keeps the digit's (`csel`, `scan_ok`), from the identity's;
then, for a negative digit, negates `2dT` as `p - 2dT` and exchanges `Y - X`
and `Y + X`, and stores the entry to slots 4–6 (`combEntry_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open VG.Proof.X25519.AArch64.Alt (exec_ldp_x exec_stp_x exec_cselc_x)
open Word64

/-! ## The digit -/

theorem combDigitS_ok {s : State} {base : Addr} (hs : Scr s base) {S i : Nat} (hi : i < 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 i)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block combDigitS) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (mag (nib S i)) ∧ t.gpr .x1 = mask (decide (nib S i < 8)) ∧
      Keeps (clob ++ ([.x1] : List Reg)) s t := by
  have hn : nib S i < 16 := nib_lt _ _
  simp only [combDigitS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combIndex_ok s hs hi hc) fun a ⟨a8, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (combNibble_ok hsa (S := S) (i := i) hi a8 (by omega_arith) (by decide)
    (by rw [ka.mem]; exact hb)) fun b ⟨b2, kb⟩ => ?_
  refine WP.mono (combSign_ok b hn b2) fun t ⟨t2, t1, kt⟩ => ⟨t2, t1, ?_⟩
  exact ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))

/-! ## The table's address -/

theorem tblAddrS_ok (s : State) {T : Addr} (hT : s.syms combSym = T) {j : Nat} (hj : j < 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block tblAddrS) s fun t =>
      t.gpr .x9 = T + BitVec.ofNat 64 (768 * j) ∧ Keeps [.x9, .x16] s t := by
  have hsh : BitVec.ofNat 64 j <<< 8 = BitVec.ofNat 64 (256 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 256 * j < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show j * 2 ^ 8 < 2 ^ 64 by omega_arith)]
    omega_arith
  have h3 : T + BitVec.ofNat 64 (256 * j) + BitVec.ofNat 64 (256 * j) + BitVec.ofNat 64 (256 * j) =
      T + BitVec.ofNat 64 (768 * j) := by
    rw [tbl_add T _ _, tbl_add T _ _, show 256 * j + 256 * j + 256 * j = 768 * j by omega_arith]
  apply WP.of_runBlock
  simp only [tblAddrS, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 8 < 64 from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false,
    reduceCtorEq, hc, hT, hsh, h3, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## One pair of words of a candidate -/

/-- `ldp x16, x17, [x9, #off]` and the two words kept in `r1`, `r2` where `Z` is set. -/
theorem pair_ok {s : State} {r1 r2 : Reg} (h12 : r1 ≠ r2) (h1 : r1 ≠ .x16 ∧ r1 ≠ .x17)
    (h2 : r2 ≠ .x16 ∧ r2 ≠ .x17) {off : Nat} (ho : off % 8 = 0 ∧ off ≤ 504)
    (hr1 : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 off) 8)
    (hr2 : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 off + 8) 8) :
    WP isa (.block [.ldp .x16 .x17 .x9 off, .cselc .x r1 .x16 r1 .eq, .cselc .x r2 .x17 r2 .eq]) s
      fun t => t.gpr r1 = (if s.zf then s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 off) 64 else s.gpr r1) ∧
        t.gpr r2 = (if s.zf then s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 off + 8) 64 else s.gpr r2) ∧
        t.zf = s.zf ∧ Keeps [.x16, .x17, r1, r2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ldp_x (by decide : Reg.x16 ≠ .x17) ho hr1 hr2, runStep_some,
    exec_cselc_x, CondCode.holds, runBlock_nil, RegUpd.zf_write, Option.some.injEq,
    exists_eq_left']
  have n1 : (r1 = Reg.x16) = False := eq_false h1.1
  have n2 : (r1 = Reg.x17) = False := eq_false h1.2
  have n3 : (r2 = Reg.x16) = False := eq_false h2.1
  have n4 : (r2 = Reg.x17) = False := eq_false h2.2
  have m1 : (Reg.x16 = r1) = False := eq_false fun e => h1.1 e.symm
  have m2 : (Reg.x17 = r1) = False := eq_false fun e => h1.2 e.symm
  have n5 : (r1 = r2) = False := eq_false h12
  have n6 : (r2 = r1) = False := eq_false fun e => h12 e.symm
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, n1, n2, n5, n6, ite_true, ite_false, BitVec.setWidth_eq]
    cases s.zf <;> simp
  · simp only [RegUpd.gpr_write, n3, n4, n6, ite_true, ite_false, BitVec.setWidth_eq]
    cases s.zf <;> simp [m2]
  · trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-! ## The candidates -/

private theorem cmp_fact : ∀ a < 9, ∀ m < 8,
    decide (BitVec.ofNat 64 a + ~~~(BitVec.ofNat 64 (m + 1)) + BitVec.ofNat 64 (true.toNat) = 0) =
      decide (a = m + 1) := by decide

private theorem imm_fact : ∀ m < 8, (BitVec.ofNat 16 (m + 1)).setWidth 64 = BitVec.ofNat 64 (m + 1) := by
  decide

theorem exec_movz0 {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true,
    BitVec.shiftLeft_zero]

/-- `Z` = `|d| = m + 1`. -/
theorem cmp_ok (s : State) {a m : Nat} (ha : a < 9) (hm : m < 8) (h2 : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block [.movz .x .x16 (BitVec.ofNat 16 (m + 1)) 0, .subs .x .x16 .x2 .x16]) s fun t =>
      t.zf = decide (a = m + 1) ∧ Keeps [.x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_movz0, runStep_some,
    VG.Proof.X25519.AArch64.Alt.exec_subs_x, runBlock_nil, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ (show ¬ Reg.x2 = .x16 by decide), h2,
    imm_fact m hm]
  refine ⟨cmp_fact a ha m hm, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_addWithCarry, RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)]
  simp only [List.mem_singleton] at hr
  simp only [hr, ite_false]

/-- Word `w` of coordinate `c` of table `j`'s entry `a`. -/
abbrev ew (j a c w : Nat) : BitVec 64 := feWord (coord c (combCached64 j a)) w

/-- Word `w` of coordinate `c` of table `j`'s entry `m + 1`, at `T + 768 j + 256 c + 32 m + 8 w`. -/
theorem tblWord {s : State} {base T : Addr} (h : TblAt s base T) {j c m w : Nat} (hj : j < 64)
    (hc : c < 3) (hm : m < 8) (hw : w < 4) :
    s.mem.readW (T + BitVec.ofNat 64 (768 * j + (256 * c + 32 * m + 8 * w))) 64 = ew j (m + 1) c w ∧
      InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (768 * j + (256 * c + 32 * m + 8 * w))) 8 := by
  have e : 768 * j + (256 * c + 32 * m + 8 * w) = 8 * (96 * j + 32 * c + 4 * m + w) := by omega_arith
  rw [e]
  exact ⟨(h.val _ (by omega_arith)).trans (combWord_eq hc hm hw),
    VG.CallLay.inRegions_sub h.rd (by omega_arith) (by decide)⟩

/-- A pair of words of candidate `m + 1`, coordinate `q + c`, words `2 h` and `2 h + 1`, from
`x9` at table `j`'s coordinate `q`. -/
theorem pairT_ok {s : State} {base T : Addr} (htb : TblAt s base T) {j q c h m o : Nat} (hj : j < 64)
    (hx9 : s.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * q)) (hc : q + c < 3) (hh : h < 2)
    (hm : m < 8) (ho : o = 256 * c + 16 * h) (hr : o + 32 * m ≤ 504) {r1 r2 : Reg} (h12 : r1 ≠ r2)
    (h1 : r1 ≠ .x16 ∧ r1 ≠ .x17) (h2 : r2 ≠ .x16 ∧ r2 ≠ .x17) :
    WP isa (.block [.ldp .x16 .x17 .x9 (o + 32 * m), .cselc .x r1 .x16 r1 .eq,
        .cselc .x r2 .x17 r2 .eq]) s fun t =>
      t.gpr r1 = (if s.zf then ew j (m + 1) (q + c) (2 * h) else s.gpr r1) ∧
      t.gpr r2 = (if s.zf then ew j (m + 1) (q + c) (2 * h + 1) else s.gpr r2) ∧
      t.zf = s.zf ∧ Keeps [.x16, .x17, r1, r2] s t := by
  have a0 : s.gpr .x9 + BitVec.ofNat 64 (o + 32 * m) =
      T + BitVec.ofNat 64 (768 * j + (256 * (q + c) + 32 * m + 8 * (2 * h))) := by
    rw [hx9, tbl_add, ho, show 768 * j + 256 * q + (256 * c + 16 * h + 32 * m) =
      768 * j + (256 * (q + c) + 32 * m + 8 * (2 * h)) by omega_arith]
  have a1 : s.gpr .x9 + BitVec.ofNat 64 (o + 32 * m) + 8 =
      T + BitVec.ofNat 64 (768 * j + (256 * (q + c) + 32 * m + 8 * (2 * h + 1))) := by
    rw [a0, VG.Proof.X25519.AArch64.Alt.eight, tbl_add, show 768 * j + (256 * (q + c) + 32 * m +
      8 * (2 * h)) + 8 = 768 * j + (256 * (q + c) + 32 * m + 8 * (2 * h + 1)) by omega_arith]
  have w0 := tblWord htb hj hc hm (w := 2 * h) (by omega_arith)
  have w1 := tblWord htb hj hc hm (w := 2 * h + 1) (by omega_arith)
  refine WP.mono (pair_ok h12 h1 h2 ⟨by omega_arith, hr⟩ (by rw [a0]; exact w0.2) (by rw [a1]; exact w1.2))
    fun t ⟨t1, t2, tz, kt⟩ => ⟨?_, ?_, tz, kt⟩
  · rw [t1, a0, w0.1]
  · rw [t2, a1, w1.1]

/-- Candidates `k ≤ n` seen: the entry `a` if `a ≤ n`, else the identity. -/
def sel (a n : Nat) : Nat := if a ≤ n then a else 0

theorem sel_succ (a n : Nat) : (if a = n + 1 then n + 1 else sel a n) = sel a (n + 1) := by
  unfold sel
  by_cases h : a = n + 1
  · simp [h]
  · by_cases h' : a ≤ n
    · simp [h, h', show a ≤ n + 1 by omega_arith]
    · simp [h, h', show ¬ a ≤ n + 1 by omega_arith]

theorem sel_ite (a n : Nat) (x : Nat → BitVec 64) :
    (if decide (a = n + 1) = true then x (n + 1) else x (sel a n)) = x (sel a (n + 1)) := by
  rw [← sel_succ]
  by_cases h : a = n + 1 <;> simp [h]

/-- The accumulators of `Y - X` and `Y + X` after the candidates `k ≤ n`. -/
def Acc1 (j a n : Nat) (s : State) : Prop :=
  s.gpr .x3 = ew j (sel a n) 0 0 ∧ s.gpr .x4 = ew j (sel a n) 0 1 ∧
  s.gpr .x5 = ew j (sel a n) 0 2 ∧ s.gpr .x6 = ew j (sel a n) 0 3 ∧
  s.gpr .x7 = ew j (sel a n) 1 0 ∧ s.gpr .x8 = ew j (sel a n) 1 1 ∧
  s.gpr .x10 = ew j (sel a n) 1 2 ∧ s.gpr .x11 = ew j (sel a n) 1 3

/-- The accumulators of `2dT`. -/
def Acc2 (j a n : Nat) (s : State) : Prop :=
  s.gpr .x12 = ew j (sel a n) 2 0 ∧ s.gpr .x13 = ew j (sel a n) 2 1 ∧
  s.gpr .x14 = ew j (sel a n) 2 2 ∧ s.gpr .x15 = ew j (sel a n) 2 3

/-- What the scan's two passes change. -/
def scanRegs₁ : List Reg := [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x16, .x17]
def scanRegs₂ : List Reg := [.x12, .x13, .x14, .x15, .x16, .x17]
def scanRegs : List Reg := [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem cand1_ok {s : State} {base T : Addr} (htb : TblAt s base T) {j a m : Nat} (hj : j < 64)
    (ha : a < 9) (hm : m < 8) (hx9 : s.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 0))
    (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (hA : Acc1 j a m s) :
    WP isa (.block (scanCand scanAccs₁ m)) s fun t => Acc1 j a (m + 1) t ∧ Keeps scanRegs₁ s t := by
  simp only [scanCand, scanAccs₁, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (cmp_ok s ha hm h2) fun b ⟨bz, kb⟩ => ?_
  have b9 : b.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 0) := by rw [kb.gpr _ (by decide)]; exact hx9
  have htb1 : TblAt b base T := htb.of_far (by rw [kb.rd, kb.wr]) fun x _ => by rw [kb.mem]
  rw [WP.block_append_iff]
  refine WP.mono (pairT_ok htb1 hj b9 (c := 0) (h := 0) (by omega_arith) (by omega_arith) hm rfl (by omega_arith)
    (r1 := .x3) (r2 := .x4) (by decide) (by decide) (by decide)) fun c ⟨c3, c4, cz, kc⟩ => ?_
  have c9 : c.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 0) := by rw [kc.gpr _ (by decide)]; exact b9
  have htb2 : TblAt c base T := htb1.of_far (by rw [kc.rd, kc.wr]) fun x _ => by rw [kc.mem]
  rw [WP.block_append_iff]
  refine WP.mono (pairT_ok htb2 hj c9 (c := 0) (h := 1) (by omega_arith) (by omega_arith) hm rfl (by omega_arith)
    (r1 := .x5) (r2 := .x6) (by decide) (by decide) (by decide)) fun d ⟨d5, d6, dz, kd⟩ => ?_
  have d9 : d.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 0) := by rw [kd.gpr _ (by decide)]; exact c9
  have htb3 : TblAt d base T := htb2.of_far (by rw [kd.rd, kd.wr]) fun x _ => by rw [kd.mem]
  rw [WP.block_append_iff]
  refine WP.mono (pairT_ok htb3 hj d9 (c := 1) (h := 0) (by omega_arith) (by omega_arith) hm rfl (by omega_arith)
    (r1 := .x7) (r2 := .x8) (by decide) (by decide) (by decide)) fun e ⟨e7, e8, ez, ke⟩ => ?_
  have e9 : e.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 0) := by rw [ke.gpr _ (by decide)]; exact d9
  have htb4 : TblAt e base T := htb3.of_far (by rw [ke.rd, ke.wr]) fun x _ => by rw [ke.mem]
  refine WP.mono (pairT_ok htb4 hj e9 (c := 1) (h := 1) (by omega_arith) (by omega_arith) hm rfl (by omega_arith)
    (r1 := .x10) (r2 := .x11) (by decide) (by decide) (by decide)) fun t ⟨t10, t11, tz, kt⟩ => ?_
  obtain ⟨a3, a4, a5, a6, a7, a8, a10, a11⟩ := hA
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kt.gpr _ (by decide), ke.gpr _ (by decide), kd.gpr _ (by decide), c3, bz, kb.gpr _ (by decide), a3]
    exact sel_ite a m (fun k => ew j k 0 0)
  · rw [kt.gpr _ (by decide), ke.gpr _ (by decide), kd.gpr _ (by decide), c4, bz, kb.gpr _ (by decide), a4]
    exact sel_ite a m (fun k => ew j k 0 1)
  · rw [kt.gpr _ (by decide), ke.gpr _ (by decide), d5, cz, bz, kc.gpr _ (by decide), kb.gpr _ (by decide), a5]
    exact sel_ite a m (fun k => ew j k 0 2)
  · rw [kt.gpr _ (by decide), ke.gpr _ (by decide), d6, cz, bz, kc.gpr _ (by decide), kb.gpr _ (by decide), a6]
    exact sel_ite a m (fun k => ew j k 0 3)
  · rw [kt.gpr _ (by decide), e7, dz, cz, bz, kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a7]
    exact sel_ite a m (fun k => ew j k 1 0)
  · rw [kt.gpr _ (by decide), e8, dz, cz, bz, kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a8]
    exact sel_ite a m (fun k => ew j k 1 1)
  · rw [t10, ez, dz, cz, bz, ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide),
      kb.gpr _ (by decide), a10]
    exact sel_ite a m (fun k => ew j k 1 2)
  · rw [t11, ez, dz, cz, bz, ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide),
      kb.gpr _ (by decide), a11]
    exact sel_ite a m (fun k => ew j k 1 3)
  · exact ((((kb.mono (by decide)).trans (kc.mono (by decide))).trans (kd.mono (by decide))).trans
      (ke.mono (by decide))).trans (kt.mono (by decide))

theorem cand2_ok {s : State} {base T : Addr} (htb : TblAt s base T) {j a m : Nat} (hj : j < 64)
    (ha : a < 9) (hm : m < 8) (hx9 : s.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 2))
    (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (hA : Acc2 j a m s) :
    WP isa (.block (scanCand scanAccs₂ m)) s fun t => Acc2 j a (m + 1) t ∧ Keeps scanRegs₂ s t := by
  simp only [scanCand, scanAccs₂, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (cmp_ok s ha hm h2) fun b ⟨bz, kb⟩ => ?_
  have b9 : b.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 2) := by rw [kb.gpr _ (by decide)]; exact hx9
  have htb1 : TblAt b base T := htb.of_far (by rw [kb.rd, kb.wr]) fun x _ => by rw [kb.mem]
  rw [WP.block_append_iff]
  refine WP.mono (pairT_ok htb1 hj b9 (c := 0) (h := 0) (by omega_arith) (by omega_arith) hm rfl (by omega_arith)
    (r1 := .x12) (r2 := .x13) (by decide) (by decide) (by decide)) fun c ⟨c12, c13, cz, kc⟩ => ?_
  have c9 : c.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 2) := by rw [kc.gpr _ (by decide)]; exact b9
  have htb2 : TblAt c base T := htb1.of_far (by rw [kc.rd, kc.wr]) fun x _ => by rw [kc.mem]
  refine WP.mono (pairT_ok htb2 hj c9 (c := 0) (h := 1) (by omega_arith) (by omega_arith) hm rfl (by omega_arith)
    (r1 := .x14) (r2 := .x15) (by decide) (by decide) (by decide)) fun t ⟨t14, t15, tz, kt⟩ => ?_
  obtain ⟨a12, a13, a14, a15⟩ := hA
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kt.gpr _ (by decide), c12, bz, kb.gpr _ (by decide), a12]
    exact sel_ite a m (fun k => ew j k 2 0)
  · rw [kt.gpr _ (by decide), c13, bz, kb.gpr _ (by decide), a13]
    exact sel_ite a m (fun k => ew j k 2 1)
  · rw [t14, cz, bz, kc.gpr _ (by decide), kb.gpr _ (by decide), a14]
    exact sel_ite a m (fun k => ew j k 2 2)
  · rw [t15, cz, bz, kc.gpr _ (by decide), kb.gpr _ (by decide), a15]
    exact sel_ite a m (fun k => ew j k 2 3)
  · exact ((kb.mono (by decide)).trans (kc.mono (by decide))).trans (kt.mono (by decide))

/-- The candidates `k ≤ n` of the first pass. -/
theorem scan1_ok {s : State} {base T : Addr} (htb : TblAt s base T) {j a : Nat} (hj : j < 64)
    (ha : a < 9) (hx9 : s.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 0))
    (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (hA : Acc1 j a 0 s) (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap (scanCand scanAccs₁))) s fun t =>
      Acc1 j a n t ∧ Keeps scanRegs₁ s t := by
  induction n with
  | zero => exact WP.block_nil ⟨hA, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t ⟨ta, kt⟩ => ?_
    refine WP.mono (cand1_ok (htb.of_far (by rw [kt.rd, kt.wr]) fun x _ => by rw [kt.mem]) hj ha
      (by omega_arith) (by rw [kt.gpr _ (by decide)]; exact hx9) (by rw [kt.gpr _ (by decide)]; exact h2) ta)
      fun u ⟨ua, ku⟩ => ⟨ua, kt.trans ku⟩

/-- The candidates `k ≤ n` of the second pass. -/
theorem scan2_ok {s : State} {base T : Addr} (htb : TblAt s base T) {j a : Nat} (hj : j < 64)
    (ha : a < 9) (hx9 : s.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 2))
    (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (hA : Acc2 j a 0 s) (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap (scanCand scanAccs₂))) s fun t =>
      Acc2 j a n t ∧ Keeps scanRegs₂ s t := by
  induction n with
  | zero => exact WP.block_nil ⟨hA, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t ⟨ta, kt⟩ => ?_
    refine WP.mono (cand2_ok (htb.of_far (by rw [kt.rd, kt.wr]) fun x _ => by rw [kt.mem]) hj ha
      (by omega_arith) (by rw [kt.gpr _ (by decide)]; exact hx9) (by rw [kt.gpr _ (by decide)]; exact h2) ta)
      fun u ⟨ua, ku⟩ => ⟨ua, kt.trans ku⟩

/-! ## The identity -/

private theorem ident_words (j : Nat) :
    ew j 0 0 0 = 1 ∧ ew j 0 0 1 = 0 ∧ ew j 0 0 2 = 0 ∧ ew j 0 0 3 = 0 ∧
    ew j 0 1 0 = 1 ∧ ew j 0 1 1 = 0 ∧ ew j 0 1 2 = 0 ∧ ew j 0 1 3 = 0 ∧
    ew j 0 2 0 = 0 ∧ ew j 0 2 1 = 0 ∧ ew j 0 2 2 = 0 ∧ ew j 0 2 3 = 0 := by
  simp only [ew, combCached64_zero, coord]
  decide

theorem scanInit_ok (s : State) (j a : Nat) :
    WP isa (.block scanInit) s fun t => Acc1 j a 0 t ∧ Acc2 j a 0 t ∧ Keeps scanRegs s t := by
  have e : ∀ c w, ew j (sel a 0) c w = ew j 0 c w := fun c w => by
    unfold sel; split
    · rename_i h; rw [show a = 0 by omega_arith]
    · rfl
  obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := ident_words j
  apply WP.of_runBlock
  simp only [scanInit, runBlock_cons, exec_movz0, runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  rotate_left 12
  · simp only [scanRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h3, h4, h5, h6, h7, h8, h10, h11, h12, h13, h14, h15, -, -⟩ := hr
    simp only [RegUpd.gpr_write, h3, h4, h5, h6, h7, h8, h10, h11, h12, h13, h14, h15, ite_false]
  all_goals
    simp only [RegUpd.gpr_write, e, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, reduceCtorEq,
      ite_true, ite_false]
    decide

/-! ## The sign -/

private theorem neg_val {R v P c : Nat} (hR : R < 2 ^ 256) (hv : v ≤ P) (hP : P < 2 ^ 256) (_hc : c ≤ 1)
    (e : R + v + (1 - 1) = P + 2 ^ 256 * (1 - c)) : R = P - v := by omega_arith

/-- `p - v` for the `2dT` words `v ≤ p` in `x12`–`x15`, into `x20`–`x23`. -/
theorem scanNeg_ok (s : State) {v : Nat}
    (hv : val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) = v) (hvp : v ≤ Spec.X25519.P) :
    WP isa (.block scanNeg) s fun t =>
      val4 (t.gpr .x20) (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) = Spec.X25519.P - v ∧
      Keeps [.x16, .x17, .x20, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [scanNeg, runBlock_cons, runStep_some, runBlock_nil, exec_movz0,
    exec_subImm_x (show 1 < 4096 by decide), exec_subImm_x (show 18 < 4096 by decide),
    VG.Proof.X25519.AArch64.Alt.exec_lsr1_x, VG.Proof.X25519.AArch64.Alt.exec_subs_x,
    VG.Proof.X25519.AArch64.Alt.exec_sbcs_x, VG.Proof.X25519.AArch64.Alt.exec_sbc_x, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, reduceCtorEq, ite_true,
    ite_false, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  have k0 : (BitVec.setWidth 64 (0 : BitVec 16) - 1#Size.x.bits - 18#Size.x.bits : BitVec 64) =
      BitVec.ofNat 64 (2 ^ 64 - 19) := by decide
  have k1 : (BitVec.setWidth 64 (0 : BitVec 16) - 1#Size.x.bits : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
  have k2 : ((BitVec.setWidth 64 (0 : BitVec 16) - 1#Size.x.bits) >>> 1 : BitVec 64) = BitVec.ofNat 64 (2 ^ 63 - 1) := by
    decide
  rw [k0, k2, k1]
  have e := sub4_value (BitVec.ofNat 64 (2 ^ 64 - 19)) (BitVec.ofNat 64 (2 ^ 64 - 1))
    (BitVec.ofNat 64 (2 ^ 64 - 1)) (BitVec.ofNat 64 (2 ^ 63 - 1)) (s.gpr .x12) (s.gpr .x13)
    (s.gpr .x14) (s.gpr .x15) true
  simp only [addCarry, carryOut] at e
  have hp : val4 (BitVec.ofNat 64 (2 ^ 64 - 19)) (BitVec.ofNat 64 (2 ^ 64 - 1))
      (BitVec.ofNat 64 (2 ^ 64 - 1)) (BitVec.ofNat 64 (2 ^ 63 - 1)) = Spec.X25519.P := by decide
  refine ⟨?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [Size.bits]
    rw [hv, hp] at e
    exact neg_val (val4_lt _ _ _ _) hvp (by decide) (Bool.toNat_le _) e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h16, h17, h20, h21, h22, h23, h24⟩ := hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, h16, h17, h20, h21, h22, h23, h24, ite_false]
  all_goals rfl

/-- The prefix of `scanSign`: the choices under the sign's mask. -/
def signSel : List Instr := scanSign.take 13

theorem scanSign_eq : scanSign = signSel ++
    (([.stp .x20 .x21 .x0 (offset 4), .stp .x22 .x23 .x0 (offset 4 + 16)] : List Instr) ++
    (([.stp .x16 .x17 .x0 (offset 5), .stp .x24 .x2 .x0 (offset 5 + 16)] : List Instr) ++
    ([.stp .x12 .x13 .x0 (offset 6), .stp .x14 .x15 .x0 (offset 6 + 16)] : List Instr))) := rfl

/-- What `signSel` changes. -/
def signRegs : List Reg := [.x12, .x13, .x14, .x15, .x20, .x21, .x22, .x23, .x16, .x17, .x24, .x2]

theorem signSel_ok (s : State) {sg : Bool} (h1 : s.gpr .x1 = mask sg) :
    WP isa (.block signSel) s fun t =>
      t.gpr .x12 = (if sg then s.gpr .x20 else s.gpr .x12) ∧ t.gpr .x13 = (if sg then s.gpr .x21 else s.gpr .x13) ∧
      t.gpr .x14 = (if sg then s.gpr .x22 else s.gpr .x14) ∧ t.gpr .x15 = (if sg then s.gpr .x23 else s.gpr .x15) ∧
      t.gpr .x20 = (if sg then s.gpr .x7 else s.gpr .x3) ∧ t.gpr .x21 = (if sg then s.gpr .x8 else s.gpr .x4) ∧
      t.gpr .x22 = (if sg then s.gpr .x10 else s.gpr .x5) ∧ t.gpr .x23 = (if sg then s.gpr .x11 else s.gpr .x6) ∧
      t.gpr .x16 = (if sg then s.gpr .x3 else s.gpr .x7) ∧ t.gpr .x17 = (if sg then s.gpr .x4 else s.gpr .x8) ∧
      t.gpr .x24 = (if sg then s.gpr .x5 else s.gpr .x10) ∧ t.gpr .x2 = (if sg then s.gpr .x6 else s.gpr .x11) ∧
      Keeps signRegs s t := by
  apply WP.of_runBlock
  cases sg <;>
  · simp only [signSel, scanSign, List.take, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
      CondCode.holds, h1, mask, BitVec.and_self, Bool.false_eq_true, RegUpd.zf_write, decide_true,
      decide_false, show (BitVec.allOnes 64 = 0) = False by decide, Bool.not_false, Bool.not_true]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := hr
    simp only [RegUpd.gpr_write, a, b, c, d, e, f, g, h, i, j, k, l, ↓reduceIte]

theorem addImm512_ok (s : State) :
    WP isa (.block [.addImm .x .x9 .x9 512]) s fun t =>
      t.gpr .x9 = s.gpr .x9 + BitVec.ofNat 64 512 ∧ Keeps [.x9] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 512 < 4096 by decide), read_x,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

theorem sel_8 {a : Nat} (ha : a < 9) : sel a 8 = a := by
  unfold sel; simp [show a ≤ 8 by omega_arith]

theorem toFe_neg (x : Spec.X25519.Fe) : VG.Proof.X25519.toFe (Spec.X25519.P - x.val) = 0 - x := by
  apply Fin.ext
  simp only [VG.Proof.X25519.toFe, Fin.val_ofNat, Fin.sub_def, Fin.val_zero, Nat.add_zero]

/-- **The digit's entry** from table `j`, `|d| = a`, to slots 4–6: its `Y - X` and `Y + X`
exchanged and its `2dT` negated for a negative digit (`sg`, the sign's mask in `x1`). -/
theorem combEntry_ok {s : State} {base T : Addr} (hs : Scr s base) (htb : TblAt s base T)
    (hT : s.syms combSym = T) {j : Nat} (hj : j < 64) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    {a : Nat} (ha : a < 9) (h2 : s.gpr .x2 = BitVec.ofNat 64 a) {sg : Bool} (h1 : s.gpr .x1 = mask sg) :
    WP isa (.block combEntry) s fun t =>
      env t.mem base 4 = (if sg then (combCached64 j a).Y else (combCached64 j a).X) ∧
      env t.mem base 5 = (if sg then (combCached64 j a).X else (combCached64 j a).Y) ∧
      env t.mem base 6 = (if sg then 0 - (combCached64 j a).Z else (combCached64 j a).Z) ∧
      Outside base (offset 4) 96 s.mem t.mem ∧ Keep base s t := by
  simp only [combEntry, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (tblAddrS_ok s hT hj hc) fun s1 ⟨x9a, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scanInit_ok s1 j a) fun s2 ⟨A1, A2, k2⟩ => ?_
  have k12 := (k1.mono (by decide : ∀ r ∈ [Reg.x9, .x16], r ∈ clob)).trans (k2.mono (by decide))
  have htb2 : TblAt s2 base T := htb.of_far (by rw [k12.rd, k12.wr]) fun x _ => by rw [k12.mem]
  have x9b : s2.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 0) := by
    rw [k2.gpr _ (by decide), x9a, Nat.mul_zero, Nat.add_zero]
  have x2b : s2.gpr .x2 = BitVec.ofNat 64 a := by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), h2]
  rw [WP.block_append_iff]
  refine WP.mono (scan1_ok htb2 hj ha x9b x2b A1 8 (by decide)) fun s3 ⟨B1, k3⟩ => ?_
  have A2' : Acc2 j a 0 s3 := by
    obtain ⟨a12, a13, a14, a15⟩ := A2
    exact ⟨by rw [k3.gpr _ (by decide)]; exact a12, by rw [k3.gpr _ (by decide)]; exact a13,
      by rw [k3.gpr _ (by decide)]; exact a14, by rw [k3.gpr _ (by decide)]; exact a15⟩
  rw [WP.block_append_iff]
  refine WP.mono (addImm512_ok s3) fun s4 ⟨x9d, k4⟩ => ?_
  have k34 := (k3.mono (by decide : ∀ r ∈ scanRegs₁, r ∈ clob)).trans (k4.mono (by decide))
  have htb4 : TblAt s4 base T := htb2.of_far (by rw [k34.rd, k34.wr]) fun x _ => by rw [k34.mem]
  have x9e : s4.gpr .x9 = T + BitVec.ofNat 64 (768 * j + 256 * 2) := by
    rw [x9d, k3.gpr _ (by decide), x9b, tbl_add]
  have x2e : s4.gpr .x2 = BitVec.ofNat 64 a := by rw [k4.gpr _ (by decide), k3.gpr _ (by decide), x2b]
  have A2'' : Acc2 j a 0 s4 := by
    obtain ⟨a12, a13, a14, a15⟩ := A2'
    exact ⟨by rw [k4.gpr _ (by decide)]; exact a12, by rw [k4.gpr _ (by decide)]; exact a13,
      by rw [k4.gpr _ (by decide)]; exact a14, by rw [k4.gpr _ (by decide)]; exact a15⟩
  rw [WP.block_append_iff]
  refine WP.mono (scan2_ok htb4 hj ha x9e x2e A2'' 8 (by decide)) fun s5 ⟨B2, k5⟩ => ?_
  unfold Acc1 at B1; unfold Acc2 at B2; rw [sel_8 ha] at B1 B2
  obtain ⟨b3, b4, b5, b6, b7, b8, b10, b11⟩ := B1
  obtain ⟨b12, b13, b14, b15⟩ := B2
  have v6 : val4 (s5.gpr .x12) (s5.gpr .x13) (s5.gpr .x14) (s5.gpr .x15) = (combCached64 j a).Z.val := by
    rw [b12, b13, b14, b15]; exact feWord_val _
  rw [WP.block_append_iff]
  refine WP.mono (scanNeg_ok s5 v6 (Nat.le_of_lt (combCached64 j a).Z.isLt)) fun s6 ⟨n6, k6⟩ => ?_
  -- the registers at `s6`, from the scan
  have g : ∀ r, r ∈ [Reg.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11] → s6.gpr r = s3.gpr r := by
    intro r hr
    have h1' : r ∉ [Reg.x16, .x17, .x20, .x21, .x22, .x23, .x24] := by revert r; decide
    have h2' : r ∉ scanRegs₂ := by revert r; decide
    have h3' : r ∉ [Reg.x9] := by revert r; decide
    rw [k6.gpr r h1', k5.gpr r h2', k4.gpr r h3']
  have g' : ∀ r, r ∈ [Reg.x12, .x13, .x14, .x15] → s6.gpr r = s5.gpr r := by
    intro r hr
    exact k6.gpr r (by revert r; decide)
  have x1f : s6.gpr .x1 = mask sg := by
    rw [k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide),
      k2.gpr _ (by decide), k1.gpr _ (by decide), h1]
  have kk : Keeps clob s s6 := (((((k12.trans (k3.mono (by decide))).trans (k4.mono (by decide))).trans
    (k5.mono (by decide))).trans (k6.mono (by decide))))
  have hs6 : Scr s6 base := hs.of_keeps kk (by decide)
  rw [scanSign_eq, WP.block_append_iff]
  refine WP.mono (signSel_ok s6 x1f) fun s7 ⟨c12, c13, c14, c15, c20, c21, c22, c23, c16, c17, c24, c2, k7⟩ => ?_
  have hs7 : Scr s7 base := hs6.of_keeps k7 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Alt.store4_ok hs7 (o := offset 4) (by decide) (by decide)
    (by decide) .x20 .x21 .x22 .x23) fun s8 e8 => ?_
  subst e8
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.Alt.store4_ok (hs7.withMem _) (o := offset 5) (by decide)
    (by decide) (by decide) .x16 .x17 .x24 .x2) fun s9 e9 => ?_
  subst e9
  refine WP.mono (VG.Proof.X25519.AArch64.Alt.store4_ok ((hs7.withMem _).withMem _) (o := offset 6)
    (by decide) (by decide) (by decide) .x12 .x13 .x14 .x15) fun t et => ?_
  subst et
  simp only [VG.Proof.X25519.AArch64.Alt.mem_withMem, VG.Proof.X25519.AArch64.Alt.gpr_withMem]
  generalize hM1 : st4 s7.mem base (offset 4) (s7.gpr .x20) (s7.gpr .x21) (s7.gpr .x22) (s7.gpr .x23) = M1
  generalize hM2 : st4 M1 base (offset 5) (s7.gpr .x16) (s7.gpr .x17) (s7.gpr .x24) (s7.gpr .x2) = M2
  generalize hM3 : st4 M2 base (offset 6) (s7.gpr .x12) (s7.gpr .x13) (s7.gpr .x14) (s7.gpr .x15) = M3
  have o1 : Outside base (offset 4) 32 s7.mem M1 := hM1 ▸ st4_outside _ _ (by decide) _ _ _ _
  have o2 : Outside base (offset 5) 32 M1 M2 := hM2 ▸ st4_outside _ _ (by decide) _ _ _ _
  have o3 : Outside base (offset 6) 32 M2 M3 := hM3 ▸ st4_outside _ _ (by decide) _ _ _ _
  have f4 : fe M3 base (offset 4) = val4 (s7.gpr .x20) (s7.gpr .x21) (s7.gpr .x22) (s7.gpr .x23) := by
    rw [o3.fe (by decide) (by decide), o2.fe (by decide) (by decide), ← hM1, fe_st4 _ _ (by decide)]
  have f5 : fe M3 base (offset 5) = val4 (s7.gpr .x16) (s7.gpr .x17) (s7.gpr .x24) (s7.gpr .x2) := by
    rw [o3.fe (by decide) (by decide), ← hM2, fe_st4 _ _ (by decide)]
  have f6 : fe M3 base (offset 6) = val4 (s7.gpr .x12) (s7.gpr .x13) (s7.gpr .x14) (s7.gpr .x15) := by
    rw [← hM3, fe_st4 _ _ (by decide)]
  have m7 : s7.mem = s.mem := by rw [k7.mem, kk.mem]
  have r : ∀ c, ∀ w, ew j a c w = feWord (coord c (combCached64 j a)) w := fun _ _ => rfl
  have vX : val4 (s6.gpr .x3) (s6.gpr .x4) (s6.gpr .x5) (s6.gpr .x6) = (combCached64 j a).X.val := by
    rw [g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), b3, b4, b5, b6]
    exact feWord_val _
  have vY : val4 (s6.gpr .x7) (s6.gpr .x8) (s6.gpr .x10) (s6.gpr .x11) = (combCached64 j a).Y.val := by
    rw [g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), b7, b8, b10, b11]
    exact feWord_val _
  have vZ : val4 (s6.gpr .x12) (s6.gpr .x13) (s6.gpr .x14) (s6.gpr .x15) = (combCached64 j a).Z.val := by
    rw [g' _ (by decide), g' _ (by decide), g' _ (by decide), g' _ (by decide)]; exact v6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show VG.Proof.X25519.toFe (fe M3 base (offset 4)) = _
    rw [f4, c20, c21, c22, c23]
    cases sg
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [vX, VG.Proof.X25519.toFe_self]
    · simp only [↓reduceIte]; rw [vY, VG.Proof.X25519.toFe_self]
  · show VG.Proof.X25519.toFe (fe M3 base (offset 5)) = _
    rw [f5, c16, c17, c24, c2]
    cases sg
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [vY, VG.Proof.X25519.toFe_self]
    · simp only [↓reduceIte]; rw [vX, VG.Proof.X25519.toFe_self]
  · show VG.Proof.X25519.toFe (fe M3 base (offset 6)) = _
    rw [f6, c12, c13, c14, c15]
    cases sg
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [vZ, VG.Proof.X25519.toFe_self]
    · simp only [↓reduceIte]; rw [n6, toFe_neg]
  · rw [← m7]
    exact ((o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))).trans
      (o3.mono (by decide) (by decide))
  · have om : Outside base 64 704 s.mem M3 := by
      rw [← m7]
      exact ((o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))).trans
        (o3.mono (by decide) (by decide))
    refine ⟨fun r hr => ?_, ?_, ?_, ?_, om⟩
    · show s7.gpr r = _
      rw [k7.gpr r (fun h => hr ((by decide : ∀ r ∈ signRegs, r ∈ clob) r h)), kk.gpr r hr]
    · show s7.rd = _
      rw [k7.rd, kk.rd]
    · show s7.wr = _
      rw [k7.wr, kk.wr]
    · show s7.sp = _
      rw [k7.sp, kk.sp]

end VG.Proof.Ed25519.AArch64
