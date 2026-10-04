import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLoop
import VerifiedGarbage.Proof.Ed448.AArch64.MemWords

/-!
# Ed448 scalar arithmetic on AArch64: entry and exit

The callee-saved registers saved in the working space and restored, the
constants set up, the remainder of the top bytes of a 114-byte input, and
the remainder written out as 57 bytes.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x const64_ok word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-! ## The callee-saved registers -/

/-- The callee-saved registers `g` in the working space at `base`. -/
def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved, word m base p.2 = g p.1

theorem saved_ok : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 64 := by decide

theorem saved_sep : saved.Pairwise (fun p q => Sep8 p.2 q.2) := by decide

theorem saveRegs_ok {s : State} {base : Addr} (b : Reg) (hb : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (saveRegs b)) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 0 64 s.mem t.mem ∧ Saved base s.gpr t.mem := by
  refine WP.mono (strs_ok b saved s hb fun p hp => ?_) fun t ht => ?_
  · obtain ⟨h8, hl⟩ := saved_ok p hp
    exact ⟨h8, by omega, _, hw, contains_sc (by omega)⟩
  · subst ht
    refine ⟨rfl, rfl, rfl, rfl,
      wrs_outside _ _ _ (by omega) _ fun p hp => ⟨Nat.zero_le _, (saved_ok p hp).2⟩,
      fun p hp => word_wrs _ _ _ _ saved_sep (fun q hq => by have := (saved_ok q hq).2; omega) p hp⟩

/-- The registers `saved` holds. -/
def savedRegs : List Reg := saved.map (·.1)

theorem restoreRegs_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block restoreRegs) s fun t =>
      (∀ p ∈ saved, t.gpr p.1 = g p.1) ∧ Keeps savedRegs s t := by
  refine WP.mono (ldrs_ok .x2 saved s hb (fun p hp => ?_) (by decide)) fun t ⟨ht, kt⟩ =>
    ⟨fun p hp => (ht p hp).trans (hsv p hp), kt⟩
  obtain ⟨h8, hl⟩ := saved_ok p hp
  exact ⟨h8, by omega, ⟨_, List.mem_append_right _ hw, contains_sc (by omega)⟩,
    (by decide : ∀ p ∈ saved, p.1 ≠ .x2) p hp⟩

/-! ## The constants -/

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun t => Consts t ∧ Keeps constRegs s t := by
  simp only [consts, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s C0 c0) fun a ⟨a0, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok a C1 c1) fun b ⟨b1, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b C2 c2) fun c ⟨c2', kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok c C3 c3) fun d ⟨d3, kd⟩ => ?_
  apply WP.of_runBlock
  simp only [KT, Z, runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [C0, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide)]; exact a0
  · simp only [C1, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide)]; exact b1
  · simp only [C2, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide)]; exact c2'
  · simp only [C3, RegUpd.gpr_write, reduceCtorEq, ite_false]; exact d3
  · simp only [KT, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [Z, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [constRegs, C0, C1, C2, C3, KT, Z, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    rw [kd.gpr _ (by simp [C3, hr.2.2.2.1]), kc.gpr _ (by simp [C2, hr.2.2.1]),
      kb.gpr _ (by simp [C1, hr.2.1]), ka.gpr _ (by simp [C0, hr.1])]
  · exact kd.mem.trans (kc.mem.trans (kb.mem.trans ka.mem))
  · exact kd.rd.trans (kc.rd.trans (kb.rd.trans ka.rd))
  · exact kd.wr.trans (kc.wr.trans (kb.wr.trans ka.wr))
  · exact kd.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))

/-! ## The top bytes -/

theorem toNat_byte (b : Byte) : ((b.setWidth 32).setWidth 64).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

theorem decode_two (m : Mem) (p : Addr) :
    decodeLE (bytesAt m p 2) = (m p).toNat + 256 * (m (p + 1)).toNat := by
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, decodeLE, BitVec.add_zero, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The remainder of the top two bytes of a 114-byte input. -/
theorem init114_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 112) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 113) 1) :
    WP isa (.block init114) s fun t =>
      rem t = decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 112) 2) ∧
      t.gpr .x3 = BitVec.ofNat 64 112 ∧
      Keeps [.x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] s t := by
  apply WP.of_runBlock
  simp only [init114, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    show (112 : Nat) % 1 = 0 from rfl,
    show (112 : Nat) < 4096 * 1 from by decide, show (113 : Nat) < 4096 * 1 from by decide,
    and_self, h0, h1, show 8 < Size.x.bits from by decide, show 16 * 0 < Size.x.bits from by decide,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [decode_two, show s.gpr .x1 + BitVec.ofNat 64 112 + 1 = s.gpr .x1 + BitVec.ofNat 64 113 by
      rw [BitVec.add_assoc]; rfl]
    simp only [rem, rv, R, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    have b0 := (s.mem (s.gpr .x1 + BitVec.ofNat 64 112)).isLt
    have b1 := (s.mem (s.gpr .x1 + BitVec.ofNat 64 113)).isLt
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, toNat_byte, toNat_byte, Nat.shiftLeft_eq]
    have z : (BitVec.setWidth Size.x.bits (0 : BitVec 16) <<< (16 * 0)).toNat = 0 := by decide
    rw [Ed25519.AArch64.read_byte, Ed25519.AArch64.read_byte, z]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## The result -/

theorem word_write_byte (m : Mem) (q : Addr) {d e : Nat} (h : d + 8 ≤ e) (he : e < 2 ^ 64)
    (v : BitVec (8 * 1)) : word (m.write (off q e) 1 v) q d = word m q d := by
  simp only [word, Mem.readW]
  rw [Mem.read_write_sep (Offset.sep q (Or.inl h) (by omega) (by omega)) (by decide)]

theorem readW_write_byte (m : Mem) (q : Addr) {d e : Nat} (h : d + 8 ≤ e) (he : e < 2 ^ 64)
    (v : BitVec (8 * 1)) :
    (m.write (q + BitVec.ofNat 64 e) 1 v).readW (q + BitVec.ofNat 64 d) 64 =
      m.readW (q + BitVec.ofNat 64 d) 64 := by
  simp only [Mem.readW]
  rw [Mem.read_write_sep (Offset.sep q (Or.inl h) (by omega) (by omega)) (by decide)]

theorem write_byte_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_lt_one, ite_true, Nat.mul_zero]
  exact BitVec.extractLsb'_eq_self

theorem toNat_zero8 : (0 : BitVec (8 * 1)).toNat = 0 := rfl

theorem outWords_ok : ∀ p ∈ outWords, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 56 := by decide

theorem outWords_sep : outWords.Pairwise (fun p q => Sep8 p.2 q.2) := by decide

/-- The zero byte at `q + 56`. -/
theorem zeroByte_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q)
    (hb : InRegions s.wr (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block [.movz .x .x12 0 0, .strb .x12 .x0 56]) s fun t =>
      t.mem = s.mem.write (q + BitVec.ofNat 64 56) 1 0 ∧ (∀ r, r ≠ .x12 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, State.read, hq,
    show 16 * 0 < Size.x.bits from by decide, show (56 : Nat) % 1 = 0 from rfl,
    show (56 : Nat) < 4096 * 1 from by decide, and_self, RegUpd.wr_write, RegUpd.gpr_write,
    RegUpd.mem_write, ite_true, ite_false, reduceCtorEq, hb, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨congrArg _ (by decide), fun r hr => by simp only [hr, ite_false], rfl, trivial, rfl⟩

/-- The remainder to the 57 bytes at `q`. -/
theorem outStore_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q) (hw : (⟨q, 57⟩ : Region) ∈ s.wr) :
    WP isa (.block (outWords.map (fun p => .str .x p.1 .x0 p.2) ++
        ([.movz .x .x12 0 0, .strb .x12 .x0 56] : List Instr))) s fun t =>
      decodeLE (bytesAt t.mem q 57) = rem s ∧ Frame [⟨q, 57⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [WP.block_append_iff]
  refine WP.mono (strs_ok .x0 outWords s hq fun p hp => ?_) fun a ha => ?_
  · obtain ⟨h8, hl⟩ := outWords_ok p hp
    exact ⟨h8, by omega, _, hw, Offset.contains_base q (by omega) (by omega)⟩
  subst ha
  have hb : InRegions s.wr (q + BitVec.ofNat 64 56) 1 :=
    ⟨_, hw, Offset.contains_base q (d := 56) (n := 1) (by omega) (by omega)⟩
  refine WP.mono (zeroByte_ok hq hb) fun t ⟨mt, gt, rdt, wrt, spt⟩ => ?_
  refine ⟨?_, ?_, gt, rdt, wrt, spt⟩
  · rw [mt, decode57]
    have hw' : ∀ p ∈ outWords, word (wrs s.mem q s.gpr outWords) q p.2 = s.gpr p.1 :=
      word_wrs _ _ _ _ outWords_sep fun p hp => by have := (outWords_ok p hp).2; omega
    have w0 := hw' (.x5, 0) (by decide)
    have w1 := hw' (.x6, 8) (by decide)
    have w2 := hw' (.x7, 16) (by decide)
    have w3 := hw' (.x8, 24) (by decide)
    have w4 := hw' (.x9, 32) (by decide)
    have w5 := hw' (.x10, 40) (by decide)
    have w6 := hw' (.x11, 48) (by decide)
    simp (disch := decide) only [readW_write_byte, write_byte_self, w0, w1, w2, w3, w4, w5, w6,
      toNat_zero8, Nat.mul_zero, Nat.add_zero]
    rw [rem_eq]
  · rw [mt]
    exact (wrs_frame q s.gpr outWords s.mem (Frame.refl _ _) fun p hp =>
      Offset.contains_base q (by have := (outWords_ok p hp).2; omega)
        (by have := (outWords_ok p hp).2; omega)).write
      (List.mem_singleton_self _) _ (Offset.contains_base q (d := 56) (n := 1) (by omega) (by omega))

end VG.Proof.Ed448.AArch64
