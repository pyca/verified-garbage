import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Gcm.Bits

/-!
# Deterministic ECDSA on AArch64: `h = bits2octets(digest)`

The digest, big-endian in four words (`load_ok`), less `n` if that does not
borrow (`sub_ok`, `select_ok`, and `reduce_math`: it is below `2^256 < 2n`,
so this is the digest modulo `n`), stored big-endian in the frame
(`store_ok`, `reduce_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut)
open VG.Proof.Mont.AArch64 (subc_ok sub_borrow const64_ok)

/-- `x ^ d` masked, then `^ d`: `x` if the mask is all ones, `d` if zero. -/
theorem sel_mask (x d : BitVec 64) (b : Bool) :
    ((x ^^^ d) &&& (if b then BitVec.allOnes 64 else 0)) ^^^ d = if b then x else d := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The chain of `subs` and `sbcs` of `x - n`, selected by its borrow, is `x mod n`. -/
theorem reduce_math (x0 x1 x2 x3 n0 n1 n2 n3 : BitVec 64) {c1 c2 c3 c4 : Bool}
    (h1 : c1 = Word64.carryOut x0 (~~~n0) true) (h2 : c2 = Word64.carryOut x1 (~~~n1) c1)
    (h3 : c3 = Word64.carryOut x2 (~~~n2) c2) (h4 : c4 = Word64.carryOut x3 (~~~n3) c3) {N : Nat}
    (hN : n3.toNat * 2 ^ 192 + n2.toNat * 2 ^ 128 + n1.toNat * 2 ^ 64 + n0.toNat = N) (hN' : 2 ^ 255 ≤ N) :
    (if (!c4) = true then x3 else Word64.addCarry x3 (~~~n3) c3).toNat * 2 ^ 192 +
        (if (!c4) = true then x2 else Word64.addCarry x2 (~~~n2) c2).toNat * 2 ^ 128 +
        (if (!c4) = true then x1 else Word64.addCarry x1 (~~~n1) c1).toNat * 2 ^ 64 +
        (if (!c4) = true then x0 else Word64.addCarry x0 (~~~n0) true).toNat =
      (x3.toNat * 2 ^ 192 + x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat) % N := by
  have e0 := sub_borrow x0 n0 true
  have e1 := sub_borrow x1 n1 c1
  have e2 := sub_borrow x2 n2 c2
  have e3 := sub_borrow x3 n3 c3
  rw [← h1] at e0; rw [← h2] at e1; rw [← h3] at e2; rw [← h4] at e3
  clear h1 h2 h3 h4
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e0
  generalize Word64.addCarry x0 (~~~n0) true = D0 at *
  generalize Word64.addCarry x1 (~~~n1) c1 = D1 at *
  generalize Word64.addCarry x2 (~~~n2) c2 = D2 at *
  generalize Word64.addCarry x3 (~~~n3) c3 = D3 at *
  have := x0.isLt; have := x1.isLt; have := x2.isLt; have := x3.isLt
  have := n0.isLt; have := n1.isLt; have := n2.isLt; have := n3.isLt
  have hX : x3.toNat * 2 ^ 192 + x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat < 2 ^ 256 := by omega
  have hsum : (D3.toNat * 2 ^ 192 + D2.toNat * 2 ^ 128 + D1.toNat * 2 ^ 64 + D0.toNat) + N =
      (x3.toNat * 2 ^ 192 + x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat) + 2 ^ 256 * (!c4).toNat := by
    rw [← hN]
    omega_using [e0, e1, e2, e3]
  have hD : D3.toNat * 2 ^ 192 + D2.toNat * 2 ^ 128 + D1.toNat * 2 ^ 64 + D0.toNat < 2 ^ 256 := by
    omega_using [D0.isLt, D1.isLt, D2.isLt, D3.isLt]
  have key := Rfc6979.mod_math _ _ _ (!c4) hsum hD hX hN'
  cases c4 <;> simpa using key

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The digest's leftmost 32 bytes, big-endian, in `x11:x10:x9:x8`; `x7 = 0`
and `x15 = sp`. -/
theorem load_ok {t : State} (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) (hn : 32 ≤ dn) :
    WP isa (.block [.movz .x .x7 0 0, .addSp .x15 0,
      .ldr .x .x8 .x1 24, .rev .x8 .x8, .ldr .x .x9 .x1 16, .rev .x9 .x9,
      .ldr .x .x10 .x1 8, .rev .x10 .x10, .ldr .x .x11 .x1 0, .rev .x11 .x11]) t fun u =>
      u.gpr .x7 = 0 ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16 ∧
      u.gpr .x8 = rev64 (t.mem.readW (L.dg + BitVec.ofNat 64 24) 64) ∧
      u.gpr .x9 = rev64 (t.mem.readW (L.dg + BitVec.ofNat 64 16) 64) ∧
      u.gpr .x10 = rev64 (t.mem.readW (L.dg + BitVec.ofNat 64 8) 64) ∧
      u.gpr .x11 = rev64 (t.mem.readW L.dg 64) ∧ Keeps [.x7, .x15, .x8, .x9, .x10, .x11] t u := by
  have d0 := hc.inDg (o := 0) (n := 8) (by omega) (by omega)
  have d8 := hc.inDg (o := 8) (n := 8) (by omega) (by omega)
  have d16 := hc.inDg (o := 16) (n := 8) (by omega) (by omega)
  have d24 := hc.inDg (o := 24) (n := 8) (by omega) (by omega)
  rw [add_ofNat_zero] at d0
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits, Nat.reduceMod,
    Nat.reduceMul, Nat.reduceLT, and_self, show 16 * 0 < Size.x.bits by decide, ite_true,
    Option.bind_some, State.load, State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.mem_write, RegUpd.sp_write, reduceCtorEq, ite_false, hc.sp, h1, add_ofNat_zero,
    d0, d8, d16, d24, Option.map_some, read8, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  rotate_left 6
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
  all_goals first | trivial | rfl

/-- `r = v`, keeping the carry flag. -/
theorem const64c_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (Impl.Mont.AArch64.const64 r v)) s fun t => t.gpr r = v ∧ Keeps [r] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [Impl.Mont.AArch64.const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

/-- One word of `x - n`: the word of `n` in `x12`, then `d = x - x12 - b`. -/
theorem subW_ok (s : State) (d x : Reg) (hx : x ≠ .x12) (v : BitVec 64) (first : Bool) {c : Bool}
    (hc : (if first then true else s.c) = c) :
    WP isa (.block (Impl.Mont.AArch64.const64 .x12 v ++
      ([if first then .subs .x d x .x12 else .sbcs .x d x .x12] : List Instr))) s fun s' =>
      s'.gpr d = Word64.addCarry (s.gpr x) (~~~v) c ∧ s'.c = Word64.carryOut (s.gpr x) (~~~v) c ∧
      Keeps [.x12, d] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (const64c_ok s .x12 v) fun s₁ ⟨e₁, k₁, c₁⟩ => ?_
  refine WP.mono (subc_ok s₁ d x .x12 first (c := c) (by rw [c₁]; exact hc)) fun s₂ ⟨e₂, c₂, k₂⟩ => ?_
  rw [e₁, k₁.gpr x (by simpa using hx)] at e₂ c₂
  exact ⟨e₂, c₂, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩

/-! ## The pieces of `reduce` -/

/-- The loads. -/
abbrev LOAD : List Instr := [.movz .x .x7 0 0, .addSp .x15 0,
  .ldr .x .x8 .x1 24, .rev .x8 .x8, .ldr .x .x9 .x1 16, .rev .x9 .x9,
  .ldr .x .x10 .x1 8, .rev .x10 .x10, .ldr .x .x11 .x1 0, .rev .x11 .x11]

/-- `x - n`, and the mask of its borrow in `x6`. -/
abbrev SUB (c : Cfg) : List Instr :=
  (Impl.Mont.AArch64.const64 .x12 (c.nWord 0) ++
    ([if true then .subs .x .x2 .x8 .x12 else .sbcs .x .x2 .x8 .x12] : List Instr)) ++
  ((Impl.Mont.AArch64.const64 .x12 (c.nWord 1) ++
    ([if false then .subs .x .x3 .x9 .x12 else .sbcs .x .x3 .x9 .x12] : List Instr)) ++
  ((Impl.Mont.AArch64.const64 .x12 (c.nWord 2) ++
    ([if false then .subs .x .x4 .x10 .x12 else .sbcs .x .x4 .x10 .x12] : List Instr)) ++
  ((Impl.Mont.AArch64.const64 .x12 (c.nWord 3) ++
    ([if false then .subs .x .x5 .x11 .x12 else .sbcs .x .x5 .x11 .x12] : List Instr)) ++
    ([.sbc .x .x6 .x7 .x7] : List Instr))))

/-- The selection. -/
abbrev SEL : List Instr :=
  ([(.x8, .x2), (.x9, .x3), (.x10, .x4), (.x11, .x5)] : List (Reg × Reg)).flatMap
    (fun (x, d) => [.logic .eor .x x x d, .logic .and .x x x .x6, .logic .eor .x x x d])

/-- The stores. -/
abbrev STORE : List Instr :=
  [.rev .x11 .x11, .str .x .x11 .x15 fH, .rev .x10 .x10, .str .x .x10 .x15 (fH + 8),
    .rev .x9 .x9, .str .x .x9 .x15 (fH + 16), .rev .x8 .x8, .str .x .x8 .x15 (fH + 24)]

theorem reduce_split (c : Cfg) : c.reduce = LOAD ++ (SUB c ++ (SEL ++ STORE)) := by
  simp only [Cfg.reduce, LOAD, SUB, SEL, STORE, List.append_assoc, List.cons_append, List.nil_append,
    ite_true, Bool.false_eq_true, ite_false]

/-- `x6` is the mask of a borrow, with `x7 = 0`. -/
theorem sbcMask6_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.sbc .x .x6 .x7 .x7]) s fun s' =>
      s'.gpr .x6 = (if (!s.c) = true then BitVec.allOnes 64 else 0) ∧ Keeps [.x6] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, hz, Option.some.injEq, exists_eq_left']
  refine ⟨by cases s.c <;> decide, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `x - n` from `x11:x10:x9:x8` into `x5:x4:x3:x2`, and the mask of its borrow in `x6`. -/
theorem sub_ok (c : Cfg) (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block (SUB c)) s fun s' =>
      let c1 := Word64.carryOut (s.gpr .x8) (~~~(c.nWord 0)) true
      let c2 := Word64.carryOut (s.gpr .x9) (~~~(c.nWord 1)) c1
      let c3 := Word64.carryOut (s.gpr .x10) (~~~(c.nWord 2)) c2
      let c4 := Word64.carryOut (s.gpr .x11) (~~~(c.nWord 3)) c3
      s'.gpr .x2 = Word64.addCarry (s.gpr .x8) (~~~(c.nWord 0)) true ∧
      s'.gpr .x3 = Word64.addCarry (s.gpr .x9) (~~~(c.nWord 1)) c1 ∧
      s'.gpr .x4 = Word64.addCarry (s.gpr .x10) (~~~(c.nWord 2)) c2 ∧
      s'.gpr .x5 = Word64.addCarry (s.gpr .x11) (~~~(c.nWord 3)) c3 ∧
      s'.gpr .x6 = (if (!c4) = true then BitVec.allOnes 64 else 0) ∧
      Keeps [.x12, .x2, .x3, .x4, .x5, .x6] s s' := by
  rw [SUB, WP.block_append_iff]
  refine WP.mono (subW_ok s .x2 .x8 (by decide) _ true (c := true) rfl) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subW_ok s₁ .x3 .x9 (by decide) _ false (c := s₁.c) rfl) fun s₂ ⟨e₂, c₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subW_ok s₂ .x4 .x10 (by decide) _ false (c := s₂.c) rfl) fun s₃ ⟨e₃, c₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subW_ok s₃ .x5 .x11 (by decide) _ false (c := s₃.c) rfl) fun s₄ ⟨e₄, c₄, k₄⟩ => ?_
  have hz₄ : s₄.gpr .x7 = 0 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), hz]
  refine WP.mono (sbcMask6_ok s₄ hz₄) fun s₅ ⟨e₅, k₅⟩ => ?_
  have g9 : s₁.gpr .x9 = s.gpr .x9 := k₁.gpr _ (by decide)
  have g10 : s₂.gpr .x10 = s.gpr .x10 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  have g11 : s₃.gpr .x11 = s.gpr .x11 := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  rw [g9, c₁] at e₂ c₂
  rw [g10, c₂] at e₃ c₃
  rw [g11, c₃] at e₄ c₄
  refine ⟨?_, ?_, ?_, ?_, ?_, (((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans
    (k₃.mono (by sub_regs))).trans ((k₄.mono (by sub_regs)).trans (k₅.mono (by sub_regs)))⟩
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), e₁]
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), e₂]
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), e₃]
  · rw [k₅.gpr _ (by decide), e₄]
  · rw [e₅, c₄]

/-- Each word of `x11:x10:x9:x8` or of `x5:x4:x3:x2`, by the mask in `x6`. -/
theorem sel_ok (s : State) {b : Bool} (h6 : s.gpr .x6 = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block SEL) s fun s' =>
      s'.gpr .x8 = (if b then s.gpr .x8 else s.gpr .x2) ∧ s'.gpr .x9 = (if b then s.gpr .x9 else s.gpr .x3) ∧
      s'.gpr .x10 = (if b then s.gpr .x10 else s.gpr .x4) ∧
      s'.gpr .x11 = (if b then s.gpr .x11 else s.gpr .x5) ∧ Keeps [.x8, .x9, .x10, .x11] s s' := by
  apply WP.of_runBlock
  simp only [SEL, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, h6, sel_mask, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  rotate_left 4
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals first | trivial | rfl

theorem rev64_rev64 (a : BitVec 64) : rev64 (rev64 a) = a := Proof.Gcm.byteRev64_byteRev64 a

/-- Four words stored in the frame's `h`, big-endian. -/
theorem store4 (m : Mem) (B : Addr) (a b c d : BitVec 64) :
    let m' := (((m.writeW (B + BitVec.ofNat 64 144) a).writeW (B + BitVec.ofNat 64 152) b).writeW
      (B + BitVec.ofNat 64 160) c).writeW (B + BitVec.ofNat 64 168) d
    Frame [⟨B + BitVec.ofNat 64 144, 32⟩] m m' ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m' (B + BitVec.ofNat 64 144) 32) =
        (rev64 a).toNat * 2 ^ 192 + (rev64 b).toNat * 2 ^ 128 + (rev64 c).toNat * 2 ^ 64 +
          (rev64 d).toNat := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 240 → y + 8 ≤ 240 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega) (by omega)
  have ct : ∀ x, 144 ≤ x → x + 8 ≤ 176 →
      (⟨B + BitVec.ofNat 64 144, 32⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega) (by omega)
  refine ⟨(((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 144 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 152 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 160 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (ct 168 (by omega) (by omega))), ?_⟩
  rw [Rfc6979.ofBytes_32, Offset.add_add, Offset.add_add, Offset.add_add]
  simp only [Nat.reduceAdd]
  rw [Mem.readW_writeW_sep (sep 144 168 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 144 160 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 144 152 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (sep 152 168 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 152 160 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (sep 160 168 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64, Mem.readW_writeW_self64]
  rfl

/-- `x11:x10:x9:x8`, big-endian, into the frame's `h`. -/
theorem store_ok {t : State} (hc : Ctx L g m₀ t) (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) :
    WP isa (.block STORE) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      (∀ r, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 144, 32⟩] t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 32) =
        (t.gpr .x11).toNat * 2 ^ 192 + (t.gpr .x10).toNat * 2 ^ 128 + (t.gpr .x9).toNat * 2 ^ 64 +
          (t.gpr .x8).toNat := by
  have w0 := hc.inFrW (d := 144) (n := 8) (by omega) (by omega)
  have w1 := hc.inFrW (d := 152) (n := 8) (by omega) (by omega)
  have w2 := hc.inFrW (d := 160) (n := 8) (by omega) (by omega)
  have w3 := hc.inFrW (d := 168) (n := 8) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [STORE, fH, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, Nat.reduceAdd, and_self, ite_true, Option.bind_some,
    State.store, State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.wr_write, RegUpd.mem_write,
    reduceCtorEq, ite_false, h15, Offset.add_add, w0, w1, w2, w3, write8, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r h8 h9 h10 h11 => ?_, (store4 _ _ _ _ _ _).1, ?_⟩
  rotate_left 3
  · simp only [h8, h9, h10, h11, ite_false]
  · rw [(store4 _ _ _ _ _ _).2]
    simp only [rev64_rev64]
  all_goals first | trivial | rfl

theorem nWords (P : RfcHash) :
    ((cfgOf P).nWord 3).toNat * 2 ^ 192 + ((cfgOf P).nWord 2).toNat * 2 ^ 128 +
      ((cfgOf P).nWord 1).toNat * 2 ^ 64 + ((cfgOf P).nWord 0).toNat = Spec.P256.n := by
  simp only [Cfg.nWord, cfgOf]
  decide +kernel

theorem n_ge : 2 ^ 255 ≤ Spec.P256.n := by decide +kernel

theorem dg_ofBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hn : 32 ≤ dn) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg 32) =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg 32) := by
  congr 1
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => (hc.dg_byte hL (by have := List.mem_range.mp hi; omega)).symm

/-- `digest` in `x1`. -/
theorem digestPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.digestPtr) t (Upd L g m₀ t .x1 L.dg) := by
  have p := hc.inFr (d := 192) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.digestPtr, fDigest, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod,
    Nat.reduceLT, and_self, ite_true, State.load, hc.sp, Offset.add_add, Nat.reduceAdd, p, Option.map_some,
    read8, hc.pDg, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .x1) (by decide) rfl rfl rfl rfl fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- A callee-saved register is none of the registers `rs` the code writes. -/
theorem not_pres {r : Reg} (hr : r ∈ preserved) (rs : List Reg) (h : ∀ q ∈ rs, q ∉ preserved) : r ∉ rs :=
  fun h' => h r h' hr

/-- `h`: the digest (at `x1`) modulo `n`, big-endian in the frame. -/
theorem reduce_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) (hn : 32 ≤ dn) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 144, 32⟩] t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 32) =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg 32) % Spec.P256.n := by
  rw [dg_ofBytes hL hc hn, Rfc6979.ofBytes_32, ← nWords P]
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  rw [reduce_split, WP.block_append_iff]
  refine WP.mono (load_ok hc h1 hn) fun u₁ ⟨z₁, f₁, a₁, b₁, c₁, d₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sub_ok (cfgOf P) u₁ z₁) fun u₂ ⟨a₂, b₂, c₂, d₂, m₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok u₂ m₂) fun u₃ ⟨a₃, b₃, c₃, d₃, k₃⟩ => ?_
  have hc₃ : Ctx L g m₀ u₃ := hc.regs hL (k₃.rd.trans (k₂.rd.trans k₁.rd)) (k₃.wr.trans (k₂.wr.trans k₁.wr))
    (k₃.mem.trans (k₂.mem.trans k₁.mem)) (k₃.sp.trans (k₂.sp.trans k₁.sp)) fun r hr _ => by
      have h₁ : r ∉ [Reg.x8, .x9, .x10, .x11] := not_pres hr _ (by decide)
      have h₂ : r ∉ [Reg.x12, .x2, .x3, .x4, .x5, .x6] := not_pres hr _ (by decide)
      have h₃ : r ∉ [Reg.x7, .x15, .x8, .x9, .x10, .x11] := not_pres hr _ (by decide)
      rw [k₃.gpr r h₁, k₂.gpr r h₂, k₁.gpr r h₃]
  have h15 : u₃.gpr .x15 = L.B + BitVec.ofNat 64 16 := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), f₁]
  refine WP.mono (store_ok hc₃ h15) fun u₄ ⟨r₄, w₄, _, _, f₄, v₄⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [r₄, k₃.rd, k₂.rd, k₁.rd]
  · rw [w₄, k₃.wr, k₂.wr, k₁.wr]
  · rw [← k₁.mem, ← k₂.mem, ← k₃.mem]; exact f₄
  · rw [v₄, a₃, b₃, c₃, d₃, a₂, b₂, c₂, d₂, k₂.gpr .x8 (by decide), k₂.gpr .x9 (by decide),
      k₂.gpr .x10 (by decide), k₂.gpr .x11 (by decide), a₁, b₁, c₁, d₁]
    exact reduce_math _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl (by rw [nWords P]; exact n_ge)

end VG.Proof.Ecdsa.Rfc6979.AArch64
