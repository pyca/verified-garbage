import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Deterministic ECDSA on AArch64: the blocks between the calls

`V = 0x01…` and `K = 0x00…` (`initKV_ok`), the number of candidates
(`initCnt_ok`), the arguments of `core` (`coreArgs_ok`), whether to go on
(`goOn_ok`, `again_ok`, `stop_ok`), and the wiping of the frame (`wipe_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ed25519.AArch64 (read_x)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The first `n` of `k` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p k).take n := by
  rw [show k = n + (k - n) by omega, Proof.Hmac.Common.bytesAt_add, List.take_left']
  simp [Spec.Sha256.bytesAt]

/-- The `8 k` bytes at `q`, each of whose words is `w`. -/
theorem bytesAt_of_readW (m : Mem) (q : Addr) (w : BitVec 64) {k : Nat}
    (h : ∀ j < k, m.readW (q + BitVec.ofNat 64 (8 * j)) 64 = w) :
    Spec.Sha256.bytesAt m q (8 * k) = (List.range (8 * k)).map fun i => w.extractLsb' (8 * (i % 8)) 8 := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [show i = 8 * (i / 8) + i % 8 by omega, Proof.Weierstrass.byte_word m q (i / 8) (Nat.mod_lt _ (by decide)),
    h _ (by omega)]
  congr 2; omega

theorem sep8 (B : Addr) {x y : Nat} (h : x + 8 ≤ y ∨ y + 8 ≤ x) (h₁ : x + 8 ≤ 256) (h₂ : y + 8 ≤ 256) :
    Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
  Offset.sep B h (by omega) (by omega)

/-- A word stored at `sp + o`, through `x15`. -/
theorem str15_ok {u : State} (hwr : u.wr = [L.FR, L.LR, L.OUT, L.SCR])
    (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) {t : Reg} {o : Nat} (ho : o % 8 = 0) (ho' : o + 8 ≤ 224) :
    WP isa (.block [.str .x t .x15 o]) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.gpr = u.gpr ∧ u'.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (16 + o)) (u.gpr t) := by
  have w : InRegions u.wr (L.B + BitVec.ofNat 64 (16 + o)) 8 :=
    ⟨L.FR, by rw [hwr]; simp, Offset.contains _ (by omega) (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, ho,
    show o < 4096 * 8 by omega, and_self, ite_true, Option.bind_some, State.store, State.read, Size.bits,
    BitVec.setWidth_eq, h15, Offset.add_add, w, write8, Option.some.injEq, exists_eq_left']

/-! ## `V` and `K` -/

theorem kvN_ok {u : State} (hwr : u.wr = [L.FR, L.LR, L.OUT, L.SCR]) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {a b : BitVec 64} (ha : u.gpr .x9 = a) (hb : u.gpr .x10 = b) : ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap fun j => [.str .x .x9 .x15 (fV + 8 * j),
      .str .x .x10 .x15 (fK + 8 * j)])) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 128⟩] u.mem u'.mem ∧
      ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (80 + 8 * j)) 64 = a ∧
        u'.mem.readW (L.B + BitVec.ofNat 64 (16 + 8 * j)) 64 = b
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (kvN_ok hwr h15 ha hb k (by omega)) fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hv₁⟩ => ?_
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (str15_ok (u := u₁) (hwr₁.trans hwr) (by rw [hg₁, h15]) (t := .x9) (o := fV + 8 * k)
      (by simp only [fV]; omega) (by simp only [fV]; omega)) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    refine WP.mono (str15_ok (u := u₂) ((hwr₂.trans hwr₁).trans hwr) (by rw [hg₂, hg₁, h15]) (t := .x10)
      (o := fK + 8 * k) (by simp only [fK]; omega) (by simp only [fK]; omega))
      fun u₃ ⟨hrd₃, hwr₃, hsp₃, hg₃, hm₃⟩ => ?_
    simp only [fV, fK, hg₂, hg₁, ha, hb, Nat.zero_add, ← Nat.add_assoc, Nat.reduceAdd] at hm₂ hm₃
    refine ⟨hrd₃.trans (hrd₂.trans hrd₁), hwr₃.trans (hwr₂.trans hwr₁), hsp₃.trans (hsp₂.trans hsp₁),
      hg₃.trans (hg₂.trans hg₁), hf₁.trans ?_, fun j hj => ?_⟩
    · rw [hm₃, hm₂]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    rw [hm₃, hm₂]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (sep8 _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep8 _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep8 _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep8 _ (by omega) (by omega) (by omega)) (by decide)]
      exact hv₁ j hj
    · rw [Mem.readW_writeW_sep (sep8 _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64, Mem.readW_writeW_self64]
      exact ⟨rfl, rfl⟩

theorem kv_bytes (m : Mem) (q : Addr) (w : BitVec 64) (o : Nat)
    (h : ∀ j < 8, m.readW (q + BitVec.ofNat 64 (o + 8 * j)) 64 = w) :
    Spec.Sha256.bytesAt m (q + BitVec.ofNat 64 o) 64 =
      (List.range 64).map fun i => w.extractLsb' (8 * (i % 8)) 8 :=
  bytesAt_of_readW (k := 8) m _ w fun j hj => by rw [Offset.add_add]; exact h j hj

theorem replicate_take (n k : Nat) (b : Byte) (h : n ≤ k) : (List.replicate k b).take n = List.replicate n b := by
  rw [List.take_replicate, Nat.min_eq_left h]

theorem movz_imm {n : Nat} (hn : n < 2 ^ 16) :
    (BitVec.ofNat 16 n).setWidth Size.x.bits <<< (16 * 0) = BitVec.ofNat 64 n := movz_val hn

/-- `V = 0x01…` and `K = 0x00…`: their first `n` bytes, for any `n ≤ 64`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 16, 128⟩] t.mem t'.mem ∧
      (∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 80) n = List.replicate n 1) ∧
      ∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) n = List.replicate n 0 := by
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  rw [Cfg.initKV, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (const64c_ok t .x9 _) fun u₁ ⟨e₁, k₁, _⟩ => ?_
  have h₂ : WP isa (.block [.movz .x .x10 0 0, .addSp .x15 0]) u₁ fun u => u.rd = t.rd ∧ u.wr = t.wr ∧
      u.sp = t.sp ∧ u.mem = t.mem ∧ u.gpr .x9 = BitVec.ofNat 64 0x0101010101010101 ∧ u.gpr .x10 = 0 ∧
      u.gpr .x15 = L.B + BitVec.ofNat 64 16 := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
      show (0 : Nat) < 4096 by decide, ite_true, RegUpd.gpr_write, RegUpd.sp_write, reduceCtorEq, ite_false,
      k₁.sp, hc.sp, Option.some.injEq, exists_eq_left']
    exact ⟨by first | atriv | exact k₁.rd, by first | atriv | exact k₁.wr, by first | atriv | exact k₁.sp,
      by first | atriv | exact k₁.mem, by first | atriv | exact e₁, by atriv,
      by first | atriv | rw [BitVec.setWidth_eq, BitVec.add_zero]⟩
  refine WP.mono h₂ fun u ⟨hrd, hwr, _, hm, ha, hb, h15⟩ => WP.mono (kvN_ok (hwr.trans hc.wr) h15 ha hb 8
    (by omega)) fun u' ⟨hrd', hwr', _, _, hf, hv⟩ => ⟨hrd'.trans hrd, hwr'.trans hwr, hm ▸ hf, fun n hn => ?_,
      fun n hn => ?_⟩
  · rw [bytesAt_take _ _ (k := 64) hn, show (80 : Nat) = 80 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).1, show (List.range 64).map
        (fun i => (BitVec.ofNat 64 0x0101010101010101).extractLsb' (8 * (i % 8)) 8) = List.replicate 64 1 by decide,
      replicate_take _ _ _ hn]
  · rw [bytesAt_take _ _ (k := 64) hn, show (16 : Nat) = 16 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).2, show (List.range 64).map
        (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) = List.replicate 64 0 by decide,
      replicate_take _ _ _ hn]

/-! ## The number of candidates -/

/-- The number of candidates left, in the frame. -/
abbrev cnt {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 192) 64

theorem initCnt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).initCnt) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 192, 8⟩] t.mem t'.mem ∧ cnt L t'.mem = BitVec.ofNat 64 8 := by
  have w := hc.inFrW (d := 192) (n := 8) (by omega) (by omega)
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  apply WP.of_runBlock
  simp only [Cfg.initCnt, cfgOf, fCnt, runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.x.bits by decide, show (0 : Nat) < 4096 by decide, ite_true, addr, Size.bytes,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, Option.bind_some, State.store, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq, ite_false, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, RegUpd.rd_write, hc.sp, BitVec.add_zero, Offset.add_add, Nat.reduceAdd, w,
    write8, Option.some.injEq, exists_eq_left']
  refine ⟨by atriv, by atriv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    ?_⟩
  simp only [cnt, Mem.readW_writeW_self64]
  decide

/-! ## `core`'s arguments -/

theorem coreArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.coreArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .x0 = L.out ∧
      t'.gpr .x1 = L.d ∧ t'.gpr .x2 = L.dg ∧ t'.gpr .x3 = L.B + BitVec.ofNat 64 80 ∧ t'.gpr .x4 = L.scr := by
  have p0 := hc.inFr (d := 224) (by omega) (by omega)
  have p1 := hc.inFr (d := 216) (by omega) (by omega)
  have p2 := hc.inFr (d := 208) (by omega) (by omega)
  have p3 := hc.inFr (d := 200) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.coreArgs, Cfg.fr, fOut, fD, fDigest, fV, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod, Nat.reduceLT, and_self, ite_true,
    State.load, RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    reduceCtorEq, ite_false, hc.sp, Offset.add_add, Nat.reduceAdd, p0, p1, p2, p3, Option.map_some,
    read8, hc.pOut, hc.pD, hc.pDg, hc.pScr, BitVec.setWidth_eq, Option.some.injEq,
    exists_eq_left']
  refine ⟨hc.regs hL rfl rfl rfl rfl fun r hr h30 => ?_, trivial⟩
  have h₁ : r ∉ [Reg.x0, .x1, .x2, .x3, .x4] := not_pres hr _ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h₁
  simp only [RegUpd.gpr_write, h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2, ite_false]

/-! ## Whether to go on -/

theorem decr_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block [.ldrSp .x9 fCnt, .subImm .x .x9 .x9 1, .addSp .x15 0, .str .x .x9 .x15 fCnt]) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.gpr .x9 = cnt L t.mem - 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x15 → u.gpr r = t.gpr r) ∧
      u.mem = t.mem.writeW (L.B + BitVec.ofNat 64 192) (cnt L t.mem - 1) := by
  have r := hc.inFr (d := 192) (by omega) (by omega)
  have w := hc.inFrW (d := 192) (n := 8) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [fCnt, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, State.load, hc.sp, Offset.add_add, Nat.reduceAdd, r, Option.map_some, read8, State.read,
    Size.bits, BitVec.setWidth_eq, show (1 : Nat) < 4096 by decide, show (0 : Nat) < 4096 by decide,
    RegUpd.gpr_write, RegUpd.sp_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, reduceCtorEq,
    ite_false, BitVec.add_zero, addr, Size.bytes, Nat.reduceMul, Option.bind_some, State.store, w, write8,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl, fun r h9 h15 => by simp only [h9, h15, ite_false], rfl⟩

theorem mask_w (a : BitVec 32) :
    (0 : BitVec 64) + ~~~0 + BitVec.ofNat 64 (decide (2 ^ 32 ≤ a.toNat + (~~~(1 : BitVec 32)).toNat +
      true.toNat)).toNat =
      if a = 0 then BitVec.allOnes 64 else 0 := by
  by_cases ha : a = 0
  · subst ha; decide
  · have : 1 ≤ a.toNat := by
      have : a.toNat ≠ 0 := fun h => ha (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    have e : (~~~(1 : BitVec 32)).toNat = 2 ^ 32 - 2 := by decide
    rw [decide_eq_true (by simp only [Bool.toNat_true]; omega :
      2 ^ 32 ≤ a.toNat + (~~~(1 : BitVec 32)).toNat + true.toNat)]
    simp only [ha, ite_false]
    decide

theorem goOn_flag (a : BitVec 32) (c : BitVec 64) :
    (((if a = 0 then BitVec.allOnes 64 else 0) &&& c) != 0) = decide (a = 0 ∧ c ≠ 0) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
  by_cases ha : a = 0
  · simp only [ha, ite_true, BitVec.allOnes_and, true_and]
  · simp only [ha, ite_false, ne_eq, false_and, iff_false, Decidable.not_not]
    apply BitVec.eq_of_toNat_eq; simp

theorem movz0 : BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) = 0 := by decide
theorem movz1 : BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 0) = 1 := by decide
theorem one32 : BitVec.setWidth 32 (1 : BitVec 64) = 1 := by decide

/-- `x12 ≠ 0` iff `w0 = 0` and `x9 ≠ 0`. -/
theorem flag_ok (t : State) :
    WP isa (.block [.movz .x .x7 0 0, .movz .x .x10 1 0, .subs .w .x16 .x0 .x10, .sbc .x .x11 .x7 .x7,
      .logic .and .x .x12 .x11 .x9]) t fun u =>
      (u.gpr .x12 != 0) = decide ((t.gpr .x0).setWidth 32 = 0 ∧ t.gpr .x9 ≠ 0) ∧
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.mem = t.mem ∧
      (∀ r, r ≠ .x7 → r ≠ .x10 → r ≠ .x16 → r ≠ .x11 → r ≠ .x12 → u.gpr r = t.gpr r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide, ite_true,
    State.read, Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.rd_addWithCarry,
    RegUpd.wr_addWithCarry, RegUpd.sp_addWithCarry, RegUpd.mem_addWithCarry, reduceCtorEq, ite_false, movz0, movz1,
    one32, mask_w, goOn_flag, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h7 h10 h16 h11 h12 => ?_⟩
  simp only [h7, h10, h16, h11, h12, ite_false]

theorem eval_nonzero (t : State) : isa.eval (.nonzero .x .x12) t = some (t.gpr .x12 != 0) := by
  show some ((t.gpr .x12).setWidth 64 != 0) = _
  rw [BitVec.setWidth_eq]

/-- One candidate fewer; `x12 ≠ 0` iff the signature failed and candidates are left. -/
theorem goOn_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.goOn) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 192, 8⟩] t.mem t'.mem ∧ cnt L t'.mem = cnt L t.mem - 1 ∧
      t'.gpr .x0 = t.gpr .x0 ∧
      isa.eval (.nonzero .x .x12) t' = some (decide ((t.gpr .x0).setWidth 32 = 0 ∧ cnt L t.mem - 1 ≠ 0)) := by
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  show WP isa (.block ([.ldrSp .x9 fCnt, .subImm .x .x9 .x9 1, .addSp .x15 0, .str .x .x9 .x15 fCnt] ++
    [.movz .x .x7 0 0, .movz .x .x10 1 0, .subs .w .x16 .x0 .x10, .sbc .x .x11 .x7 .x7,
      .logic .and .x .x12 .x11 .x9])) t _
  rw [WP.block_append_iff]
  refine WP.mono (decr_ok hc) fun u ⟨hrd, hwr, hsp, h9, hg, hm⟩ => WP.mono (flag_ok u)
    fun u' ⟨hf, hrd', hwr', hsp', hm', hg'⟩ => ⟨hrd'.trans hrd, hwr'.trans hwr, ?_, ?_, ?_, ?_⟩
  · rw [hm', hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · simp only [cnt, hm', hm, Mem.readW_writeW_self64]
  · rw [hg' _ (by decide) (by decide) (by decide) (by decide) (by decide), hg _ (by decide) (by decide)]
  · rw [eval_nonzero, hf, h9, hg _ (by decide) (by decide)]

/-- Go on. -/
theorem again_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.again) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      isa.eval (.nonzero .x .x12) t' = some true :=
  WP.mono (movz_ok hL hc (d := .x12) (by decide) (n := 1) (by decide)) fun _ h =>
    ⟨h.ctx, h.mem, by rw [eval_nonzero, h.val]; rfl⟩

/-- Stop. -/
theorem stop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.stop) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      isa.eval (.nonzero .x .x12) t' = some false ∧ t'.gpr .x0 = t.gpr .x0 :=
  WP.mono (movz_ok hL hc (d := .x12) (by decide) (n := 0) (by decide)) fun _ h =>
    ⟨h.ctx, h.mem, by rw [eval_nonzero, h.val]; rfl, h.keep _ (by decide)⟩

/-! ## Wiping the frame -/

theorem zeroN_ok {u : State} (hwr : u.wr = [L.FR, L.LR, L.OUT, L.SCR]) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) :
    ∀ k ≤ 22, WP isa (.block ((List.range k).map fun j => .str .x .x14 .x15 (8 * j))) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 176⟩] u.mem u'.mem
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_ok hwr h15 k (by omega)) fun u₁ ⟨hrd, hwr₁, hsp, hg, hf⟩ => ?_
    refine WP.mono (str15_ok (u := u₁) (hwr₁.trans hwr) (by rw [hg, h15]) (t := .x14) (o := 8 * k) (by omega)
      (by omega)) fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ⟨hrd₂.trans hrd, hwr₂.trans hwr₁, hsp₂.trans hsp,
        hg₂.trans hg, hf.trans ?_⟩
    rw [hm₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- `K`, `V` and `h` cleared, keeping `x0`. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.wipe) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .x0 = t.gpr .x0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 176⟩] t.mem t'.mem := by
  have h := Ctx.of_keep (Q := fun t' => t'.gpr .x0 = t.gpr .x0) hL hc (is := Cfg.wipe)
    (ws := [⟨L.B + BitVec.ofNat 64 16, 176⟩]) ?_ (by rfl) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  · exact WP.mono h fun _ ⟨hc', hf, ha⟩ => ⟨hc', ha, hf⟩
  rw [Cfg.wipe, WP.block_append_iff]
  have h₁ : WP isa (.block [.addSp .x15 0, .movz .x .x14 0 0]) t fun u => u.rd = t.rd ∧
      u.wr = t.wr ∧ u.sp = t.sp ∧ u.mem = t.mem ∧ u.gpr .x0 = t.gpr .x0 ∧
      u.gpr .x15 = L.B + BitVec.ofNat 64 16 := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
      show (0 : Nat) < 4096 by decide, ite_true, RegUpd.gpr_write, RegUpd.sp_write, reduceCtorEq, ite_false,
      hc.sp, Option.some.injEq, exists_eq_left']
    exact ⟨by atriv, by atriv, by atriv, by atriv, by atriv, by rw [BitVec.setWidth_eq, BitVec.add_zero]⟩
  exact WP.mono h₁ fun u ⟨hrd, hwr, hsp, hm, ha, h15⟩ => WP.mono (zeroN_ok (hwr.trans hc.wr) h15 22 (by omega))
    fun u' ⟨hrd', hwr', _, hg, hf⟩ => ⟨hrd'.trans hrd, hwr'.trans hwr, hm ▸ hf, by rw [hg, ha]⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64
